

include("trees.jl")

import Base.==
import Base.isequal
import Base.hash
import Base.getindex

# A "Signature" is a type signature (I didn't want to use language which would
# overlap with the Julia type system).

abstract type Signature end

struct ESig <: Signature # The empty signature. This is compatible with no contents, analogous to an invalid region.
end

struct VSig <: Signature # Signature of a first-order signia variable.
end

# Signature of a tuple variable. The tuple of types can be specified
# or unspecified. Both specified and unspecified TSigs have a set of
# "negative" specifications, which the signature's specification is
# constrained not to be.

struct UnspecifiedTSig <: Signature
  antispec::Set{Vector{Signature}}
end

UnspecifiedTSig() = UnspecifiedTSig(Set{Vector{Signature}}())

struct SpecifiedTSig <: Signature
  spec::Vector{Signature} # When we specify, it's actually a vector of signatures.
  antispec::Set{Vector{Signature}}
end

SpecifiedTSig(v::Vector) = SpecifiedTSig(v, Set{Vector{Signature}}())

# Signature of a predicate variable.
#
# Each predicate will correspond to an int, determined during rulesystem
# compilation. In addition, predicates with N universal variables will be
# indexed by N additional integers (so N+1 total). PSigs encode a range in each
# index, so, they hold a vector of ranges (UnitRange, specifically). The first
# range in the vector represents the predicate name, and any others present
# represent universal variables.
#
# The range is inclusive. Note that the "min" and "max" of a UnitRange r are
# given by r.start and r.stop.
#
# A vector cut short is to be understood as having unrestricted range in the
# remaining variables, if there are any, so [1:100] can match with [4:4, 2:50]
# for example. (This is important since it would otherwise be difficult to
# represent the thing that can match with any predicate whatsoever, [].)
# However, I will have to be careful not to create ambiguity, EG about whether
# a universal variable has really been eliminated.
#
# PSigs and TSigs together will be the only sig types to participate
# nontrivially in the VarLoc addressing system: both of these keep further dims
# inside of themselves, and so, VarLoc addressing recurs on both of these types
# (whereas any other sig types merely get located by a VarLoc address).

struct PSig <: Signature
  ranges::Array{UnitRange{Int64}, 1}
end

const largest_p = div(typemax(Int),2)
pwir(x::Int) = max(min(x, largest_p), 1)
rwir(r::UnitRange) = pwir(r.start):pwir(r.stop)
awir(a::Array{UnitRange}) = map(rwir, a)

#PSig(a::Array) = map(rwir, a)
PSig(x::UnitRange) = PSig([rwir(x)])
PSig(x::Int, y::Int) = PSig([pwir(x):pwir(y)])
PSig(x::Int) = PSig([pwir(x):pwir(x)])

getindex(p::PSig, i::Int) = p.ranges[i]



# An isolated usig. While I don't intend to support isolated usigs in rule
# syntax, I will need them to represent some rulespaces.

struct USig <: Signature
  range::UnitRange{Int64}
end

USig() = USig(1:largest_p)

function ==(s1::Signature, s2::Signature)
  t1 = typeof(s1)
  t2 = typeof(s2)
  if t1 == t2
    if t1 == ESig
      return true
    elseif t1 == VSig
      return true
    elseif t1 == UnspecifiedTSig
      return s1.antispec == s2.antispec
    elseif t1 == SpecifiedTSig
      return s1.spec == s2.spec && s1.antispec == s2.antispec
    elseif t1 == PSig
      return s1.ranges == s2.ranges
    elseif t1 == USig
      return s1.range == s2.range
    else
      error("Unrecognized signature in signature equality check.")
    end
  else
    return false
  end
end

isequal(s1::Signature, s2::Signature) = s1==s2

# To correctly use signatures in dictionaries, I need to redefine hash.

function hash(s::Signature)
  t = typeof(s)
  if t == ESig
    return hash(ESig)
  elseif t == VSig
    return hash(VSig)
  elseif t == UnspecifiedTSig
    hc = hash(UnspecifiedTSig)
    for i in s.antispec
      hc = hc + 22037*hash(i)
    end
    return hash(hc)
  elseif t == SpecifiedTSig
    hc = hash(SpecifiedTSig)
    for i in s.spec
      hc = hc*22037 + hash(i)
    end
    for i in s.antispec
      hc = hc + 2207*hash(i)
    end
    return hash(hc)
  elseif t == PSig
    return hash(hash(PSig) + hash(s.ranges))
  elseif t == USig
    return hash(hash(USig) + hash(s.range))
  else
    return error("Could not compute hash for $s.")
  end
end


# I need a way to refer to locations in a signature. This is
# done with a vector of ints giving arg numbers. So, for example,
# the top-level predicate is a loc of [1]. The top-level arg list is [2]. The
# 3rd argument to the predicate is [2, 3], since this is nested within the arg
# list. And so on. This format is formalized as the type VarLoc.
#
# As mentioned previously, the two types of sig which can have an internal
# address are SpecifiedTSigs and PSigs. SpecifiedTSigs are what holds every
# other type of sig, and can be nested arbitrarily. PSigs don't actually hold
# any sigs, but a VarLoc address can point to their universal variables.
# So for example, for the pattern pred(x,y) the address [1] refers to the PSig,
# but [1,1] refers to the dimension for the name "pred" specifically, while
# [1,2], [1,3], and so on would refer to universal variables indexing instances.

VarLoc = Vector{Int}

# A VarMap gives the dimension number for each first-order variable in a
# signature, as given by their VarLoc.

VarMap = Dict{VarLoc, Int}

# A domain gives an area where values are defined. 'sig' is the signature under
# which the values are defined, which determines the spatial dimensions and the
# predicates involved. 'reg' gives confines within those spatial dimensions.
# 'map' gives the relationship between dim-nums in reg and variable locations in
# sig.

struct Domain
  sig::Signature
  reg::Region
  map::VarMap
end

# Constructors for cases with less arguments.

Domain(s::Signature, r::Region) = Domain(s, r, Dict{VarLoc, Int}(map(((varloc,n) -> varloc=>n), sig_vars(s), collect(1:length(sig_vars(s))))))
Domain(s::Signature) = Domain(s, boundless_reg(length(sig_vars(s))))

function ==(d1::Domain, d2::Domain)
  if d1.sig != d2.sig
    return false
  else
    (combined_map, reg2) = bring_domain_and_leaf_in_line(d1.map, d2.map, d2.reg)
    return d1.reg == d2.reg
  end
  # return d1.sig == d2.sig && d1.map == d2.map && d1.reg == d2.reg
end


# MemTree is an "upper level" of memory organization above the BSPTrees, which
# splits on predicate variables and on tuple variable signatures. The "leaves"
# of the MemTree are BSPTrees. Conceptually, this is just an ordering heuristic;
# we could split on ordinary variable dimensions, predicate variables, and tuple
# variables in any order; so we could have one tree type rather than a
# MemTree vs BSPTree. It seems like a good heuristic  to always split on the
# regular first-order variables last, though.

# As with BSPTree vs BSPNode, there is MemTree vs MemNode. A MemTree carries a
# signature, which is like the boundary of a MemNode. The signature of the
# memory tree will be:
# SpecifiedTSig([PSig((1,10)), UnspecifiedTSig()]), but with whatever number of
# predicates is present rather than "10".
# This is because all predicates have a name and arg list (though, it's
# possible the arg list will be []).

abstract type MemNode end

struct MemTree
  domain::Domain
  root::MemNode
end

function ==(m1::MemTree, m2::MemTree)
  return m1.domain == m2.domain && m1.root == m2.root
end

MemTree(d::Domain, m::MemTree) = MemTree(intersection(d, m.domain), m.root)
MemTree(d::Domain, v::Number) = MemTree(d,MemLeaf(LeafNode(v), d.map))

# The split nodes for the MemTree have to specify the location of the variable
# they're splitting on in the recursive signature structure.

# In addition, a structure for organizing the different split values is needed.
# I'm currently using a Dict for the TSplits. For reference purposes, here are
# the common manipulations for a Dict d: Dict construction looks like
# Dict(key1=>val1, key2=>val2). Given a key (an int i for a dimensionality, here),
# access the value with d[key] if you want to throw an error for non-keys, or
# get(d, key, default) to output a defauld value in that case instead. keys(d)
# given an iterator for the keys; values(d) for the values. haskey(d, k) checks
# if a key exists. A Dict can be extended by Dict(union(d, Dict(newkey=>newval))).

struct TSplit <: MemNode
  var::VarLoc # A vector of ints giving the recursive location of the variable being split on.
  branches::Dict{SpecifiedTSig, MemNode} # The SpecifiedTSig should ONLY be a one-level signature, IE, all internal TSigs should be UnspecifiedTSigs. It should also have an emply antisig.
  default::MemNode
end

function ==(t1::TSplit,t2::TSplit)
  if t1.var != t2.var || t1.default != t2.default
    return false
  end
  keys1 = keys(t1.branches)
  keys2 = keys(t2.branches)
  sd = symdiff(keys1, keys2)
  if length(sd) > 0
    return false
  else
    for key in keys1
      if t2.branches[key] != t1.branches[key]
        return false
      end
    end
    return true
  end
end


# PSplit uses the same var location notation, but splits in binary-tree manner
# rather than with a dictionary. As with BSPTrees, the positive branch is
# inclusive and the negative is exclusive; if a query with range (3,10) splits
# with loc 6, the pos query will be (6,10) while the neg will be
# (3,5).
#
# Keep in mind that VarLocs index into the dimensions of a PSig. So if a PSig
# has VarLoc [3,2], any PSiplits refining that PSig should have one-longer
# VarLocs. [3,2,1] would split on the actual predicate name; [3,2,2] would split
# on the first universal variable; and so on.
#
# NOTE: The VarLoc for a PSplit can now point to a USig! I still want to treat
# this as a TSplit, since it is a split on a predicate variable.

struct PSplit <: MemNode # Splitting on a predicate variable.
  var::VarLoc # A vector of ints giving the recursive location of the variable being split on.
  loc::Int # Split between pos and neg range; pos gets the split loc.
  neg::MemNode
  pos::MemNode
end

function ==(p1::PSplit, p2::PSplit)
  return p1.var == p2.var && p1.loc == p2.loc && p1.neg == p2.neg && p1.pos == p2.pos
end

struct MemLeaf <: MemNode
  value::BSPNode
  map::VarMap
end

# Constructors for simpler cases.

MemLeaf(f::Float64, m::VarMap) = MemLeaf(LeafNode(f), m)
MemLeaf(v::BSPNode) = MemLeaf(v, Dict{VarLoc, Int}()) # this seems like it could cause trouble
MemLeaf(f::Float64) = MemLeaf(LeafNode(f), Dict{VarLoc, Int}())
MemLeaf(h::Hyper) = MemLeaf(LeafNode(h), Dict{VarLoc, Int}())
MemLeaf(i::Int) = MemLeaf(LeafNode(i), Dict{VarLoc, Int}())

function ==(l1::MemLeaf, l2::MemLeaf)
  if l1.map == l2.map
    return l1.value == l2.value
  else
    (combined_map, reordering) = bring_m2_in_line(l1.map, l2.map)
    (rv, l) = reorder_vect_and_targ_length(combined_map, reordering)
    return l1.value == reorder(l2.value, rv, l)
  end
end


# Takes a tuple representation of the signature, like (:v, (:v, :t), :t) and
# turns it into a proper signature. Predicate variables are specified as a
# quoted vector, so for example sig((:[0:10], :v)) will become
# SpecifiedTSig([PSig([0:10]), VSig()]). For convenience, numbers like 10 will
# become singleton ranges, like :[10:10].

function sig(v)
  if v == :e # abbreviation for esig
    return ESig()
  elseif v == :v # abbreviation for vsig
    return VSig()
  elseif v == :p # unbounded psig
    return PSig([1:largest_p])
  elseif typeof(v) <: Expr # returns true for quoted vectors and false for everything else here; bounded psig
    a = v.args
    for i=1:length(a)
      if typeof(a[i]) == Int # for convenience, convert single numbers to a singleton range
        a[i] = a[i]:a[i]
      else
        a[i] = eval(a[i]) # if it's a unitrange, we need to eval the unitrange because it's given to us quoted
      end
    end
    return PSig(a)
  elseif typeof(v) <: Int64 # also psig
    return PSig([v:v])
  elseif v == :t # abbreviation for unspecified tsig
    return UnspecifiedTSig()
  elseif v == :u # uvar
    return USig()
  elseif typeof(v) <: Tuple # recursion
    return SpecifiedTSig([map((x -> sig(x)), v)...])
  elseif typeof(v) <: Signature
    return v
  else
    error("sig() doesn't know how to convert to signature: $v")
  end
end

# sigv undoes the operation of the previous. Does not show antispecs.

function sigv(s)
  if s == ESig()
    return :e
  elseif s == VSig()
    return :v
  elseif typeof(s) == PSig
    return :[$(s.ranges...)]
  elseif s == UnspecifiedTSig()
    return :t
  elseif typeof(s) == USig
    return s.range
  else
    return tuple(map((x -> sigv(x)), s.spec)...)
  end
end

# A similar notation for domains.

function dom(v)
  if v == :e
    return Domain(ESig(), boundless_reg(0), Dict{VarLoc, Int}())
  elseif typeof(v) <: Vector # first-order variable
    return Domain(VSig(), rect_region([v[1]], [v[2]]), Dict(Int[]=>1))
  elseif v == :v # unbounded first-order variable
    return Domain(VSig())
  elseif v == :p # unbounded predicate variable
    return Domain(PSig([1:largest_p]))
  elseif typeof(v) == Expr # bound predicate variable
    a = v.args
    for i=1:length(a)
      a[i] = eval(a[i]) # we need to eval it, because it was quoted
      if typeof(a[i]) == Int # for convenience, convert single numbers to a singleton range
        a[i] = a[i]:a[i]
      end
    end
    return Domain(PSig(a), boundless_reg(0), Dict{VarLoc, Int}())
  elseif typeof(v) <: Int64 # also pred
    return Domain(PSig([v:v]), boundless_reg(0), Dict{VarLoc, Int}())
  elseif v == :t # unspecified tuple variable
    return Domain(UnspecifiedTSig(), boundless_reg(0), Dict{VarLoc, Int}())
  elseif typeof(v) <: Tuple # specified tuple variable
    pieces = [map((x -> dom(x)), v)...]
    # now we need to construct the sig, reg and map from the domains we get for each piece of the tuple.
    new_sig = SpecifiedTSig(map((x->x.sig), pieces))
    dim_count = 0
    new_reg = boundless_reg(0)
    new_map = Dict{VarLoc,Int}()
    for i=1:length(pieces)
      transformed_map = map((pair -> vcat([i], pair[1])=>(pair[2]+dim_count)), [pieces[i].map...])
      new_map = Dict(union(new_map, transformed_map))
      r = pieces[i].reg
      transformed_reg = reorder(r, collect(dim_count+1:dim_count+r.dimensionality), dim_count+r.dimensionality)
      new_reg = reorder(new_reg, collect(1:dim_count), dim_count+r.dimensionality)
      new_reg = intersection(new_reg, transformed_reg)
      dim_count = dim_count + r.dimensionality
    end
    return Domain(new_sig, new_reg, new_map)
  elseif typeof(v) == Domain
    return v
  elseif typeof(v) <: Signature
    return Domain(v, boundless_reg(0), Dict{VarLoc, Int}())
  else
    return error("dom() doesn't know how to convert to domain: $v")
  end
end

# Notations for conveniently constructing memtrees. This is only intended to
# work for BSP content which is already in standard variable order.

ml(v) = MemLeaf(v)
#ml(v,m) = MemLeaf(v,m)

ts(v::VarLoc,b,d) = TSplit(v,Dict{SpecifiedTSig, MemNode}(map((pair -> flatten_signature(pair[1])=>pair[2]), [b...])),d)

ps(v::VarLoc,l,n,p) = PSplit(v,l,n,p)

function mt(d,n)
  if empty_domain(d)
    return MemTree(d, n)
  elseif typeof(n) == MemLeaf
    return MemTree(d, MemLeaf(n.value, standard_varmap(d.sig)))
  elseif typeof(n) == TSplit
    map_fn = (branch -> branch[1]=>(mt(follow_tuple_branch(MemTree(d,n), branch).domain, branch[2]).root))
    new_branches = Dict(map(map_fn, [n.branches...]))
    new_def = mt(follow_tuple_default(MemTree(d,n)).domain, n.default).root
    return MemTree(d, TSplit(n.var, new_branches, new_def))
  elseif typeof(n) == PSplit
    new_neg = mt(takeneg(MemTree(d,n)).domain, n.neg).root
    new_pos = mt(takepos(MemTree(d,n)).domain, n.pos).root
    return MemTree(d, PSplit(n.var, n.loc, new_neg, new_pos))
  else
    return mt(d, ml(n))
  end
end


# `access` implements the location system which is used by splits (and which
# will be used by some other functions, I'm sure).

# Given a VarLoc, 'access' gives you the sub-signature at that location. Note
# that this operation doesn't always return a signature: in the case of VarLocs
# pointing to dimensions inside of a PSig, a UnitRange is returned instead.

function access(s::Signature, l::VarLoc)
  for i in l
    if typeof(s)==SpecifiedTSig
      s = s.spec[i]
    else # should be a PSig
      if i <= length(s.ranges)
        return s.ranges[i]
      else
        return 1:largest_p
      end
    end
  end
  return s
end

# `access_defined` checks whether there is anything to access at a given
# location-vector. IE, it checks whether the tree shape of the signature has
# any node corresponding to the given location. Keep in mind that this may
# return "false" for valid addresses, when the address points to a predicate
# dimension (within a predicate variable).
#=
function access_defined(s::Signature, l::VarLoc)
  for i in l
    if !(typeof(s)==SpecifiedTSig) || i > length(s.spec) || i < 1
      return false
    else
      s = s.spec[i]
    end
  end
  return true
end =#

# version of "access_defined" that returns true for all valid addresses (IE
# including predicate dimension addresses), rather than only those which point
# to a signature.

function access_defined(s::Signature, l::VarLoc)
  for i = 1:length(l)
    if typeof(s) == SpecifiedTSig
      if l[i] > length(s.spec)
        return false
      elseif l[i] < 1
        return false
      else
        s = s.spec[l[i]]
      end
    elseif typeof(s) == PSig
      if l[i] > length(s.ranges)
        return false
      elseif l[i] < 1
        return false
      else
        s = USig(s.ranges[l[i]])
      end
    else
      return false
    end
  end
  return true
end

# spec_allowed checks whether a TSig spec is allowable based on an antispec.

function spec_allowed(s::Vector{Signature}, anti::Set{Vector{Signature}})
  for a in anti
    if subset(SpecifiedTSig(s), SpecifiedTSig(a))
      return false
    end
  end
  for sig in s
    if !sig_allowed(sig)
      return false
    end
  end
  return true
end

function sig_allowed(s::Signature)
  if typeof(s) == ESig
    return false
  elseif typeof(s) == SpecifiedTSig
    return spec_allowed(s.spec, s.antispec)
  elseif typeof(s) == PSig
    for r in s.ranges
      if r.stop < r.start || r.stop < 1 || r.start > largest_p # invalid ranges
        return false
      end
    end
    return true
  else
    return true
  end
end

# Intersection for signatures.

function intersection(s1::Signature, s2::Signature)
  if !sig_allowed(s1) || !sig_allowed(s2)
    return ESig()
  end
  t1 = typeof(s1)
  t2 = typeof(s2)
  if s1 == s2
    return s1
  elseif t1 == UnspecifiedTSig
    if t2 == SpecifiedTSig # If one is specified and the othe isn't, we want to use the specified one.
      if spec_allowed(s2.spec, s1.antispec) # But, we must also make sure the antispec allows it.
        return SpecifiedTSig(s2.spec, union(s1.antispec, s2.antispec)) # And we must take the union of the two antispecs.
      else
        return ESig()
      end
    elseif t2 == UnspecifiedTSig # If both are unspecified, return union of antispecs.
      return UnspecifiedTSig(union(s1.antispec, s2.antispec))
    else
      return ESig() # tried to unify a tuple type with some other type. Fail.
    end
  elseif t1 == SpecifiedTSig
    if t2 == UnspecifiedTSig # Mirror of the above situation.
      if spec_allowed(s1.spec, s2.antispec)
        return SpecifiedTSig(s1.spec, union(s1.antispec, s2.antispec))
      else
        return ESig()
      end
    elseif t2 == SpecifiedTSig # now we try to intersect the two tuple signatures.
      if length(s1.spec) == length(s2.spec)
        i::Vector{Signature} = map(((x,y)->intersection(x,y)),s1.spec,s2.spec)
        # Check whether we've generated any ESigs in sub-parts.
        for t in i
          if t == ESig()
            return ESig() # Return failure signature if any of the types in the tuple fail.
          end
        end
        # Check the antispecs.
        anti_u = union(s1.antispec, s2.antispec)
        if !spec_allowed(i, anti_u)
          return ESig()
        else
          return SpecifiedTSig(i, anti_u) # Otherwise, we've succeeded.
        end
      else # If the lengths don't match, it's failure.
        return ESig()
      end
    else # Tried to unify tuple type with non-tuple. Fail.
      return ESig()
    end
  elseif t1 == PSig && t2 == PSig
    l1 = length(s1.ranges)
    l2 = length(s2.ranges)
    result = Array{UnitRange,1}(undef, max(l1,l2))
    for i=1:min(l1, l2)
      start = max(s1.ranges[i].start, s2.ranges[i].start)
      stop = min(s1[i].stop, s2[i].stop)
      if start > stop || stop < 1 || start > largest_p
        return ESig() # return esig if any of these are contradictory
      else
        result[i] = start:stop
      end
    end
    if l1 > l2
      longer = s1
    else
      longer = s2
    end
    for i=(min(l1, l2) + 1):max(l1,l2) # fill in the rest from the longer item
      result[i] = longer[i]
    end
    return PSig(result)
  elseif t1 == USig && t2 == USig
    lower_lim = max(s1.range.start, s2.range.start)
    upper_lim = min(s1.range.stop, s2.range.stop)
    if lower_lim <= upper_lim
      return USig(lower_lim:upper_lim)
    else
      return ESig()
    end
  elseif t1 == VSig && t2 == VSig
    return VSig()
  else # All other cases should be irreconcilable signatures.
    return ESig()
  end
end

intersects(s1::Signature, s2::Signature) = !(intersection(s1,s2) == ESig())

# extend_ranges makes sure there are at least n dimensions explicitly
# represented in a psig. In addition, it always returns a new vector which we
# can safely modify, not the same old vector.

function extend_ranges(ranges::Array{UnitRange{Int64}, 1}, n::Int64)
  l = length(ranges)
  if l < n
    additions = Array{UnitRange{Int64}, 1}(UndefInitializer(), n - l)
    for i=1:length(additions)
      additions[i]=1:largest_p
    end
    return vcat(ranges, additions)
  else
    return copy(ranges)
  end
end

# 'specialize_sig' takes a signature and a location, much like 'access', but also a
# replacement for the sub-signature at the location. Returns a new signature
# with the replacement intersected into the location. Specialization which is
# not compatible with existing signature is like trying to insert ESig().
# Attempting to replace any sub-part with ESig() yields ESig() at the top, since
# a signature with a sub-part which can't be instantiated, can't be instantiated
# (and we want to spot this readily). The same goes for a PSig with a minimum
# predicate-number above its maximum. Attempting to replace at a location which
# is not defined will result in an error; if there's doubt of that, it should be
# checked with access_defined. (Yes, it should be access_defined, not
# varloc_valid, because this type signature is necessarily specializing a sig,
# not a predicate var. However, there will also be a version of this fn for the
# predicate var case.)

function specialize_sig(s::Signature, l::VarLoc, r::Signature)
  if length(l) == 0 # Specializing something else than a SpecifiedTSig
    return intersection(r,s)
  else
    new_spec = copy(s.spec)
    new_spec[l[1]] = specialize_sig(new_spec[l[1]], l[2:length(l)], r)
    if new_spec[l[1]] == ESig()
      return ESig()
    elseif !spec_allowed(new_spec, s.antispec)
      return ESig()
    else
      return SpecifiedTSig(new_spec, s.antispec)
    end
  end
end

# Version of specialize_sig for the predicate variable case. In this case, we
# take a UnitRange instead of the replacement signature, and we intersect the
# pre-existing range of the target variable with the given range.

function specialize_sig(s::Signature, l::VarLoc, r::UnitRange)
  if length(l) > 1 # recursive case
    new_spec = copy(s.spec)
    new_spec[l[1]] = specialize_sig(new_spec[l[1]], l[2:length(l)], r)
    if new_spec[l[1]] == ESig()
      return ESig()
    elseif !spec_allowed(new_spec, s.antispec)
      return ESig()
    else
      return SpecifiedTSig(new_spec, s.antispec)
    end
  elseif length(l) == 1
    # either we're now locating a dim within the pred var, or we're locating the pred var within a tsig, but in the second case we're just going to take the first pred dim
    if typeof(s) == PSig # good news, we're locating a p dim inside a p var
      l = l[1] # let's just cut down on the clutter, shall we
      new_ranges = extend_ranges(s.ranges, l)
      new_ranges[l] = max(new_ranges[l].start, r.start):min(new_ranges[l].stop, r.stop)
      return PSig(new_ranges)
    else # good news, we're not down to a pvar yet, but we're just going to take the first p dim when we get there
      return specialize_sig(s, [l[1], 1], r) # just tack a 1 on the end there and we're good to go
    end
  else # length(l) < 1
    throw("specialize_sig was handed the varloc [], which is a bit weird")
  end
end

function specialize_dom(d::Domain, l::Vector{Int}, replacement::Any)
  s = specialize_sig(d.sig, l, replacement)
  return Domain(s, d.reg, d.map)
end

# Makes the dommain map complete, while preserving the already-present mappings.

function complete_dom_dims(d::Domain)
  s = d.sig
  varlocs = sig_vars(d.sig)
  new_varlocs = setdiff(varlocs, keys(d.map))
  available_dim_nums = setdiff(collect(1:(length(varlocs)+length(values(d.map)))), values(d.map))[1:length(new_varlocs)]
  new_varloc_dim_nums = Dict{VarLoc,Int}(map(=>, new_varlocs, available_dim_nums))
  m = Dict{VarLoc,Int}(union(d.map, new_varloc_dim_nums))
  r = LinRegion(d.reg.bounds, length(m))
  return Domain(s, r, m)
end

# xbutnoty is a helper function for intersection. It takes the intersection
# between a signature x and the compliment of a signature y. If the structures
# of the two simply do not match, it returns x. If x is a subset of y, then it
# returns esig. Otherwise, if y is a subset of x, it returns x modified to
# forbid the y-type structures.

#function xbutnoty(x::Signature, y::Signature)



# Takes two VarMaps. Returns a Dict{Int, Int} giving the pairs of overlapping
# variables; that is, those which map to the same VarLoc. The dict maps dim-nums
# from m1 to m2.

function varmatches(m1::VarMap, m2::VarMap)
  result = Dict{Int, Int}()
  for i in m1
    if haskey(m2, i[1])
      result = Dict(union(result, Dict(i[2]=>m2[i[1]])))
    end
  end
  return result
end

# Takes a reordering represented in a Dict{Int, Int} mapping, and returns an
# equivalent reordering vector such that if d[x]=y for the dict, v[x]=y for the
# vector. Sets the vector to [1,2,3,....] as a default before filling in the
# stuff from the dict. If the input dict is a permutation, this has the
# advantage of naturally extending it to a new permutation of length max_dim
# which leaves unmentioned dims alone. However, in other situations, the
# convention can easily create overlaps, like [2,2,3] from  Dict(1=>2,3=>3); in
# particular, you could actually get this result if applying
# reorder_dict_to_reorder_vect directly to the output of varmatches. If this
# soulds like a problem, you probably want to get the initial dict from
# find_varmap_match_reordering instead of varmatches.

function reorder_dict_to_reorder_vect(pair_reord::Dict{Int,Int}, max_dim)
  reordering = collect(1:max_dim)
  for pair in pair_reord
    reordering[pair[1]] = pair[2]
  end
  return reordering
end

function reorder_vect_to_reorder_dict(vect_reord::Vector{Int})
  return Dict{Int, Int}(map(((x,y) -> x=>y), collect(1:length(vect_reord)), vect_reord))
end

# Takes two VarMaps. Constructs a Dict{Int, Int} substitution map which, applied
# to the variable-nums of the second map, (1) collapses all matched
# dimensions as per varmatches, and (2) preserves the orderdng of m1, adding any
# non-matched variables from m2 after those.

function find_varmap_match_reordering(m1::VarMap, m2::VarMap)
  #max1 = maximum(values(m1))
  #max2 = maximum(values(m2))
  # Find the vars which match. Initializing with the easy ones: we want to move the m2 dims to their matching m1 dims.
  to_move = varmatches(m2, m1)
  # Dim-nums from m2 that we don't know what to do with yet.
  matched = collect(keys(to_move))
  # The things we still have to move. We'll want to move them to dim-nums unmentioned in m1 (not just unmatched).
  unmatched = [setdiff(values(m2), matched)...]
  # We want to get a list of dimension numbers not mentioned in m1, long enough for all the unmatched from m2.
  free_numbers = setdiff(1:(length(unmatched)+length(m1)), values(m1))
  for i = 1:length(unmatched)
    to_move[unmatched[i]] = free_numbers[i] # add the new mappings based on free numbers to to_move
  end
  return to_move
end

# Combines varmaps using find_varmap_match_reordering, but returns the tuple
# (combined_map, varmap_match_reordering) so that we can use the reordering
# for other purposes as well.

function bring_m2_in_line(m1::VarMap, m2::VarMap)
  varmap_match_reordering = find_varmap_match_reordering(m1, m2)
  combined_map = Dict{VarLoc,Int}(union(m1, map((pair -> pair[1]=>varmap_match_reordering[pair[2]]), [m2...])))
  return (combined_map, varmap_match_reordering)
end

function reorder_vect_and_targ_length(combined_map::VarMap, dimnum_reordering::Dict{Int,Int})
  # reorder_vec_length needs to be the largest number we may be mapping _from_
  reorder_vect_length = maximum(union([0], keys(dimnum_reordering)))
  # the size of space we will be mapping _to_ is the max over the dim-nums in the new map
  reorder_target_length = maximum(union([0], values(combined_map)))
  # here's the reordering permutation, finally
  reorder_vect = reorder_dict_to_reorder_vect(dimnum_reordering, reorder_vect_length)
  return (reorder_vect, reorder_target_length)
end

# Reorder the domain region to be compatible with the dimension numbering of the leaf, also getting the new dimnum map so we know what's where.

function bring_domain_and_leaf_in_line(leafmap::VarMap, dommap::VarMap, reg::LinRegion)
  if leafmap == dommap
    return (leafmap, reg)
  end
  # figure out how to merge the maps, & do it
  (full_map, dimnum_reordering) = bring_m2_in_line(leafmap, dommap)
  # calculate how we're going to re-map the region
  (reorder_vect, reorder_target_length) = reorder_vect_and_targ_length(full_map, dimnum_reordering)
  # re-map the region
  reordered_reg = reorder(reg, reorder_vect, reorder_target_length)
  return (full_map, reordered_reg)
end

# Takes the intersection of two domains by taking the signature intersection and
# re-ordering the regions so that the region-intersection can be taken. Creates
# a domain whose reg has dim-nums compatible with those of the first argument.
# (Other functions may rely on that fact for efficiency, though it doesn't feel
# clean.) Does not check for empty domain region, or trim redundant constraints.

function intersection(d1::Domain, d2::Domain)
  new_sig = intersection(d1.sig, d2.sig)
  if new_sig == ESig()
    return Domain(ESig())
  else
    # We need to make the two maps consistent before merging things; in particular we'll make a new map conistent wih d1.map.
    # bring_domain_and_leaf_in_line does what we want even though we're not working with memleafs
    (combined_map, reg2) = bring_domain_and_leaf_in_line(d1.map, d2.map, d2.reg)
    #
    #reorder2::Dict{Int,Int} = find_varmap_match_reordering(d1.map, d2.map) # we'll follow d1's var numbering
    max_dim = maximum(vcat([d1.reg.dimensionality],[values(combined_map)...])) # either the dimensionality of d1.reg, or the highest dim-num in the combined map
    #reg2 = reorder(d2.reg, reorder_dict_to_reorder_vect(reorder2, max_dim), max_dim)
    # reg1 = reorder(d1.reg, collect(1:max_dim), max_dim)
    reg1 = LinRegion(d1.reg.bounds, max_dim) # extend the dimensionality of d1.reg
    #new_map = Dict(union(d1.map, map((pair -> pair[1]=>reorder2[pair[2]]), d2.map)))
    return Domain(new_sig, intersection(reg1, reg2), combined_map)
  end
end

function subset(sub::Signature, sup::Signature)
  if sub == ESig()
    return true
  end
  i = intersection(sub, sup)
  if i == ESig()
    return false
  elseif i == sub
    return true
  else
    return false
  end
end

empty_domain(d::Domain) = d.sig == ESig() || !sig_allowed(d.sig) || !regvalid(d.reg)

function subset(sub::Domain, sup::Domain)
  if empty_domain(sub)
    return true
  elseif !subset(sub.sig, sup.sig)
    return false
  else
    i = intersection(sub,sup)
    if !regvalid(i.reg)
      return false
    end
    # reorder sub.reg so that it can be compared to i.reg
    # reordered_sub_reg = reorder(sub.reg, collect(1:i.reg.dimensionality), i.reg.dimensionality)
    reordered_sub_reg = LinRegion(sub.reg.bounds, i.reg.dimensionality) # using the fact that domain intersection creates something whose dimnums are compatible with those of its first argument
    if i.sig == sub.sig && subset(reordered_sub_reg, i.reg)
      return true
    else
      return false
    end
  end
end


# spec_only strips out antispec recursively.

function spec_only(s::Signature)
  t = typeof(s)
  if t == SpecifiedTSig
    return SpecifiedTSig(map(spec_only, s.spec))
  elseif t == UnspecifiedTSig
    return UnspecifiedTSig()
  else
    return s
  end
end


# Follow a particular branch of a TSplit. (Does not trim! However, if the tree
# is trimmed already, the branch should also be trimmed with respect to the more
# specialized signature within.)

function follow_tuple_branch(m::MemTree, b::Pair)
  return MemTree(specialize_dom(m.domain, m.root.var, b[1]), b[2])
end

function follow_tuple_default(m::MemTree)
  # We'll be wanting to put the branch signatures into the antispec.
  sig_holes = UnspecifiedTSig(Set{Vector{Signature}}(map((s -> s.spec), [keys(m.root.branches)...])))
  new_domain = specialize_dom(m.domain, m.root.var, sig_holes)
  return MemTree(new_domain, m.root.default)
end

#= This fn seems to never be used.
# Follow the neg branch of a PSplit.

function takeneg(s::Signature, p::PSplit)
  if s == ESig()
    return s
  else
    #pvar_loc = p.var[1:(length(p.var)-1)]
    #pvar_dim = p.var[length(p.var)]
    #old_psig = access(s, pvar_loc)
    #new_psig = PSig(extend_ranges(old_psig.ranges, pvar_dim))
    return specialize_sig(s, p.var, 1:(p.loc-1))
    #new_psig.ranges[pvar_dim] = (new_psig[pvar_dim].start):(p.loc-1)
    #return specialize_sig(s, p.var, new_psig) #PSig(access(s, p.var).min, p.loc-1))
  end
end
=#

# Takeneg for memtrees assumes the root is a psplit, since otherwise, it isn't
# clear what it means to take the negative branch.

function takeneg(m::MemTree)
  #if m.root <: MemLeaf || !access_defined(m.domain.sig, m.root.var) #empty_domain(m.domain)
  #  return m
  #else
    neg_range = 1:(m.root.loc-1)
    return MemTree(specialize_dom(m.domain, m.root.var, neg_range), m.root.neg)
  #end
end

#= This fn seems to never be used.
# Follow pos branch of PSplit. (Does not trim!)

function takepos(s::Signature, p::PSplit)
  if s == ESig()
    return s
  else
    old_psig = access(s, p.var)
    new_psig = PSig(extend_ranges(old_psig.ranges, p.dim))
    new_psig.ranges[p.dim] = (p.loc):(new_psig[p.dim].stop)
    return specialize_sig(s, p.var, PSig()) # PSig(p.loc, access(s, p.var).max))
  end
end
=#

# Takepos for memtrees assumes the root is a psplit, since otherwise, it isn't
# clear what it means to take the positive branch.

function takepos(m::MemTree)
  #if empty_domain(m.domain)
  #  return m
  #else
    pos_range = (m.root.loc):largest_p
    return MemTree(specialize_dom(m.domain, m.root.var, pos_range), m.root.pos)
  #end
end

# memleaf_bsptree takes a memtree whose root is a leaf, and finds the BSPTree
# obtained by taking the leaf contents and bounding it by the domain region,
# with dimension numbering consistent with the leaf map.
# Returns a Tuple{VarMap, BSPTree}, with the VarMap being the full dimension
# numbering -- it may include new varloc=>dimnum correspondences in order to
# serve a variable which is in the domain map but happens not to be explicitly
# represented in the leaf map, so we need to know about it.

function memleaf_bsptree(m::MemTree)
  if typeof(m.root) != MemLeaf
    return error("memleaf_bsptree cannot handle a MemTree whose root is not a MemLeaf: $m")
  end
  #l = maximum(union([0], values(m.root.map), values(m.domain.map)))
  #reordering = find_varmap_match_reordering(m.root.map, m.domain.map)
  #l = maximum(vcat([0], values(reordering), values(m.root.map))) # new reg dimensionality is the highest mentioned
  #matching = varmatches(m.domain.map, m.root.map)
  #unmatched_domain_map_varlocs = setdiff(keys(m.domain.map), keys(m.root.map))
  ## figure out where we can put the unmatched
  #available = setdiff(collect(1:l), values(matching))
  #place_unmatched = Dict{Int,Int}(map(((varloc, dimnum) -> m.domain.map[varloc]=>dimnum), unmatched_domain_map_varlocs, available[1:length(unmatched_domain_map_varlocs)]))
  #reordering = Dict{Int,Int}(union(matching, place_unmatched))
  #r = reorder_dict_to_reorder_vect(reordering, l)
  #return BSPTree(reorder(m.domain.reg, r, l), m.root.value)
  #
  (combined_map, reordered_reg) = bring_domain_and_leaf_in_line(m.root.map, m.domain.map, m.domain.reg)
  return (combined_map, BSPTree(reordered_reg, m.root.value))
end

# Like memleaf_bsptree, but uses standard_varmap to determine ordering.

function memleaf_bsptree_standard(m::MemTree)
  if typeof(m.root) != MemLeaf
    return error("memleaf_bsptree cannot handle a MemTree whose root is not a MemLeaf: $m")
  end
  sv = standard_varmap(m.domain.sig)
  l = length(sv)
  rr = reorder_dict_to_reorder_vect(find_varmap_match_reordering(sv, m.domain.map), l)
  lr = reorder_dict_to_reorder_vect(find_varmap_match_reordering(sv, m.root.map), l)
  return BSPTree(reorder(m.domain.reg, rr, l), reorder(m.root.value, lr, l))
end

# Flattened signatures are what appear in TSplits, to further specify a tuple
# just one level deeper.
# Note: also discards anti_specs.
#

function flatten_signature(s::Signature)
  if typeof(s) == SpecifiedTSig
    new_spec = copy(s.spec)
    for i in collect(1:length(s.spec))
      if typeof(s.spec[i]) == SpecifiedTSig || typeof(s.spec[i]) == UnspecifiedTSig
        new_spec[i] = UnspecifiedTSig()
      elseif typeof(s.spec[i]) == PSig # need to 'standardize' the tsigs by putting them to (minimum, maximum) value. TSplits should not be in the business of making predicate vars more specific!
        new_spec[i] = PSig(1, largest_p)
      end
    end
    return SpecifiedTSig(new_spec)
  else
    return s
  end
end

# Takes a signature, and returns the Set of VarLocs which are VSig.

function sig_vars(s::Signature)
  if s == VSig()
    return Set{VarLoc}((Int[],))
  elseif typeof(s) == SpecifiedTSig
    result = Set{VarLoc}()
    for i = 1:length(s.spec)
      result = union(result, Set{VarLoc}(map((vl -> vcat([i], vl)), [sig_vars(s.spec[i])...])))
    end
    return result
  else
    return Set{VarLoc}()
  end
end

# Takes a signature, and outputs the varmap which assigns all first-order vars
# to dim-nums in order of occurrence in the signature.

function standard_varmap(s::Signature)
  if s == VSig()
    return Dict{VarLoc,Int}(Int[]=>1)
  elseif typeof(s) == SpecifiedTSig
    result = Dict{VarLoc,Int}()
    for i = 1:length(s.spec)
      result = Dict(union(result, Dict{VarLoc,Int}(map((pair -> vcat([i], pair[1])=>(pair[2]+length(result))), [standard_varmap(s.spec[i])...]))))
    end
    return result
  else
    return Dict{VarLoc,Int}()
  end
end



# Trim for MemTrees. Constructs the domains which branches should have,
# descending the tree recursively. Trims BSPTrees at leaves. Trims away branches
# whose signature is ESig() or whose BSPTree contents are just None(),
# recursively up the tree. (If a node has all its branches trimmed away, it
# becomes a leaf holding None() which gets passed back up to be trimmed.)
# Unlike first-order trimming, does not currently do any epsilon equality check
# to merge equal branches.

# TODO: add epsilon equality checks everywhere. I've added them just for tsplits now.
# TODO: I should probably make different versions of this and test speed, including
# versions with and without epsilon equality tests.
# TODO: Why doesn't this check for the domain region being empty? Why doesn't this trim the domain region? Too costly?

function trim(m::MemTree)
  t = typeof(m.root)
  if empty_domain(m.domain) #m.domain.sig == ESig()
    return MemTree(Domain(ESig(), boundless_reg(0)), MemLeaf(None()))
  #elseif !sig_allowed(m.domain.sig) #typeof(m.domain.sig) == SpecifiedTSig && !spec_allowed(m.domain.sig.spec, m.domain.sig.antispec)
  #  return MemTree(Domain(ESig(), boundless_reg(0)), MemLeaf(None()))
  elseif t == TSplit
    d = m.root.branches
    if access_defined(m.domain.sig, m.root.var) # if access is defined, it should be a tsig
      flat = flatten_signature(access(m.domain.sig, m.root.var))
      if haskey(d, flat) # The signature falls into one of the branches, so we just take that branch and ignore everything else.
        return MemTree(m.domain, trim(follow_tuple_branch(m, flat=>d[flat])).root) # trim(MemTree(m.domain, d[flat]))
      end
    end
    # Either access is undefined, or there isn't an exact branch map. Trim all branches, including the default value.
    # (BTW, access should really be defined! Otherwise there'd be trouble following any branch (including the default branch) anyway.)
    trimmed_default = trim(follow_tuple_default(m))
    new_d = Dict{SpecifiedTSig, MemNode}()
    for b in d # for branch in branches
      branch_trim = trim(follow_tuple_branch(m,b))
      # Unless the signature is an ESig, add trimmed branch in to the new dict.
      # We could also eliminate branches which are epsilonequal to default, but, this might be too costly to check.
      # Revision: now I'm checking that. Small trees are the route to speed, after all.
      comparison = MemTree(branch_trim.domain, trimmed_default.root)
      if !(branch_trim.domain.sig == ESig()) && !epsilonequal(branch_trim, comparison)
        new_d = Dict{SpecifiedTSig, MemNode}(new_d..., b[1]=>(branch_trim.root))
      end
    end
    d = new_d
    l = length(d)
    if l > 0
      return MemTree(m.domain, TSplit(m.root.var, d, trimmed_default.root))
    else # l == 0
      return MemTree(m.domain, trimmed_default.root)
    end
  elseif t == PSplit
    acc = access(m.domain.sig, m.root.var)
    if typeof(acc) == PSig
      throw("Trim was handed a PSplit whose VarLoc accessed the PSig, rather than a specific predicate variable.")
    end
    pvar_loc = m.root.var
    psig_loc = pvar_loc[1:(length(pvar_loc)-1)]
    ranges = access(m.domain.sig, psig_loc).ranges
    for range in ranges # check to see whether any dimension is already invalid
      if range.start > range.stop || range.stop < 1 || range.start > largest_p
        return MemTree(Domain(ESig(), boundless_reg(0)), MemLeaf(None()))
      end
    end
    split = m.root.loc # where do we split this dimension?
    dim = pvar_loc[length(pvar_loc)] # the dimension's number is the last element of the pvar_loc
    ranges = extend_ranges(ranges, dim) # make sure it exists
    pos_range = split:(ranges[dim].stop)
    neg_range = (ranges[dim].start):(split-1)
    pos_exists = pos_range.start <= pos_range.stop
    neg_exists = neg_range.start <= neg_range.stop
    if neg_exists && !pos_exists
      # It might look like I'm not checking whether the result of trimming is None(), but I'd just want to pass None() up in any case. So, since I'm passing up the result of trimming, I'm good.
      return trim(MemTree(specialize_dom(m.domain, pvar_loc, neg_range), m.root.neg))
    elseif pos_exists && !neg_exists
      # (Same comment re: None() as previous case.)
      return trim(MemTree(specialize_dom(m.domain, pvar_loc, pos_range), m.root.pos))
    else # both must exist, since I took care of the case where the range contained nothing earlier.
      pos = trim(MemTree(specialize_dom(m.domain, pvar_loc, pos_range), m.root.pos))
      neg = trim(MemTree(specialize_dom(m.domain, pvar_loc, neg_range), m.root.neg))
      if neg.root == pos.root # TODO could be epsilonequal
        return MemTree(m.domain, pos.root)
      else
        return MemTree(m.domain, PSplit(pvar_loc, m.root.loc, neg.root, pos.root))
      end
    end
  elseif t == MemLeaf # trim the bsptree in the leaf
    # need to convert the domain reg into the leaf dim ordering
    (combined_map, reg) = bring_domain_and_leaf_in_line(m.root.map, m.domain.map, m.domain.reg)
    bsp = BSPTree(reg, m.root.value)
    value = trim(bsp).root
    memleaf = MemLeaf(value, combined_map)
    return MemTree(m.domain, memleaf)
    #
    #node = MemLeaf(trim(memleaf_bsptree(m)).root, m.root.map)
    #sv = standard_varmap(m.domain.sig)
    #l = length(sv)
    #if !(sv == m.root.map) # used to be a narrower condition: l > length(m.root.map)  # would be good to use the narrowest condition that still avoids problems with == working.
    #  vm = varmatches(m.root.map, sv)
    #  new_bsp = reorder(node.value, reorder_dict_to_reorder_vect(vm, l), l)
    #  node = MemLeaf(new_bsp, sv)
    #end
    #return MemTree(m.domain, node)
  end
end


# Query takes a MemTree and a Domain, and returns a new MemTree restricted to
# the given Domain. The ordering of the new domain is followed as much as
# possible; there may be additional variables which are put after those in the
# query domain, but the variables in the query domain are put in order.

function query(tree::MemTree, s::Domain)
  return trim(MemTree(intersection(s, tree.domain), tree.root))
end

function query(tree::MemTree, s::Signature)
  return trim(MemTree(Domain(intersection(s, tree.domain.sig), tree.domain.reg, tree.domain.map), tree.root))
end


function epsilonequal(m1::MemTree, m2::MemTree, epsilon::Float64=0.0000001)
  i = intersection(m1.domain, m2.domain)
  if empty_domain(i) # i.sig == ESig() # empty_domain(i) would be more accurate, but it would also be slower, and epsilonequal needs to be fast. Also, if the tree is trimmed it won't matter.
    return true      # Note that intersection does not amount to doing this already; domain intersection does not check for constraint inconsistency.
  elseif typeof(m1.root) == TSplit
    for b in m1.root.branches
      if !epsilonequal(follow_tuple_branch(m1,b), m2, epsilon)
        return false
      end
    end
    if !epsilonequal(follow_tuple_default(m1), m2, epsilon)
      return false
    end
    return true
  elseif typeof(m1.root) == PSplit
    if !epsilonequal(takepos(m1), m2, epsilon)
      return false
    elseif !epsilonequal(takeneg(m1), m2, epsilon)
      return false
    else
      return true
    end
  elseif typeof(m2.root) == TSplit
    for b in m2.root.branches
      if !epsilonequal(m1, follow_tuple_branch(m2,b), epsilon)
        return false
      end
    end
    if !epsilonequal(m1, follow_tuple_default(m2), epsilon)
      return false
    end
    return true
  elseif typeof(m2.root) == PSplit
    if !epsilonequal(m1, takepos(m2), epsilon)
      return false
    elseif !epsilonequal(m1, takeneg(m2), epsilon)
      return false
    else
      return true
    end
  else # Now, both m1 and m2 have to be at leaves
    # we need i, m1's leaf, and m2's leaf to be on the same page about dim nums
    if i.map == m1.root.map == m2.root.map # TODO could refine this to save work when just two are equal, also
      t1 = m1.root.value
      t2 = m2.root.value
      reordered_reg = i.reg
    else
      (both_leaf_map, translate_second_leaf_to_first) = bring_m2_in_line(m1.root.map, m2.root.map)
      (tri_map, translate_i_to_map) = bring_m2_in_line(both_leaf_map, i.map)
      # now we can use i.reg as the bsp boundary
      (reg_reorder_vect, targ_length) = reorder_vect_and_targ_length(tri_map, translate_i_to_map)
      reordered_reg = reorder(i.reg, reg_reorder_vect, targ_length)
      (t2_reorder_vect, targ_length) = reorder_vect_and_targ_length(tri_map, translate_second_leaf_to_first) # recomputes targ_length unnecessarily; could avoid
      t1 = m1.root.value
      t2 = reorder(m2.root.value, t2_reorder_vect, targ_length)
    end
    t1 = trim(BSPTree(reordered_reg, t1))
    t2 = trim(BSPTree(reordered_reg, t2))
    #
    #q1 = query(m1, i)
    #q2 = query(m2, i)
    #t1 = memleaf_bsptree(q1)
    #t2 = memleaf_bsptree(q2)
    #vm = varmatches(q2.root.map, q1.root.map)
    #if vm != Dict(map((a -> a=>a), collect(1:length(vm)))) # this may be wrong if one of the maps just doesn't represent a var -- currently trim ensures that won't happen, but that may change
    #  t2 = reorder(t2, reorder_dict_to_reorder_vect(vm, length(vm)), length(vm))
    #end
    return epsilonequal(t1, t2, epsilon)
  end
end

function epsilonequal(tree::MemTree, n::Number)
  t2 = MemTree(tree.domain, MemLeaf(n))
  return epsilonequal(tree, t2)
end

# version of the bsptree treediff function for memtrees

function treediff(m1::MemTree, m2::MemTree, epsilon::Float64=0.0000001)
  i = intersection(m1.domain, m2.domain)
  if i.sig == ESig()
    return MemTree[]
  elseif typeof(m1.root) == TSplit
    result = MemTree[]
    for b in m1.root.branches
      result = vcat(result, [treediff(follow_tuple_branch(m1,b), m2, epsilon)])
    end
    result = vcat(result, [treediff(follow_tuple_default(m1), m2, epsilon)])
    return result
  elseif typeof(m1.root) == PSplit
    return vcat(treediff(takepos(m1), m2, epsilon), treediff(takeneg(m1), m2, epsilon))
  elseif typeof(m2.root) == TSplit
    result = MemTree[]
    for b in m2.root.branches
      result = vcat(result, [treediff(m1, follow_tuple_branch(m2,b), epsilon)])
    end
    result = vcat(result, [treediff(m1, follow_tuple_default(m2), epsilon)])
    return result
  elseif typeof(m2.root) == PSplit
    return vcat(treediff(m1, takepos(m2), epsilon), treediff(m1, takeneg(m2), epsilon))
  else # Now, both m1 and m2 have to be at leaves
    # we need i, m1's leaf, and m2's leaf to get on the same page about dim nums
    (both_leaf_map, translate_second_leaf_to_first) = bring_m2_in_line(m1.root.map, m2.root.map)
    (tri_map, translate_i_to_map) = bring_m2_in_line(both_leaf_map, i.map)
    # now we can use i.reg as the bsp boundary
    (reg_reorder_vect, targ_length) = reorder_vect_and_targ_length(tri_map, translate_i_to_map)
    reordered_reg = reorder(i.reg, reg_reorder_vect, targ_length)
    (t2_reorder_vect, targ_length) = reorder_vect_and_targ_length(tri_map, translate_second_leaf_to_first) # recomputes targ_length unnecessarily; could avoid
    t1 = m1.root.value
    t2 = reorder(m2.root.value, t2_reorder_vect, targ_length)
    t1 = trim(BSPTree(reordered_reg, t1))
    t2 = trim(BSPTree(reordered_reg, t2))
    #
    #q1 = query(m1, i)
    #q2 = query(m2, i)
    #t1 = memleaf_bsptree(q1)
    #t2 = memleaf_bsptree(q2)
    #vm = varmatches(q2.root.map, q1.root.map)
    #if vm != Dict(map((a -> a=>a), collect(1:length(vm))))
    #  t2 = reorder(t2, reorder_dict_to_reorder_vect(vm, length(vm)), length(vm))
    #end
    diffs = treediff(t1, t2, epsilon)
    return map((d -> MemTree(Domain(m1.domain.sig, d.boundary, tri_map), MemLeaf(d.root, tri_map))), diffs)
  end
end

#=

# Next, I need to insert items into MemTrees. I first need to descend the target
# MemTree, testing which branches match the signature in order to find which to
# descend. If no branches match the signature, then we switch into branch-
# creation mode. We make nodes to specify down to the signature of the source.
# Because of the second step, we have to carry the domain of the target along
# as we descend, making it increasingly specific in accordance with the
# branching. This helps determine what split nodes are needed in the new branch.
# (The tree should never have something inserted without sufficient branching to
# fully specify its intended signature from where it sits.) If the source
# doesn't match the signature of the target at all, then an error is thrown; it
# can't be inserted. Doesn't produce any redundancies to be trimmed at the
# MemTree level, but does at the BSPTree level (since BSPTree insertion does
# create a structure which could use a trim).

function insert(source::MemTree, target::MemTree)
  if !subset(source.domain, target.domain)
    source = query(source, target.domain) # narrow down to fit into target
  end
  return MemTree(target.domain, insert(source, target.root, target.domain.sig))
end

function insert(source::MemTree, target::MemNode, target_sig::Signature)
  t = typeof(target)
  if t == TSplit
    if access_defined(source.domain.sig, target.var) && typeof(access(source.domain.sig, target.var)) == SpecifiedTSig # If a TSplit splits on a variable which is specified in the source, then we should either be descending one (matching) branch or creating a branch that matches us.
      split_sig = flatten_signature(access(source.domain.sig, target.var))
      if haskey(target.branches, split_sig) # If haskey, descend that branch.
        new_branches = copy(target.branches)
        b = target.branches[split_sig]
        new_branches[split_sig] = insert(source, b, specialize_sig(target_sig, target.var, split_sig)) # descend the one matching branch
        return TSplit(target.var, new_branches, target.default)
      else # No key like that? Then we need to create a new branch.

        situated_source = make_subtree(source, target_sig)
        with_new_branch = TSplit(target.var, Dict(union(target.branches, Dict(split_sig=>inserted_content))), target.default)
        # replace None()s with content from the target
        inserted_content = take_left(new_memtree, target).root
        return TSplit(target.var, Dict(union(target.branches, Dict(split_sig=>inserted_content))), target.default)
      end
    else # If the source doesn't contain that tuple variable, or contains it as an UnspecifiedTSig, it's got to be inserted into all branches, and the default value.
      new_branches = Dict(map((b -> b[1]=>insert(source, b[2], specialize_sig(target_sig, target.var, b[1]))), target.branches))
      new_default = insert(source, target.default, target_sig)
      return TSplit(target.var, new_branches, new_default)
    end
  elseif t == PSplit
    if access_defined(source.domain.sig, target.var) # As with TSplit, the source may not even contain the split variable.
      source_range = access(source.domain.sig, target.var)
      if source_range.min < target.loc # Test whether we need to insert anything into the neg branch. "<" because neg is exclusive at the top.
        if source_range.max >= target.loc # Test whether we need to insert into pos branch.
          # Insert in both.
          neg_sig = takeneg(target_sig, target)
          pos_sig = takepos(target_sig, target)
          if neg_sig == ESig() || pos_sig == ESig()
            return error("insert ended up down a blind alley, probably because it was handed an untrimmed target.")
          else
            return PSplit(target.var, target.loc, insert(source, target.neg, neg_sig), insert(source, target.pos, pos_sig))
          end
        else # We need to insert into neg but not pos.
          neg_sig = takeneg(target_sig, target)
          if neg_sig == ESig()
            return error("insert ended up down a blind alley, probably because it was handed an untrimmed target.")
          else
            return PSplit(target.var, target.loc, insert(source, target.neg, neg_sig), target.pos)
          end
        end
      else # no need to insert into neg
        if source_range.max >= target.loc # Test whether we need to insert into pos
          pos_sig = takepos(target_sig, target)
          if pos_sig == ESig()
            return error("insert ended up down a blind alley, probably because it was handed an untrimmed target.")
          else
            return PSplit(target.var, target.loc, target.neg, insert(source, target.pos, pos_sig))
          end
        else # no insertion at all (this probably shouldn't happen)
          return target
        end
      end
    else # source doesn't contain this variable; insert into both neg and pos
      neg_sig = takeneg(target_sig, target)
      pos_sig = takepos(target_sig, target)
      if neg_sig == ESig() || pos_sig == ESig()
        return error("insert ended up down a blind alley, probably because it was handed an untrimmed target.")
      else
        return PSplit(target.var, target.loc, insert(source, target.neg, neg_sig), insert(source, target.pos, pos_sig))
      end
    end
  elseif t == MemLeaf # We've arrived at a BSPTree we need to insert into.
    return make_subtree(source, target_sig, target.value, target.map)
  end
end

# make_subtree is a utility function for insertion, which handles the case where
# we need to construct new branches in order to place the content at its level of
# signature specificity (to avoid over-generalization). It takes a MemTree "source",
# a signature "target_sig", and optional arguments existing_content and
# existing_map. It returns a tree of memnodes based on any further specificity
# which exists in the source signature but not in target_sig, whose leaves are
# BSPTrees with the existing_content (possibly reordered), and with the source
# inserted where appropriate (IE, when the leaf sits within the source signature).

function make_subtree(source::MemTree, target_sig::Signature, existing_content=None()::BSPNode, existing_map=VarMap()::VarMap)
  relevant_soucre_material = query(source, target_sig) # this narrows down the source content to what's within the target sig
  source_sig = relevant_soucre_material.domain.sig
  branch = make_subtree_init(relevant_soucre_material, existing_content, existing_map)
  return make_subtree_recur(branch, source_sig, target_sig, Int[], existing_content, existing_map)
end

# Takes 'source', the stuff we want to insert, 'content', the pre-existing
# contents of the target we're inserting into, and 'map', the varmap for
# content. Source domain must already be intersected with target domain.
# make_subtree_init handles the BSPTree insertion of the source content into the
# target content, within the source content *before* making the branch to
# support it. This serves as the initial 'twig' to build a branch back from.
# Recurs to the leaves of the source, and replaces them with the source content
# inserted into the target content.

function make_subtree_init(source::MemTree, content::BSPNode, content_map::VarMap)
  t = typeof(source.root)
  if t==TSplit
    return TSplit(source.root.var, Dict(map((p -> (p[1]=>(make_subtree_init(follow_tuple_branch(source, p), content, content_map)))), source.root.branches)), make_subtree_init(follow_tuple_default(source), content, content_map))
  elseif t==PSplit
    return PSplit(source.root.var, source.root.loc, make_subtree_init(takeneg(source), content, content_map), make_subtree_init(takepos(source), content, content_map))
  else # t==MemLeaf; reorder the source and existing content to the same ordering, and do bsp insertion.
    # map the source domain boundary into the dimnums of the content
    (part_combined_map, reordered_source_reg) = bring_domain_and_leaf_in_line(content_map, source.domain.map, source.domain.reg)
    # map the source memleaf value into the same
    (full_combined_map, source_tree_to_content_tree) = bring_m2_in_line(part_combined_map, source.root.map)
    (source_tree_reorder_vec, out_d) = reorder_vect_and_targ_length(full_combined_map, source_tree_to_content_tree)
    reordered_source_bsp = reorder(source.root.value, source_tree_reorder_vec, out_d)
    s = unfoldboundary(BSPTree(reordered_source_reg, reordered_source_bsp))
    inserted = insert(s, content)
    return MemLeaf(inserted, full_combined_map)
    #
    #if content_map == source.root.map
    #  s = unfoldboundary(memleaf_bsptree(source))
    #  inserted = insert(s, content)
    #  return MemLeaf(inserted, content_map)
    #else
    #  sv::Dict{VarLoc,Int} = standard_varmap(source.domain.sig)
    #  l = length(sv)
    #  r = reorder_dict_to_reorder_vect(find_varmap_match_reordering(sv, content_map), l)
    #  s = unfoldboundary(memleaf_bsptree_standard(source))
    #  content = reorder(content, r, l)
    #  inserted = insert(s, content)
    #  return MemLeaf(inserted, content_map)
    #end
  end
end


# make_subtree_recur handles the recursive traversal of the source signature to
# construct a new branch specific enough to place the source content into the
# target. It takes the branch being built up, and returns this with any
# elaborations it added. It also takes the source signature fragment currently
# being examined, and the corresponding target signature fragment. It also takes
# a VarLoc in order to track the location within the (source and target)
# signatures, which is necessary for the sake of putting it in new splits.
# existing_content provides the content of the BSP we're inserting into, for
# "fill" in places in the tree where we don't want to put our new content.
# Finally, 'map' holds the VarMap for the BSPTree content.

function make_subtree_recur(branch::MemNode, source_sig_fragment::Signature, target_sig_fragment::Signature, var::VarLoc, existing_content::BSPNode, existing_map::VarMap)
  source_type = typeof(source_sig_fragment)
  target_type = typeof(target_sig_fragment)
  if source_type == ESig || target_type == ESig
    return error("make_subtree_recur handed ESig")
  elseif source_type == VSig
    if target_type == VSig
      return branch
    else
      return error("make_subtree_recur handed non-matching signatures")
    end
  elseif source_type == UnspecifiedTSig
    if target_type == UnspecifiedTSig
      return branch
    elseif target_type == SpecifiedTSig
      error("make_subtree_recur handed target more specific than source")
    else
      error("make_subtree_recur handed non-matching signatures")
    end
  elseif source_type == SpecifiedTSig
    if target_type == UnspecifiedTSig # We've hit new content; specify branches!
      return make_subtree_entire(branch, source_sig_fragment, var, existing_content, existing_map)
    elseif target_type == SpecifiedTSig # Recur on each tuple location.
      l = length(target_sig_fragment.spec)
      if l != length(source_sig_fragment.spec)
        return error("make_subtree_recur given SpecifiedTSigs of differing lengths")
      end
      for i = 1:l
        branch = make_subtree_recur(branch, source_sig_fragment.spec[i], target_sig_fragment.spec[i], vcat(var, [i]), existing_content, existing_map)
      end
      return branch
    end
  elseif source_type == PSig
    if target_type == PSig
      if source_sig_fragment.min > target_sig_fragment.min
        branch = PSplit(var, source_sig_fragment.min, MemLeaf(existing_content, existing_map), branch)
      end
      if source_sig_fragment.max < target_sig_fragment.max
        branch = PSplit(var, source_sig_fragment.max+1, branch, MemLeaf(existing_content, existing_map))
      end
      return branch
    else
      return error("make_subtree_recur handed non-matching signatures")
    end
  else
    return error("source signature type not recognized")
  end
end

# Handles the part of make_subtree_recur where we have gone entirely beyond
# what's in the target, so we just want to make branch-parts for all the details
# in this sub-expression of the source signature.

function make_subtree_entire(branch::MemNode, source_sig::Signature, var::VarLoc, existing_content::BSPNode, existing_map::VarMap)
  t = typeof(source_sig)
  if t == SpecifiedTSig # branch on tuple signature and all sub-types
    for i = 1:length(source_sig.spec)
      branch = make_subtree_entire(branch, source_sig.spec[i], vcat(var, [i]), existing_content, existing_map)
    end
    return TSplit(var, Dict(flatten_signature(source_sig)=>branch), MemLeaf(existing_content, existing_map))
  elseif t == UnspecifiedTSig
    return branch
  elseif t == VSig
    return branch
  elseif t == PSig # branch on predicate range
    branch = PSplit(var, source_sig.min, MemLeaf(existing_content, existing_map), branch)
    branch = PSplit(var, source_sig.max+1, branch, MemLeaf(existing_content, existing_map))
    return branch
  elseif t == ESig
    return error("make_subtree_entire handed ESig")
  else
    return error("make_subtree_entire didn't recognize signature type")
  end
end

=#


# Reordering MemTrees consists mainly of correcting all the VarLocs within the
# tree to point to the desired locations in the new tree. Therefore, we use
# a reorder function on VarLocs. It takes a Dict mapping old VarLocs to new, and
# a VarLoc v. We want to check whether any prefix of v is in the dictionary, and
# modify the prefix if so. It's possible that the dictionary contains a mapping
# from the empty location, like []=>[2,3], which means that ALL locations are
# being mapped to sub-locations of [2,3]. In this case, any other dictionary
# entries would be ignored. More generally, shorter prefixes take precedence.

function reorder(reordering::Dict{VarLoc, VarLoc}, v::VarLoc)
  for i=0:length(v)
    if haskey(reordering, v[1:i])
      return vcat(reordering[v[1:i]], v[i+1:length(v)])
    end
  end
  return v
end

# A pure reordering on signatures would be overly complicated, because you'd
# have to infer the full target signature. This isn't even possible in general.
# Plus, we should in fact know the signature of the space we're mapping to.
# So, reorder a source signature "onto" a target signature: specialize the target
# sig to match any source-sig locations which are to be mapped on. The target
# signature must contain all the VarLocs which are values in the reorder dict r.
# This should be the case anyway, because we couldn't have generated a reordering
# with a destination varloc not present in the target we were reordering to.

function reorder(r::Dict{VarLoc, VarLoc}, target::Signature, source::Signature)
  result = target
  for mapping in r
    result = specialize_sig(result, mapping[2], access(source, mapping[1]))
  end
  return result
end

# Reordering for domains. Like reordering for sigs, it requires a target; but,
# the target is just a sig, not another domain. If the reordering doesn't touch
# a dimension present in the domain region, that dimension is projected out.

function reorder(r::Dict{VarLoc, VarLoc}, target::Signature, d::Domain)
  doesnt_map = setdiff(keys(d.map), keys(r))
  reg = d.reg
  for vl in doesnt_map
    reg = project_region(reg, d.map[vl])
  end
  new_map = Dict{VarLoc,Int}()
  for pair in d.map
    if haskey(r, pair[1])
      new_map = Dict{VarLoc,Int}(union(new_map, Dict{VarLoc,Int}(reorder(r, pair[1])=>pair[2])))
    end
  end
  return Domain(reorder(r, target, d.sig), reg, new_map)
end

# Reordering for MemNodes.

function reorder(r::Dict{VarLoc, VarLoc}, n::MemNode)
  t = typeof(n)
  if t==TSplit
    return TSplit(reorder(r, n.var), Dict(map((branch -> branch[1]=>reorder(r, branch[2])), [n.branches...])), reorder(r, n.default))
  elseif t==PSplit
    return PSplit(reorder(r, n.var), n.loc, reorder(r, n.neg), reorder(r, n.pos))
  elseif t==MemLeaf
    return MemLeaf(n.value, Dict(map((pair -> reorder(r, pair[1])=>pair[2]), [n.map...])))
  end
end

# Reordering for MemTrees. Like reordering for signatures, it requires a target
# signature.

function reorder(r::Dict{VarLoc, VarLoc}, target::Signature, m::MemTree)
  return MemTree(reorder(r, target, m.domain), reorder(r, m.root))
end


# ==== Combination Operations ====

# Like treearithmetic in trees.jl, this compiles combination operators; but, for
# memories rather than BSPTrees.

function memarithmetic(operator, base_type)
  eval(
    quote

      function $operator(node::MemNode, val::$base_type) # Only work on raw nodes if we're combining with the base type.
        t = typeof(node)
        if t == TSplit
          branches = Dict(map((pair -> pair[1]=>( $operator(pair[2], val))), [node.branches...]))
          return TSplit(node.var, branches, $operator(node.default, val))
        elseif t == PSplit
          return PSplit(node.var, node.loc, $operator(node.neg, val), $operator(node.pos, val))
        else # t == MemLeaf
          return MemLeaf($operator(node.value, val), node.map)
        end
      end

      function $operator(val::$base_type, node::MemNode) # Reverse of previous case.
        t = typeof(node)
        if t == TSplit
          branches = Dict(map((pair -> pair[1]=>( $operator(val, pair[2]))), [node.branches...]))
          return TSplit(node.var, branches, $operator(val, node.default))
        elseif t == PSplit
          return PSplit(node.var, node.loc, $operator(val, node.neg), $operator(val, node.pos))
        else # t == MemLeaf
          return MemLeaf($operator(val, node.value), node.map)
        end
      end

      function $operator(val::$base_type, tree::MemTree) # Cembining the base type with a tree, simplify to combining with a node.
        return MemTree(tree.domain, $operator(val, tree.root))
      end

      function $operator(tree::MemTree, val::$base_type) # Reverse case.
        return MemTree(tree.domain, $operator(tree.root, val))
      end

      function $operator(t1::MemTree, t2::MemTree) # Memtree combination.
        i = intersection(t1.domain, t2.domain)
        if i.sig == ESig()
          return MemTree(i, MemLeaf(None(), i.map))
        elseif !sig_allowed(i.sig)
          return MemTree(dom(ESig()), MemLeaf(None(), i.map))
        end
        t = typeof(t1.root)
        if t == TSplit
          branches = [t1.root.branches...]
          new_branch_doms = map((branch -> specialize_dom(i, t1.root.var, branch[1])), branches) # could avoid specializing doms before we specialize sigs to check whether the branch is valid, for a bit of efficiency gain
          new_branch_trees = MemTree[]
          num_new = 0
          for b in 1:length(branches) # check whether each new branch would be non-empty before creating it
            if new_branch_doms[b].sig != ESig()
              new_branch_trees = vcat(new_branch_trees, $operator(MemTree(new_branch_doms[b], branches[b][2]), t2))
              num_new += 1
            end
          end
          new_default_tree = identity( $operator(follow_tuple_default(t1), t2)) # combining the defult value with the other tree
          if num_new == 0 # If no new branches actually exist, we can just use the combination with the default .
            return new_default_tree
          elseif num_new == 1 && access_defined(t2.domain.sig, t1.root.var) && typeof(access(t2.domain.sig, t1.root.var)) == SpecifiedTSig # If there is exactly one valid branch because there is exactly one way _to_ branch & still be consistent with the second tree,
            return new_branch_trees[1] # we can just return the one branch
          else  # Otherwise, probably no way around creating a whole new tsplit.
            new_branches = Dict{SpecifiedTSig, MemNode}()
            for b in 1:num_new
              new_branches[branches[b][1]] = new_branch_trees[b].root
            end
            return MemTree(i, TSplit(t1.root.var, new_branches, new_default_tree.root))
          end
          #branches = Dict(map((pair -> pair[1]=>(identity( $operator(follow_tuple_branch(t1, pair), t2)).root)), t1.root.branches))
          #return MemTree(i, TSplit(t1.root.var, branches, default))
        elseif t == PSplit
          neg = identity( $operator(takeneg(t1), t2)).root
          pos = identity( $operator(takepos(t1), t2)).root
          return MemTree(i, PSplit(t1.root.var, t1.root.loc, neg, pos))
        else # t == MemLeaf. Trim the 2nd tree at this juncture, then descend it.
          return MemTree(i, $operator(t1.root, trim(MemTree(i, t2.root))))
        end
      end

      function $operator(t1::MemLeaf, t2::MemTree) # This case is for the purpose of descending the 2nd argument. Returns a MemNode.
        if t2.domain.sig == ESig()
          return MemLeaf(None())
        elseif !sig_allowed(t2.domain.sig)
          return MemLeaf(None())
        end
        t = typeof(t2.root)
        if t == TSplit
          branches = Dict(map((pair -> pair[1]=>(identity( $operator(t1, follow_tuple_branch(t2, pair))))), [t2.root.branches...]))
          default = identity( $operator(t1, follow_tuple_default(t2)))
          return TSplit(t2.root.var, branches, default)
        elseif t == PSplit
          neg = $operator(t1, takeneg(t2))
          pos = $operator(t1, takepos(t2))
          return PSplit(t2.root.var, t2.root.loc, neg, pos)
        else # Both arguments are now at MemLeafs. Combine the BSPTrees.
          #l1 = length(t1.map)
          #l2 = length(t2.root.map)
          #vm = varmatches(t1.map, t2.root.map)
          #matched = collect(keys(vm))
          #not_matched = setdiff(collect(1:l1), matched)
          #out_d = l2+length(not_matched)
          #mapping = Dict{Int,Int}(union(vm, map(((nm, x) -> nm=>x), not_matched, collect(l2+1:out_d))))
          #dimnum_reordering = find_varmap_match_reordering(t2.root.map, t1.map)
          #mapped_domain_map =
          #vmap = reorder_dict_to_reorder_vect(mapping, out_d)
          #mapped_t1_tree = reorder(t1.value, vmap, out_d)
          #mapped_t1_map = Dict(map((pair -> pair[1]=>vmap[pair[2]]), t1.map))
          #combined_map = Dict{Vector{Int},Int}(union(t2.root.map, mapped_t1_map))
          #
          # We have to map the t2 domain reg to the t2 leaf dimnums, and also map t1 to these dimnums
          #
          # (combined_t2_map, reordered_reg) = bring_domain_and_leaf_in_line(t2.root.map, t2.domain.map, t2.domain.reg)
          # (combined_map, t1_to_t2_map) = bring_m2_in_line(combined_t2_map, t1.map)
          # (t1_reord_vec, out_d) = reorder_vect_and_targ_length(combined_map, t1_to_t2_map)
          #TODO add case(s) to avoid doing work if the maps already align
          (combined_leaf_map, t1_to_t2_map) = bring_m2_in_line(t2.root.map, t1.map)
          (combined_map, reordered_reg) = bring_domain_and_leaf_in_line(combined_leaf_map, t2.domain.map, t2.domain.reg)
          (t1_reord_vec, out_d) = reorder_vect_and_targ_length(combined_map, t1_to_t2_map)
          #t1_reord_vec = reorder_dict_to_reorder_vect(t1_to_t2_map, maximum(keys(t1_to_t2_map)))
          #out_d = maximum(values(combined_map))
          reordered_t1 = reorder(t1.value, t1_reord_vec, out_d)
          #if length(not_matched) > 0
          #  mapped_t2_tree = convert_dims(t2.root.value, out_d)
          #else
          #  mapped_t2_tree = t2.root.value
          #end
          #region = t2.domain.reg
          #if !(t2.domain.map == t2.root.map)
          #  r_l = length(t2.domain.map)
          #  r_vm = varmatches(t2.domain.map, combined_map)
          #  r_matched = collect(keys(r_vm))
          #  r_not_matched = setdiff(values(t2.domain.map), r_matched) # setdiff(collect(1:r_l), r_matched)
          #  reg_reordering_map = Dict{Int,Int}(union(r_vm::Dict{Int,Int}, Dict{Int,Int}(map(=>, r_not_matched, (setdiff(collect(1:(length(combined_map)+length(r_not_matched))), values(combined_map)))[1:length(r_not_matched)]))))
          #  out_l = r_l + length(r_not_matched)
          #  r_reordering = reorder_dict_to_reorder_vect(reg_reordering_map, out_l)
          #  region = reorder(region, r_reordering, out_l)
          #  unmatched_keys = setdiff(keys(t2.domain.map), keys(combined_map))
          #  combined_map = Dict(union(combined_map, map((key -> key=>reg_reordering_map[t2.domain.map[key]]), unmatched_keys)))
          #end
          return MemLeaf(identity( $operator(BSPTree(reordered_reg, reordered_t1), BSPTree(reordered_reg, t2.root.value))).root, combined_map)
        end
      end
    end)
end

# Now apply the function to compile the needed combination operators. Must match
# those in trees.jl.

memarithmetic(op) = memarithmetic(op, Number)

memarithmetic(:+)
memarithmetic(:*)
memarithmetic(:max)
memarithmetic(:min)
memarithmetic(:/)
memarithmetic(:-)
memarithmetic(:^,Integer)
memarithmetic(:^)

# take_second was defined in trees.jl, and behaves similarly to insert, except
# with respect to how it handles boundaries (since arithmetic takes the
# intersection of boundaries, whereas insertion has to take the target
# boundary.) Here we extend it to memory trees, meaning it behaves similarly to
# second-order insertion, but with memarithmetic's behavior wrt domains.
memarithmetic(:take_left)

# safe_div is like /, except that division by zero just returns the numerator.
memarithmetic(:safe_div)


# ==== Insertion ====

# The strategy I now want to use for insertion is to implement an
# unfoldboundary type function, and then insert the unfolded content into the
# target via take_left.

# unfold_domain_boundary descends to the MemLeafs, and uses unfoldboundary to
# insert the domain boundary into the BSPTrees at the leaves, putting None()s
# outside of that boundary.

function unfold_domain_boundary(t::MemTree)
  reg = t.domain.reg
  d = reg.dimensionality
  bounds = reg.bounds
  root_type = typeof(t.root)
  new_domain = Domain(t.domain.sig)
  if root_type == PSplit
    neg = unfold_domain_boundary(takeneg(t))
    pos = unfold_domain_boundary(takepos(t))
    return MemTree(new_domain, PSplit(t.root.var, t.root.loc, neg.root, pos.root))
  elseif root_type == TSplit
    branches = [t.root.branches...]
    unfolded = [pair[1]=>(unfold_domain_boundary(follow_tuple_branch(t, pair)).root) for pair in branches]
    default = unfold_domain_boundary(follow_tuple_default(t)).root
    return MemTree(new_domain, TSplit(t.root.var, Dict(unfolded), default))
  elseif root_type == MemLeaf
    (combined_map, reordered_reg) = bring_domain_and_leaf_in_line(t.root.map, t.domain.map, reg)
    bspt = BSPTree(reordered_reg, t.root.value)
    bspn = unfoldboundary(bspt)
    return MemTree(new_domain, MemLeaf(bspn, combined_map))
  end
end

# unfold_loc is a recursive way to unfold the signature. It takes a MemTree and
# a varloc, and returns a MemTree with the signature at that VarLoc converted
# into tree elements (placing None() outside of the previously-defined area).
# NOTE: This does not fix the domain signature to remove the sub-signature at
# the given varloc; IE, if you trimmed the resulting tree it would get rid of
# all the added structure.

function unfold_loc(t::MemTree, loc::Vector{Int})
  sub_sig = access(t.domain.sig, loc)
  result = t
  if typeof(sub_sig) == ESig
    result = MemTree(Domain(ESig()), MemLeaf(None()))
  elseif typeof(sub_sig) == SpecifiedTSig
    for i=1:length(sub_sig.spec)
      new_loc = [loc..., i]
      result = unfold_loc(result, new_loc)
    end
    flat = flatten_signature(sub_sig)
    result = MemTree(t.domain, TSplit(loc, Dict((flat=>(result.root))), MemLeaf(None())))
  elseif typeof(sub_sig) == PSig
    ranges = sub_sig.ranges
    for i in 1:length(ranges)
      result = MemTree(t.domain, PSplit([loc..., i], ranges[i].stop+1, PSplit([loc..., i], ranges[i].start, MemLeaf(None()), result.root), MemLeaf(None())))
    end
  end # don't need to do anything for VSigs or for UnspecifiedTSigs
  return result
end

# unfold_domain takes a MemTree and returns a MemTree whose domain is dom(:t).
# The new MemTree agrees with the old wherever the old was defined. In new
# regions of the domain, it contains None()s.

function unfold_domain(t::MemTree)
  # First unfold the domain boundary.
  t = unfold_domain_boundary(t)
  # Then unfold the signature.
  return MemTree(dom(:t),unfold_loc(t, Int[]).root)
end

function insert(source, target)
  source = unfold_domain(source)
  return trim(take_left(source, target))
  # TODO should I really be trimming here? Since I use insertion to put things
  # into WM, this means I have to touch the whole of WM in order to insert each
  # little thing, which is terrible. However, I think I have that same problem
  # already, just with using take_left, even without trimming. Next time I want
  # to do serious optimization, I should think harder about how I want to do
  # insertions.
end

# ==== Summary Operations ====

# Summarization removes a variable from the signature, which moves some of the
# other varlocs around. For example, in sig((:v, (:v, :v, :v))), if we summarize
# [2, 2], then the variable at [2,3] becomes the new [2,2]. References to [2,3]
# would no longer make any sense. So, as we're summarizing a tree, we have to
# fix all the references.

# varloc_adjustment takes an arbitrary varloc vl, and the varloc being
# summarized, d. It returns an adjusted version of vl.

function varloc_adjustment(vl::VarLoc, d::VarLoc)
  result = copy(vl)
  initial_segment = d[1:(length(d)-1)]
  l = length(d)
  if length(vl) >= l && vl[1:(l-1)] == initial_segment && vl[l] > d[l]
    result[l] -= 1
  end
  return result
end

function dimnum_adjustment(dn::Int, summarizing::Int)
  return dn > summarizing ? dn-1 : dn
end

function varmap_adjustment(m::Dict{VarLoc,Int}, d::VarLoc)
  if haskey(m, d)
    dimnum = m[d]
    m = Dict{VarLoc, Int}(setdiff(m, Dict(d=>(m[d]))))
    return Dict(map((p -> ((varloc_adjustment(p[1], d))=>dimnum_adjustment(p[2],dimnum))), [m...]))
  else
    return Dict(map((p -> ((varloc_adjustment(p[1], d))=>p[2])), [m...]))
  end
end

function varloc_adjustment(m::MemNode, d::VarLoc)
  t = typeof(m)
  if t == TSplit
    branches = Dict{SpecifiedTSig, MemNode}(map((branch -> branch[1]=>varloc_adjustment(branch[2], d)), [m.branches...]))
    return TSplit(varloc_adjustment(m.var, d), branches, varloc_adjustment(m.default, d))
  elseif t == PSplit
    return PSplit(varloc_adjustment(m.var, d), m.loc, varloc_adjustment(m.neg, d), varloc_adjustment(m.pos, d))
  elseif t == MemLeaf
    return MemLeaf(m.value, varmap_adjustment(m.map, d))
  end
end

# = Tsplit Default Summarization Ops =
# The summarization of tsplit default values needs to be implemented for each
# summary op seperately. This operation is invoked when an unspecified tsig is
# the subject of integration. If the memtree contains a tsplit on that tsig,
# then

# iden_t_default_summary takes the tuple default value and simply returns it.
# This is appropriate for both max and min, as the max and min of a constant
# value is just the constant value. The tsplit default value gives one value for
# all possible tuples, aside from those in the tsplit branches.
function iden_t_default_summary(t::MemTree, dim::VarLoc)
  return MemTree(integrate(t.domain, dim), t.root)
end

# error_t_default_summary throws an error. This is appropriate for integration
# and pintegration, which have no way to return a sensible value.
function error_t_default_summary(name)
  return function (t::MemTree, dim::VarLoc)
           return error("Signia doesn't know how to $name the following default value: $t")
         end
end

function last_subsig(dim::VarLoc, sig::Signature)
  if dim == Int[]
    return true
  elseif typeof(sig) == SpecifiedTSig
    if dim[1] == length(sig.spec) && last_subsig(dim[2:length(dim)], access(sig, [dim[1]]))
      return true
    else
      return false
    end
  else
    return false
  end
end


# memsummary mirrors treesummary.
# TODO I could be doing more trimming during integration -- or, I could trim before integration (I should experiment w/ this sort of thing while testing speed)

function memsummary(name, comb_op, iden, t_default)
  eval(
    quote
      function $name(tree::MemTree, dim::VarLoc)
        t = typeof(tree.root)
        if tree.domain.sig == ESig()
          return MemTree(tree.domain, MemLeaf(None()))
        end
        s = access(tree.domain.sig, dim)
        # cases based on type of the dimension of integration
        if typeof(s) == SpecifiedTSig # If var is a specified tsig, integrate out all the dims in its spec and return.
          result = tree
          # remove each dimension in the tuple
          for i=length(s.spec):-1:1 # better to count down, because otherwise we have to refer to shifting items
            result = trim($name(result, vcat(dim, [i])))
          end
          # Now remove the tuple altogether.
          # Apply $name to the domain to remove any references to the tvar.
          # Apply varloc_adjustment to the nodes, to fix references.
          # There shouldn't be any explicit references to the removed varloc,
          # since this was a specifiedtsig and thus shouldn't be split on.
          result = MemTree($name(result.domain, dim), varloc_adjustment(result.root, dim))
          return result
        elseif typeof(s) == PSig # if var is a psig, we need to integrate over any predicate variables within, in the same way as for tsigs
          result = tree
          # remove each dimension represented in 'ranges'
          for i=length(s.ranges):-1:1 # better to count down, because otherwise we have to refer to shifting items
            result = trim($name(result, vcat(dim, [i])))
          end
          # now remove the varloc from sigs altogether
          result = MemTree($name(result.domain, dim), varloc_adjustment(result.root, dim))
          return result
        #elseif typeof(s) == UnitRange # integrating out a specific universal variable
        #
        end
        # cases based on type of the current root node
        if t == TSplit
          if tree.root.var == dim # if the tsplit is also the dimension of integration
            # print(tree.root.default)
            # integrating the branches
            result = MemLeaf(LeafNode($iden), Dict{VarLoc, Int}()) # set to the identity to start
            result = MemTree(($name(tree.domain, dim)), result)
            for branch in tree.root.branches # combine the integration of each branch into the result.
              integrated = follow_tuple_branch(tree, branch)
              # Following the branch turns the unspecified tsig into a specified tsig.
              # Integrating out that tsig then serves to integrate out each element of the tuple.
              integrated = $name(integrated, dim)
              # integrated = MemTree(result.domain, varloc_adjustment(integrated.root, dim))
              # for i = length(branch[1].spec):-1:1 # Integrate out each dim in the tuple spec.
                # integrated = $name(integrated, vcat(dim, [i]))
              # end
              result = $comb_op(result, integrated) # combine into the result
            end
            # Now we have to integrate the default branch, too, and combine that
            # into the result.
            # I'm going to really oversimplify things, here, and just integrate
            # out the default value and then add it in.
            default_summary = trim($name(follow_tuple_default(tree), dim))
            return $comb_op(result, default_summary)
            # Attempts to do better ~~
            #=
            # If the tsplit default value is holding None() or the identity,
            if (typeof(tree.root.default) == MemLeaf) ? (tree.root.default.value == None() || tree.root.default.value == LeafNode($iden)) : epsilonequal(follow_tuple_default(tree), MemTree(tree.domain, MemLeaf(LeafNode($iden))))
              #|| (epsilonequal(BSPTree(tree.domain.reg, tree.root.default.value), BSPTree(tree.domain.reg, LeafNode($iden)))))) || epsilonequal(follow_tuple_default(tree), MemTree(tree.domain, MemLeaf(LeafNode($iden))))
              # no need to do anything wrt the default value
              return result
            end
            # summarize out any other tsplits on the same variable
            # if i were being really careful i would also zero out any places already covered by branches, here, which would negate the need for the epsilonequal test in the earlier pre-integration tests
            default = $name(follow_tuple_default(tree), dim)
            # check if new value looks innocent
            if epsilonequal(default, MemTree(default.domain, MemLeaf(LeafNode($iden)))) || epsilonequal(default, MemTree(default.domain, MemLeaf(None())))
              return result
            else # == Summarizing Over Possible Tuple Values ==
              # Taking the sum of all possible tuples doesn't make a lot of
              # sense; even with the hyperreal representation, there's no
              # appropriate infinite value to assign to this. However, it does
              # make sense in the case of other summary ops, like max and min.
              # So we are using a passed-in function to define this on a case by
              # case basis. The function should take and return memtrees.
              #n = $name
              #return error("$n doesn't know how to summarize default value $(tree.root.default) in dimension $(dim); not implemented yet!")
              # OK, using passed-in functions:
              default_summary = $t_default(follow_tuple_default(tree), dim)
              return $comb_op(result, default_summary)
            end
            =#
          else # This isn't our target. Integrate the default and each branch, but don't combine.
            new_default = ($name(follow_tuple_default(tree), dim)).root
            new_branches = Dict(map((branch -> branch[1]=>($name(follow_tuple_branch(tree, branch), dim).root)), [tree.root.branches...]))
            return MemTree(($name(tree.domain, dim)), TSplit(varloc_adjustment(tree.root.var, dim), new_branches, new_default))
          end
        elseif t == PSplit
          neg = $name(takeneg(tree), dim)
          pos = $name(takepos(tree), dim)
          if tree.root.var == dim # if the dimension for splitting is also the dimension of integration
            if empty_domain(neg.domain) # checking to see if we can return just one side might slow us down, but can speed us up as well, if we can avoid the combination. Trade-off unclear. But mainly, it makes the code more robust; if things aren't trimmed or trimming has done something wrong, we risk returning an ESig here when there was a sensible result to return.
              return pos # (but mainly, this shouldn't be necc, if we trusted that trim removed all empty branches)
            elseif empty_domain(pos.domain)
              return neg
            else
              return $comb_op(neg, pos)
            end
          else
            return MemTree(($name(tree.domain, dim)), PSplit(varloc_adjustment(tree.root.var, dim), tree.root.loc, neg.root, pos.root))
          end
        else # t == MemLeaf
          if typeof(s) == UnspecifiedTSig
            if typeof(tree.root.value) == LeafNode && tree.root.value.value == $(iden)
              ()
            else
              @warn "Summarizing over not-simply-identity value, with an unspecified tuple variable. This will not always produce sensible results."
            end
            # We're going to dangerously/improperly just return the value in
            # this case, because that's the correct thing to do in the case
            # where there is a correct thing to do, and it's not entirely clear
            # how to check whether it's the right thing to do.
            #
            # We have to handle some dimension reordering, in case the
            # unspecifiedtsig isn't the last dimension, and hence, messes up
            # some indices.
            if last_subsig(dim, tree.domain.sig) # this should be true in normal situations
              return MemTree(Domain( $name(tree.domain.sig, dim), tree.domain.reg, tree.domain.map), tree.root)
            else
              return MemTree( $name(tree.domain, dim), varloc_adjustment(tree.root, dim))
            end
            #=
            # Add an artificial split, so that this can be handled by the TSplit case.
            return $name(MemTree(tree.domain, TSplit(dim, Dict{SpecifiedTSig, MemNode}(), tree.root)), dim)
            =#
          else
            varmap = tree.root.map
            if !haskey(varmap,dim)
              # If the dim isn't present, we have to add it so that we hand first-order integration something which contains the dim to sum.
              # NOTE: There are two different reasons this can happen. One reason is that there was just no reason to represent
              # The variable in question explicitly before now. The second reason is that we may be summarizing a predicate var.
              # In this case, we're adding a "fake" first-order dimension so that we can integrate it out using first-order code.
              varmap = Dict(union(varmap, Dict(dim=>(maximum(union([0],values(varmap))) + 1)))) # would be a little cleaner to find the first unused dim, but ... a bit slower?
            end
            # Reorder the domain region to be compatible with the dimension numbering of the leaf, also getting the new dimnum map so we know what's where.
            (varmap, reordered_reg) = bring_domain_and_leaf_in_line(varmap, tree.domain.map, tree.domain.reg) # TODO make a special case to avoid this if the maps are already equal
            if typeof(s) <: UnitRange
              # add constraints to reordered_reg representing what the domain knows about the predicate variable
              new_bounds = [LinBound(rect_split(varmap[dim], s.start, varmap[dim]), true),
                            LinBound(rect_split(varmap[dim], s.stop+1, varmap[dim]), false)]
              reordered_reg = LinRegion(union(reordered_reg.bounds, new_bounds), reordered_reg.dimensionality)
            end
            # index in first-order tree to sum out
            tree_dim = varmap[dim]
            # first-order summary
            summary = $name(BSPTree(reordered_reg, tree.root.value), tree_dim)
            # remove the summarized dimension from the map, and readjust other varlocs
            varmap = varmap_adjustment(varmap, dim)
            return MemTree(Domain( $name(tree.domain.sig, dim), summary.boundary, varmap), MemLeaf(summary.root, varmap))
          end
        end
      end
      function $name(t::MemTree)
        return $name(t, Int[])
      end
      function $name(s::Signature, var::VarLoc)
        if length(var) == 0 # wait, doesn't this mean to integrate out everything?
          # was returning s unmodified in this case
          # now I think what I should do is return SpecifiedTSig([])
          # there's also an argument for UnspecifiedTSig(), since we also want
          # to integrate out the TSig?? But this only half does it... you still
          # have the tsig, you just don't have anything specific. I guess if I
          # ever run into a case where I need this, I'll be more clear about
          # what should be returned in such a case.
          return UnspecifiedTSig() # throw("$name was asked to summarize out varloc [] (the empty varloc). It's not clear what to do here. \nTree: $tree") # s
        elseif length(var) == 1
          if typeof(s) == PSig
            new_ranges = vcat(s.ranges[1:(var[1]-1)], s.ranges[(var[1]+1):length(s.ranges)])
            return PSig(new_ranges)
          elseif typeof(s) == ESig
            return ESig()
          else # should be a SpecifiedTSig
            new_spec = vcat(s.spec[1:(var[1]-1)], s.spec[(var[1]+1):length(s.spec)])
            return SpecifiedTSig(new_spec)
          end
        else
          new_spec = copy(s.spec)
          new_spec[var[1]] = $name(new_spec[var[1]], var[2:length(var)])
          return SpecifiedTSig(new_spec)
        end
      end
      function $name(d::Domain, var::VarLoc)
        sig = $name(d.sig, var)
        reg = d.reg
        map = d.map
        if haskey(d.map, var)
          reg = project_and_strip(reg, d.map[var])
          map = varmap_adjustment(map, var)
        end
        return Domain(sig,reg,map)
      end
    end
  )
end

# Compilation of summary operators.

memsummary(:integrate,
            #leaf_integrate,
            :+,
            0.0,
            error_t_default_summary(:integrate)
            )

memsummary(:pintegrate,
            #leaf_pintegrate,
            :*,
            1.0,
            error_t_default_summary(:pintegrate)
            )

memsummary(:maxintegrate,
            #((tree, dim) -> tree.root),
            :max,
            -Inf,
            iden_t_default_summary
            )

memsummary(:mintegrate,
            #((tree, dim) -> tree.root),
            :min,
            Inf,
            iden_t_default_summary
            )

# Normalize takes a memtree and returns that memtree after summarizing out all
# variables.

function normalize(t::MemTree)
  denom = integrate(t).root.value.value
  if denom == 0.0
    return mt(t.domain, 1.0)
  else
    return safe_div(t, mt(t.domain, integrate(t).root))
  end
end

function remap_remap(remap::Dict{VarLoc, VarLoc}, d::VarLoc)
  result = Dict{VarLoc, VarLoc}()
  for pair in remap
    result = Dict(varloc_adjustment(pair[1], d) => pair[2], result...)
  end
  return result
end

function integrate_fo(t::MemTree, l::VarLoc=Int[], remap::Dict{VarLoc, VarLoc}=Dict{VarLoc, VarLoc}())
  result = t
  s = t.domain.sig
  if access_defined(s, l) && typeof(access(s, l)) == SpecifiedTSig
    for i in length(access(s, l).spec):-1:1
      (result, remap) = integrate_fo(result, vcat(l, i), remap)
    end
  elseif access_defined(s, l) && typeof(access(s,l)) == VSig
    result = integrate(t, l)
    remap = remap_remap(remap, l)
  else
    remap = Dict(l=>l, remap...)
  end
  return (result, remap)
end

function normalize_fo(t::MemTree)
  (integrated, remap) = integrate_fo(t)
  remapped = MemTree(t.domain, reorder(remap, integrated.root))
  return safe_div(t, remapped)
end







# small test case I started to write





























































# :)     :D
