include("hyperreal.jl")
using JuMP
using Clp

import Base.==


# A split can represent any way of dividing n-dimensional space into two parts.
# This provides the foundation of a BSP tree. The convention here will be to refer
# to the two parts as 'neg' and 'pos' (negative and positive). The "pos" side
# will be the _closed_ side, as well, meaning that the content directly on the
# split belongs to pos.
abstract type Split end

# A LinSplit defines a hyperplane split, with a series of coefficients and a
# constant. If the dot-product of a point with the coefficients is higher than
# or equal to the constant, then the point is on the positive side of the split.
# IE, the positive side is thought of as the closed side.

struct LinSplit <: Split
  coefs::Vector{Float64}
  con::Float64
end

function ==(l1::LinSplit,l2::LinSplit)
  if l1.con!=l2.con
    return false
  else
    for i in 1:max(length(l1.coefs), length(l2.coefs))
      if get(l1.coefs, i, 0.0) != get(l2.coefs, i, 0.0)
        return false
      end
    end
    return true
  end
end

#import Base.hash
#hash(l::LinSplit) = hash([hash(l.coefs),hash(l.con)])

# Just to make things more convenient, I like the constructor to convert things
# to the correct type when necessary.

LinSplit(coef,con) =
  LinSplit(convert(Vector{Float64}, coef), convert(Float64, con))

# An abstract type for a node in a BSPTree.

abstract type BSPNode end

# A sub-type for a "null value".

struct None <: BSPNode
end

# A SplitNode organizes space into two parts by a split.
# The two parts get held in a negative and positive side.

struct SplitNode <: BSPNode
  split::Split # split definition
  neg::BSPNode # negative side
  pos::BSPNode # positive side
end

==(s1::SplitNode, s2::SplitNode) =
  s1.split == s2.split && s1.neg == s2.neg && s1.pos == s2.pos

#hash(s::SplitNode) = hash([hash(s.split),hash(s.neg),hash(s.pos)])

# And then, a leaf type to hold actual contents.

# Aside: I ran into trouble trying to make this a parametric
# type, TreeNode{a} where a represents the leaf content type; when
# I did this, I would get errors when trying to construct
# TreeNode(split, t1, t2) in a generic way. The parameter
# type must be explicitly given. This is a run-time cost
# (look up the type of the trees being handled) so it seemed
# quite silly.

struct LeafNode <: BSPNode
  value::Any
end

==(l1::LeafNode,l2::LeafNode) =
  l1.value == l2.value

#hash(l::LeafNode) = hash(l.value)

# In the simple case, the BSPTree leaves hold Float values.
# Later it may be appropriate to add linear values, making
# it possible to represent piecewise linear functions in the
# BSPTrees.

# It may also be useful to represent non-numerical values, in an even later
# and more general version of the architecture.

# A region compactly dilineates an area of space, such as a rectangle
# or a polyhedron. The main purpose of regions are to indicate the
# area on which a function represented by a BSPTree is defined.

abstract type Region end

# A LinRegion is a region based on hyperplane splits. It is represented by a
# list of splits together with a sign bit for each, indicating whether the
# region is on the positive or negative side. (As previously stated, the
# positive side is the closed side.) "true" indicates the positive side.

# Note: Although this format could actually be used to represent any kind of
# region, I'm not generalizing it now because it's not necessarily the most
# *efficient* representation for all cases.

struct LinBound
  split::LinSplit
  positive::Bool
end

==(l1::LinBound,l2::LinBound) =
  l1.split == l2.split && l1.positive == l2.positive

import Base.isless

function isless(l1::LinBound, l2::LinBound) # defining so they can be sorted
  if l1.positive < l2.positive
    return true
  elseif l2.positive < l1.positive
    return false
  elseif l1.split.con < l2.split.con
    return true
  elseif l2.split.con < l1.split.con
    return false
  else
    for i in 1:length(l1.split.coefs)
      if l1.split.coefs[i] < l2.split.coefs[i]
        return true
      elseif l2.split.coefs[i] < l1.split.coefs[i]
        return false
      end
    end
    return false
  end
end

struct LinRegion <: Region
  bounds::Vector{LinBound}
  dimensionality::Int
end

function regularize_bound(b::LinBound)
  z = sqrt(sum(b.split.coefs .^ 2))
  if z == 0.0
    return b
  else
    return LinBound(LinSplit(b.split.coefs / z, b.split.con / z), b.positive)
  end
end

function ==(l1::LinRegion,l2::LinRegion)
  b1 = map(regularize_bound, trim_region(l1).bounds)
  b2 = map(regularize_bound, trim_region(l2).bounds)
  return sort(b1) == sort(b2)
end

boundless_reg(d::Int) = LinRegion(Vector{LinBound}(),d)

function rect_split(dim,loc,numdims)
  z = zeros(numdims)
  z[dim]=1.0
  return LinSplit(z,loc)
end

function rect_region(mins, maxs)
  max_d = length(mins)
  s = Vector{LinBound}()
  for d in 1:max_d
    z = zeros(max_d)
    z[d] = 1.0
    s = union(s,[LinBound(LinSplit(z,mins[d]), true)])
  end
  for d in 1:max_d
    z = zeros(max_d)
    z[d] = 1.0
    s = union(s,[LinBound(LinSplit(z,maxs[d]), false)])
  end
  return LinRegion(s,max_d)
end

# ==(x,y) is supposed to be implemented by any type that's thought of
# as being a numeric container, like arrays etc
# ==(x::LinRegion,y::LinRegion) =
#  ==(x.bounds,y.bounds)

# I need to extend the isequal function to get the behavior I want for the new datatype.
# In order to extend its behavior, I must first import it.

import Base.isequal

isequal(t1::SplitNode, t2::SplitNode) =
  isequal(t1.split, t2.split) &&
  isequal(t1.pos, t2.pos) &&
  isequal(t1.neg, t2.neg)

isequal(t1::LinSplit, t2::LinSplit) =
  t1.coefs == t2.coefs &&
  t1.con == t2.con

#isequal(t1::Nothing, t2::Nothing) = true


# A BSPTree holds a region which defines the boundary of the
# function defined by the tree, and the root BSPNode for the
# tree.

struct BSPTree
  boundary::Region
  root::BSPNode
end

==(t1::BSPTree, t2::BSPTree) = (t1.boundary == t2.boundary) && isequal(t1.root, t2.root)
isequal(t1::BSPTree, t2::BSPTree) = t1 == t2


# Abbreviations to make tree construction easier.

bsp(b,r) = BSPTree(b,r)
ln(v) = LeafNode(v)
sn(s,n::Float64,p::Float64) = SplitNode(s,ln(n), ln(p))
sn(s,n::Float64,p) = SplitNode(s,LeafNode(n),p)
sn(s,n,p::Float64) = SplitNode(s,n,LeafNode(p))
sn(s,n,p) = SplitNode(s,n,p)
rr(mins, maxs) = rect_region(mins, maxs)
rsp(dim, loc, numdims) = rect_split(dim, loc, numdims)


# `makemodel` returns a pair: the linear system representing a region, and the
# JuMP variable needed to access it.

function makemodel(r::LinRegion)
  #m = Model(solver=ClpSolver(InfeasibleReturn=1,LogLevel=0))
  m = Model(optimizer_with_attributes(Clp.Optimizer, "InfeasibleReturn" => 1, "LogLevel" => 0))
  d = r.dimensionality
  @variable(m,x[1:d])
  for bound in r.bounds
    if bound.positive
      @constraint(m, sum(x[i]*bound.split.coefs[i] for i=1:length(bound.split.coefs)) >= bound.split.con)
    else
      @constraint(m, sum(x[i]*bound.split.coefs[i] for i=1:length(bound.split.coefs)) <= bound.split.con)
    end
  end
  # add "walls at infinity"
  large_num = 1000000000000.0
  for i=1:d
    @constraint(m, x[i]<=large_num)
    @constraint(m, x[i]>=-large_num)
  end
  return (m, x)
end

# `regsat` checks if the linear system for a region has any solutions. This is
# not enough to tell if the region is nonempty, as it ignores whether the region
# is open or closed. Linear solvers don't usually handle strict inequalities.

function regsat(m::Tuple{Model,Array{VariableRef,1}})
  #s = solve(m, suppress_warnings=true)
  @objective(m[1], Max, sum((m[2])[i] for i=1:length(m[2])))
  optimize!(m[1])
  s = termination_status(m[1])
  if s == JuMP.MathOptInterface.INFEASIBLE
    return false
  elseif s == JuMP.MathOptInterface.OPTIMAL
    return true
  elseif s == JuMP.MathOptInterface.DUAL_INFEASIBLE
    # Since the primal problem is feasible, this usually means the problem is
    # unbounded. The JuMP docs say that it could mean something else in some
    # "technical exceptions". Currently this function could return the wrong
    # answer in those exceptional scenarios. TODO: figure out what the technical
    # exceptions are, and whether I need to do something about them.
    @warn "JuMP found a model to be feasible but DUAL_INFEASIBLE. This probably means the region is unbounded, and I'm going with that assumption. However, under some circumstances this could be incorrect. \n Model: \n $(m)"
    return true
  elseif JuMP.MathOptInterface.LOCALLY_SOLVED
    @warn "JuMP found a region to be LOCALLY_SOLVED. This could mean something else, but I'm going to assume it's actually solved. \n Model: \n $(m)"
    return true
  elseif JuMP.MathOptInterface.LOCALLY_INFEASIBLE
    @warn "JuMP found a region to be LOCALLY_INFEASIBLE. This could mean something else, but I'm going to assume it's actually infeasible. \n Model: \n $(m)"
    return false
  elseif JuMP.MathOptInterface.INFEASIBLE_OR_UNBOUNDED
    error("JuMP found a model to be INFEASIBLE_OR_UNBOUNDED. We need to know which of those two hold, but JuMP doesn't say. \n Model: \n $(m)")
  else
    return error("Failed to check feasibility of region. \nExit status: $s\nModel: $m")
  end
end

# Computes the most a region can go in a particular direction, EI, the maximum
# dot-product which can be obtained with a given vector. Ignores the closed or
# open status of constraints. Optionally, takes a final boolean argument (false
# by default); if true, returns the utmost point in that direction rather than
# the value achieved by that point. NOTE: the region given should be feasible.

function sup_in_direction(m::Tuple{Model,Array{VariableRef,1}}, d::Vector{Float64}, argmax=false)
  @objective(m[1], Max, sum(d[i]*(m[2])[i] for i=1:length(d)))
  #s = solve(m[1], suppress_warnings=true)
  optimize!(m[1])
  s = termination_status(m[1])
  if s == JuMP.MathOptInterface.OPTIMAL
    if argmax
      return JuMP.value.(m[2])
    else
      return JuMP.objective_value(m[1])
    end
  elseif JuMP.MathOptInterface.DUAL_INFEASIBLE # assuming feasibility, this should imply unboundedness, except in some "technical cases"
    @warn "sup_in_direction is assuming that DUAL_INFEASIBLE implies unboundedness. This may not be the case."
    if argmax
      error("sup_in_direction doesn't know how to return the argmax of an unbounded linear optimization.")
    else
      return Inf
    end
  elseif JuMP.MathOptInterface.LOCALLY_SOLVED
    @warn "sup_in_direction is assuming LOCALLY_SOLVED means solved."
    if argmax
      return JuMP.value(m[2])
    else
      return JuMP.objective_value(m[1])
    end
  else
    return error("sup_in_direction failed to get useful results from linear optimization. \nExit status: $s\nModel:\n$m")
  end
end

#

# Check if the region is a rectangle. If so, return +1 if it's valid, and -1 if
# not. Otherwise, return 0.

function rect_valid(r::Region)
  max_d = r.dimensionality
  maxs = fill(Inf, max_d)
  maxs_closed = trues(max_d) # whether the maximum is closed
  mins = fill(-Inf, max_d)
  mins_closed = trues(max_d) # whether the minimum is closed
  for bound in r.bounds # Go through bounds checking number of nonzero coefs; if >1, return 0; if 1, record the new min/max implied.
    bound_coefs = bound.split.coefs
    bound_length = length(bound_coefs)
    if bound_length > max_d
      throw("rect_valid handed a region with more coefficients than dimensions: $r")
    end
    nonzero_count = 0
    nonzero_loc = 0
    for dim in 1:bound_length
      if !(bound_coefs[dim] == 0.0)
        nonzero_count = nonzero_count + 1
        if nonzero_count > 1
          return 0
        end
        nonzero_loc = dim
      end
    end
    if nonzero_loc > 0 #if the bound is doing anything at all
      # Now that we know the bound is uni-dimensional, add it to the list of dimension bounds.
      adjusted_con = bound.split.con/bound_coefs[nonzero_loc] # The actual location for this bound.
      if bound.positive # closed bound
        if bound_coefs[nonzero_loc] > 0.0 # positive coef, so bound.positive=true means the bound is expressing a minimum
          if adjusted_con > mins[nonzero_loc] # lower bound would be increased
            mins[nonzero_loc] = adjusted_con
            mins_closed[nonzero_loc] = true # inherits the closed status, since we increased past whatever the bound previously might have been
          end # if the bound is less than or equal to one already established, we have no need to update the open or closed status in this case, since it could only be loosening the constraint, which we don't want to do
        elseif bound_coefs[nonzero_loc] < 0.0 # negative coef, so bound is actually a maximum, since -x>=c means x<=c
          if adjusted_con < maxs[nonzero_loc] # existing upper bound would be decreased
            maxs[nonzero_loc] = adjusted_con
            maxs_closed[nonzero_loc] = true # inherits the open status, since we decreased past whatever the previous bound would have been
          end # no need to update open/closed status otherwise
        end
      else # open bound
        if bound_coefs[nonzero_loc] > 0.0 # positive coef, so bound is saying x<c, IE giving a max
          if adjusted_con < maxs[nonzero_loc] # new max would be lower than old max
            maxs[nonzero_loc] = adjusted_con # lower the max
            maxs_closed[nonzero_loc] = false # inherit the open status
          elseif adjusted_con == maxs[nonzero_loc] # if they're equal, we don't need to update the max, but we may need to switch it from closed to open since an open constraint is stricter
            maxs_closed[nonzero_loc] = false # let's just assign; no point checking
          end # otherwise, nothing to update; we were already maximally strict
        elseif bound_coefs[nonzero_loc] < 0.0 && adjusted_con >= mins[nonzero_loc] # negative coef, so we're saying -x<c, IE x>c, so we are giving a min
          if adjusted_con > mins[nonzero_loc] # new min would be higher
            mins[nonzero_loc] = adjusted_con
            mins_closed[nonzero_loc] = false # inherit the open status
          elseif adjusted_con == mins[nonzero_loc] # if they're equal, we still need to enforce openness
            mins_closed[nonzero_loc] = false
          end
        end
      end
    else # no nonzero locs in this bound, because we already checked whether there's 1, and returned for the case where there's more than one
      if bound.positive && bound.split.con > 0 # no way to get > 0 with no coefficients; this region is invalid
        return -1
      elseif !bound.positive && bound.split.con <= 0 # if the constant is 0 or below, there's no way we can get strictly under it
        return -1
      end
    end
  end
  # Now that we've added all the bounds, check for validity.
  for dim in 1:max_d
    if maxs[dim] < mins[dim] || (maxs[dim]==mins[dim] && !(maxs_closed[dim] && mins_closed[dim]))
      return -1
    end
  end
  return +1
end

# TODO use this somewhere, eg, to eliminate useless bounds, or as part of a quick initial check in regvalid 
function zero_bound_check(b::LinBound) # using the same idea as the zero-coef bound case in rect_valid, returns +1 if the bound rules out nothing, -1 if everything, otherwise zero
  if all((x->x==0.0), b.split.coefs)
    if b.positive
      if b.split.con > 0
        return -1
      else
        return +1
      end
    else
      if b.split.con <= 0
        return -1
      else
        return +1
      end
    end
  else
    return 0
  end
end


# `regvalid` takes a region and checks if it is non-empty. This doesn't mean
# "has nonzero area"; it means "contains any points". This is more than just
# feasibility of the linear system constraining us to the region, because
# linear programming ignores whether edges are open. I include false negatives
# rather than false positives; regions with open edges may be declared empty
# if I can't optimize away from those edges by more than epsilon (moving
# orthogonally to the open hyperplane).

function regvalid(r::LinRegion, epsilon::Float64=0.0000001)
  l = length(r.bounds)
  if l == 0
    return true
  end
  r_v = rect_valid(r)
  if r_v==1
    return true
  elseif r_v==-1
    return false
  end
  m = makemodel(r)
  if !regsat(m) # first check whether the model is feasible. This pretends all constraints are closed.
    return false
  end
  # The closure is feasible. Now we have to check whether each open constraint has room to breathe.
  for bound in r.bounds
    if !(bound.positive)
      d = -bound.split.coefs
      @objective(m[1], Max, sum(d[i]*(m[2])[i] for i=1:length(d))) # optimize away from each face
      #s = solve(m[1], suppress_warnings=true)
      optimize!(m[1])
      s = termination_status(m[1])
      if s == JuMP.MathOptInterface.OPTIMAL
        # the region's closure has points in it
        # now we just need to figure out whether the region actually has points in it
        optimize_away = JuMP.objective_value(m[1])
        difference = optimize_away + bound.split.con # Since things are negative, I want the optimized value minus the **negative of** the constant; so really I want to add them.
        if difference < epsilon
          return false
        end
      # The INFEASIBLE case should absolutely be tested outside of the loop, not
      # inside, because I only loop over < constraints, not >= constraints; so
      # I would miss infeasibility for all->= regions (closed regions).
      #elseif s == JuMP.MathOptInterface.INFEASIBLE
      #  return false # The whole problem is infeasible. Definitely an invalid region.
      elseif s == JuMP.MathOptInterface.DUAL_INFEASIBLE
        # Pushed unboundedly far in one direction. This means this particular
        # constraint is definitely good to go. But, others could still fail!
        () # do nothing
      else # We already made sure the model wasn't infeasible, so something weird must have happened
        error("regvalid didn't manage to solve a linear program.\nTermination status:\n$(s)\nRegion:\n$(r)\nModel:\n$(m)")
      end
    end
  end
  return true
end

regvalid(r::BSPTree) =
  regvalid(r.boundary)


# Remove redundant bounds in a region.

function trim_region(r::LinRegion)
  current = 1
  bounds = r.bounds
  max = length(bounds)
  while current <= max
    others = union(bounds[1:current-1], bounds[current+1:max])
    b = bounds[current]
    # Commented out the all-zero check below. Regvalid should handle that case as well, now.
    if !regvalid(LinRegion(union(others, [LinBound(b.split, !b.positive)]), r.dimensionality)) # || all((x -> x==0.0), b.split.coefs) # See if there's currently anything this added split would rule out. (This happens if EITHER the bound's negation doesn't capture anything from the current region, OR the bound's coefficients are all 0.0.)
      bounds = others # if not, take it out,
      max = length(bounds) # and set the new max.
    else # in the case that the constraint was necessary,
      current = current + 1 # move to the next constraint to check.
    end
  end
  return LinRegion(bounds,r.dimensionality)
end

function trim_region(t::BSPTree)
  return BSPTree(trim_region(t.boundary), t.root)
end


# intersection takes the intersection of two regions. Does not check for
# inconsistency of constraints or redundancy of constraints.

function intersection(r1::LinRegion, r2::LinRegion)
  # if !(r1.dimensionality==r2.dimensionality)
    # error("Dimensions did not match when taking intersection:\n $r1\n $r2")
  # end
  return LinRegion(union(r1.bounds, r2.bounds), max(r1.dimensionality, r2.dimensionality))
end


# Check whether two regions intersect.

function intersects(r1::Region, r2::Region)
  return regvalid(intersection(r1, r2))
end

# Makes a split a desired length, but throws an error if you're trying to make
# it shorter.

function correct_split_length(s::LinSplit, d::Int)
  l = length(s.coefs)
  if d<length(s.coefs)
    throw("Tried to extend split dimensions to less that already existed: wanted $d dimensions for $l")
  elseif l == d
    return s
  else
    new_coefs = zeros(d)
    new_coefs[1:l] = s.coefs
    return LinSplit(new_coefs, s.con)
  end
end

# `takepos` and `takeneg` take the respective halves of a region according to a
# newly provided split; or, if given a BSPTree, according to the top split
# (this'll be an error if the top node is not a SplitNode). Split length is
# corrected when adding to a region, because region manipulation functions may
# not work with the wrong lengths.
# TODO I might want to strip out the length check to increase efficiency, and
# make sure all region-handling functions assume zero values when vectors come
# up short, instead.

takepos(reg::LinRegion, split::LinSplit) = LinRegion(union(reg.bounds, [LinBound(split, true)]), reg.dimensionality)
takeneg(reg::LinRegion, split::LinSplit) = LinRegion(union(reg.bounds, [LinBound(split, false)]), reg.dimensionality)

takepos(tree::BSPTree) =
  BSPTree(takepos(tree.boundary, tree.root.split), tree.root.pos)

takeneg(tree::BSPTree) =
  BSPTree(takeneg(tree.boundary, tree.root.split), tree.root.neg)


# Check whether the first region is a subset of the second. This is not a
# strict subset; all regions count as a subset of themselves.

function subset(sub::LinRegion, sup::LinRegion)
  if !(regvalid(sub)) # if sub is the empty set, it's trivially a subset
    return true
  elseif !(intersects(sub,sup))
    return false # If sub is non-empty but doesn't intersect sup, definitely not a subset.
  else
    for bound in sup.bounds
      cut = bound.positive ? takeneg(sub, bound.split) : takepos(sub, bound.split) # Add the negation of each of sup's bounds to sub.
      if regvalid(cut)
        return false # If some of the sub is outside the sup, not a subset.
      end
    end
    return true
  end
end


# The query function is used to retrieve a desired part of a BSPTree. The output
# is still a BSPTree. It takes a tree and a query region.

function query(tree::BSPTree, region::LinRegion)
  tree = trim(BSPTree(intersection(region, tree.boundary), tree.root))
  return tree
end


# Trim(tree) removes unnecessary parts of a tree; specifically, anything which
# falls outside of the region of the tree, and anything which falls in a region
# which would be invalid.
# NOTE: does not trim the region of excess bounds. That's an expensive
# procedure, since the current implementation checks feasibility many times.

# The goal is to (1) remove splits which aren't actually doing anything, and
# (2) merge splits which are dividing identical regions. For (2), I could in
# theory have a somewhat more sophisticated strategy.
#   -> Perhaps _first_ trim the two branches, and _then_ merge if equal.
#      Imagine a fairly shattered region of all the same value. The current
#      strategy starts at the top and checks whether two halves of (the
#      untrimmed version of) the tree are epsilonequal, involving descending
#      both sides in their large untrimmed form. It then discards one as
#      unnecessary, and trims the other -- meaning it descends half the tree
#      again, performing the epsilonequal comparison at every level. On the
#      other hand, trimming first descends the tree with trim, rather than
#      epsilonequal. It then starts asking whether stuff is identical as it
#      returns, merging recursively.
#        -> Hm... Ok, both end up calling epsilonequal at every tree level, so I
#           guess that's not very persuasive.
#        -> Ah, but the proposed modification calls epsilonequal on smaller,
#           trimmed trees. The disadvantage is that it does not discard a tree
#           before trimming, in the lucky case of equality.
#        -> ... But then again, epsilonequal doesn't get too much benefit from
#           being called on trimmed trees, I think -- it checks region validity
#           as it goes, so it'll onle go one step into an invalid branch. Hm.
#           That could still be a significant cost, tho, since checking region
#           validity is expensive.
#        -> It might be that I'd do better to trim boundaries and merge equal
#           values as entirely seperate recursions.
#   -> Another idea is to take the suggestion above, but only do a simple
#      comparison of leaf values for equality. This trims less overall, but, it
#      is potentially much cheaper, and could get most of the benefit. I could
#      differentiate these two trims ass a cheaper and more expensive trim, and
#      somehow do the more expensive trim occasionally.
# NOTE: The current trimming alg checks region validity at each node. An
# alternative would be to check region validity only at leaf nodes, and
# return some kind of null signal to indicate invalidity. This would cut the
# number of validity checks in half, for trees which actually don't need
# trimming. However, the current approach is potentially much more efficient for
# trees that DO need trimming -- its worst-case number of checks is about twice
# the number of nodes with valid regions, which may be much less than all the
# nodes.

#=
function trim(tree::BSPTree)
  if !(regvalid(tree.boundary))
    return BSPTree(tree.boundary, None())
  elseif typeof(tree.root) == SplitNode #
    pos_tree = takepos(tree)
    neg_tree = takeneg(tree)
    pos_valid = regvalid(pos_tree)
    neg_valid = regvalid(neg_tree)
    if pos_valid && neg_valid
      if epsilonequal(BSPTree(tree.boundary,tree.root.pos), BSPTree(tree.boundary,tree.root.neg))
        return trim(BSPTree(tree.boundary,tree.root.pos))
      else
        return BSPTree(tree.boundary, SplitNode(tree.root.split, trim(neg_tree).root, trim(pos_tree).root))
      end
    elseif pos_valid
      return BSPTree(tree.boundary, trim(pos_tree).root)
    elseif neg_valid
      return BSPTree(tree.boundary, trim(neg_tree).root)
    else
      return error("Trim error: Tree region valid, but neither side of its split valid, in: $tree")
    end
  elseif typeof(tree.root) == LeafNode
    return tree
  elseif typeof(tree.root) == None
    return tree
  else
    error("Trim encountered unfamiliar node type in: $tree")
  end
end
=#

trim(tree::BSPTree) = modified_trim(tree)


# Trims with an additional boundary region.

trim(tree::BSPTree, r::Region) = trim(BSPTree(intersection(tree.boundary, r), tree.root))

# Trimming everything under a node with no boundary.

#trim(node::BSPNode) = trim(BSPTree(boundless_reg(),node)).root


function orig_trim(tree::BSPTree)
  if !(regvalid(tree.boundary))
    return BSPTree(tree.boundary, None())
  elseif typeof(tree.root) == SplitNode #
    pos_tree = takepos(tree)
    neg_tree = takeneg(tree)
    pos_valid = regvalid(pos_tree)
    neg_valid = regvalid(neg_tree)
    if pos_valid && neg_valid
      if epsilonequal(BSPTree(tree.boundary,tree.root.pos), BSPTree(tree.boundary,tree.root.neg))
        return orig_trim(BSPTree(tree.boundary,tree.root.pos))
      else
        return BSPTree(tree.boundary, SplitNode(tree.root.split, orig_trim(neg_tree).root, orig_trim(pos_tree).root))
      end
    elseif pos_valid
      return BSPTree(tree.boundary, orig_trim(pos_tree).root)
    elseif neg_valid
      return BSPTree(tree.boundary, orig_trim(neg_tree).root)
    else
      return error("Trim error: Tree region valid, but neither side of its split valid, in: $tree")
    end
  elseif typeof(tree.root) == LeafNode
    return tree
  elseif typeof(tree.root) == None
    return tree
  else
    error("Trim encountered unfamiliar node type in: $tree")
  end
end


# partial trim may be appropriate when recursively processing a
# tree: we want to trim off the parts we know are irrelevant at the
# moment, but we don't want to descend the entire tree to do that,
# because we will descend the tree as we go anyway. Therefore we
# can just trim unnecessary split nodes when we encounter them.

function partialtrim(tree::BSPTree)
  if typeof(tree.root) == SplitNode
    if epsilonequal(tree.root.pos, tree.root.neg)
      return BSPTree(tree.boundary, tree.root.pos)
    else
      pos_tree = takepos(tree)
      neg_tree = takeneg(tree)
      pos_valid = regvalid(pos_tree)
      neg_valid = regvalid(neg_tree)
      if pos_valid
        if neg_valid
          return tree
        else
          return pos_tree
        end
      elseif neg_valid
        return neg_tree
      else
        return BSPTree(tree.boundary,None())
      end
    end
  end
end

# Almost exactly like regular trim, except it trims the pos branch before doing
# the epsilonequal check. Hopefully that's measurably faster.

function s_trim(tree::BSPTree)
  if !(regvalid(tree.boundary))
    return BSPTree(tree.boundary, None())
  elseif typeof(tree.root) == SplitNode #
    pos_tree = takepos(tree)
    neg_tree = takeneg(tree)
    pos_valid = regvalid(pos_tree)
    neg_valid = regvalid(neg_tree)
    if pos_valid && neg_valid
      trimmed_pos = s_trim(pos_tree).root
      if epsilonequal(BSPTree(tree.boundary, trimmed_pos), BSPTree(tree.boundary, tree.root.neg))
        return BSPTree(tree.boundary, trimmed_pos)
      else
        return BSPTree(tree.boundary, SplitNode(tree.root.split, s_trim(neg_tree).root, trimmed_pos))
      end
    elseif pos_valid
      return BSPTree(tree.boundary, s_trim(pos_tree).root)
    elseif neg_valid
      return BSPTree(tree.boundary, s_trim(neg_tree).root)
    else
      return error("Trim error: Tree region valid, but neither side of its split valid, in: $tree")
    end
  elseif typeof(tree.root) == LeafNode
    return tree
  elseif typeof(tree.root) == None
    return tree
  else
    error("Trim encountered unfamiliar node type in: $tree")
  end
end


# Trim without epsilonequal check. This should be significantly cheaper.

function cheap_trim(tree::BSPTree)
  if !(regvalid(tree.boundary))
    return BSPTree(tree.boundary, None())
  elseif typeof(tree.root) == SplitNode #
    pos_tree = takepos(tree)
    neg_tree = takeneg(tree)
    pos_valid = regvalid(pos_tree)
    neg_valid = regvalid(neg_tree)
    if pos_valid && neg_valid
      return BSPTree(tree.boundary, SplitNode(tree.root.split, cheap_trim(neg_tree).root, cheap_trim(pos_tree).root))
    elseif pos_valid
      return BSPTree(tree.boundary, cheap_trim(pos_tree).root)
    elseif neg_valid
      return BSPTree(tree.boundary, cheap_trim(neg_tree).root)
    else
      return error("Trim error: Tree region valid, but neither side of its split valid, in: $tree")
    end
  elseif typeof(tree.root) == LeafNode
    return tree
  elseif typeof(tree.root) == None
    return tree
  else
    error("Trim encountered unfamiliar node type in: $tree")
  end
end

cheap_trim(tree::BSPTree, r::Region) = cheap_trim(BSPTree(intersection(tree.boundary, r), tree.root))

# Merge epsilonequal stuff top-down. Assumes argument has already had a
# cheap_trim. Top-down has the benefit of discarding identical branches early,
# at the cost of more costly epsilonequal calculations due to not handing it
# maximally merged trees.

function merge_top_down(tree::BSPTree)
  if typeof(tree.root) == SplitNode
    merged_pos = merge_top_down(takepos(tree)).root
    if epsilonequal(BSPTree(tree.boundary, merged_pos), BSPTree(tree.boundary, tree.root.neg))
      return BSPTree(tree.boundary, merged_pos)
    else
      merged_neg = merge_top_down(takeneg(tree)).root
      return BSPTree(tree.boundary, SplitNode(tree.root.split, merged_neg, merged_pos))
    end
  else # LeafNode or None
    return tree
  end
end

# Merge epsilonequal stuff bottom-up. In my testing, this one turns out to be
# the faster of the two options.

function merge_bottom_up(tree::BSPTree)
  if typeof(tree.root) == SplitNode
    merged_pos = merge_bottom_up(takepos(tree)).root
    merged_neg = merge_bottom_up(takeneg(tree)).root
    if epsilonequal(BSPTree(tree.boundary, merged_pos), BSPTree(tree.boundary, merged_neg))
      return BSPTree(tree.boundary, merged_pos)
    else
      return BSPTree(tree.boundary, SplitNode(tree.root.split, merged_neg, merged_pos))
    end
  else # LeafNode or None
    return tree
  end
end

# Cheap_merge only checks epsilon equality of values in leaf nodes.

function cheap_merge(tree::BSPTree)
  if typeof(tree.root) == SplitNode
    merged_pos = cheap_merge(takepos(tree)).root
    merged_neg = cheap_merge(takeneg(tree)).root
    if typeof(merged_pos) == LeafNode && typeof(merged_neg) == LeafNode
      if epsilonequal(merged_pos.value, merged_neg.value)
        return BSPTree(tree.boundary, merged_pos)
      end
    end
    return BSPTree(tree.boundary, SplitNode(tree.root.split, merged_neg, merged_pos))
  else # LeafNode or None
    return tree
  end
end

# Get the same result as trim() in two seperate steps.

function two_part_trim(tree::BSPTree)
  return merge_top_down(cheap_trim(tree))
end

function two_part_trim_2(tree::BSPTree)
  return merge_bottom_up(cheap_trim(tree))
end

# The regular trim function checks epsilon-equality before descending splits,
# so that it can avoid descending identical branches. This trim function instead
# trims before checking equality, so that it can call epsilonequal on trimmed
# trees (at the cost of not discarding duplicate trees early).

function modified_trim(tree::BSPTree)
  if !(regvalid(tree.boundary))
    return BSPTree(tree.boundary, None())
  elseif typeof(tree.root) == SplitNode #
    pos_tree = takepos(tree)
    neg_tree = takeneg(tree)
    pos_valid = regvalid(pos_tree)
    neg_valid = regvalid(neg_tree)
    if pos_valid && neg_valid
      trimmed_pos = modified_trim(pos_tree).root
      trimmed_neg = modified_trim(neg_tree).root
      if epsilonequal(BSPTree(tree.boundary, trimmed_pos), BSPTree(tree.boundary, trimmed_neg))
        return BSPTree(tree.boundary,trimmed_pos)
      else
        return BSPTree(tree.boundary, SplitNode(tree.root.split, trimmed_neg, trimmed_pos))
      end
    elseif pos_valid
      return BSPTree(tree.boundary, modified_trim(pos_tree).root)
    elseif neg_valid
      return BSPTree(tree.boundary, modified_trim(neg_tree).root)
    else
      return error("Trim error: Tree region valid, but neither side of its split valid, in: $tree")
    end
  elseif typeof(tree.root) == LeafNode
    return tree
  elseif typeof(tree.root) == None
    return tree
  else
    error("Trim encountered unfamiliar node type in: $tree")
  end
end

# g_trim is like modified_trim that's trying to get some of the advantage of
# orig_trim. It waits until later to do the epsilonequal test, but it does an
# == test right away. This may get most of the advantage: a large branch
# discarded due to epsilon-equality is probably an == branch created by insert.
# OTOH even an == check might be too expensive to be worth it.
# ETA indeed, turns out this wasn't a very good idea. It's only a little faster
# than s_trim. Far slower than modified_trim and the two_part_trims.

function g_trim(tree::BSPTree)
  if !(regvalid(tree.boundary))
    return BSPTree(tree.boundary, None())
  elseif typeof(tree.root) == SplitNode #
    pos_tree = takepos(tree)
    neg_tree = takeneg(tree)
    pos_valid = regvalid(pos_tree)
    neg_valid = regvalid(neg_tree)
    if pos_valid && neg_valid
      trimmed_pos = g_trim(pos_tree).root
      if pos_tree == neg_tree
        return BSPTree(tree.boundary, trimmed_pos)
      else
        trimmed_neg = g_trim(neg_tree).root
        if epsilonequal(BSPTree(tree.boundary, trimmed_pos), BSPTree(tree.boundary, trimmed_neg))
          return BSPTree(tree.boundary,trimmed_pos)
        else
          return BSPTree(tree.boundary, SplitNode(tree.root.split, trimmed_neg, trimmed_pos))
        end
      end
    elseif pos_valid
      return BSPTree(tree.boundary, g_trim(pos_tree).root)
    elseif neg_valid
      return BSPTree(tree.boundary, g_trim(neg_tree).root)
    else
      return error("Trim error: Tree region valid, but neither side of its split valid, in: $tree")
    end
  elseif typeof(tree.root) == LeafNode
    return tree
  elseif typeof(tree.root) == None
    return tree
  else
    error("Trim encountered unfamiliar node type in: $tree")
  end
end


# Trim with a minimal merging step, which only checks the epsilon-equality of
# leaf nodes.

function leaf_merge_trim(tree::BSPTree)
  if !(regvalid(tree.boundary))
    return BSPTree(tree.boundary, None())
  elseif typeof(tree.root) == SplitNode #
    pos_tree = takepos(tree)
    neg_tree = takeneg(tree)
    pos_valid = regvalid(pos_tree)
    neg_valid = regvalid(neg_tree)
    if pos_valid && neg_valid
      trimmed_pos = leaf_merge_trim(pos_tree).root
      trimmed_neg = leaf_merge_trim(neg_tree).root
      if (typeof(trimmed_pos) == LeafNode && typeof(trimmed_neg) == LeafNode) && epsilonequal(trimmed_pos.value, trimmed_neg.value)
        return BSPTree(tree.boundary,trimmed_pos)
      else
        return BSPTree(tree.boundary, SplitNode(tree.root.split, trimmed_neg, trimmed_pos))
      end
    elseif pos_valid
      return BSPTree(tree.boundary, leaf_merge_trim(pos_tree).root)
    elseif neg_valid
      return BSPTree(tree.boundary, leaf_merge_trim(neg_tree).root)
    else
      return error("Trim error: Tree region valid, but neither side of its split valid, in: $tree")
    end
  elseif typeof(tree.root) == LeafNode
    return tree
  elseif typeof(tree.root) == None
    return tree
  else
    error("Trim encountered unfamiliar node type in: $tree")
  end
end

# 'semantic' equality check (ignoring tree structure)

# epsilonequal takes two BSPTrees and an epsilon, creates regions
# corresponding to the intersections of leaf regions of the two,
# and checks to see if the two trees in these regions are
# within epsilon of being equal. Warning: areas outside the
# boundary of either tree are not checked. In other words,
# this checks equality at the intersection of the regions
# of each tree, not elsewhere. This allows the recursion to
# have a simple form, avoiding breaking into many cases for
# the intersecting and non-intersecting parts.

# Another warning: this treats None() and non-None() as not being epsilonequal.
# This is inconsistent with the convention of treating out-of-bounds and None()
# in the same way. So, don't rely on that convention.


function epsilonequal(t1::BSPTree, t2::BSPTree, epsilon::Float64=0.0000001)
  if !(regvalid(intersection(t1.boundary, t2.boundary), epsilon))
    return true # If they have no intersection, they trivially agree about it!
  elseif typeof(t1.root) == SplitNode
    return epsilonequal(takepos(t1), t2, epsilon) && epsilonequal(takeneg(t1), t2, epsilon)
  elseif typeof(t2.root) == SplitNode
    return epsilonequal(takepos(t2), t1, epsilon) && epsilonequal(takeneg(t2), t1, epsilon)
  elseif t1.root == None() && t2.root == None()
    return true
  elseif t1.root == None() || t2.root == None()
    return false
  else
    return epsilonequal(t1.root.value, t2.root.value, epsilon)
  end
end


# Modified version which may be faster on trimmed input. Seems MUCH slower on
# untrimmed input, however. Could warrant further investigation.
#=
function epsilonequal(t1::BSPTree, t2::BSPTree, epsilon::Float64=0.0000001)
  if typeof(t1.root) == SplitNode
    return epsilonequal(takepos(t1), t2, epsilon) && epsilonequal(takeneg(t1), t2, epsilon)
  elseif !(regvalid(intersection(t1.boundary, t2.boundary), epsilon))
    return true # If they have no intersection, they trivially agree about it!
  elseif typeof(t2.root) == SplitNode
    return epsilonequal(takepos(t2), t1, epsilon) && epsilonequal(takeneg(t2), t1, epsilon)
  elseif t1.root == None() && t2.root == None()
    return true
  elseif t1.root == None() || t2.root == None()
    return false
  else
    return epsilonequal(t1.root.value, t2.root.value, epsilon)
  end
end
=#

# epsilonequal(a::Float64, b::Float64, epsilon::Float64=0.0000001) = (a == b) || (abs(a - b) < epsilon)

# I need NaNs to be equal in order to correctly quiesce in their presence.
# Without that, I'm getting rules that think their output is continuing to
# change due to their NaNs. This is making such a rule fire over and over,
# blocking progress in the computation as we continue computing such a rule over
# and over again.

function epsilonequal(a::Float64, b::Float64, epsilon::Float64=0.0000001)
  if isnan(a) && isnan(b) # can't use == to test equality for NaN, as NaN is not == to NaN.
    return true
  else
    return (a == b) || (abs(a - b) < epsilon)
  end
end

function epsilonequal(a::Hyper, b::Hyper, epsilon::Float64=0.0000001)
  if a==b
    return true
  elseif (a.mantissa == b.mantissa) && epsilonequal(a.value, b.value, epsilon)
    return true
  elseif a.value == Inf && b.value == Inf
    return true
  elseif a.value == -Inf && b.value == -Inf
    return true
  else
    return false
  end
end

epsilonequal(a::Hyper, b::Number, epsilon::Float64=0.0000001) = epsilonequal(a, convert(Hyper,b), epsilon)

epsilonequal(a::Number, b::Hyper, epsilon::Float64=0.0000001) = epsilonequal(convert(Hyper,a), b, epsilon)

epsilonequal(a::Number, b::Number, epsilon::Float64=0.0000001) = epsilonequal(convert(Float64,a), convert(Float64,b), epsilon)

epsilonequal(a::LinBound, b::LinBound, epsilon::Float64=0.0000001) =
  a.positive == b.positive && epsilonequal(a.split, b.split, epsilon)

epsilonequal(a::LinSplit, b::LinSplit, epsilon::Float64=0.0000001) =
  epsilonequal(a.con, b.con, epsilon) && all(map(((x,y) -> epsilonequal(x,y, epsilon)), a.coefs, b.coefs)) # shouldn't really be assuming the vectors have same length here

# for nodes
# epsilonequal(t1::BSPNode, t2::BSPNode, epsilon) = epsilonequal(BSPTree(boundless_reg(),t1), BSPTree(boundless_reg(),t2), epsilon)



# Diff between two trees. Returns a vector of bsptrees from the first arg which
# differ from the corresponding region in the second.

function treediff(t1::BSPTree, t2::BSPTree, epsilon::Float64=0.0000001)
  if !(regvalid(intersection(t1.boundary, t2.boundary)))
    return BSPTree[] # If they have no intersection, they trivially agree about it!
  elseif typeof(t1.root) == SplitNode
    return vcat(treediff(takepos(t1), t2, epsilon), treediff(takeneg(t1), t2, epsilon))
  elseif typeof(t2.root) == SplitNode
    return vcat(treediff(t1, takepos(t2), epsilon), treediff(t1, takeneg(t2), epsilon))
  elseif t1.root == None() && t2.root == None()
    return BSPTree[]
  elseif t1.root == None() || t2.root == None()
    return BSPTree[trim_region(t1)]
  else
    if epsilonequal(t1.root.value, t2.root.value, epsilon)
      return BSPTree[]
    else
      return BSPTree[BSPTree(trim_region(intersection(t1.boundary, t2.boundary)), t1.root)]
    end
  end
end

#treediff(t1::BSPTree, t2::BSPTree) = treediff(t1, t2, epsilon)


# Useful functions for constructing trees.

# sqtree makes a square at given coordinates; for example, v=[0.0,0.0] makes a
# square in the 2D plane from the origin to [1.0,1.0].

sqtree(v::Vector, val::Number) =  BSPTree(rect_region(v,v.+1.0), LeafNode(val))
sqtree(v::Vector) = sqtree(v, 1.0)

function randomrect(n)
  mins = rand(n)
  maxs = rand(n)+mins
  return rect_region(mins,maxs)
end

function randomrect()
  randomrect(2)
end

function randomsplit(n)
  LinSplit(rand(n),rand())
end

function random_rect_split(n)
  coefs = zeros(n)
  coefs[rand(1:n)] = 1.0
  LinSplit(coefs,rand())
end

# creates a balanced tree of the given depth
function randomtree(dims, depth)
  if depth == 0
    return LeafNode(rand())
  else
    return SplitNode(randomsplit(dims),
                     randomtree(dims,depth-1),
                     randomtree(dims,depth-1))
  end
end

function random_rect_tree(dims, depth)
  if depth == 0
    return LeafNode(rand())
  else
    return SplitNode(random_rect_split(dims),
                     random_rect_tree(dims,depth-1),
                     random_rect_tree(dims,depth-1))
  end
end

function delta_slice(s::LinSplit, value)
  if !(typeof(value) <: BSPNode)
    value = LeafNode(value)
  end
  return SplitNode(s,
    LeafNode(0.0),
    SplitNode(LinSplit(-s.coefs,-s.con),
      LeafNode(0.0),
      value))
end

delta_slice(s::LinSplit) = delta_slice(s, Hyper(1.0,1))

function delta_reg(s::LinSplit)
  bound1 = LinBound(s,true)
  bound2 = LinBound(LinSplit(-s.coefs, -s.con), true)
  return LinRegion([bound1,bound2],length(s.coefs))
end

# TODO converting into an array
#=
import Base.convert
function convert(::Type{BSPTree}, v::Array{Float64, 1})
  result = BSPTree(RectRegion([0.0], convert(Float64,length(v))), LeafNode(0.0))
  stack = [(1,length(v)) for i = 1:integer(floor(log(2, length(v))))]
  depth = 1
  for i = 1:(2*length(v))

  end
end
=#


# Dimension reordering is a necessary step of combination, putting
# all the functions into the same dimensional space. In this case,
# the permutation is represented as an array of integers; the Nth
# dimension becomes the Mth dimension, where M is the integer in
# the Nth location of the permutation array. For example, the array
# [2 3 4 1] would put the first dimension in the input as the 2nd
# in the output, the 4th dimension in the input to the 1st in the
# output, and so on. Additionally, a permutation may be given as
# a None, in which case we return the first argument unchanged. [temporarily? suspended None() permutation]

#   If the output dimensionality is to be larger than the input dimensionality,
# we have some destinations with no source and must pad empty spaces with
# something (which defaults to zero). On the other hand, an out_d less than the
# input dimensionality will raise an error.
#   If the permutation vector is longer than the number of dimensions in the
# input (or the output), that's fine. If it's shorter than the number of dims in
# the input, that will raise an error, even if it's not shorter than the desired
# output (because we don't have enough information to construct the output).
#   A desired out_d longer than the input
# On the other hand, there is no problem with using this reordering
# to collapse the number of dims; it is fine to give a region with more
# dimensions than are mentioned in the permutation. It's necessary to handle
# that by filling in appropriate values for the additional dimensions.

function reorder(v::Vector, perm::Vector, out_d::Int, default=0.0::Any)
  r = Array{typeof(default),1}(undef, out_d)
  fill!(r, default)
  for i=1:length(v)
    r[perm[i]] = v[i]
  end
  return r
end

#function reorder(item::Any, perm::None, out_d::Int, default=0.0::Any)
#  reorder(item, collect(1:length(item), out_d, default))
#end

reorder(node::SplitNode, perm::Vector, out_d::Int) =
  SplitNode(reorder(node.split, perm, out_d::Int),
            reorder(node.neg, perm, out_d::Int),
            reorder(node.pos, perm, out_d::Int))

reorder(split::LinSplit, perm::Vector, out_d::Int) =
  LinSplit(reorder(split.coefs,perm,out_d::Int,0.0), split.con)

# because a leaf currently only holds a float, not a linear function,
# no reordering is needed.
reorder(leaf::LeafNode, perm::Vector, out_d::Int) = leaf

reorder(tree::None, perm::Vector, out_d::Int) =  None()

reorder(tree::BSPTree, perm::Vector, out_d::Int) =
  BSPTree(reorder(tree.boundary, perm, out_d::Int), reorder(tree.root, perm, out_d::Int))

reorder(r::LinRegion, perm::Vector, out_d::Int) =
  LinRegion(map((bound -> LinBound(reorder(bound.split, perm, out_d::Int), bound.positive)), r.bounds), out_d)

function not_in(source::Vector{Int}, target::Int)
  for i=1:length(source)
    if source[i] == target
      return false
    end
  end
  return true
end

function find_first(source::Vector{Int}, target::Int)
  for i=1:length(source)
    if source[i] == target
      return i
    end
  end
  return error("find_first was unable to find $(target) in $(source).")
end

# findreorder takes two dimension-orderings (or orderings of anything, really)
# and returns a permutation from one to the other. This currently fails to
# return a meaningful result if the destination does not include a dimension
# which is included in the source. If a source dimension appears multiple
# times in the destination, the first is used. (Repetitions in source creates
# no issues.) Any dimensions which exist in the target and which do not exist
# in the source must be appended to the end of the permutation.

#=
function findreorder(source::Vector, destination::Vector)
  not_in_source = filter((x -> length(findin(source, [x]))<1), destination)
  return [findin(destination, [x])[1] for x = vcat(source, not_in_source)]
end =#

# EDIT: findreorder now throws an error if the target does not include a dim
# which is included in the source, and also, only works for int types.

function findreorder(source::Vector, target::Vector)
  not_in_source = filter((x -> not_in(source, x)), target)
  return [find_first(target, x) for x = vcat(source, not_in_source)]
end

invert_reordering(perm::Vector) = findreorder(collect(1:max(perm...)),perm)

unreorder(x::Any, perm::Vector) = reorder(x, invert_reordering(perm), length(perm))


# convert_dims strips away or adds dimensions up to a given n.

convert_dims(t::BSPTree, n::Int) =
  BSPTree(convert_dims(t.boundary, n), convert_dims(t.root, n))

function convert_dims(r::LinRegion, n::Int)
  LinRegion(map((bound -> convert_dims(bound, n)), r.bounds), n)
end

function convert_dims(b::LinBound, n::Int)
  return LinBound(convert_dims(b.split, n),b.positive)
end

function convert_dims(s::LinSplit, n::Int)
  new_coefs = zeros(n)
  common = min(n, length(s.coefs))
  new_coefs[1:common] = s.coefs[1:common]
  return LinSplit(new_coefs, s.con)
end

function convert_dims(sp::SplitNode, n::Int)
  return SplitNode(convert_dims(sp.split,n), convert_dims(sp.neg,n), convert_dims(sp.pos,n))
end

function convert_dims(l::LeafNode, n::Int) # assumes constant leaf; will need extended for linear leaves
  return l
end

function convert_dims(nth::None, n)
  return None()
end

# strip_dim strips away a specific dimension.

strip_dim(t::BSPTree, n::Int) =
  BSPTree(strip_dim(t.boundary, n), strip_dim(t.root, n))

function strip_dim(r::LinRegion, n::Int)
  d = r.dimensionality
  if n <= d
    d = r.dimensionality - 1
  end
  return LinRegion(map((bound -> strip_dim(bound, n)), r.bounds), d)
end

function strip_dim(b::LinBound, n::Int)
  return LinBound(strip_dim(b.split, n),b.positive)
end

function strip_dim(s::LinSplit, n::Int)
  l = length(s.coefs)
  if n <= l
    new_coefs = zeros(l-1)
    new_coefs[1:n-1] = s.coefs[1:n-1]
    new_coefs[n:l-1] = s.coefs[n+1:l]
    return LinSplit(new_coefs, s.con)
  else
    return s
  end
end

function strip_dim(sp::SplitNode, n::Int)
  return SplitNode(strip_dim(sp.split,n), strip_dim(sp.neg,n), strip_dim(sp.pos,n))
end

function strip_dim(l::LeafNode, n::Int) # assumes constant leaf; will need extended for linear leaves
  return l
end

function strip_dim(nth::None, n)
  return None()
end



# Treemap takes a function and a tree, and applies the function to the
# leaves of the tree to produce a new tree having the same internal structure.

function treemap(fun::Function, tree::BSPNode)
  if typeof(tree) == SplitNode
    SplitNode(tree.split, treemap(fun, tree.neg), treemap(fun, tree.pos))
  elseif tree == None()
    None()
  else # should be a LeafNode at this point
    LeafNode(fun(tree.value))
  end
end

function treemap(fun::Function, tree::BSPTree)
  BSPTree(tree.boundary, treemap(fun, tree.root))
end

nonz(x::Number) = x==0 ? 1 : x
nonz(x::BSPNode) = treemap(nonz, x)
nonz(x::BSPTree) = treemap(nonz, x)


# treearithmetic compiles general combination functions for trees, taking (1)
# the combination operator we wish to extend, (2) its existing argument type.
# None() acts like a left and right identity for all combination functions.
#       -> NOTA BENE: If None acts like identity, it can act as if it is several
#          different and inconsistent values within one expression. For example,
#          in a+b*c, if b and c are none, they combine with a like zero. Yet, if
#          either b or c takes on a value, the other acts like a 1. This may be
#          undesirable. If the * is supposed to act like "and", getting a
#          positive value out when only one value is defined will be unexpected.
#          Ah, well, that applies to multiplication in isolation as well, not
#          only to compound expressions where None()s can act like multiple
#          different values.
# TODO Figure out how to reduce code duplication in this.
# TODO Optimize specific values with special properties, like 0.
#       -> It would be easiy enough to take extra arguments for the identity and
#          annihilator elements, & add cases checking base-type arguments
#          before the cases checking the tree type arguments. Added benefit of
#          annihilators annihilating everything, including None(), which seems
#          right.
#       -> The problem is that I also support some non-commutative ops such as
#          division. I need to deal with left- and right- identities and
#          annihilators, or leave them un-optimized.
#       -> Also, I should test the speedup when I do this.
function treearithmetic(operator, base_type)
  eval(
    quote

      function $operator(n1::BSPNode, n2::$base_type) # Only work on raw nodes if we're combining with a number; otherwise we want to track regions to avoid computing things which would be trimmed, since that can make an exponential difference.
        if typeof(n1) == LeafNode
          return LeafNode( $operator(n1.value, n2))
        elseif n1 == None()
          # return None()
          return LeafNode(n2) # None() combined with anything else acts like an identity element.
        elseif typeof(n1) == SplitNode
          return SplitNode(n1.split, $operator(n1.neg, n2),
                                     $operator(n1.pos, n2))
        end
      end

      function $operator(n1::$base_type, n2::BSPNode)
        if typeof(n2) == LeafNode
          return LeafNode( $operator(n1, n2.value))
        elseif n2 == None()
          #return None()
          return LeafNode(n1) # None() combined with anything else acts like an identity element.
        elseif typeof(n2) == SplitNode
          return SplitNode(n2.split, $operator(n1, n2.neg),
                                     $operator(n1, n2.pos))
        end
      end

      function $operator(t1::BSPTree, t2::BSPTree)
        i = intersection(t1.boundary, t2.boundary)
        #if !regvalid(i)
        #  return BSPTree(i, None())
        #end
        #i = trim_region(i)
        #t1 = trim(t1,i) # TODO (done?) test speed with and without these lines commented out
        #t2 = trim(t2,i)
        if typeof(t1.root) == LeafNode
          if !regvalid(i)
            return BSPTree(i, None()) # TODO Does this test help or harm efficiency? Testing validity can be expensive, but descending t2 uneccessarily is also. Might want to perform a similar check if t2 is a leaf.
          end
          #i = trim_region(i)
          return BSPTree(i, ($operator(t1.root.value, trim(t2, i).root)))
        elseif typeof(t1.root) == SplitNode
          pos = takepos(t1)
          neg = takeneg(t1)
          # TODO: remove next two lines probably
          # pos_int = intersection(pos.boundary, t2.boundary) # Constructing these intersections but not testing whether they're nonempty -- regvalid can be expensive.
          # neg_int = intersection(neg.boundary, t2.boundary) # OTOH, I may want to test for rectangular regions, and do the rect_valid test in that case since it is efficient.
          return BSPTree(i,
                         SplitNode(t1.root.split,
                                   identity($operator(neg, t2)).root, # I have to use "identity" here to prevent the order of operations from being changed when $operator is expanded.
                                   identity($operator(pos, t2)).root)) #
        #elseif t1.root == None() || t2.root == None()
        #  return BSPTree(i, None()) # none combined w/ anything makes none. TODO: this is inconsistent with the convention for summarization.
        elseif  t1.root == None()
          return t2
        elseif t2.root == None()
          return t1
        end
      end

      $operator(t1::BSPTree, t2::$base_type) = BSPTree(t1.boundary, $operator(t1.root, t2))
      $operator(t1::$base_type, t2::BSPTree) = BSPTree(t2.boundary, $operator(t1, t2.root))
    end
    )
end

treearithmetic(op) = treearithmetic(op, Number)

# Now use that general implementation to extend all the combination functions
# we want to use.

#=
import Base.+
treearithmetic(:+)
import Base.*
treearithmetic(:*)
import Base.max
treearithmetic(:max)
import Base.min
treearithmetic(:min)
import Base./
treearithmetic(:/)
import Base.-
treearithmetic(:-)
import Base.^
treearithmetic(:^,Integer) # adding the integer definitions to eliminate some compiler warnings about ambiguous matches
treearithmetic(:^)
=#

# A version of treearithmetic which produces trimmed results. Does not use trim;
# instead, checks reg validity itself as it goes. Makes the assumption that the
# top-level region of the first argument is valid -- trying to combine invalid
# BSPTrees may not return fully trimmed results.

function trim_treearithmetic(operator, base_type)
  eval(
    quote

      function $operator(n1::BSPNode, n2::$base_type) # Only work on raw nodes if we're combining with a number; otherwise we want to track regions to avoid computing things which would be trimmed, since that can make an exponential difference.
        if typeof(n1) == LeafNode
          return LeafNode( $operator(n1.value, n2))
        elseif n1 == None()
          return LeafNode(n2) # None() combined with anything else acts like an identity element.
        elseif typeof(n1) == SplitNode
          return SplitNode(n1.split, $operator(n1.neg, n2),
                                     $operator(n1.pos, n2))
        end
      end

      function $operator(n1::$base_type, n2::BSPNode)
        if typeof(n2) == LeafNode
          return LeafNode( $operator(n1, n2.value))
        elseif n2 == None()
          return LeafNode(n1) # None() combined with anything else acts like an identity element.
        elseif typeof(n2) == SplitNode
          return SplitNode(n2.split, $operator(n1, n2.neg),
                                     $operator(n1, n2.pos))
        end
      end

      function $operator(t1::BSPTree, t2::BSPTree)  # TODO: try partialtrim or otherwise cheaper trimming
        i = intersection(t1.boundary, t2.boundary)
        #if !regvalid(i)
        #  return BSPTree(i, None())
        #end
        if typeof(t1.root) == LeafNode
          if !regvalid(i)
            return BSPTree(i, None()) # TODO Does this test help or harm efficiency? Testing validity can be expensive, but descending t2 uneccessarily is also. Might want to perform a similar check if t2 is a leaf.
          end
          #i = trim_region(i)
          # Trimming t2 and then combining with the leaf value may result in an
          # untrimmed result, due to e.g. the creation of a lot of 0.0 values.
          # Thus we need to call merge_bottom_up to keep things trimmed. This
          # also seems to be a significant performance increase in practice.
          return merge_bottom_up(BSPTree(i, ($operator(t1.root.value, cheap_trim(t2, i).root))))
        elseif typeof(t1.root) == SplitNode
          pos = takepos(t1)
          neg = takeneg(t1)
          pos_int = intersection(pos.boundary, t2.boundary)
          neg_int = intersection(neg.boundary, t2.boundary)
          pos_valid = regvalid(pos_int)
          neg_valid = regvalid(neg_int)
          if pos_valid && neg_valid
            combined_neg = $operator(neg, t2)
            combined_pos = $operator(pos, t2)
            if epsilonequal(BSPTree(i, combined_neg.root), BSPTree(i, combined_pos.root))
              return BSPTree(i, combined_neg.root)
            else
              return BSPTree(i, SplitNode(t1.root.split, combined_neg.root, combined_pos.root))
            end
          elseif pos_valid
            return $operator(BSPTree(i, pos.root), t2)
          elseif neg_valid
            return $operator(BSPTree(i, neg.root), t2)
          else
            return BSPTree(i, None())
          end
        #elseif t1.root == None() || t2.root == None()
        #  return BSPTree(i, None()) # none combined w/ anything makes none. TODO: this is inconsistent with the convention for summarization.
        elseif  t1.root == None()
          return t2
        elseif t2.root == None()
          return t1
        end
      end

      $operator(t1::BSPTree, t2::$base_type) = trim(BSPTree(t1.boundary, $operator(t1.root, t2)))
      $operator(t1::$base_type, t2::BSPTree) = trim(BSPTree(t2.boundary, $operator(t1, t2.root)))
    end
    )
end

trim_treearithmetic(op) = trim_treearithmetic(op, Number)

#=
import Base.+
trim_treearithmetic(:+)
import Base.*
trim_treearithmetic(:*)
import Base.max
trim_treearithmetic(:max)
import Base.min
trim_treearithmetic(:min)
import Base./
trim_treearithmetic(:/)
import Base.-
trim_treearithmetic(:-)
import Base.^
trim_treearithmetic(:^,Integer) # adding the integer definitions to eliminate some compiler warnings about ambiguous matches
trim_treearithmetic(:^)
=#

# safe_treearithmetic returns trimmed results if it is handed trimmed regions.
# It accomplishes this by using cheap_trim on t2 at t1's leaf nodes before
# combining, and then merge_top_down after combining in order to merge any
# regions from t2 which have become identical in value. It then checks for
# epsilonequal values as it pops out of the stack and puts results together. This
# should be significantly cheaper than trim_treearithmetic, since there is no
# need to check region validity in internal nodes.
# TODO: doesn't do the merging as it pops back up the stack yet.

function safe_treearithmetic(operator, base_type)
  eval(
    quote

      function $operator(n1::BSPNode, n2::$base_type) # Only work on raw nodes if we're combining with a number; otherwise we want to track regions to avoid computing things which would be trimmed, since that can make an exponential difference.
        if typeof(n1) == LeafNode
          return LeafNode( $operator(n1.value, n2))
        elseif n1 == None()
          # return None()
          return LeafNode(n2) # None() combined with anything else acts like an identity element.
        elseif typeof(n1) == SplitNode
          return SplitNode(n1.split, $operator(n1.neg, n2),
                                     $operator(n1.pos, n2))
        end
      end

      function $operator(n1::$base_type, n2::BSPNode)
        if typeof(n2) == LeafNode
          return LeafNode( $operator(n1, n2.value))
        elseif n2 == None()
          #return None()
          return LeafNode(n1) # None() combined with anything else acts like an identity element.
        elseif typeof(n2) == SplitNode
          return SplitNode(n2.split, $operator(n1, n2.neg),
                                     $operator(n1, n2.pos))
        end
      end

      function $operator(t1::BSPTree, t2::BSPTree)  # TODO: try partialtrim or otherwise cheaper trimming
        i = intersection(t1.boundary, t2.boundary)
        #if !regvalid(i)
        #  return BSPTree(i, None())
        #end
        #i = trim_region(i)
        #t1 = trim(t1,i) # TODO (done?) test speed with and without these lines commented out
        #t2 = trim(t2,i)
        if typeof(t1.root) == LeafNode
          if !regvalid(i)
            return BSPTree(i, None()) # TODO Does this test help or harm efficiency? Testing validity can be expensive, but descending t2 uneccessarily is also. Might want to perform a similar check if t2 is a leaf.
          end
          #i = trim_region(i)
          return merge_bottom_up(BSPTree(i, ($operator(t1.root.value, cheap_trim(t2, i).root))))
        elseif typeof(t1.root) == SplitNode
          pos = takepos(t1)
          neg = takeneg(t1)
          # TODO: remove next two lines probably
          # pos_int = intersection(pos.boundary, t2.boundary) # Constructing these intersections but not testing whether they're nonempty -- regvalid can be expensive.
          # neg_int = intersection(neg.boundary, t2.boundary) # OTOH, I may want to test for rectangular regions, and do the rect_valid test in that case since it is efficient.
          combined_neg = $operator(neg, t2)
          combined_pos = $operator(pos, t2)
          if epsilonequal(BSPTree(i, combined_neg.root), BSPTree(i, combined_pos.root))
            return BSPTree(i, combined_neg.root)
          else
            return BSPTree(i, SplitNode(t1.root.split, combined_neg.root, combined_pos.root))
          end
        #elseif t1.root == None() || t2.root == None()
        #  return BSPTree(i, None()) # none combined w/ anything makes none. TODO: this is inconsistent with the convention for summarization.
        elseif  t1.root == None()
          return t2
        elseif t2.root == None()
          return t1
        end
      end

      $operator(t1::BSPTree, t2::$base_type) = merge_bottom_up(BSPTree(t1.boundary, $operator(t1.root, t2)))
      $operator(t1::$base_type, t2::BSPTree) = merge_bottom_up(BSPTree(t2.boundary, $operator(t1, t2.root)))
    end
    )
end

safe_treearithmetic(op) = safe_treearithmetic(op, Number)

#=
import Base.+
safe_treearithmetic(:+)
import Base.*
safe_treearithmetic(:*)
import Base.max
safe_treearithmetic(:max)
import Base.min
safe_treearithmetic(:min)
import Base./
safe_treearithmetic(:/)
import Base.-
safe_treearithmetic(:-)
import Base.^
safe_treearithmetic(:^,Integer) # adding the integer definitions to eliminate some compiler warnings about ambiguous matches
safe_treearithmetic(:^)
=#

# nov_treearithmetic is a variant of treearithmetic which doesn't make any reg
# validity checks except indirectly by calling trim.

function nov_treearithmetic(operator, base_type)
  eval(
    quote

      function $operator(n1::BSPNode, n2::$base_type) # Only work on raw nodes if we're combining with a number; otherwise we want to track regions to avoid computing things which would be trimmed, since that can make an exponential difference.
        if typeof(n1) == LeafNode
          return LeafNode( $operator(n1.value, n2))
        elseif n1 == None()
          # return None()
          return LeafNode(n2) # None() combined with anything else acts like an identity element.
        elseif typeof(n1) == SplitNode
          return SplitNode(n1.split, $operator(n1.neg, n2),
                                     $operator(n1.pos, n2))
        end
      end

      function $operator(n1::$base_type, n2::BSPNode)
        if typeof(n2) == LeafNode
          return LeafNode( $operator(n1, n2.value))
        elseif n2 == None()
          #return None()
          return LeafNode(n1) # None() combined with anything else acts like an identity element.
        elseif typeof(n2) == SplitNode
          return SplitNode(n2.split, $operator(n1, n2.neg),
                                     $operator(n1, n2.pos))
        end
      end

      function $operator(t1::BSPTree, t2::BSPTree)
        i = intersection(t1.boundary, t2.boundary)
        #if !regvalid(i)
        #  return BSPTree(i, None())
        #end
        #i = trim_region(i)
        #t1 = trim(t1,i) # TODO (done?) test speed with and without these lines commented out
        #t2 = trim(t2,i)
        if typeof(t1.root) == LeafNode
          #if !regvalid(i)
          #  return BSPTree(i, None()) # TODO Does this test help or harm efficiency? Testing validity can be expensive, but descending t2 uneccessarily is also. Might want to perform a similar check if t2 is a leaf.
          #end
          #i = trim_region(i)
          return BSPTree(i, ($operator(t1.root.value, trim(t2, i).root)))
        elseif typeof(t1.root) == SplitNode
          pos = takepos(t1)
          neg = takeneg(t1)
          # TODO: remove next two lines probably
          # pos_int = intersection(pos.boundary, t2.boundary) # Constructing these intersections but not testing whether they're nonempty -- regvalid can be expensive.
          # neg_int = intersection(neg.boundary, t2.boundary) # OTOH, I may want to test for rectangular regions, and do the rect_valid test in that case since it is efficient.
          return BSPTree(i,
                         SplitNode(t1.root.split,
                                   identity($operator(neg, t2)).root, # I have to use "identity" here to prevent the order of operations from being changed when $operator is expanded.
                                   identity($operator(pos, t2)).root)) #
        #elseif t1.root == None() || t2.root == None()
        #  return BSPTree(i, None()) # none combined w/ anything makes none. TODO: this is inconsistent with the convention for summarization.
        elseif  t1.root == None()
          return t2
        elseif t2.root == None()
          return t1
        end
      end

      $operator(t1::BSPTree, t2::$base_type) = BSPTree(t1.boundary, $operator(t1.root, t2))
      $operator(t1::$base_type, t2::BSPTree) = BSPTree(t2.boundary, $operator(t1, t2.root))
    end
    )
end

nov_treearithmetic(op) = nov_treearithmetic(op, Number)

#=
import Base.+
nov_treearithmetic(:+)
import Base.*
nov_treearithmetic(:*)
import Base.max
nov_treearithmetic(:max)
import Base.min
nov_treearithmetic(:min)
import Base./
nov_treearithmetic(:/)
import Base.-
nov_treearithmetic(:-)
import Base.^
nov_treearithmetic(:^,Integer) # adding the integer definitions to eliminate some compiler warnings about ambiguous matches
nov_treearithmetic(:^)
=#

# Like safe_treearithmetic and trim_treearithmetic, cheap_treearithmetic merges
# after trimming and then combining, at t1 leaf nodes. Unlike them, it doesn't
# merge elsewhere. Also unlike them, it uses cheap_trim rather than a full trim.

# === WINNER ===
# This seems like the fastest way of doing things.

function cheap_treearithmetic(operator, base_type)
  eval(
    quote

      function $operator(n1::BSPNode, n2::$base_type) # Only work on raw nodes if we're combining with a number; otherwise we want to track regions to avoid computing things which would be trimmed, since that can make an exponential difference.
        if typeof(n1) == LeafNode
          return LeafNode( $operator(n1.value, n2))
        elseif n1 == None()
          # return None()
          return LeafNode(n2) # None() combined with anything else acts like an identity element.
        elseif typeof(n1) == SplitNode
          return SplitNode(n1.split, $operator(n1.neg, n2),
                                     $operator(n1.pos, n2))
        end
      end

      function $operator(n1::$base_type, n2::BSPNode)
        if typeof(n2) == LeafNode
          return LeafNode( $operator(n1, n2.value))
        elseif n2 == None()
          #return None()
          return LeafNode(n1) # None() combined with anything else acts like an identity element.
        elseif typeof(n2) == SplitNode
          return SplitNode(n2.split, $operator(n1, n2.neg),
                                     $operator(n1, n2.pos))
        end
      end

      function $operator(t1::BSPTree, t2::BSPTree)
        i = intersection(t1.boundary, t2.boundary)
        #if !regvalid(i)
        #  return BSPTree(i, None())
        #end
        #i = trim_region(i)
        #t1 = trim(t1,i) # TODO (done?) test speed with and without these lines commented out
        #t2 = trim(t2,i)
        if typeof(t1.root) == LeafNode
          if !regvalid(i)
            return BSPTree(i, None())
          end
          #i = trim_region(i)
          return merge_bottom_up(BSPTree(i, ($operator(t1.root.value, cheap_trim(t2, i).root))))
        elseif typeof(t1.root) == SplitNode
          pos = takepos(t1)
          neg = takeneg(t1)
          # TODO: remove next two lines probably
          # pos_int = intersection(pos.boundary, t2.boundary) # Constructing these intersections but not testing whether they're nonempty -- regvalid can be expensive.
          # neg_int = intersection(neg.boundary, t2.boundary) # OTOH, I may want to test for rectangular regions, and do the rect_valid test in that case since it is efficient.
          return BSPTree(i,
                         SplitNode(t1.root.split,
                                   identity($operator(neg, t2)).root, # I have to use "identity" here to prevent the order of operations from being changed when $operator is expanded.
                                   identity($operator(pos, t2)).root)) #
        #elseif t1.root == None() || t2.root == None()
        #  return BSPTree(i, None()) # none combined w/ anything makes none. TODO: this is inconsistent with the convention for summarization.
        elseif  t1.root == None()
          return t2
        elseif t2.root == None()
          return t1
        end
      end

      $operator(t1::BSPTree, t2::$base_type) = BSPTree(t1.boundary, $operator(t1.root, t2))
      $operator(t1::$base_type, t2::BSPTree) = BSPTree(t2.boundary, $operator(t1, t2.root))
    end
    )
end

cheap_treearithmetic(op) = cheap_treearithmetic(op, Number)


import Base.+
cheap_treearithmetic(:+)
import Base.*
cheap_treearithmetic(:*)
import Base.max
cheap_treearithmetic(:max)
import Base.min
cheap_treearithmetic(:min)
import Base./
cheap_treearithmetic(:/)
import Base.-
cheap_treearithmetic(:-)
import Base.^
cheap_treearithmetic(:^,Integer) # adding the integer definitions to eliminate some compiler warnings about ambiguous matches
cheap_treearithmetic(:^)

# take_left will take the first argument when both are defined. However,
# because treearithmetic treats None() as the identity, take_left will as
# well; so, it will take on the 2nd value in places where the 1st contains
# None(). This means take_left behaves similarly to insert(source, target),
# although it will handle boundaries very differently.
take_left(x::Number, y::Number) = x
cheap_treearithmetic(:take_left)

# safe_div is like /, but handles division by zero by returning the numerator.
# I also wanted it to return 1 in the 0/0 case, to help combat the undesired
# all-zero fixed points of some rule systems such as BP; however, this ended up
# causing other problems for me.
function safe_div(x::Number, y::Number) # = y==0 ? x : x/y
  if y==0
    #if x==0
    #  return 1.0
    #else
      return x
    #end
  else
    return x/y
  end
end

cheap_treearithmetic(:safe_div)



# like cheap_treearithmetic, but adds optimization for identity and absorber
# elements. These are left-identity and left-absorber, which matters for non-
# commutative ops like ^.
function opt_treearithmetic(operator, iden, absorber, base_type=Number)
  eval(
    quote

      function $operator(n1::BSPNode, n2::$base_type) # Only work on raw nodes if we're combining with a number; otherwise we want to track regions to avoid computing things which would be trimmed, since that can make an exponential difference.
        if typeof(n1) == LeafNode
          return LeafNode( $operator(n1.value, n2))
        elseif n1 == None()
          # return None()
          return LeafNode(n2) # None() combined with anything else acts like an identity element.
        elseif typeof(n1) == SplitNode
          return SplitNode(n1.split, $operator(n1.neg, n2),
                                     $operator(n1.pos, n2))
        end
      end

      function $operator(n1::$base_type, n2::BSPNode)
        if typeof(n2) == LeafNode
          return LeafNode( $operator(n1, n2.value))
        elseif n2 == None()
          #return None()
          return LeafNode(n1) # None() combined with anything else acts like an identity element.
        elseif typeof(n2) == SplitNode
          return SplitNode(n2.split, $operator(n1, n2.neg),
                                     $operator(n1, n2.pos))
        end
      end

      function $operator(t1::BSPTree, t2::BSPTree)
        i = intersection(t1.boundary, t2.boundary)
        #if !regvalid(i)
        #  return BSPTree(i, None())
        #end
        #i = trim_region(i)
        #t1 = trim(t1,i) # TODO (done?) test speed with and without these lines commented out
        #t2 = trim(t2,i)
        if typeof(t1.root) == LeafNode
          if !regvalid(i)
            return BSPTree(i, None())
          end
          v = t1.root.value
          if v == $(iden)
            return BSPTree(i, t2.root)
          elseif v == $(absorber)
            return BSPTree(i, LeafNode($(absorber)))
          else
           return merge_bottom_up(BSPTree(i, ($operator(t1.root.value, cheap_trim(t2, i).root))))
          end
        elseif typeof(t1.root) == SplitNode
          pos = takepos(t1)
          neg = takeneg(t1)
          # TODO: remove next two lines probably
          # pos_int = intersection(pos.boundary, t2.boundary) # Constructing these intersections but not testing whether they're nonempty -- regvalid can be expensive.
          # neg_int = intersection(neg.boundary, t2.boundary) # OTOH, I may want to test for rectangular regions, and do the rect_valid test in that case since it is efficient.
          return BSPTree(i,
                         SplitNode(t1.root.split,
                                   identity($operator(neg, t2)).root, # I have to use "identity" here to prevent the order of operations from being changed when $operator is expanded.
                                   identity($operator(pos, t2)).root)) #
        #elseif t1.root == None() || t2.root == None()
        #  return BSPTree(i, None()) # none combined w/ anything makes none. TODO: this is inconsistent with the convention for summarization.
        elseif  t1.root == None()
          return t2
        elseif t2.root == None()
          return t1
        end
      end

      $operator(t1::BSPTree, t2::$base_type) = BSPTree(t1.boundary, $operator(t1.root, t2))
      $operator(t1::$base_type, t2::BSPTree) = BSPTree(t2.boundary, $operator(t1, t2.root))
    end
    )
end

#=
import Base.+
opt_treearithmetic(:+, 0.0, false)
import Base.*
opt_treearithmetic(:*, 1.0, 0.0)
import Base.max
opt_treearithmetic(:max, -Inf, Inf)
import Base.min
opt_treearithmetic(:min, Inf, -Inf)
import Base./
opt_treearithmetic(:/, false, 0.0) # TODO optimize the 'false' case by excluding the check from code
import Base.-
opt_treearithmetic(:-, 0.0, false)
import Base.^
opt_treearithmetic(:^, false, 0.0, Integer) # adding the integer definitions to eliminate some compiler warnings about ambiguous matches
opt_treearithmetic(:^, false, 0.0) # TODO enable multiple absorbers to be given, to handle exponentiation
=#





# Inserting one tree into another, it is important to have a null value
# to delineate the parts which are not to change.
# The None type is used for that (see types at the beginning of this file).
# The insert function non-destructively creates a modified
# version of "target", which takes on the values of "source" wherever
# "source" has value other than None().

# The result of this function is not trimmed.

function insert(source::BSPNode, target::BSPNode)
  if source == None()
    return target
  elseif typeof(source) == SplitNode
    return SplitNode(source.split,
                    insert(source.neg, target),
                    insert(source.pos, target))
  else # should be a LeafNode
    return source
  end
end

# A BSPTree has a boundary associated with it, whereas a node in
# the tree does not. In order to insert a tree into the structure of
# another tree, we wish to transform the boundary structure to
# a series of split nodes, with None() on the "outer" side.

function unfoldboundary(tree::BSPTree, default=None())
  node = tree.root
  bounds = tree.boundary.bounds
  for bound in bounds
    if bound.positive
      node = SplitNode(bound.split, default, node)
    else
      node = SplitNode(bound.split, node, default)
    end
  end
  return node
end

# We can now define insertion for trees. The output is trimmed.

function insert(source::BSPTree, target::BSPTree)
  trim(BSPTree(target.boundary,
               insert(unfoldboundary(source),
                      target.root)))
end

# TODO: as a matter of consistency with Julia conventions, it may be
# a good idea to reverse the argument ordering here, so that we say
# insert(target, source) and insert!(mem, source).

# TODO: the insertion above is very crude in that it does no
# balancing at all, and is in fact quite likely to create very
# unbalanced trees.






# ==== code related to summary operations ====


function vec_pad_sum(v1::Vector{Float64}, v2::Vector{Float64})
  l = max(length(v1),length(v2))
  result = Array{Float64,1}(undef,l)
  for i in 1:l
    result[i] = get(v1,i,0.0)+get(v2,i,0.0)
  end
  return result
end

# project_region computes a system of linear constraints which is equivalent
# except that it lacks the targeted dimension. This doesn't actually remove
# the target dimension. Instead, it creates a region which is unconstrained
# in that dimension; the dimension may then be safely removed.
# Use project_and_strip to do both at once.
# TODO: Consider making a rect_project special case, analogous to rect_valid.

function project_region(r::LinRegion, d::Int)
  # A slight modification of the Fourier-Motzkin elimination method to handle my open-or-closed bound.
  if d > r.dimensionality # let's set aside this case right away
    return r
  end
  # Get the bounds with coefficient zero on d out.
  # Note that I'm **NOT** currently using epsilon to define "close enough to zero" here, like I do most places. I don't see a reason to.
  zer_d = filter((bound -> get(bound.split.coefs,d,0.0)==0.0), r.bounds)
  non_z = setdiff(r.bounds,zer_d)
  # temp helper function divi to divide all the numbers in a bound by a constant:
  divi = ((bound, n) -> LinBound(LinSplit(bound.split.coefs/n,bound.split.con/n), bound.positive))
  # divi isn't something that's correct for negative n; it would mess up closed/open.
  # Therefore we only normalize by absolute value, leaving the coefficients of d as 1 or -1.
  non_z = [divi(bound, abs(get(bound.split.coefs,d,0.0))) for bound in non_z] #
  # Sort the non_z inequalities into d occurring negatively vs positively, and closed vs open.
  # A positive coefficient and a positive constraint type mean a closed lower bound on d.
  closed_lower = filter((bound -> get(bound.split.coefs,d,0.0)>0.0 && bound.positive), non_z)
  # A negative bound where d occurs negatively is really positive for our purposes (IE, it gives a lower bound on d (an open one)).
  open_lower = filter((bound -> get(bound.split.coefs,d,0.0)<0.0 && !bound.positive), non_z) # -d < con - coefs
  # remaining = setdiff(r.bounds,union(pos_closed,pos_open)) # Doing something like this might speed things up, but it's tricky. Better to go iterative probably
  # A negative d-coef and a positive constraint is an upper bound (closed)
  closed_upper = filter((bound -> get(bound.split.coefs,d,0.0)<0.0 && bound.positive), non_z) # con - coefs <= -d
  # Positive d-coef and negative constraint means an open upper bound.
  open_upper = filter((bound -> get(bound.split.coefs,d,0.0)>0.0 && !bound.positive), non_z) # d < con - coefs
  # Now we need to make new bounds by transitivity: any two lower and upper bounds on d are lower and upper bounds on each other as well.
  new_bounds = Vector{LinBound}()
  add_bound = (bound -> new_bounds = union(new_bounds, [bound]))
  for l in closed_lower # constraint with form  l.con - l.coefs <= d   ( <- pretending d is removed from the other coefs in these formula sommaries; also pretending coefs have their variables multiplied in)
    for u in closed_upper # d <= u.coefs - u.con
      # I need to create a closed bound equivalent to (l.con - l.coefs) <= (u.coefs - u.con)
      # In my representation, a closed bound has to be positive (ie, lower), so I need (l.con + u.con) <= (l.coefs + u.coefs)
      new_coefs = vec_pad_sum(l.split.coefs, u.split.coefs)
      new_con = l.split.con + u.split.con
      length(new_coefs)>=d ? new_coefs[d] = 0.0 : ()
      add_bound(LinBound(LinSplit(new_coefs, new_con), true))
    end
    for u in open_upper # constraint with form  d < u.con - u.coefs
      # The reasoning here is similar, but openness is contagious when combining inequalities.
      # I need something equivalent to l.con - l.coefs < u.con - u.coefs.
      # Open bounds are negative (upper), so I need  u.coefs - l.coefs < u.con - l.con
      new_coefs = vec_pad_sum(u.split.coefs, -l.split.coefs)
      new_con = u.split.con - l.split.con
      length(new_coefs)>=d ? new_coefs[d] = 0.0 : ()
      add_bound(LinBound(LinSplit(new_coefs, new_con), false))
    end
  end
  for l in open_lower #  l.coefs - l.con < d
    # Again, openness is contagious; so all the rest of the new constraints will be open, and therefore in upper-bound form.
    for u in closed_upper #  d <= u.coefs - u.con
      # I need something equivalent to l.coefs - l.con < u.coefs - u.con
      # It's got to be written in upper-bound form, so,  l.coefs - u.coefs < l.con - u.con
      new_coefs = vec_pad_sum(l.split.coefs, -u.split.coefs)
      new_con = l.split.con - u.split.con
      length(new_coefs)>=d ? new_coefs[d] = 0.0 : ()
      add_bound(LinBound(LinSplit(new_coefs, new_con), false))
    end
    for u in open_upper #  d < u.con - u.coefs
      # Needs to be equivalent to l.coefs - l.con < u.con - u.coefs
      # So, l.coefs + u.coefs < l.con + u.con
      new_coefs = vec_pad_sum(l.split.coefs, u.split.coefs)
      new_con = l.split.con + u.split.con
      length(new_coefs)>=d ? new_coefs[d] = 0.0 : ()
      add_bound(LinBound(LinSplit(new_coefs, new_con), false))
    end
  end
  return trim_region(LinRegion(union(new_bounds, zer_d), r.dimensionality))
end

function project_and_strip(r::LinRegion, d::Int)
  r = project_region(r,d)
  r = strip_dim(r,d)
  return r
end


function closure(b) # helper for faces(reg); returns a closed version of a bound.
  if b.positive
    return b
  else
    return LinBound(LinSplit(-b.split.coefs, -b.split.con), true)
  end
end

function closure(r::LinRegion)
  return LinRegion(map((b -> closure(b)), r.bounds), r.dimensionality)
end

# faces(reg) takes a LinRegion and returns a Vector{Tuple{LinRegion,LinBound}}
# containing all faces of the original region, paired with the bound which
# induced the face.. At present, it's also possible that it contains
# some edges/corners/etc by accident.

# WARNING: input region must not have duplicate constraints.

function faces(reg::LinRegion)
  faces_ = Vector{Tuple{LinRegion,LinBound}}()
  for bound in reg.bounds
    removed_con = setdiff(reg.bounds, [bound])
    closed = closure(bound)
    reversed = closure(LinBound(bound.split, !bound.positive))
    face = LinRegion(union(removed_con, [closed,reversed]), reg.dimensionality)
    if regvalid(face)
      faces_ = union(faces_,[(face,bound)])
    end
  end
  return faces_
end

# Tests to see whether something is a lower face.

function lower_face(d,bound)
  coef = get(bound.split.coefs, d, 0.0)
  return (coef > 0.0 && bound.positive) || (coef < 0.0 && !bound.positive)
end

# Tests to see whether something is an upper face.

function upper_face(d,bound)
  lower_face(d, LinBound(bound.split, !bound.positive))
end

# face_tree takes a dimension, a region which should be the projection of the
# region the faces come from, and a Vector{Tuple{LinRegion,LinBound}} of faces.
# It produces a BSPTree which has the shadows of the faces as leaves and the
# splits of the bounds as leaf values.

function face_tree(d::Int, shadow::LinRegion, s::Vector{Tuple{LinRegion,LinBound}})
  t = BSPTree(shadow,None())
  for face in s
    t = insert(BSPTree(project_region(closure(face[1]), d), LeafNode(face[2])), t) # it's necessary to take the closure here to prevent unwarranted "cracks" from forming!
  end
  return t
end

# face_difference takes a dimension of integration, an upper face,
# a lower face, and the intersection of their shadows. It returns an approximate
# difference between the two, including an infinitesimal difference to indicate
# an integration multiplier (for delta-function integration) in the case where
# the difference is zero.

function face_difference(d::Int, u::LinSplit, l::LinSplit, shadow::LinRegion)
  # Solve for d. Subtract con from both sides, divide both sides by the negative coefficient of d, add d to both sides.
  u_solved = LinSplit(-u.coefs*get(u.coefs,d,0.0), u.con*get(u.coefs,d,0.0))
  l_solved = LinSplit(-l.coefs*get(l.coefs,d,0.0), l.con*get(l.coefs,d,0.0))
  # Now u_solved - l_solved is the linear function giving the distance between them in d.
  # This should not really be thought of as another hyperplane; it's a representation of a quantity dependent on location (but not dimension d). I'm just representing it as a split.
  diff_coefs = vec_pad_sum(u_solved.coefs, -l_solved.coefs)
  diff_con = u_solved.con - l_solved.con
  length(diff_coefs)>=d ? diff_coefs[d] = 0.0 : () # zero out d's coefficient if it's defined
  is_zero = epsilonequal(diff_con,0.0) && all((c -> epsilonequal(c, 0.0)), diff_coefs)
  if is_zero
    diff_con = Hyper(1/abs(get(u.coefs,d,0.0)/sqrt(sum([x^2 for x in u.coefs]))), -1) # Return infinitesimal value ϵ/cos(Θ), where Θ is u's angle of maximum incline (treating d as up)
  end
  #return LinSplit(diff_coefs, diff_con)
  # take the linear function and find the points giving extreme values in the shadow
  max_point = sup_in_direction(makemodel(shadow), diff_coefs, true)
  min_point = sup_in_direction(makemodel(shadow), -diff_coefs, true)
  # use these to find the middle value
  mid_point = (max_point + min_point)/2
  dot_prod = 0.0
  for i in 1:length(mid_point)
    dot_prod += mid_point[i]*get(diff_coefs, i, 0.0)
  end
  mid_val = dot_prod + diff_con
  return BSPTree(shadow, LeafNode(mid_val))
end

# BSPTree version of the function, so that I can call it on trees representing
# upper and lower functions (from face_tree).

function face_difference(d::Int, u::BSPTree, l::BSPTree)
  i = intersection(l.boundary,u.boundary)
  if !regvalid(i)
    return BSPTree(i, None())
  elseif u.root == None() && l.root == None() # boundless difference returns a hyperreal
    return BSPTree(i, LeafNode(Hyper(1.0,1)))
  elseif u.root == None() || l.root == None() # half-boundless is still hyperreal, but, half as big
    return BSPTree(i, LeafNode(Hyper(0.5,1)))
  elseif typeof(u.root) == SplitNode
    return BSPTree(i,SplitNode(u.root.split, face_difference(d,takeneg(u),l).root, face_difference(d,takepos(u),l).root))
  elseif typeof(l.root) == SplitNode
    return BSPTree(i,SplitNode(l.root.split, face_difference(d,u,takeneg(l)).root, face_difference(d,u,takepos(l)).root))
  else # both must be leaf nodes.
    return face_difference(d, u.root.value.split, l.root.value.split, i)
  end
end

# Integrate a leaf by multiplying the tree which romes out of face differences
# by the actual value contained therein.

function leaf_integrate(leaf::BSPTree, dim::Int)
  boundary = trim_region(leaf.boundary)
  s = faces(boundary)
  i = project_region(boundary, dim)
  upper_faces = face_tree(dim, i, filter((face -> upper_face(dim,face[2])), s))
  lower_faces = face_tree(dim, i, filter((face -> lower_face(dim,face[2])), s))
  return strip_dim(face_difference(dim, upper_faces, lower_faces) * leaf.root.value, dim)
end

# Product-integras version.

function leaf_pintegrate(leaf::BSPTree, dim::Int)
  boundary = trim_region(leaf.boundary)
  s = faces(boundary)
  i = project_region(boundary, dim)
  upper_faces = face_tree(dim, i, filter((face -> upper_face(dim,face[2])), s))
  lower_faces = face_tree(dim, i, filter((face -> lower_face(dim,face[2])), s))
  return strip_dim(leaf.root.value ^ face_difference(dim, upper_faces, lower_faces), dim)
end

# Max and min versions are a little simpler.

function leaf_maxintegrate(leaf::BSPTree, dim::Int)
  boundary = trim_region(leaf.boundary)
  i = project_and_strip(boundary, dim)
  return BSPTree(i, leaf.root)
end

function leaf_mintegrate(leaf::BSPTree, dim::Int) # TODO: seems like this shouldn't actually need to project; isn't it redundant w/ work done in the recursive summary function?
  boundary = trim_region(leaf.boundary)
  i = project_and_strip(boundary, dim)
  return BSPTree(i, leaf.root)
end

# A general summary operator compilation function, analogous to the general
# combination operation. Here, we need a name for the summary operation,
# a function leaf_val which computes a BSPTree approximating the integrated
# value of a leaf based on the leaf region, a combination operation for
# integrated values, and the identity value for comb_op. leaf_val should take
# as arguments the tree and the dimension of integration, returning
# a BSPTree. comb_op is just a regular combination
# operation like +, *, min, max (must be defined for BSPTrees).
# slice_op is a function from BSPNodes to BSPNodes.
# TODO: fix the wasteful use of unfoldboundary. I have reason to suspect it's
# adding a whole lot of unnecessary nodes, when accumulated through the
# recursive computation.
# TODO: supposing the arguments are given trimmed (generally true) and supposing
# comb_op preserves the property (often true, may be more true in the future),
# what could I do to make this preserve trimmed-ness?

function treesummary(name, leaf_val, comb_op, iden)
  eval(
    quote
      function $name(tree::BSPTree, dim::Int)
        if tree.root == None()
          return BSPTree(project_and_strip(tree.boundary, dim), LeafNode($iden)) # treat None() as an identity op, so that summarizing over a partially defined thing summarizes the defined values.
        elseif typeof(tree.root) == LeafNode
          return $(leaf_val)(tree, dim)
        else # typeof(tree.root) == SplitNode
          b = project_and_strip(tree.boundary, dim)
          pos = $name(takepos(tree), dim)
          neg = $name(takeneg(tree), dim)
          return $comb_op(BSPTree(b, unfoldboundary(neg, LeafNode($iden))), BSPTree(b, unfoldboundary(pos, LeafNode($iden))))
        end
      end
    end
    )
end


# Now use it to compile the specific summary operations we want.

#=
treesummary(:integrate,
            leaf_integrate,
            :+,
            0.0
            )

treesummary(:pintegrate,
            leaf_pintegrate,
            :*,
            1.0
            )

treesummary(:maxintegrate,
            leaf_maxintegrate,
            :max,
            -Inf
            )

treesummary(:mintegrate,
            leaf_mintegrate,
            :min,
            Inf
            )
=#

# Various alterations which I've tested for speed.

# lt_treesummary calls trim after combining the parts of a SplitNode, to avoid
# the large blowup I've been seeing (hence "late trim", ie, "lt")


function lt_treesummary(name, leaf_val, comb_op, iden)
  eval(
    quote
      function $name(tree::BSPTree, dim::Int)
        if tree.root == None()
          return BSPTree(project_and_strip(tree.boundary, dim), LeafNode($iden)) # treat None() as an identity op, so that summarizing over a partially defined thing summarizes the defined values.
        elseif typeof(tree.root) == LeafNode
          return $(leaf_val)(tree, dim)
        else # typeof(tree.root) == SplitNode
          b = project_and_strip(tree.boundary, dim)
          pos = $name(takepos(tree), dim)
          neg = $name(takeneg(tree), dim)
          return trim($comb_op(BSPTree(b, unfoldboundary(neg, LeafNode($iden))), BSPTree(b, unfoldboundary(pos, LeafNode($iden)))))
        end
      end
    end
    )
end


#=
lt_treesummary(:integrate,
            leaf_integrate,
            :+,
            0.0
            )

lt_treesummary(:pintegrate,
            leaf_pintegrate,
            :*,
            1.0
            )

lt_treesummary(:maxintegrate,
            leaf_maxintegrate,
            :max,
            -Inf
            )

lt_treesummary(:mintegrate,
            leaf_mintegrate,
            :min,
            Inf
            )
=#



# et_treesummary calls trim before combining the parts of a SplitNode, to avoid
# the large blowup I've been seeing (hence "early trim", ie, "lt")

function et_treesummary(name, leaf_val, comb_op, iden)
  eval(
    quote
      function $name(tree::BSPTree, dim::Int)
        if tree.root == None()
          return BSPTree(project_and_strip(tree.boundary, dim), LeafNode($iden)) # treat None() as an identity op, so that summarizing over a partially defined thing summarizes the defined values.
        elseif typeof(tree.root) == LeafNode
          return $(leaf_val)(tree, dim)
        else # typeof(tree.root) == SplitNode
          b = project_and_strip(tree.boundary, dim)
          pos = $name(takepos(tree), dim)
          neg = $name(takeneg(tree), dim)
          pos_part = cheap_trim(BSPTree(b, unfoldboundary(pos, LeafNode($iden))))
          neg_part = cheap_trim(BSPTree(b, unfoldboundary(neg, LeafNode($iden))))
          return $comb_op(neg_part, pos_part)
        end
      end
    end
    )
end

#=

et_treesummary(:integrate,
            leaf_integrate,
            :+,
            0.0
            )

et_treesummary(:pintegrate,
            leaf_pintegrate,
            :*,
            1.0
            )

et_treesummary(:maxintegrate,
            leaf_maxintegrate,
            :max,
            -Inf
            )

et_treesummary(:mintegrate,
            leaf_mintegrate,
            :min,
            Inf
            )
=#



# elt_treesummary combines the early trim and late trim by first doing a cheap
# trim and then doing a merge.

function elt_treesummary(name, leaf_val, comb_op, iden)
  eval(
    quote
      function $name(tree::BSPTree, dim::Int)
        if tree.root == None()
          return BSPTree(project_and_strip(tree.boundary, dim), LeafNode($iden)) # treat None() as an identity op, so that summarizing over a partially defined thing summarizes the defined values.
        elseif typeof(tree.root) == LeafNode
          return $(leaf_val)(tree, dim)
        else # typeof(tree.root) == SplitNode
          b = project_and_strip(tree.boundary, dim)
          pos = $name(takepos(tree), dim)
          neg = $name(takeneg(tree), dim)
          pos_part = cheap_trim(BSPTree(b, unfoldboundary(pos, LeafNode($iden))))
          neg_part = cheap_trim(BSPTree(b, unfoldboundary(neg, LeafNode($iden))))
          return merge_bottom_up($comb_op(neg_part, pos_part))
        end
      end
    end
    )
end


#=
elt_treesummary(:integrate,
            leaf_integrate,
            :+,
            0.0
            )

elt_treesummary(:pintegrate,
            leaf_pintegrate,
            :*,
            1.0
            )

elt_treesummary(:maxintegrate,
            leaf_maxintegrate,
            :max,
            -Inf
            )

elt_treesummary(:mintegrate,
            leaf_mintegrate,
            :min,
            Inf
            )
=#


function split_is_ortho(s::LinSplit)
  split_coefs = s.coefs
  nonzero_count = 0
  nonzero_loc = 0
  for dim in 1:length(split_coefs)
    if !(split_coefs[dim] == 0.0)
      nonzero_count = nonzero_count + 1
      if nonzero_count > 1
        return (false, 0)
      end
      nonzero_loc = dim
    end
  end
  return (true, nonzero_loc)
end


# ortho_treesummary is like et_treesummary in its handling of the general case,
# but also optimizes the orto case.

function ortho_treesummary(name, leaf_val, comb_op, iden)
  eval(
    quote
      function $name(tree::BSPTree, dim::Int)
        if tree.root == None()
          return BSPTree(project_and_strip(tree.boundary, dim), LeafNode($iden)) # treat None() as an identity op, so that summarizing over a partially defined thing summarizes the defined values.
        elseif typeof(tree.root) == LeafNode
          return $(leaf_val)(tree, dim)
        else # typeof(tree.root) == SplitNode
          b = project_and_strip(tree.boundary, dim)
          pos = $name(takepos(tree), dim)
          neg = $name(takeneg(tree), dim)
          coefs = tree.root.split.coefs
          if isassigned(coefs, dim) && coefs[dim] == 0.0
            new_split = strip_dim(tree.root.split, dim)
            return BSPTree(b, SplitNode(new_split, neg.root, pos.root))
          #elseif pos.boundary == neg.boundary
          #  return $comb_op(neg, pos)
          #end
          #(is_ortho, nonz_dim) = split_is_ortho(tree.root.split)
          #if is_ortho
          #  if nonz_dim == dim
          #    return $comb_op(neg, pos)
          #  else
          #    new_split = strip_dim(tree.root.split, dim)
          #    return BSPTree(b, SplitNode(new_split, neg.root, pos.root))
          #  end
          else
            pos_part = cheap_trim(BSPTree(b, unfoldboundary(pos, LeafNode($iden))))
            neg_part = cheap_trim(BSPTree(b, unfoldboundary(neg, LeafNode($iden))))
            return $comb_op(neg_part, pos_part)
          end
        end
      end
    end
    )
end



ortho_treesummary(:integrate,
            leaf_integrate,
            :+,
            0.0
            )

ortho_treesummary(:pintegrate,
            leaf_pintegrate,
            :*,
            1.0
            )

ortho_treesummary(:maxintegrate,
            leaf_maxintegrate,
            :max,
            -Inf
            )

ortho_treesummary(:mintegrate,
            leaf_mintegrate,
            :min,
            Inf
            )








# A dummy summary for use when the summary operation for a rule shouldn't
# actually be used and we want to throw an error if it is.

function error_summary(a::Any, b::Any)
  error("This summary operation should never be called.")
end

function error_combination(a::Any, b::Any)
  error("This combination operation should never be called.")
end




























# :)
