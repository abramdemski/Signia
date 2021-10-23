
# This file includes the rule data-structure and related structures, rule
# compilation from the Signia DSL to these data-structures, and the solution of
# rule systems by iteration.

# Queues will be used for processing all of the computations.

#import Base.Collections: PriorityQueue, enqueue!, dequeue!, peek

import Base.insert!

# Rules operate on working memory, which will be represented as one big MemTree.

include("memories.jl")
include("pq.jl")

# ==== Data Structures =====


# A Rule holds the information relevant to a particular propagation rule.
# * The sources correspond to the predicate expressions pulled out of the rule
# body. Normally, you would think of these as giving the predicate number and
# argument types, so that you could pull the data associated with the relevant
# predicate instance out of working memory. If 2nd-order stuff is going on, it
# will be more complicated; a predicate variable could mean we're not
# restricted to dealing with a single predicate, and tuple variables could mean
# we're not restricted to a concrete arg list.
# * The sourcemaps give translations, in the form of Dict{VarLoc,VarLoc} maps,
# from the source domains in WM to the rule space. You can think of this as
# giving the variable matches: if two variables map to the same VarLocs, they
# are matched.
# * The combination function determines how things will be combined when they
# all go into the rulespace together. Things will first be dranslated into the
# rulespace domain by the maps, and then combined into one MemTree by the combo
# function. It takes a vector of MemTrees and turns them into one MemTree.
# * The summarize function takes the combined material and summarizes out the
# dimensions which are not in the target, for example by integration.
# * The target domain gives the location in working memory where the result can
# go; as with the sources, you can usually think of this as specifying the
# predicate number and argument type.

mutable struct Rule
  sources::Array{Domain} # An array of domains representing the predicate-patterms pulled from.
  sourcemaps::Array{Dict{VarLoc, VarLoc}} # Each source must have its own mapping from the common WM space to the rulespace; this determines variable matching.
  target::Domain
  rulespace::Domain # Declares the type/extent of the rulespace. Needed when mapping into rulespace, since MemTree reordering requires a target domain.
  combine::Function
  summarize::Function
  merge::Function # The function used to merge results with rules having overlapping targets.
  overlapping_rules::Array{Int} # The rule_nums of rules with matching output type and overlapping targets, for purposes of merging results.
  rule_num::Int # The number of the rule, used to index it in e.g. overlapping_rules.
  overlapping_types::Vector{Function} # the set of merge types the rule overlaps, not including its own
  fire_count::Int
  useless_fire_count::Int
end

Rule(a,b,c,d,e,f,g,h,i,j) = Rule(a,b,c,d,e,f,g,h,i,j,0,0)



# A change represents a triggering of a particular rule; it carries the edit to
# WM and a rule triggered by this edit, along with the domain in rule-space
# which needs to be recalculated. (This must be calculated by mapping in the
# source domain of the wm modification which triggered the rule.)

struct Change
  rule::Rule
  domain::Domain
end

# A RuleSystem is a set of propagation rules to be solved by iteration. They
# share a common WM for value storage and a priority queue for propagation of
# changes. patterns is a list of all the domains of predicate-patterns occurring
# in rule bodies, used to check if a change to wm triggers any rules, together
# with the rule which would be triggered and the number of the source within
# the rule which matches that pattern (so that we can make a Change).
# 'pred_nums' holds a map from the predicate numbers, used internally, to the
# predictate symbols used in the written rules. 'pred_names' reverses this, to
# give the symbol given the number.

mutable struct RuleSystem
  rules::Vector{Rule}
  patterns::Vector{Tuple{Domain, Rule, Int}}
  output_buffers::Vector{MemTree} # hold results to facilitate merging results of rules with overlapping targets; one memtree for each rule.
  wm::MemTree
  pqs::Vector{PQ}
  pred_names::Dict{Int, Symbol}
  pred_nums::Dict{Symbol, Int}
  lines # The source code of the rule system, used when it's included in another rule system.
  merge_output_buffers::Dict{Function, MemTree} # map from merge ops to a unified output buffer for that merge type, for merge purposes
  local_defaults::MemTree
  last_fired::Change
  last_fired_useful::Bool
  step::Int
end

blankdom = Domain(ESig())
blankrule = Rule(Domain[], Dict{VarLoc,VarLoc}[], blankdom, blankdom, identity, identity, identity, Int[], 0, Function[])
blankchange = Change(blankrule, blankdom)

RuleSystem(a,b,c,d,e,f,g,h,i,j) = RuleSystem(a,b,c,d,e,f,g,h,i,j,blankchange, true, 0)

Base.copy(x::T) where T = T([getfield(x, k) for k ∈ fieldnames(T)]...)


# ===== Compilation =====

# First let's define some predicates to recognize the important aspects of the
# proposed syntax.

function is_predicate(s, preds::Set{Symbol})
  return in(s,preds)
end

function is_predicate_var(s)
  return typeof(s) == Symbol && isuppercase(string(s)[1])
end

function is_uvar(s)
  return typeof(s) == Symbol && reverse(string(s))[1] == '!'
end

function is_tuple_var(s)
  return typeof(s) == Symbol && reverse(string(s))[1] == '_' && string(s)[1] == '_'
end

function is_firstorder(s, preds::Set{Symbol})
  return typeof(s) == Symbol && islowercase(string(s)[1]) && (!(is_predicate(s, preds) || is_predicate_var(s) || is_uvar(s) || is_tuple_var(s)))
end

#function is_tuple_access(e::Any)
#  return typeof(e) == Expr && e.head == :. && is_tuple_var(args[1])
#end

# Delta functions are specified directly as linear constraints, in square brackets, such as [2*x + 3*y = z].

#function is_delta_fn(e)
#  return typeof(e) == Expr && e.head == :vect && length(e.args) == 1 && e.args[1].head == :(=)
#end

# Constraints are written [1<a<=2], and are 1 when true and 0 when false.
# (Generalizes delta functions; so, actually hyperreal  infinity in the case of
# equality, like [x==y].)
# Adding [[P == pred1]] notation, allowing second-order constrainst without
# allowing them to be mixed with first-order constraints. I'm not being careful
# about checking that a given constraint is either a proper first-order or a
# proper second-order thing for now; is_constraint just checks for the brackets
# with something inside them, and I'll throw errors elsewhere if the stuff
# inside is not in the right format. Could revisit that later.
# Adding tuple constraints, [[_t_ = (x,y)]].

function is_constraint(e)
  return typeof(e) == Expr && e.head == :vect && length(e.args) == 1 # && typeof(e.args[1]) == Expr && e.args[1].head == :comparison
end

function is_secondorder_constraint(e)
  return is_constraint(e) && typeof(e.args[1]) == Expr && e.args[1].head == :vect # doubly nested vect
end

function secondorder_constraint_var(e) # get the second order variable from a second order constraint; it is assumed to appear first
  return e.args[1].args[1].args[2]
end

function secondorder_constraint_instance(e) # grab the other side of the equality in the second order constraint
  return e.args[1].args[1].args[3]
end

function is_pred_constraint(e)
  return is_secondorder_constraint(e) && is_predicate_var(secondorder_constraint_var(e))
end

function is_tuple_constraint(e)
  return is_secondorder_constraint(e) && is_tuple_var(secondorder_constraint_var(e))
end

function is_predicate_pattern(preds::Set{Symbol}, s)
  if typeof(s) == Expr && s.head == :call
    if in(s.args[1], preds) || is_predicate_var(s.args[1])
      return true
    elseif typeof(s.args[1]) == Expr && s.args[1].head == :curly
      if in(s.args[1].args[1], preds) || is_predicate_var(s.args[1].args[1])
        return true
      end
    end
  end
  return false
end

# get_p_expressions pulls out sub-expressions satisfying a given predicate.

function get_p_expressions(p::Function, expr::Any)
  if p(expr)
    return Set([expr])
  elseif typeof(expr) == Expr
    if expr.head == :call
      #return reduce(union, Set([]), map((arg -> get_p_expressions(p, arg)), expr.args[2:end]))
      return reduce(union, map((arg -> get_p_expressions(p, arg)), expr.args[2:end]); init=Set([]))
    elseif expr.head == :(=) || expr.head == :tuple || expr.head == :block || expr.head == :comparison || expr.head == :vect
      #return reduce(union, Set([]), map((arg -> get_p_expressions(p, arg)), expr.args[1:end]))
      return reduce(union, map((arg -> get_p_expressions(p, arg)), expr.args[1:end]); init=Set([]))
    else # not a thing we know how to descend
      return Set([])
    end
  else # not an expression (could be a single symbol)
    return Set([])
  end
end

# pattern_expressions pulls out the predicate patterns from the expression
# which is the rule body.

function pattern_expressions(preds::Set{Symbol}, expr::Any)
  return get_p_expressions((x -> is_predicate_pattern(preds, x)), expr)
end

# delta_expressions pulls out the delta expressions from the rule body.

#function delta_expressions(expr::Any)
#  return get_p_expressions(is_delta_fn, expr)
#end

# constraint_expressions pulls out the constraint expressions from the rule body

function constraint_expressions(expr::Any)
  return get_p_expressions(is_constraint, expr)
end

# here's just the tuple constraints

function tuple_constraint_expressions(expr::Any)
  return get_p_expressions(is_tuple_constraint, expr)
end

# Takes a pattern (a rule head, or extracted from the rule body) and returns
# the domain of that pattern (where it would be stored in WM).

function pattern_domain(pred_nums::Dict{Symbol, Int}, expr::Any)
  if typeof(expr) == Expr && expr.head == :call # if it's a pattern as expected
    # figure out car
    uvar_num = 0               # this is true if no curly brackets
    pred_symbol = expr.args[1] # this is true if no curly brackets
    if typeof(expr.args[1]) == Expr && expr.args[1].head == :curly # any curly brackets?
      uvar_num = length(expr.args[1].args)-1  # count the uvars
      pred_symbol = expr.args[1].args[1]      # correct the pred symbol
    end
    psig_ranges = Vector(undef, uvar_num+1)
    #p_max = length(pred_nums)
    if is_predicate_var(pred_symbol) # predicate is variable
      psig_ranges[1] = 1:largest_p#p_max
    else # predicate is a given constant
      car_pred_num = pred_nums[pred_symbol]
      psig_ranges[1] = car_pred_num:car_pred_num
    end
    for i=1:uvar_num # now figure out the rest of the dimensions (if any)
      uvar_representation = expr.args[1].args[i+1]
      if typeof(uvar_representation) == Expr && uvar_representation.args[1] == :(:) # a range is given
        psig_ranges[i+1] = eval(uvar_representation)
      elseif typeof(uvar_representation) <: Int # a single number is given
        psig_ranges[i+1] = uvar_representation:uvar_representation
      else
        psig_ranges[i+1] = 1:largest_p # uvars can range higher than the number of predicates
      end
    end
    car_sig = PSig(psig_ranges)
    # figure out cdr
    if length(expr.args) > 1 && typeof(expr.args[2]) == Expr && expr.args[2].head == :... # A tuple variable is occurring in argument-capture form
      if length(expr.args) > 2
        throw("In pattern_domain: A tuple variable is capturing all the arguments; no further arguments should be given: $expr")
      end
      cdr_sig = UnspecifiedTSig()
    else
      cdr_sig = SpecifiedTSig(map((x -> expression_sig(pred_nums, x)), expr.args[2:length(expr.args)]))
    end
    # combine them
    exp_sig = SpecifiedTSig([car_sig, cdr_sig])
    # exp_domain = Domain(exp_sig)
    # look for first-order variable equalities.
    varlocs = get_variable_locs(expr, Set(keys(pred_nums))) # get_variable_locs returns a set of pairs, not a Dict, so that we can see duplicate variables
    # first_order_varlocs =  [filter((pair -> is_firstorder(pair[1], Set(keys(pred_nums)))), varlocs)...]
    # duplicates = Vector{Tuple{VarLoc,VarLoc}}[]
    # for v1 in 1:length(first_order_varlocs)
    #   for v2 in 1:(v1-1) # only look at v2 earlier than v1 to avoid counting twice
    #     if (first_order_varlocs[v1])[1] == (first_order_varlocs[v2])[1] # if the symbol is the same,
    #       duplicates = vcat(duplicates, ((first_order_varlocs[v1])[2], (first_order_varlocs[v2])[2])) # record the varlocs.
    #     end
    #   end
    # end
    # reg = exp_domain.reg
    # for dup in duplicates # constrain the reg to make the vars equal for each matched variable
    #   coefs = zeros(reg.dimensionality)
    #   n1 = exp_domain.map[dup[1]]
    #   n2 = exp_domain.map[dup[2]]
    #   coefs[n1] = 1.0
    #   coefs[n2] = -1.0
    #   s = LinSplit(coefs, 0.0)
    #   reg = intersection(reg, delta_reg(s))
    # end
    (reg, dimnum_map) = first_order_constraints(pred_nums, varlocs)
    exp_domain = Domain(exp_sig, reg, dimnum_map)
    return exp_domain
  else
    throw("pattern_domain handed a non-pattern, $expr")
  end
end

# Recurs down the expression tree returning signatures.

function expression_sig(pred_nums::Dict{Symbol, Int}, expr::Any)
  if typeof(expr) == Expr
    if expr.head == :tuple # if this is a tuple
      return SpecifiedTSig(map((e -> expression_sig(pred_nums, e)), expr.args))
    elseif expr.head == :curly # this is a predicate w uvars attached
      return PSig(map((e -> (s -> typeof(s) == USig ? s.range : s.ranges[1])(expression_sig(pred_nums, e))), expr.args))
    elseif expr.head == :call && expr.args[1] == :(:)
      return USig(eval(expr))
    else
      throw("When converting $expr into a domain, unsure how to procede.")
    end
  elseif is_tuple_var(expr)
    return UnspecifiedTSig()
  elseif is_predicate_var(expr)
    return PSig([1:largest_p])
  elseif is_predicate(expr, Set(keys(pred_nums)))
    n=pred_nums[expr]
    return PSig([n:n])
  elseif is_uvar(expr)
    return USig(1:largest_p)
  elseif typeof(expr) == Symbol
    return VSig()
  else
    throw("When converting $expr into a domain, unsure how to procede.")
  end
end

#= discarded the idea of putting uvars in body
# Counts uvars in the body, so that we know how many to put into the psig.

function count_uvars(expr::Any)
  if typeof(expr) == Expr
    if expr.head == :tuple # if this is a tuple
      return sum(map((e -> count_uvars(e)), expr.args))
    else
      throw("When counting uvars in $expr, unsure how to procede.")
    end
  elseif is_tuple_var(expr)
    return 0
  elseif is_predicate_var(expr)
    return 0
  elseif is_universal_var(expr)
    return 1
  elseif is_predicate(expr, Set(keys(pred_nums)))
    return 0
  elseif typeof(expr) == Symbol
    return 0
  else
    throw("When converting $expr into a domain, unsure how to procede.")
  end
end =#

# get_variables takes a pattern and crawls it, extracting (variable, location)
# pairs as a set.

function get_variable_locs(expr::Expr, preds::Set{Symbol})
  return get_variable_locs(expr, Int[], preds)
end

# Recursive case of get_variable_locs. The expression expr is recursively broken
# down; IE, the various cases should deal direcly with expr, not with the sub-
# expression indicated by the loc, and should pass down simplified expressions,
# not the whole expression. The loc, on the other hand, is built on as we
# descend the recursion, so that when we arrive at single variables, we know
# what location to return. This is returned as a set of (variable, location)
# pairs, which is then recursively built up as interior calls return.

function get_variable_locs(expr::Any, loc::VarLoc, preds::Set{Symbol})
  if typeof(expr) == Expr # indicates that we will probably need to recur
    if expr.head == :call
      # calls, like p(x), are given signatures as if they're a tuple like ((p), (x, y)).
      head_set = get_variable_locs(expr.args[1], vcat(loc, 1), preds)
      if length(expr.args) > 1 && typeof(expr.args[2]) == Expr && expr.args[2].head == :... # A tuple variable is occurring in argument-capture form
        if length(expr.args) > 2
          throw("In get_variable_locs: A tuple variable is capturing all the arguments; no further arguments should be given: $expr")
        else
          tail_set = Set{Tuple{Symbol, VarLoc}}((Tuple{Symbol, VarLoc}((expr.args[2].args[1], vcat(loc ,Int[2]))),)) # tuple var just has location 2 relative to the whole call location
        end
      else # normal argument list
        if length(expr.args) > 2
          tail_set = union(map(((x,y) -> get_variable_locs(x, vcat(loc, Int[2,y]), preds)), expr.args[2:length(expr.args)], collect(1:(length(expr.args)-1)))...)
        elseif length(expr.args) == 2
          tail_set = get_variable_locs(expr.args[2], Int[2,1], preds)
        else
          tail_set = Set{Tuple{Symbol, VarLoc}}()
        end
      end
      return union(head_set, tail_set)
    elseif expr.head == :curly
      # uvars, like p{u!,v!}(x,y), are given locations as if it's like ((p, u!, v!), (x, y)).
      # if we're at a curly, we've already descended down to an expression like p{u!,v!}.
      pred_given = expr.args[1] # the actual predicate is the first pvar
      uvars = expr.args[2:length(expr.args)] # the uvars are the rest
      vmap = [(uvars[i], vcat(loc, i+1)) for i=1:length(uvars)] # location of pvars is loc, plus 1, plus their number
      filtered_map = filter((x -> typeof(x[1])==Symbol), vmap) # remove UnitRange elements; these are not variables! This must be done after assigning locations, for the locations to be correct.
      result = Set{Tuple{Symbol, VarLoc}}(filtered_map)
      if is_predicate_var(pred_given) # Record the car if it's a predicate variable
        result = union(result, Set{Tuple{Symbol, VarLoc}}(((pred_given, vcat(loc, Int[1])),)))
      end
      return result
    elseif expr.head == :tuple
      recurrence_sets = map(((x,y) -> get_variable_locs(x, vcat(loc, y), preds)), expr.args, collect(1:length(expr.args)))
      return Set{Tuple{Symbol, VarLoc}}(union(Tuple{Symbol,VarLoc}[], recurrence_sets...))
    elseif expr.head == :(:) # a range, standing for a plural uvar constant
      return Set{Tuple{Symbol, VarLoc}}()
    else
        throw("get_variable_locs encountered a $(expr.head) in the arguments of a pattern.")
    end
  else # should be a variable or a constant
    if is_predicate(expr, preds)
      return Set{Tuple{Symbol, VarLoc}}()
    else
      if is_predicate_var(expr) # have to add 1 at the end of the loc for preds, acconding for the fact that the pred is its own first var
        return Set{Tuple{Symbol, VarLoc}}(((expr, [loc...,1]),))
      elseif is_predicate(expr, preds) # predicate constant
        return Set{Tuple{Symbol, VarLoc}}()
      elseif typeof(expr) <: Int # singular uvar constant
        return Set{Tuple{Symbol, VarLoc}}()
      else
        return Set{Tuple{Symbol, VarLoc}}(((expr, loc),))
      end
    end
  end
end

# Strip out the variables from the var,varloc pairs.

function just_variables(pairs::Set{Tuple{Symbol, VarLoc}})
  Set(map((pair -> pair[1]), [pairs...]))
end

function get_variable_groups(expr::Any, preds::Set{Symbol})
  if typeof(expr) == Expr && typeof(expr.args[1]) == Expr && expr.args[1].head == :curly
    return Set{Any}((expr.args[1], just_variables(get_variable_locs(Expr(:tuple, expr.args[2:length(expr.args)]...), preds))...))
  elseif typeof(expr) == Expr && expr.head == :tuple
    return union(map((arg -> get_variable_groups(arg, preds)), expr.args)...)
  else
    return just_variables(get_variable_locs(expr, Int[], preds))
  end
end

function first_order_constraints(pred_nums::Dict{Symbol, Int}, vl_pairs::Set{Tuple{Symbol, VarLoc}})
  first_order_varlocs =  [filter((pair -> is_firstorder(pair[1], Set(keys(pred_nums)))), vl_pairs)...]
  just_varlocs = map((sv -> sv[2]), first_order_varlocs)
  varmap = Dict{VarLoc,Int}(Set(map((n -> (just_varlocs[n])=>n), collect(1:length(first_order_varlocs)))))
  duplicates = Vector{Tuple{VarLoc,VarLoc}}[]
  for v1 in 1:length(first_order_varlocs)
    for v2 in 1:(v1-1) # only look at v2 earlier than v1 to avoid counting twice
      if (first_order_varlocs[v1])[1] == (first_order_varlocs[v2])[1] # if the symbol is the same,
        duplicates = vcat(duplicates, ((first_order_varlocs[v1])[2], (first_order_varlocs[v2])[2])) # record the varlocs.
      end
    end
  end
  reg = boundless_reg(length(first_order_varlocs))
  for dup in duplicates # constrain the reg to make the vars equal for each matched variable
    coefs = zeros(reg.dimensionality)
    n1 = varmap[dup[1]]
    n2 = varmap[dup[2]]
    coefs[n1] = 1.0
    coefs[n2] = -1.0
    s = LinSplit(coefs, 0.0)
    reg = intersection(reg, delta_reg(s))
  end
  return (reg, varmap)
end


# Creates a domain from expression_sig

function expression_dom(pred_nums::Dict{Symbol, Int}, expr::Any)
  vl = get_variable_locs(expr, Int[], Set(keys(pred_nums)))
  (reg, vmap) = first_order_constraints(pred_nums, vl)
  return Domain(expression_sig(pred_nums, expr), reg, vmap)
end

# From the set of pattern expressions in the body plus the one in the head, I
# need to create a rulespace containing all the variables, and mappings into the
# rulespace. So that it's easy to know which dimensions to summarize out when
# that's necessary, it is important to enforce the convention that the initial
# segment of the rulespace is the targetspace, IE, the space of the predicate
# pattern in the rule head.

# CHANGE: Now that I have added tuple constraints, I need to also extract vars
# from those, because it is possible that a tuple constraint introduces some
# variables which are not matched anywhere else (which need to be summarized
# out when all the extra variables are summarized out).

# First step is to get a variable ordering for rulespace. rulespace_var_order
# takes the expression of the rule head, and the set of all variables which
# occur in the rule. It returns a constructed pattern which never occurs
# anywhere, but which has an initial part agreeing with the head pattern.
# More specifically: it returns a tuple whose first element is the head of the
# rule head, EG "p" or "p{x!}", and second element is the tail, IE the argument
# list fed to p (or a single tuple variable, if argument-capture is happening).
# The remaining elements are individual vars which don't occur anywhere in the
# first two elements.

# CHANGE: now that I've added universal variables, I need to accept a set of
# "variable groups" (so Set{Any}, to accommodate expressions rather than just
# symbols), to include things like pred{x!, y!} rather than just lone vars.
# Hmm. Seems

function rulespace_var_order(target_pattern::Expr, variable_groups::Set{Any}, preds::Set{Symbol})
  target_symbols::Set{Symbol} = just_variables(get_variable_locs(target_pattern, preds))
  head = target_pattern.args[1]
  if length(target_pattern.args)>1 && typeof(target_pattern.args[2])==Expr && target_pattern.args[2].head==:(...)
    arguments = target_pattern.args[2].args[1]
  else
    arguments = Expr(:tuple, target_pattern.args[2:length(target_pattern.args)]...)
  end
  extras = remove_target_symbols(variable_groups, target_symbols)
  return Expr(:tuple, head, arguments, extras...)
end

rulespace_var_order(target_pattern::Expr, variable_groups::Set{Symbol}, preds::Set{Symbol}) = rulespace_var_order(target_pattern::Expr, variable_groups::Set{Any}, preds::Set{Symbol})

function remove_target_symbols(variable_groups::Set{Any}, target_symbols::Set{Symbol})
  #extras = setdiff(variable_groups, target_symbols)
  just_sym = filter((x -> typeof(x)==Symbol), variable_groups)
  just_exp = setdiff(variable_groups, just_sym)
  extra_sym = setdiff(just_sym, target_symbols)
  extra_exps = Set{Any}()
  for exp in just_exp # go thru the expressions. Determine whether they need to be modified.
    barrier = false
    new_exp = copy(exp)
    for i in length(exp.args):-1:1
      if !in(exp.args[i], target_symbols)
        barrier = true
      else
        if barrier == true
          return throw("The match implied by $(exp) cannot be achieved without reordering universal variables, which is not yet implemented.")
        end
        new_exp.args = new_exp.args[1:(i-1)]
      end
    end
    if length(new_exp.args) >= 1
      extra_exps = union(extra_exps, [new_exp])
    end
  end
  return union(extra_sym, extra_exps)
end

# We can compute the sourcemaps by looking at the var,location pairs extracted
# from the source patterns and comparing these to the var,location pairs we can
# extract from the rulespace pattern. I assume no duplicated variables in
# patterns.

function compute_sourcemap(rulespace_varlocs::Set{Tuple{Symbol, VarLoc}}, source_varlocs::Set{Tuple{Symbol, VarLoc}})
  results = Dict{VarLoc,VarLoc}()
  for source_pair in source_varlocs
    for target_pair in rulespace_varlocs
      if source_pair[1] == target_pair[1]
        results = Dict{VarLoc,VarLoc}(union(results, Dict(source_pair[2]=>target_pair[2])))
      end
    end
  end # If the double loop does become inefficient, better convert one set to dict and use access
  return results
end

# expressionreplace takes two vectors which should be the same length, and a quoted
# expression. It recursively descends the Expr structure, replacing anything which
# is == to an item in the 1st vector with the item at the same index in the 2nd vector.

function findin(originals::Vector, expression::Any)
  for i=1:length(originals)
    if expression == originals[i]
      return i
    end
  end
  return 0
end

function expressionreplace(originals::Vector, replacements::Vector, expression::Any)
  index = findin(originals, expression) # if we find one of the originals,
  if index > 0
    return replacements[index] # return corresponding replacement.
  end
  if typeof(expression) == Expr # Otherwise, recur if possible,
    cp = copy(expression)
    cp.args = map((x -> expressionreplace(originals, replacements, x)), cp.args)
    return cp
  else
    return expression # or return the expression as-is.
  end
end


# take a linear expression (one side of a linear constraint) and return a vector
# with the first n entries being the coefficients for the variables, and the
# final entry helding the sum of any constant terms. Variables occur in the
# order indicated by a Dict{Symbol, Int}, v.

function convert_linear_expression(e, v::Dict{Symbol, Int})
  result = zeros(length(v)+1) # initialize
  if typeof(e) <: Number # if it's a constant
    result[length(v)+1] = e # put it into the constant position
  elseif typeof(e) == Symbol # if it's a variable w/o coefficient
    result[v[e]] = 1 # put it in its position
  elseif typeof(e) == Expr && e.head == :call && e.args[1] == :* && length(e.args) == 3 # it's (hopefully) a variable times a constant
    if typeof(e.args[2]) <: Number && typeof(e.args[3]) == Symbol # number first
      result[v[e.args[3]]] = e.args[2]
    elseif typeof(e.args[3]) <: Number && typeof(e.args[2]) == Symbol # variable first
      result[v[e.args[2]]] = e.args[3]
    else # don't know what to do
      throw("convert_linear_expression doesn't know how to handle $e")
    end
  elseif typeof(e) == Expr && e.head == :call && e.args[1] == :+ # it is a sum of terms
    for i in 2:length(e.args)
      result = result + convert_linear_expression(e.args[i] ,v)
    end
  elseif typeof(e) == Expr && e.head == :call && e.args[1] == :- && length(e.args) == 3  # term minus term
    result = convert_linear_expression(e.args[2], v) - convert_linear_expression(e.args[3], v)
  elseif typeof(e) == Expr && e.head == :call && e.args[1] == :- && length(e.args) == 2 # negative term
    result = -convert_linear_expression(e.args[2], v)
  elseif typeof(e) == Expr && e.head == :block # a block of code
    if length(e.args) > 2
      throw("convert_linear_expression doesn't know how to handle blocks like $(e.args)")
    end
    for item in e.args
      if typeof(item) != LineNumberNode
        return convert_linear_expression(item, v)
      end
    end
  else # don't know what to do
    throw("convert_linear_expression doesn't know how to handle $e")
  end
  return result
end

# Convert linear expressions representing the left and right side of a
# constraint (an equality or inequality) into a solved form represented by a
# vector of length one greater than the number of variables, in which the
# first n numbers are coefficients in the variable-order v, on the left, and the
# final number is the constant on the right.

function parse_linear_equation(l::Any, r::Any, v::Dict{Symbol, Int})
  left = convert_linear_expression(l, v)
  right = convert_linear_expression(r, v)
  # need to flip the constants to represent putting them on the other side of the equation
  left[length(left)] = -left[length(left)]
  right[length(right)] = -right[length(right)]
  result = left - right # represents solving by putting all variables on one side and constants on the other
  return result
end

# standard_varnums combines get_variable_locs with standard_varmap to make a
# standardized map from variable names to varnums based on a given pattern.

function standard_varnums(dom::Domain, e::Expr, preds::Set{Symbol})
  varlocs = get_variable_locs(e, Int[], preds)
  varlocs = filter((pair -> is_firstorder(pair[1], preds)), varlocs)
  vm = standard_varmap(dom.sig)
  return Dict{Symbol,Int}(map((vl -> vl[1]=>vm[vl[2]]), [varlocs...]))
end

# Take a linear constraint, and return a MemTree which can be incorporated into
# the rule combination function in its place, expressing the constraint.

function constraints_unpack(constraint::Expr, rulespace_tuple::Expr, rulespace_domain::Domain, preds::Set{Symbol}, pred_nums::Dict{Symbol, Int})
  if is_secondorder_constraint(constraint) # typeof(constraint.args[1]) == Expr && constraint.args[1].head == :vect # doubly nested vect; go to second order case
    return unpack_second_order_constraint(constraint, rulespace_tuple, rulespace_domain, preds, pred_nums)
  end
  v = standard_varnums(rulespace_domain, rulespace_tuple, preds) # a standardized Dict{Symbol, Int} to use
  varmap = standard_varmap(rulespace_domain.sig) # a standard Dict{VarLoc, Int}
  comparison_vector = (constraint.args)[1].args
  num_comparisons = (length(comparison_vector)-1)÷2
  if num_comparisons == 1 # In this situation, things are in [op arg1 arg2 order]
    result = constraint_unpack(comparison_vector[2], comparison_vector[3], comparison_vector[1], v, varmap, rulespace_domain)
  else # otherwise, things are in [arg1 op arg2 op arg3...] order
    result = constraint_unpack(comparison_vector[1], comparison_vector[3], comparison_vector[2], v, varmap, rulespace_domain)
    for comp in 2:num_comparisons
      shift = comp*2
      result = result * constraint_unpack(comparison_vector[shift-1], comparison_vector[shift+1], comparison_vector[shift], v, varmap, rulespace_domain)
    end
    return result
  end
end

# Helper function for constraints_unpack. Creates the MemTree for just one
# constraint in a constraint chain.

function constraint_unpack(l::Any, r::Any, connective::Symbol, v::Dict{Symbol, Int}, varmap::Dict{VarLoc, Int}, rulespace_domain::Domain)
  solved = parse_linear_equation(l, r, v)
  coefs = solved[1:(length(solved)-1)]
  cons = solved[length(solved)]
  # some cases can be reduced to other cases
  if connective == :(>)
    coefs = -coefs
    cons = -cons
    connective = :(<)
  elseif connective == :(<=)
    coefs = -coefs
    cons = -cons
    connective = :(>=)
  end
  # base cases
  if connective == :(==)
    split = LinSplit(coefs, cons)
    root = delta_slice(split)
  elseif connective == :(>=) # positive side of split includes points where dot product with coefs is >= the constant; negative includes >
    split = LinSplit(coefs, cons) # now we want negative dot products on the neg side, and we put 1.0 on that side
    root = SplitNode(split, LeafNode(0.0), LeafNode(1.0)) # child ordering is neg, pos
  elseif connective == :(<)
    split = LinSplit(coefs, cons)
    root = SplitNode(split, LeafNode(1.0), LeafNode(0.0))
  elseif connective == :(!=)
    split1 = LinSplit(coefs, cons)
    split2 = LinSplit(-coefs, -cons)
    root = SplitNode(split1, LeafNode(1.0), SplitNode(split2, LeafNode(1.0), LeafNode(0.0)))
  else
    throw("constraint_unpack encountered unknown connective, $(connective), between $(l) and $(r)")
  end
  mleaf = MemLeaf(root, varmap)
  mtree = MemTree(rulespace_domain, mleaf)
  return mtree
end

function unpack_second_order_constraint(constraint::Expr, rulespace_tuple::Expr, rulespace_domain::Domain, preds::Set{Symbol}, pred_nums::Dict{Symbol, Int})
  # extract the second order variable, which is assumed to be before the equality rather than after
  var_mentioned = secondorder_constraint_var(constraint) # constraint.args[1].args[1].args[1]
  # find the varloc of the second-order variable mentioned in the constraint, so that we can split on its location
  vls = Dict{Symbol,VarLoc}(map((pair -> pair[1]=>pair[2]), [get_variable_locs(rulespace_tuple, Int[], preds)...]))
  vl = vls[var_mentioned]
  if is_predicate_var(var_mentioned) # it's a predicate-variable constraint
    # figure out what numerical value the predicate named has
    pred_mentioned = constraint.args[1].args[1].args[3]
    num = pred_nums[pred_mentioned]
    # construct a tree with value 1 when the 2nd order var has the desired value, 0 otherwise
    return mt(rulespace_domain, ps(vl, num+1, ps(vl, num, ml(0.0), ml(1.0)), ml(0.0)))
  else # it's a tuple-variable constraint
    explicit_tuple = constraint.args[1].args[1].args[3]
    bound_sig = tuple_sig(explicit_tuple, preds)
    first_order_variable_numbers = standard_varnums(rulespace_domain, rulespace_tuple, preds)
    # initialize memleaf root, memleaf map, map_size, equal_vars_list
    memleaf_root = LeafNode(1.0)
    memleaf_map = standard_varmap(rulespace_domain.sig) # will be consistent with first_order_variable_numbers; both use standard_varmap to number
    map_size = length(memleaf_map)
    equal_vars_list = Dict{Int,Int}()
    for i in 1:length(explicit_tuple.args)
      if is_firstorder(explicit_tuple.args[i], preds) # if the ith item is first order, add an appropriate variable to memleaf_map and to list of equal vars
        # extend the map
        new_varloc = vcat(vl,i)
        map_size += 1
        memleaf_map = push!(memleaf_map, new_varloc=>map_size)
        # extend the list of vars we'll need to constrain
        if haskey(first_order_variable_numbers, explicit_tuple.args[i])
          corresponding_variable = first_order_variable_numbers[explicit_tuple.args[i]]
          equal_vars_list = push!(equal_vars_list, map_size=>corresponding_variable)
        end
      else # the element wasn't first order
        throw("Problem unpacking $constraint element $(explicit_tuple.args[i]): Non-first-ordr items in tuple destructuring is not yet supported.")
      end
    end
    # now add all the necessary constraints to the root
    for pair in equal_vars_list
      memleaf_root = var_equality_constraint(pair[1], pair[2], map_size, memleaf_root) * Hyper(1.0,1)
    end
    return MemTree(rulespace_domain, TSplit(vl, Dict(bound_sig=>MemLeaf(memleaf_root, memleaf_map)), MemLeaf(0.0,standard_varmap(rulespace_domain.sig))))
  end
end

function tuple_sig(tuple, preds)
  l = length(tuple.args)
  vec = Array{Signature}(undef, l) # Vector{Signature}(l)
  for i in 1:l
    if is_predicate_var(tuple.args[i])
      vec[i] = PSig([1:largest_p])
    elseif is_tuple_var(tuple.args[i])
      vec[i] = UnspecifiedTSig()
    elseif is_firstorder(tuple.args[i], preds)
      vec[i] = VSig()
    else
      throw("Unable to unpack tuple $tuple")
    end
  end
  return SpecifiedTSig(vec)
end

function var_equality_constraint(v1::Int, v2::Int, max_dim::Int, value)
  v = zeros(max_dim)
  v[v1] = 1.0
  v[v2] = -1.0
  split = LinSplit(v, 0.0)
  return delta_slice(split, value)
end


# take a delta function expression, and return the memtree to put into the
# function body in its place.

#function delta_fn_unpack(delta_exp::Expr, rulespace_pattern::Expr, rulespace_domain::Domain, preds::Set{Symbol})
#  v = standard_varnums(rulespace_domain, rulespace_pattern, preds)
#  varmap = standard_varmap(rulespace_domain.sig)
#  solved = parse_linear_equation(delta_exp.args[1], v)
#  coefs = solved[1:(length(solved)-1)]
#  cons = solved[length(solved)]
#  split1 = LinSplit(coefs, cons) # positive side of split includes points where dot product with coefs is > the constant; negative includes >=
#  split2 = LinSplit(-coefs, -cons) # reverse: same hyperplane, but the == case is now on the positive side
#  root = SplitNode(split1, SplitNode(split2, LeafNode(Hyper(1.0, 1)), LeafNode(0.0)), LeafNode(0.0))
#  #tree = BSPTree(boundless_reg(length(coefs)), root)
#  mleaf = MemLeaf(root, varmap)
#  mtree = MemTree(rulespace_domain, mleaf)
#  return mtree
#end

# makecombofun takes the predicate ordering and the rule body, and creates
# the combination function from these.

function makecombofun(patterns::Vector, body::Any, rulespace_tuple::Expr, rulespace_domain::Domain, preds::Set{Symbol}, pred_nums::Dict{Symbol, Int})
  names = [gensym() for x = patterns]
  newbody = expressionreplace(patterns, names, body)
  constraint_exps = [constraint_expressions(body)...]
  constraint_fns = map((expr -> constraints_unpack(expr, rulespace_tuple, rulespace_domain, preds, pred_nums)), constraint_exps)
  newbody = expressionreplace(constraint_exps, constraint_fns, newbody)
  #newbody = :(MemTree($(rulespace_domain), MemLeaf(1.0))*$(newbody)) # make sure it has the right domain, in case it's a pure arithmetic expression with no patterns TODO this is an ugly hack
  newbody = :(MemTree($(rulespace_domain), $(newbody))) # make sure it has the right domain, in case it's a pure arithmetic expression with no patterns
  code = Expr(:->, Expr(:tuple, names...), newbody)
  return code
end

# Takes the predicate ordering and the rule body to be compiled, and
# returns a function combining a vector of trees to a single tree
# via the appropriate combination.
# TODO: doesn't eval within the original environment, which means that
# the user may be surprised by the incorrect behavior with respect to
# user parameters within the function body.

function compilecombofun(patterns::Vector, body::Any, rulespace_tuple::Expr, rulespace_domain::Domain, preds::Set{Symbol}, pred_nums::Dict{Symbol, Int})
  #print("New combo fn:\n")
  #print("patterns = $(patterns)\n")
  #print("body = $(body)\n")
  #print("rulespace_tuple = $(rulespace_tuple)\n")
  #print("rulespace_domain = $(rulespace_domain)\n")
  #print("preds = $(preds)\n")
  #print("result: ")
  #print(makecombofun(patterns, body, rulespace_tuple, rulespace_domain, preds, pred_nums))
  #print("\n")
  # return (x -> (eval(makecombofun(patterns, body, rulespace_tuple, rulespace_domain, preds, pred_nums)))(x...))
  code = makecombofun(patterns, body, rulespace_tuple, rulespace_domain, preds, pred_nums)
  return eval(code)
end

function make_rule(head::Expr, body::Any, sumfn::Function, preds::Set{Symbol}, pred_nums::Dict{Symbol, Int}, overlapping_rules::Vector{Int}, rule_num::Int, overlapping_types::Vector{Function})
  patterns = [pattern_expressions(preds, body)...]
  source_domains = map((pattern -> pattern_domain(pred_nums, pattern)), patterns)
  target_domain = pattern_domain(pred_nums, head)
  source_varlocs = map((x -> get_variable_locs(x, preds)), patterns)
  constraint_exps = Expr[constraint_expressions(body)...]
  # constraint_vars = union(map((exp -> [get_p_expressions((x -> is_firstorder(x,preds)), exp)...]), constraint_exps)...)
  constraint_vars = union(Symbol[], map((exp -> [get_p_expressions((x -> is_firstorder(x,preds)), exp)...]), constraint_exps)...)
  #body_vars = Set{Symbol}(union(constraint_vars, map(just_variables, source_varlocs)...))
  body_vars = Set{Any}(union(constraint_vars, map((pattern -> get_variable_groups(pattern, preds)), patterns)...))
  rulespace_tuple = rulespace_var_order(head, body_vars, preds)
  # rulespace_sig = expression_sig(pred_nums, rulespace_tuple)
  # rulespace_domain = Domain(rulespace_sig)
  rulespace_domain = expression_dom(pred_nums, rulespace_tuple)
  rulespace_varlocs::Set{Tuple{Symbol, VarLoc}} = get_variable_locs(rulespace_tuple, Int[], preds)
  sourcemaps = Vector{Dict{VarLoc,VarLoc}}(map((source_vl -> compute_sourcemap(rulespace_varlocs, source_vl)), source_varlocs))
  comfn = compilecombofun(patterns, body, rulespace_tuple, rulespace_domain, preds, pred_nums)
  mergefn = find_summary_comb(sumfn)
  r = Rule(source_domains,
           sourcemaps,
           target_domain,
           rulespace_domain,
           comfn,
           sumfn,
           mergefn,
           overlapping_rules,
           rule_num,
           overlapping_types)
  return r
end

# Turns the keywords for the summary operators into the actual functions.

function find_summary_op(s::Symbol)
  if s == Symbol("@sum")
    return integrate
  elseif s == Symbol("@prod")
    return pintegrate
  elseif s == Symbol("@max")
    return maxintegrate
  elseif s == Symbol("@min")
    return mintegrate
  elseif s == Symbol("@just") # this keyword can be used to explicitly indicate no summary function
    return error_summary
  else
    return eval(s) # allows arbitrary functions to be used
  end
end

# Finds the combination function which should be used to merge results of rules given their summary functions.

function find_summary_comb(f::Function)
  if f == integrate
    return +
  elseif f == pintegrate
    return *
  elseif f == maxintegrate
    return max
  elseif f == mintegrate
    return min
  elseif f == error_summary
    #error("@just rules cannot overlap any other rules")
    return error_combination
  else
    return error("find_summary_comb doesn't know what combination op is analogous to summary op $f")
  end
end

function find_summary_id(f::Function)
  if f == integrate
    return 0
  elseif f == pintegrate
    return 1
  elseif f == maxintegrate
    return -Inf
  elseif f == mintegrate
    return Inf
  elseif f == error_summary
    return 0
  else
    return error("find_summary_id doesn't know what value acts as the identity element for summary op $f")
  end
end

function find_comb_id(f::Function)
  if f == +
    return 0
  elseif f == *
    return 1
  elseif f == max
    return -Inf
  elseif f == min
    return Inf
  elseif f == error_combination
    return 0
  else
    return error("find_comb_id doesn't know about $f")
  end
end

const merge_type_order = [error_combination,+,*,min,max]

# extract only the relevant lines for @rules compilation

function relevant_lines(code::Any)
  #print(code)
  #println()
  #dump(code)
  if typeof(code) == Expr
    if code.head == :block
      return vcat([relevant_lines(x) for x in code.args]...)
    elseif code.head == :(=) && typeof(code.args[2]) == Expr && code.args[2].head == :block && typeof(code.args[2].args[2]) == Expr && code.args[2].args[2].head == :macrocall
      line = code
      if typeof(code.args[2].args[1]) != Expr
        line = Expr(:(=), code.args[1], Expr(:block, code.args[2].args[2]))
      end
      if typeof(line.args[2].args[1].args[2]) != Expr
        line = Expr(:(=), line.args[1], Expr(:block, Expr(:macrocall, line.args[2].args[1].args[1], line.args[2].args[1].args[3])))
      end
      return [line]
    elseif code.head == :(=)
      return [code]
    elseif code.head == :line
      return Expr[]
    elseif code.head == :using
      return eval(code.args[1].args[1]).lines
    else # not a block or an equation; don't know what to do
      throw("@rules didn't know what to do with the following, found in the code it was handed: $code")
    end
  elseif typeof(code) == LineNumberNode
    return Expr[] # empty set
  else # not an Expr or a LineNumberNode. I don't know how to deal with it.
    throw("@rules didn't know what to do with the following, found in the code it was handed: $code")
  end
end

# named_predicates extracts (name, number) pairs for predicates (number chosen
# fairly arbitrarily) from the (relevant) lines. Avoids already_taken and below.

function named_predicate_nums(lines::Vector{Expr}, already_taken::Int)
  pairs = Set{Tuple{Symbol, Int}}()
  unique_symbols = Set{Symbol}()
  n = already_taken
  for line in lines
    possible_pred = line.args[1].args[1]
    if typeof(possible_pred) == Expr
      if possible_pred.head == :curly
        possible_pred = possible_pred.args[1]
      else
        throw("Invalid line syntax: $line")
      end
    end
    if !(is_predicate_var(possible_pred) || is_tuple_var(possible_pred)) && !(in(possible_pred, unique_symbols)) # if it's a plain predicate and it's not already seen
      push!(unique_symbols, possible_pred) # add it to what's been seen
      n = n+1
      push!(pairs, (possible_pred, n)) # give it a number
    end
  end
  return pairs
end

# rule_predicate_nums assigns names and numbers to the

#function rule_predicate_nums(lines::Vector{Expr}, starting_num)

function pred_name_map(pairs::Set{Tuple{Symbol, Int}})
  return Dict{Int, Symbol}([p[2]=>p[1] for p in pairs])
end

function pred_num_map(pairs::Set{Tuple{Symbol, Int}})
  return Dict{Symbol, Int}([p[1]=>p[2] for p in pairs])
end

# 'rules' constructs a RuleSystem. The format looks like:
#  rs = @rules begin
#    f(x,y) = @sum g(x,y,z)
#    g(x,y,z) = @prod f(x,y)*f(y,z)
#  end

macro rules(code::Any)
  lines = relevant_lines(code)
#  # Extract the predicate names, and give them numbers starting one greater than the number of lines.
#  extracted_predicates = named_predicate_nums(lines, length(lines))
#  # create special predicates which serve as output buffers, so that we can combine the output of rules pointing to the same predicates. These are given numbers based on lines.
#  rule_preds = Set{Tuple{Symbol,Int}}([(gensym(),l) for l in 1:length(lines)])
#  extracted_predicates = union(extracted_predicates, rule_preds)
  extracted_predicates = named_predicate_nums(lines, 0)
  pred_names = pred_name_map(extracted_predicates)
  pred_nums = pred_num_map(extracted_predicates)
  preds = Set{Symbol}(keys(pred_nums))
  rules = Array{Rule,1}(undef, length(lines))
#  summary_op_clusters = Dict{Function, Set{Int}}()
#  # create modified rules which point to the output buffers
  for i in 1:length(lines)
    line = lines[i]
    summary_op = find_summary_op(line.args[2].args[1].args[1])
    #summary_op_clusters[summary_op] = union(get(summary_op_clusters, summary_op, Set{Int}()), Set{Int}(i))
    head = line.args[1]
    #modified_head = Expr(:call, pred_names[i], [literal_head.args[1], Expr(:tuple, literal_head.args[2:length(literal_head.args)]...)]...) # re-write x(a,b,c) to rulesym(x,(a,b,c))
    body = line.args[2].args[1].args[2]
    rules[i] = make_rule(head,
                         body,
                         summary_op,
                         preds,
                         pred_nums,
                         Int[],
                         i,
                         Function[])
  end
  # run through the list of rules again to find the overlapping rules.
  for r in 1:length(lines)
    #rules[r].overlapping_types = Function[rules[r].merge]
    for other_rule in 1:length(lines)
      if !(r == other_rule) && !empty_domain(intersection(rules[r].target, rules[other_rule].target))
        if rules[r].merge != rules[other_rule].merge
          @warn "Rules $(r) and $(other_rule) have conflicting summary types, but overlapping target domains. This may produce unexpected results."
          # possibly modify this to avoid redundant entries
          rules[r].overlapping_types = [rules[other_rule].merge, rules[r].overlapping_types...]
        else
          rules[r].overlapping_rules = [other_rule, rules[r].overlapping_rules...]
        end
      end
    end
  end
  wm = MemTree(dom((:[1:$(largest_p)], :t)), MemLeaf(None()))
  output_buffers = Array{MemTree,1}(undef,length(lines))
  #for i in 1:length(lines)
  #  value = find_summary_id(rules[i].summarize)
  #  output_buffers[i] = MemTree(dom((:[1,$(length(pred_names))], :t)), MemLeaf(LeafNode(value)))
  #end
#  for i in 1:length(lines)
#    value = find_summary_id(rules[i].summarize)
#    wm = insert(MemTree(dom((:[$i,$i], :t)), MemLeaf(LeafNode(value))), wm)
#  end
#  # merge the results in the output buffers back into regular working memory
#  merge_rules = Vector{Rule}(length(keys(summary_op_clusters)))
#  place = 1
#  for op in keys(summary_op_clusters)
#    numbers = summary_op_clusters[op]
#    comb = find_summary_comb(op)
#    id = find_summary_id(op)
#    merge_rules[place] = make_rule(Expr(:call, :Pred, Expr(:..., :_args_)), # head
#                                        Expr(:call, comb, vcat(id,[:(($(pred_names[n]))(Pred,_args_)) for n in numbers])...), # body
#                                        error_summary,
#                                        preds,
#                                        pred_nums)
#    place = place+1
#  end
#  plain_rules = rules
#  rules = vcat(rules, merge_rules)
  patterns = Vector{Tuple{Domain, Rule, Int}}[]
  pqs = Vector{PQ}(UndefInitializer(), length(rules))
  # set up the pattern library for matching
  for rule in rules
    #for i in collect([1:length(rule.sources)])
    for i in 1:length(rule.sources)
      patterns = vcat(patterns, [(rule.sources[i], rule, i)])
    end
  end
  rs = RuleSystem(rules, patterns, output_buffers, wm, pqs, pred_names, pred_nums, lines, Dict{Function, MemTree}(), wm)
  new_init!(rs)
#  # run each rule once to initialize the rest of working memory, and seed the first changes
#  for rule in plain_rules
#    push_wm_alteration!(rs, computeresult(rs, Change(rule, rule.rulespace)))
#  end
#  for rule in merge_rules
#    push_wm_alteration!(rs, computeresult(rs, Change(rule, rule.rulespace)))
#  end
  # push an initial change to the pq for each rule
  #for rule in rules
  #  enqueue!(rs.pq, Change(rule, rule.rulespace), -rule.rule_num)
  #end
  return rs
end

function old_init!(rs::RuleSystem)
  rs.last_fired = blankchange
  # set rule counts to zero
  for r in rs.rules
    r.fire_count = 0
    r.useless_fire_count = 0
  end
  # initialize priority queues
  for i=1:length(rs.rules)
    rs.pqs[i] = PQ(Change)
    rule = rs.rules[i]
    enqueue!(rs.pqs[i], Change(rule, rule.rulespace), -i + 200)
  end
  #rs.pq = PQ(Change)
  #for rule in rs.rules
  #  enqueue!(rs.pqs, Change(rule, rule.rulespace), -rule.rule_num + 200)
  #end
  # initialize memory
  rs.wm = MemTree(dom((:[1:largest_p], :t)), MemLeaf(None()))
  # Initialize output buffers with identity values, and put those initial
  # outputs into wm. In cases of overlap, we need to prioritize according to
  # merge type.
  rs.output_buffers = Array{MemTree,1}(undef,length(rs.rules))
  rs.merge_output_buffers = Dict{Function, MemTree}()
  for merge_op in reverse(merge_type_order) # go thru merge types in reverse order, to prioritize initial values of earlier types
    for i in 1:length(rs.rules)
      if merge_op == find_summary_comb(rs.rules[i].summarize) # if merge type is right
        val = find_summary_id(rs.rules[i].summarize)
        domain = rs.rules[i].target
        # rs.output_buffers[i] = MemTree(dom((:[1,$(length(rs.pred_names))], :t)), MemLeaf(LeafNode(value)))
        rs.output_buffers[i] = MemTree(domain, MemLeaf(LeafNode(val)))
        insert!(rs.output_buffers[i], rs) # also put the result into wm, enforcing the assumption that anything in output buffers is already represented within wm
      end
    end
    # initialize the merge type output buffers with identity values, as well
    val = find_comb_id(merge_op)
    rs.merge_output_buffers[merge_op] = MemTree(dom((:[1:largest_p], :t)), MemLeaf(LeafNode(val)))
  end
  # the current initialized values become the permanent "default" values used in output merging
  rs.local_defaults = rs.wm
end


function rule_is_firstorder(rule::Rule)
  return rule.target.sig.spec[1].ranges[1].start == rule.target.sig.spec[1].ranges[1].stop
end

function new_init!(rs::RuleSystem)
  rs.step = 0
  rs.last_fired = blankchange
  # set rule counts to zero
  for r in rs.rules
    r.fire_count = 0
    r.useless_fire_count = 0
  end
  # initialize priority queues
  for i=1:length(rs.rules)
    rs.pqs[i] = PQ(Change)
    rule = rs.rules[i]
    enqueue!(rs.pqs[i], Change(rule, rule.rulespace), -i + 200)
  end
  #rs.pq = PQ(Change)
  #for rule in rs.rules
  #  enqueue!(rs.pqs, Change(rule, rule.rulespace), -rule.rule_num + 200)
  #end
  # initialize memory
  rs.wm = MemTree(dom((:[1:largest_p], :t)), MemLeaf(None()))
  # Initialize output buffers with identity values, and put those initial
  # outputs into wm. In cases of overlap, we need to prioritize according to
  # merge type.
  rs.output_buffers = Array{MemTree,1}(undef,length(rs.rules))
  rs.merge_output_buffers = Dict{Function, MemTree}()
  # First go thru second order rules, to prioritize firstorder rules in init
  for merge_op in reverse(merge_type_order) # go thru merge types in reverse order, to prioritize initial values of earlier types
    for i in 1:length(rs.rules)
      if merge_op == find_summary_comb(rs.rules[i].summarize) # if merge type is right
        if !rule_is_firstorder(rs.rules[i])
          val = find_summary_id(rs.rules[i].summarize)
          domain = rs.rules[i].target
          # rs.output_buffers[i] = MemTree(dom((:[1,$(length(rs.pred_names))], :t)), MemLeaf(LeafNode(value)))
          rs.output_buffers[i] = MemTree(domain, MemLeaf(LeafNode(val)))
          insert!(rs.output_buffers[i], rs) # also put the result into wm, enforcing the assumption that anything in output buffers is already represented within wm
        end
      end
    end
    # initialize the merge type output buffers with identity values, as well
    val = find_comb_id(merge_op)
    rs.merge_output_buffers[merge_op] = MemTree(dom((:[1:largest_p], :t)), MemLeaf(LeafNode(val)))
  end
  # Now do the same thing for first order rules, so their implied initial values have prioty.
  for merge_op in reverse(merge_type_order) # go thru merge types in reverse order, to prioritize initial values of earlier types
    for i in 1:length(rs.rules)
      if merge_op == find_summary_comb(rs.rules[i].summarize) # if merge type is right
        if rule_is_firstorder(rs.rules[i])
          val = find_summary_id(rs.rules[i].summarize)
          domain = rs.rules[i].target
          # rs.output_buffers[i] = MemTree(dom((:[1,$(length(rs.pred_names))], :t)), MemLeaf(LeafNode(value)))
          rs.output_buffers[i] = MemTree(domain, MemLeaf(LeafNode(val)))
          insert!(rs.output_buffers[i], rs) # also put the result into wm, enforcing the assumption that anything in output buffers is already represented within wm
        end
      end
    end
    # initialize the merge type output buffers with identity values, as well
    val = find_comb_id(merge_op)
    rs.merge_output_buffers[merge_op] = MemTree(dom((:[1:largest_p], :t)), MemLeaf(LeafNode(val)))
  end
  # the current initialized values become the permanent "default" values used in output merging
  rs.local_defaults = rs.wm
end

# ===== Solving =====

# MemTrees are immutable, but the WM is mutable; to insert, we swap out the old
# tree for the new tree that's got the value inserted.

function insert!(value::MemTree, rs::RuleSystem)
  #rs.wm = insert(value, trim(rs.wm)) # TODO trim after insert rather than before, probably? Or, _don't_ trim all of WM?
  # Insertion already trims its output! So WM should be trimmed all the time. So
  # there should be no point to trimming here.
  rs.wm = insert(value, rs.wm)
  # But, TODO: I really shouldn't trim the whole WM all the time like this! I
  # should come up with a better way to insert things into WM. HOWEVER, I did
  # previously have special-case insertion code (not too clever, mind), and it
  # was TERRIBLY complex, to the point where I replated it with the take_leff
  # combination fn purely to avoid the hypothetical horror of debugging it if
  # anything ever did go wrong with it.
end

# The maps which put things into rule space when interpreted in the
# forward direction can be reversed to help generate the queries we need to
# extract relevant information from the sources. So, I need a map-reversing
# function.

function reversemap(m::Dict{VarLoc, VarLoc})
  return Dict(map((pair -> pair[2]=>pair[1]), [m...]))
end

# Given an "active" region in rulespace (based on a change), a rule, and a
# source number, find the domain to query in that source.

function querydomain(active::Domain, r::Rule, sourcenum::Int)
  sourcemap = r.sourcemaps[sourcenum] # get the map which puts the given source into rulespace
  rmap = Dict{VarLoc,VarLoc}(reversemap(sourcemap)) # reverse it so that we are mapping things from rulespace to that source
  target_sig = r.sources[sourcenum].sig # domain reordering needs to be handed the signature being mapped onto
  return reorder(rmap, target_sig, active) # Now reorder and return.
end

# Given an active region (we don't care where it's from, it's already in the
# rule space), query the needed regions in sources and compute the result.
# Query the overlapping rule output buffers

function computeresult(rs::RuleSystem, r::Rule, active::Domain)
  # finds the relevant query domains and performs the queries.
  queries = [query(rs.wm, querydomain(active, r, i)) for i = 1:length(r.sources)]
  # Now the results need to be mapped into rule-space.
  mapped = [reorder(r.sourcemaps[i], r.rulespace.sig, queries[i]) for i = 1:length(r.sources)]
  # Apply the combination function from the rule.
  combination = trim((r.combine)(mapped...)) #TODO Trimming here ensures that the result is trimmed at least once, and that it is trimmed before we integrate. However, it isn't clearly the best strategy -- for example, integration could do more trimming internally.
  # Summarize out variables not in the target space.
  # Assumption: rulespace and target signatures must be in sig((:p, args)) format where args is a specifiedTSig.
  for i = length(r.rulespace.sig.spec):-1:3 # starting with the last argument in rulespace, integrate out the ith element counting down, until you've got the target space.
    combination = trim((r.summarize)(combination, Int[i])) # integrate the ith item in the args
  end
  return combination
end

# Calls the above based on a Change. Returns the result of the rule calculation.

function computeresult(rs::RuleSystem, change::Change)
  return computeresult(rs, change.rule, change.domain)
end

# We must also merge the result with the output of overlapping rules.

function merge_same_type(rs::RuleSystem, results::MemTree, r::Rule)
  n = length(r.overlapping_rules)
  merge_op = r.merge
  merge_id = find_comb_id(merge_op)
  default_tree = MemTree(results.domain, MemLeaf(LeafNode(merge_id)))
  for i in r.overlapping_rules
    overlap = query(rs.output_buffers[i], results.domain)
    augmented = insert(overlap, default_tree) # should I be trimming here?
    results = merge_op(augmented, results)
  end
  return results
end

function generalize_sig(s::Signature)
  t = typeof(s)
  if t == SpecifiedTSig
    return UnspecifiedTSig()
  elseif t == UnspecifiedTSig
    return s
  elseif t == VSig
    return s
  elseif t == USig
    return USig(1:largest_p)
  elseif t == ESig
    return s
  elseif t == PSig
    return PSig(1:largest_p)
  end
end

function find_active_region(rule::Rule, sourcenum::Int, common_part::Domain)
  rulespace_subset = reorder(rule.sourcemaps[sourcenum], rule.rulespace.sig, common_part)
  target_sig = SpecifiedTSig(copy(rulespace_subset.sig.spec))
  l = length(target_sig.spec)
  for i in l:-1:3
    rulespace_subset = integrate(rulespace_subset, [i])
  end
  target_dom = Domain(target_sig, rulespace_subset.reg, rulespace_subset.map)
  for i in 3:l
    target_dom.sig.spec[i] = generalize_sig(target_dom.sig.spec[i])
  end
  return target_dom
end

# Finds the rules which have to be fired based on a wm modification.

function firetest(rs::RuleSystem, tree::MemTree)
  changes = Change[] # initialize list of changes
  for (sourcedomain, rule, sourcenum) in rs.patterns
    common_part = intersection(sourcedomain, tree.domain)
    if !empty_domain(common_part) # if there's a nonzero intersection
      current = query(rs.wm, common_part)
      new = trim(MemTree(common_part, tree.root))
      if !epsilonequal(current, new) # if the relevant area of WM is being changed
        # add to changes
        #active = reorder(rule.sourcemaps[sourcenum], rule.rulespace.sig, common_part) # compute the active region in rulespace
        active = find_active_region(rule, sourcenum, common_part)
        changes = vcat(changes, [Change(rule, active)])
      end
    end
  end
  return changes
end

# Given a working memory alteration (generally the output of computeresult),
# make changes to working memory, and push new changes to the queue reflecting
# this. Returns the list of changes.

function push_wm_alteration!(rs::RuleSystem, wm_alteration::MemTree, rule_just_fired::Int=0)
  changeset = firetest(rs, wm_alteration)
  for ch in changeset
    #rule_priority = -ch.rule.rule_num - step*10  # lower numbered rules get higher priority; more recent firings get lower priority
    # Change of plans: the rule prioritization should now closely mimic the
    # "just loop over the rules" strategy.
    #rule_fire_count = rs.rules[rule_just_fired].fire_count
    #rule_useless_count = rs.rules[rule_just_fired].useless_fire_count
    #rule_priority = -ch.rule.rule_num*5 -step/5 -rule_fire_count*10 -rule_useless_count*3
#    rule_priority = -ch.rule.rule_num -step/5 -rule_fire_count*10 -rule_useless_count*3
    #if ch.rule.rule_num <= rule_just_fired
    #  rule_priority += -25
    #end
    # Change of plans again -- I'm trying prioritizing recent messages
    rule_priority = rs.step
    enqueue!(rs.pqs[ch.rule.rule_num], ch, rule_priority)
  end
  insert!(wm_alteration, rs)
  return changeset
end


# sizes of queues for a rule system

function queue_sizes(rs::RuleSystem)
  return map(length, rs.pqs)
end


# Put partial result in output buffer, and merged result in WM.

function store_result!(rs::RuleSystem, rule::Rule, rule_output::MemTree, detailed=false)
  rule.fire_count += 1
  if !epsilonequal(rule_output, rs.output_buffers[rule.rule_num]) # if the result differs from the rule's existing outputs
    rs.output_buffers[rule.rule_num] = insert(rule_output, rs.output_buffers[rule.rule_num]) # update the output buffer
    type_matched_merge = merge_same_type(rs, rule_output, rule) # merge the result with those of overlapping rules
    rs.merge_output_buffers[rule.merge] = insert(type_matched_merge, rs.merge_output_buffers[rule.merge]) # put in merge output buffer
    # now we need to combine appropriately with the other merge output buffers
    if length(rule.overlapping_types) > 0 # if there is anything else to combine
      # find the right initial value
      wm_alteration = query(rs.local_defaults, type_matched_merge.domain)
      # combine with other merge types if there's an overlap
      for merge_op in merge_type_order
        if findfirst(isequal(merge_op), rule.overlapping_types) != nothing
          wm_alteration = merge_op(wm_alteration, rs.merge_output_buffers[merge_op])
        elseif merge_op == rule.merge
          if merge_op == error_combination
            wm_alteration = type_matched_merge
          else
            wm_alteration = merge_op(wm_alteration, type_matched_merge)
          end
        end
      end
    else # if there is nothing to combine
      wm_alteration = type_matched_merge # just take the results
    end
    changes = push_wm_alteration!(rs, wm_alteration, rule.rule_num) # push to WM (which also has the effect of adding appropriate changes to the priority queue)
    if detailed
      return Dict(
        :queue_sizes=>queue_sizes(rs),
        :calculated_rule=>rule.rule_num,
        :changed_wm=>true,
        :result_sig=>rule_output.domain.sig,
        :num_rules_effected=>length(changes),
        :output_buffers=>rs.output_buffers,
        :merge_output_buffers=>rs.merge_output_buffers,
        :wm=>rs.wm)
    else
      return Dict(
        :queue_sizes=>queue_sizes(rs),
        :calculated_rule=>rule.rule_num,
        :result_sig=>rule_output.domain.sig,
        :changed_wm=>true,
        :num_rules_effected=>length(changes))
    end
  else
    rule.useless_fire_count += 1
    if detailed
      return Dict(
        :queue_sizes=>queue_sizes(rs),
        :calculated_rule=>rule.rule_num,
        :changed_wm=>false,
        :result_sig=>rule_output.domain.sig,
        :num_rules_effected=>0,
        :output_buffers=>rs.output_buffers,
        :merge_output_buffers=>rs.merge_output_buffers,
        :wm=>rs.wm)
    else
      return Dict(
        :queue_sizes=>queue_sizes(rs),
        :calculated_rule=>rule.rule_num,
        :result_sig=>rule_output.domain.sig,
        :changed_wm=>false,
        :num_rules_effected=>0)
    end
  end
end

function find_next_to_fire(rs::RuleSystem)
  next_to_fire = mod(rs.last_fired.rule.rule_num, length(rs.rules)) + 1 # increment once
  for i = 1:(length(rs.rules)-1) # at most we want to loop back to the previous rule
    if rs.pqs[next_to_fire].size != 0 # but we want to break out as soon as we find something we can fire
      break
    end
    next_to_fire = mod(next_to_fire, length(rs.rules)) + 1
  end
  if rs.pqs[next_to_fire].size == 0 # if we couldn't find something nonempty
    return false
  else
    return next_to_fire
  end
end

# Given a rule system, takes a change off the queue (if any remain), computes
# the result of firing the rule in the change, checks whether it made any
# difference, and if so, changes working memory and adds changes to the queue.
# Returns information about what happened.

function step!(rs::RuleSystem, detailed=false)
  rs.step += 1
  next_to_fire = find_next_to_fire(rs)
  if next_to_fire != false
    change = dequeue!(rs.pqs[next_to_fire])
    result = computeresult(rs, change)
    rs.last_fired = change
    return store_result!(rs, change.rule, result, detailed)
  else
    if detailed
      return Dict(
        :queue_sizes=>length(rs.pq),
        :calculated_rule=>false,
        :change_mattered=>false,
        :result_sig=>rule_output.domain.sig,
        :num_rules_effected=>0,
        :output_buffers=>rs.output_buffers,
        :merge_output_buffers=>rs.merge_output_buffers,
        :wm=>rs.wm)
    else
      return Dict(
        :queue_sizes=>queue_sizes(rs),
        :calculated_rule=>false,
        :changed_wm=>false,
        :num_rules_effected=>0)
    end
  end
end


#=
  next_to_fire = rs.last_fired + 1
  if next_to_fire > length(rs.rules)
    next_to_fire = 1
  end
  if length(rs.pq) > 0
  change = dequeue!(rs.pqs[next_to_fire])
  result = computeresult(rs, change)
  return store_result!(rs, change.rule, result, step, detailed)



  if length(rs.pq) > 0
    if rs.last_fired == peek(rs.pq) && rs.last_fired_useful == false
      dequeue!(rs.pq)
    else
      change = dequeue!(rs.pq)
      result = computeresult(rs, change)
      return store_result!(rs, change.rule, result, step, detailed)
    end
  end
  if detailed
    return Dict(
      :queue_size=>length(rs.pq),
      :calculated_rule=>false,
      :change_mattered=>false,
      :num_rules_effected=>0,
      :wm=>rs.wm)
  else
    return Dict(:queue_size=>length(rs.pq), :calculated_rule=>false, :changed_wm=>false, :num_rules_effected=>0)
  end
end
=#


function run!(rs::RuleSystem, times::Int, detailed=false)
  history = Array{Any,1}(undef,times)
  for i in 1:times
    history[i] = step!(rs, detailed)
  end
  return history
end

# Variation for firing a specific rule (given by number)

function step_rule!(rs::RuleSystem, r::Int)
  rule = rs.rules[r]
  result = computeresult(rs, Change(rule, rule.rulespace))
  store_result!(rs, rule, result)
end

function history_diff(h1::Dict, h2::Dict)
  diffs = h2[:queue_sizes] - h1[:queue_sizes]
  return [1:length(diffs) diffs]
end

history_diff(h::Array, n::Number) = history_diff(h[n-1], h[n])

# A rulesystem-aware query function.
# TODO: write a predicate-aware version, so that I don't have to write predicate
# numbers when dealing with a specific rule system. Specifically, I would like
# my domain abbreviation syntax -- when used in rulesystem queries -- to know
# that, eg, :some_random_predicate translates to :[15,15] or whatever. This
# would not be a waste of time, to implement, as it would greatly speed up
# debugging.

function query(rs::RuleSystem, pred::Symbol)
  num = rs.pred_nums[pred]
  return query(rs.wm, sig((:[$(num):$(num)],:t)))
end

function query(rs::RuleSystem, d::Domain)
  return query(rs.wm, d)
end

function query(rs::RuleSystem, pred::Symbol, argdom::Any)
  num = rs.pred_nums[pred]
  return query(rs.wm, dom((:[$(num):$(num)],argdom)))
end

query(rs::RuleSystem, s::Signature) = query(rs.wm, s)













# :)
