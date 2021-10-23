#using Base.Test
include("rules.jl")

some_preds = Set([:a, :b, :c])

@assert  is_predicate(:a, some_preds)
@assert !is_predicate(:d, some_preds)
@assert  is_predicate_var(:Var)
@assert  is_predicate_var(:YES)
@assert  is_predicate_var(:NO0)
@assert !is_predicate_var(:_c_)
@assert !is_predicate_var(:vVar)
@assert !is_predicate_var(:vaR)
@assert !is_predicate_var(:!)
@assert !is_predicate_var(:())
@assert !is_predicate_var(:(1+1))
@assert  is_tuple_var(:_tuple_)
@assert  is_tuple_var(:__)
@assert  is_tuple_var(:_)
@assert !is_tuple_var(:())
@assert !is_tuple_var(:c)
@assert !is_firstorder(:c, some_preds)
@assert  is_firstorder(:d, some_preds)
@assert  is_firstorder(:c_, some_preds)
@assert !is_firstorder(:_c, some_preds)
@assert !is_firstorder(:c!, some_preds)
@assert  is_uvar(:c!)
@assert !is_firstorder(:(), some_preds)
@assert !is_firstorder(:(a(b)), some_preds)
@assert !is_firstorder(:YES, some_preds)
@assert !is_firstorder(:_benedict_, some_preds)
@assert !is_constraint(:[])
# @assert !is_constraint(:[2*a+3*b])
@assert  is_constraint(:[2*x+3+g==1])
@assert  is_constraint(:[[P == pred1]])
@assert  is_secondorder_constraint(:[[P == a]])
@assert  is_secondorder_constraint(:[[_t_ == (x,y)]])
@assert !is_secondorder_constraint(:[P == a])
@assert !is_secondorder_constraint(:[x + 1 == y])
@assert  secondorder_constraint_var(:[[P == a]]) == :P
@assert  secondorder_constraint_var((:[[_t_ == (x,y)]])) == :_t_
@assert  secondorder_constraint_instance(:[[_t_ == (x,y)]]) == :(x,y)
@assert  secondorder_constraint_instance(:[[P == a]]) == :a
@assert  is_pred_constraint(:[[P == a]])
@assert !is_pred_constraint(:[P == a])
@assert !is_pred_constraint(:[[_t_ == (x,y)]])
@assert  is_tuple_constraint(:[[_t_ == (x,y)]])
@assert !is_tuple_constraint(:[[P == a]])
@assert !is_tuple_constraint(:[_t_ == (x,y)])
@assert  is_predicate_pattern(some_preds, :(a(b)))
@assert  is_predicate_pattern(some_preds, :(b(x,y,32,c(24))))
@assert !is_predicate_pattern(some_preds, :x)
@assert !is_predicate_pattern(some_preds, :b)
@assert !is_predicate_pattern(some_preds, :(f(x,y)))
@assert  is_predicate_pattern(some_preds, :(a()))
@assert  is_predicate_pattern(some_preds, :(a{x!,1:2}(x,y,z)))
@assert !is_predicate_pattern(some_preds, :(x{x!,1:2}(x,y,z)))
@assert  is_predicate_pattern(some_preds, :(a{}()))

some_expr = :(a(x) = b(y) + [x==c] + c(z))
is_some_pred_pattern(e) = is_predicate_pattern(some_preds, e)
@assert get_p_expressions((x -> is_firstorder(x, some_preds)), some_expr) == Set([:x, :y, :z])
@assert get_p_expressions(is_constraint, some_expr) == Set([:[x==c]])
@assert pattern_expressions(some_preds, some_expr) == Set([:(a(x)), :(b(y)), :(c(z))])
@assert constraint_expressions(some_expr) == Set([:[x==c]])

some_pred_nums = Dict(:a=>1, :b=>2, :c=>3)
@assert pattern_domain(some_pred_nums, :(a(x))).sig == SpecifiedTSig([PSig(1:1), SpecifiedTSig([VSig()])])
@assert pattern_domain(some_pred_nums, :(a(x))).reg == boundless_reg(1)
@assert pattern_domain(some_pred_nums, :(a(x,y))).sig == sig((:[1:1], (:v,:v)))
@assert pattern_domain(some_pred_nums, :(a(x,y))).reg == boundless_reg(2)
@assert pattern_domain(some_pred_nums, :(a(x,y,_r_))).sig == sig((:[1:1], (:v,:v,:t)))
@assert pattern_domain(some_pred_nums, :(a(x,(r,u),_r_))).sig == sig((:[1:1], (:v,(:v,:v),:t)))
@assert pattern_domain(some_pred_nums, :(a{x!}(y))).sig == SpecifiedTSig([PSig([1:1, 1:largest_p]), SpecifiedTSig([VSig()])])

@assert expression_sig(some_pred_nums, :(a,(x,))) == SpecifiedTSig([PSig(1,1), SpecifiedTSig([VSig()])])
@assert expression_sig(some_pred_nums, :(a,(x,y))) == sig((:[1:1], (:v,:v)))
@assert expression_sig(some_pred_nums, :(a,(x,y,_r_))) == sig((:[1:1], (:v,:v,:t)))
@assert expression_sig(some_pred_nums, :(a,(x,(r,u),_r_))) == sig((:[1:1], (:v,(:v,:v),:t)))

@assert get_variable_locs(:(a(x,(y,z))), some_preds) == Set([(:x,[2,1]),(:y,[2,2,1]),(:z,[2,2,2])])
@assert get_variable_locs(:(A(x,(y,z))), some_preds) == Set([(:A,[1,1]),(:x,[2,1]),(:y,[2,2,1]),(:z,[2,2,2])])
@assert get_variable_locs(:(a(_t_)), some_preds) == Set([(:_t_, [2,1])])
@assert get_variable_locs(:(A(_t_)), some_preds) == Set([(:_t_, [2,1]), (:A, [1,1])])
@assert get_variable_locs(:(a(x,_t_)), some_preds) == Set([(:_t_, [2,2]), (:x, [2,1])])
@assert get_variable_locs(:(a(_t_...)), some_preds) == Set([(:_t_, [2])])
@assert get_variable_locs(:(a{u!,v!}(x,_t_)), some_preds) == Set([(:_t_, [2,2]), (:x, [2,1]), (:u!, [1,2]), (:v!, [1,3])])
@assert get_variable_locs(:(A{u!,v!}(x,_t_)), some_preds) == Set([(:_t_, [2,2]), (:x, [2,1]), (:u!, [1,2]), (:v!, [1,3]), (:A,[1,1])])

@assert get_variable_locs(:(a,(x,(y,z))), Int[], some_preds) == Set([(:x,[2,1]),(:y,[2,2,1]),(:z,[2,2,2])])
@assert get_variable_locs(:(A,(x,(y,z))), Int[], some_preds) == Set([(:A,[1,1]),(:x,[2,1]),(:y,[2,2,1]),(:z,[2,2,2])])
@assert get_variable_locs(:(a,(_t_,)), Int[], some_preds) == Set([(:_t_, [2,1])])
@assert get_variable_locs(:(A,(_t_,)), Int[], some_preds) == Set([(:_t_, [2,1]), (:A, [1,1])])
@assert get_variable_locs(:(a,(x,_t_)), Int[], some_preds) == Set([(:_t_, [2,2]), (:x, [2,1])])

@assert just_variables(get_variable_locs(:(a(x,(y,z))), some_preds)) == Set([:x,:y,:z])
@assert just_variables(get_variable_locs(:(A(x,(y,z))), some_preds)) == Set([:A,:x,:y,:z])

@assert remove_target_symbols(Set{Any}((:a, :b, :x, :y, :(f{a, b}), :(a{b}), :(f{x,y}), :(f{x, a}))), some_preds) == Set{Any}((:x, :y, :(f{}), :(f{x,y}), :(f{x})))

@assert rulespace_var_order(:(a(x,y)), Set{Any}([:x,:z]), some_preds) == :(a,(x,y),z)
@assert rulespace_var_order(:(a(x,(r,u),_r_)), Set{Any}([:x,:z]), some_preds) == :(a,(x,(r,u),_r_),z)
@assert rulespace_var_order(:(a(x,(r,u),_r_)), Set{Any}([:x]), some_preds) == :(a,(x,(r,u),_r_))
@assert rulespace_var_order(:(a(_t_)), Set{Any}([:x]), some_preds) == :(a,(_t_,),x)
@assert rulespace_var_order(:(a(_t_...)), Set{Any}([:x]), some_preds) == :(a,_t_,x)
@assert rulespace_var_order(:(a(_t_)), Set{Any}([]), some_preds) == :(a,(_t_,))
@assert rulespace_var_order(:(a(_t_...)), Set{Any}([]), some_preds) == :(a,_t_)
@assert rulespace_var_order(:(a{u!,v!}(x,y)), Set{Any}([:x,:z]), some_preds) == :(a{u!,v!},(x,y),z)

compute_sourcemap(get_variable_locs(:(a(x,(y,z))), some_preds), get_variable_locs(:(c(y,x)), some_preds))

@assert expressionreplace([:a],[:b],:a) == :b
@assert expressionreplace([:a,:b,:c],[:x,:y,:z],:(a(b,(c,d),(x,y)))) == :(x(y,(z,d),(x,y)))
@assert expressionreplace([:a,:(1,2),:c],[:x,:y,:(a,b)],:(a((1,2),(c,d),(x,y)))) == :(x(y,((a,b),d),(x,y)))

@assert convert_linear_expression(:(3+x+2*y), Dict(:x=>1,:y=>2)) == [1.0,2.0,3.0]
@assert convert_linear_expression(:(3-x-2*y), Dict(:x=>1,:y=>2)) == [-1.0,-2.0,3.0]
@assert convert_linear_expression(:(3-(x-2*y)), Dict(:x=>1,:y=>2)) == [-1.0,2.0,3.0]
@assert convert_linear_expression(:x, Dict(:x=>1,:y=>2)) == [1.0,0.0,0.0]
@assert convert_linear_expression(:(1), Dict(:x=>1,:y=>2)) == [0.0,0.0,1.0]

@assert parse_linear_equation(:(a+2*b+c-b+b+(-3*c+4*d+5*c)), :(5), Dict(:a=>1,:b=>2,:c=>3,:d=>4)) == [1.0,2.0,3.0,4.0,5.0]
@assert parse_linear_equation(:(a+2*b+c-b+b+(-3*c+4*d+5*c)+5), :(a+2*b+c-b+b+(-3*c+4*d+5*c)+5), Dict(:a=>1,:b=>2,:c=>3,:d=>4)) == [0.0,0.0,0.0,0.0,0.0]
@assert parse_linear_equation(:(a+2*b+c-b+b+(-3*c+4*d+5*c)-5), :(a+2*b+c-b+b+(-3*c+4*d+5*c)+5), Dict(:a=>1,:b=>2,:c=>3,:d=>4)) == [0.0,0.0,0.0,0.0,10.0]
@assert parse_linear_equation(:(a+2*b+c+b+b+(-3*c+4*d+5*c)+5), :(a+2*b+c-b+b+(-3*c+4*d+5*c)+5), Dict(:a=>1,:b=>2,:c=>3,:d=>4)) == [0.0,2.0,0.0,0.0,0.0]

preds_1 = Set([:p,:x,:y])
pred_nums_1 = Dict(:p=>1, :x=>2, :y=>3)
rulespace_pattern_1 = :(p,(a,b,c,d,e))
rulespace_domain_1 = Domain(expression_sig(pred_nums_1, rulespace_pattern_1))
csts1 = constraints_unpack(:([a+2.0*b+c-b+b+(-3.0*c+4.0*d+5.0*c)==5.0]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
@assert csts1 == trim(csts1) # tests whether anything was put into an invalid region of the tree
csts1a = constraints_unpack(:([a+2.0*b+4.0*d+3.0*c==5.0]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
@assert csts1 == csts1a
csts1b = constraints_unpack(:([a+2.0*b+4.0*d==5.0-3*c]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
@assert csts1b == csts1
csts1c = constraints_unpack(:([a+2.0*b+4.0*d+3.0*c>=5.0]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts1d = constraints_unpack(:([a+2.0*b+4.0*d+3.0*c<=5.0]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts1e = csts1c * csts1d * Hyper(1.0,1)
@assert epsilonequal(csts1, csts1e)
v_1 = standard_varnums(rulespace_domain_1, rulespace_pattern_1, preds_1)
varmap_1 = standard_varmap(rulespace_domain_1.sig)
csts2 = constraint_unpack(:(a+2.0*b+c-b+b+(-3.0*c+4.0*d+5.0*c)), :(5.0), :(==), v_1, varmap_1, rulespace_domain_1)
@assert epsilonequal(csts1, csts2)
csts3 = constraints_unpack(:([a==5]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts4 = constraints_unpack(:([5==a]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
#csts5 = constraints_unpack(:([5==a==5]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts6 = constraints_unpack(:([5>=a==5]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts7 = constraints_unpack(:([5<=a<=5]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts7a = csts7 * Hyper(1.0,1)
csts8 = constraints_unpack(:([5!=a]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
@assert epsilonequal(csts3, csts3)
@assert epsilonequal(csts3, csts4)
#@assert epsilonequal(csts3, csts5)
@assert epsilonequal(csts3, csts6)
@assert !epsilonequal(csts3, csts7)
@assert epsilonequal(csts3, csts7a)
@assert epsilonequal(csts4, csts4)
#@assert epsilonequal(csts4, csts5)
@assert epsilonequal(csts4, csts6)
@assert !epsilonequal(csts4, csts7)
@assert epsilonequal(csts4, csts7a)
#@assert epsilonequal(csts5, csts5)
#@assert epsilonequal(csts5, csts6)
#@assert !epsilonequal(csts5, csts7)
#@assert epsilonequal(csts5, csts7a)
@assert epsilonequal(csts6, csts6)
@assert !epsilonequal(csts6, csts7)
@assert epsilonequal(csts7, csts7)
@assert !epsilonequal(csts7, csts8)
@assert epsilonequal(csts8, 1.0-(csts3/Hyper(1.0,1)))
csts8 = constraints_unpack(:([a<5]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts8a = constraints_unpack(:([a>5]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts9 = constraints_unpack(:([-a>-5]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts10 = constraints_unpack(:([5>a]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts11 = constraints_unpack(:([-5<-a]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts12 = constraints_unpack(:([a>=5]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts13 = constraints_unpack(:([-a<=-5]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts14 = constraints_unpack(:([5<=a]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts15 = constraints_unpack(:([-5>=-a]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
@assert epsilonequal(csts8, mt(rulespace_domain_1, ml(SplitNode(LinSplit([1.0,0.0,0.0,0.0,0.0],5.0), LeafNode(1.0), LeafNode(0.0)))))
@assert epsilonequal(csts8a, mt(rulespace_domain_1, ml(SplitNode(LinSplit([-1.0,0.0,0.0,0.0,0.0],-5.0), LeafNode(1.0), LeafNode(0.0)))))
@assert epsilonequal(csts12, mt(rulespace_domain_1, ml(SplitNode(LinSplit([1.0,0.0,0.0,0.0,0.0],5.0), LeafNode(0.0), LeafNode(1.0)))))
@assert !epsilonequal(csts8a, mt(rulespace_domain_1, ml(SplitNode(LinSplit([1.0,0.0,0.0,0.0,0.0],5.0), LeafNode(0.0), LeafNode(1.0)))))
@assert !epsilonequal(csts12, mt(rulespace_domain_1, ml(SplitNode(LinSplit([-1.0,0.0,0.0,0.0,0.0],-5.0), LeafNode(1.0), LeafNode(0.0)))))
@assert epsilonequal(csts8, csts8)
@assert epsilonequal(csts8, csts9)
@assert epsilonequal(csts8, csts10)
@assert epsilonequal(csts8, csts11)
@assert !epsilonequal(csts8, csts12)
@assert epsilonequal(csts8, 1-csts12)
@assert !epsilonequal(csts8, csts13)
@assert !epsilonequal(csts8, csts14)
@assert !epsilonequal(csts8, csts15)
@assert epsilonequal(csts9, csts9)
@assert epsilonequal(csts9, csts10)
@assert epsilonequal(csts9, csts11)
@assert !epsilonequal(csts9, csts12)
@assert !epsilonequal(csts9, csts13)
@assert !epsilonequal(csts9, csts14)
@assert !epsilonequal(csts9, csts15)
@assert epsilonequal(csts10, csts10)
@assert epsilonequal(csts10, csts11)
@assert !epsilonequal(csts10, csts12)
@assert !epsilonequal(csts10, csts13)
@assert !epsilonequal(csts10, csts14)
@assert !epsilonequal(csts10, csts15)
@assert epsilonequal(csts11, csts11)
@assert !epsilonequal(csts11, csts12)
@assert !epsilonequal(csts11, csts13)
@assert !epsilonequal(csts11, csts14)
@assert !epsilonequal(csts11, csts15)
@assert epsilonequal(csts12, csts12)
@assert epsilonequal(csts12, csts13)
@assert epsilonequal(csts12, csts14)
@assert epsilonequal(csts12, csts15)
@assert epsilonequal(csts13, csts13)
@assert epsilonequal(csts13, csts14)
@assert epsilonequal(csts13, csts15)
@assert epsilonequal(csts14, csts14)
@assert epsilonequal(csts14, csts15)
@assert epsilonequal(csts15, csts15)
@assert epsilonequal(1-csts8, csts12)
@assert epsilonequal(1-csts9, csts12)
@assert epsilonequal(1-csts10, csts12)
@assert epsilonequal(1-csts11, csts12)
@assert !epsilonequal(1-csts8, csts9)

csts16 = constraints_unpack(:([a==b]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts17 = constraints_unpack(:([b==a]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
#csts18 = constraints_unpack(:([b==a==b]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
#csts19 = constraints_unpack(:([b>=a==b]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts20 = constraints_unpack(:([b<=a<=b]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
@assert epsilonequal(csts16, csts16)
@assert epsilonequal(csts16, csts17)
#@assert epsilonequal(csts16, csts18)
#@assert epsilonequal(csts16, csts19)
@assert !epsilonequal(csts16, csts20)
@assert epsilonequal(csts16, csts20*Hyper(1,1))
@assert epsilonequal(csts17, csts17)
#@assert epsilonequal(csts17, csts18)
#@assert epsilonequal(csts17, csts19)
#@assert epsilonequal(csts17, csts20)
#@assert epsilonequal(csts18, csts18)
#@assert epsilonequal(csts18, csts19)
#@assert epsilonequal(csts18, csts20)
#@assert epsilonequal(csts19, csts19)
#@assert epsilonequal(csts19, csts20)
@assert epsilonequal(csts20, csts20)
csts21 = constraints_unpack(:([a<b]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts22 = constraints_unpack(:([-a>-b]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts23 = constraints_unpack(:([b>a]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts24 = constraints_unpack(:([-b<-a]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
@assert epsilonequal(csts21, csts21)
@assert epsilonequal(csts21, csts22)
@assert epsilonequal(csts21, csts23)
@assert epsilonequal(csts21, csts24)
@assert epsilonequal(csts22, csts22)
@assert epsilonequal(csts22, csts23)
@assert epsilonequal(csts22, csts24)
@assert epsilonequal(csts23, csts23)
@assert epsilonequal(csts23, csts24)
@assert epsilonequal(csts24, csts24)
csts25 = constraints_unpack(:([a>=b]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts26 = constraints_unpack(:([-a<=-b]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts27 = constraints_unpack(:([b<=a]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
csts28 = constraints_unpack(:([-b>=-a]), rulespace_pattern_1, rulespace_domain_1, preds_1, pred_nums_1)
@assert epsilonequal(csts25, csts25)
@assert epsilonequal(csts25, csts26)
@assert epsilonequal(csts25, csts27)
@assert epsilonequal(csts25, csts28)
@assert epsilonequal(csts26, csts26)
@assert epsilonequal(csts26, csts27)
@assert epsilonequal(csts26, csts28)
@assert epsilonequal(csts27, csts27)
@assert epsilonequal(csts27, csts28)
@assert epsilonequal(csts28, csts28)
@assert !epsilonequal(csts21, csts25)
@assert epsilonequal(1-csts21, csts25)

preds_2 = Set([:p,:x,:y])
pred_nums_2 = Dict(:p=>1, :x=>2, :y=>3)
rulespace_pattern_2 = :(Pred1,(a,b,Pred2,e))
rulespace_domain_2 = Domain(expression_sig(pred_nums_2, rulespace_pattern_2))
csts29 = constraints_unpack(:[[Pred1 == p]], rulespace_pattern_2, rulespace_domain_2, preds_2, pred_nums_2)
@assert epsilonequal(csts29, mt(rulespace_domain_2, ps([1], 1, ml(0.0), ps([1], 2, ml(1.0), ml(0.0)))))
csts30 = constraints_unpack(:[[Pred2 == x]], rulespace_pattern_2, rulespace_domain_2, preds_2, pred_nums_2)
@assert epsilonequal(csts30, mt(rulespace_domain_2, ps([2,3], 2, ml(0.0), ps([2,3], 3, ml(1.0), ml(0.0)))))

preds_3 = Set([:p,:x,:y])
pred_nums_3 = Dict(:p=>1, :x=>2, :y=>3)
rulespace_pattern_3 = :(Pred1,(a,b,Pred2,_t_))
rulespace_domain_3 = Domain(expression_sig(pred_nums_3, rulespace_pattern_3))
csts31 = constraints_unpack(:([[_t_ == (a,b)]]), rulespace_pattern_3, rulespace_domain_3, preds_3, pred_nums_3)
rulespace_pattern_4 = :(Pred1,(a,b,Pred2,(c,d)))
rulespace_domain_4 = Domain(expression_sig(pred_nums_3, rulespace_pattern_4))
csts32 = constraints_unpack(:[a == c], rulespace_pattern_4, rulespace_domain_4, preds_3, pred_nums_3)
csts32 = csts32 * constraints_unpack(:[b == d], rulespace_pattern_4, rulespace_domain_4, preds_3, pred_nums_3)
@assert epsilonequal(csts31, csts32)
@assert epsilonequal(csts31, insert(csts32, csts31))

#rulespace_domain_4 = pattern_domain(pred_nums_3, rulespace_pattern_4)
#query(csts31, rulespace_domain_4)


compilecombofun([:p], :(1+p(x,y)), :(p(x,y)), Domain(sig((:[1,1], :v, :v))), Set([:p]), Dict(:p=>1))

r = :(a(x,z) = @sum a(x,y) * a(y,z))
make_rule(:(a(x,z)), :(a(x,y) * a(y,z)), integrate, Set([:a]), Dict(:a=>1), Int[], 1, Function[])

# transitive relation f
rs = @rules begin
  f(x,z) = @sum g(x,y,z)
  g(x,y,z) = @prod f(x,y)*f(y,z)
end

lines = relevant_lines(:(begin
  f(x,z) = @sum g(x,y,z)
  g(x,y,z) = @prod f(x,y)*f(y,z)
end))

extracted_predicates = named_predicate_nums(lines, length(lines))
rule_preds = Set{Tuple{Symbol,Int}}([(gensym(),l) for l in 1:length(lines)])

simple_trans = @rules begin
  f(x,z) = @sum f(xy)*f(y,z)
end

@assert simple_trans.rules[1].summarize == integrate
@assert simple_trans.rules[1].merge == +
@assert length(simple_trans.rules[1].overlapping_rules) == 0
@assert length(simple_trans.rules) == 1
#@assert simple_trans.rules[1].combine.body == :(f(xy)*f(y,z))



rs1 = @rules begin
  f(x) = @sum 5
  g(x) = @sum 10
  h(x) = @sum f(x) + g(x)
end

rs1.rules[1].target == dom((:[1:1], (:v,)))
rs1.rules[2].target == dom((:[2:2], (:v,)))
rs1.rules[3].target == dom((:[3:3], (:v,)))
@assert query(rs1.wm, dom((:[1:1], (:v,)))).root.value == LeafNode(0.0)
step_rule!(rs1, 1)
@assert query(rs1.wm, dom((:[1:1], (:v,)))).root.value.value == 5.0
@assert query(rs1.wm, dom((:[2:2], (:v,)))).root.value.value == 0.0
@assert query(rs1.wm, dom((:[3:3], (:v,)))).root.value.value == 0.0
step_rule!(rs1, 2)
@assert query(rs1.wm, dom((:[1:1], (:v,)))).root.value.value == 5.0
@assert query(rs1.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs1.wm, dom((:[3:3], (:v,)))).root.value.value == 0.0
step_rule!(rs1, 3)
@assert query(rs1.wm, dom((:[1:1], (:v,)))).root.value.value == 5.0
@assert query(rs1.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs1.wm, dom((:[3:3], (:v,)))).root.value.value == 15.0
step_rule!(rs1, 3)
@assert query(rs1.wm, dom((:[1:1], (:v,)))).root.value.value == 5.0
@assert query(rs1.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs1.wm, dom((:[3:3], (:v,)))).root.value.value == 15.0
step_rule!(rs1, 2)
@assert query(rs1.wm, dom((:[1:1], (:v,)))).root.value.value == 5.0
@assert query(rs1.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs1.wm, dom((:[3:3], (:v,)))).root.value.value == 15.0

resulting_mem = rs1.wm
old_init!(rs1)
run!(rs1, 30)
@assert epsilonequal(rs1.wm, resulting_mem)

rs2 = @rules begin
  f(x) = @sum 5 + i(y)
  g(x) = @sum 10
  h(x) = @sum f(x) + g(x)
  i(x) = @sum 0
  i(x) = @sum [1<x<4]
end

@assert rs2.rules[1].target == dom((:[1:1], (:v,)))
@assert rs2.rules[2].target == dom((:[2:2], (:v,)))
@assert rs2.rules[3].target == dom((:[3:3], (:v,)))
@assert rs2.rules[4].target == dom((:[4:4], (:v,)))
@assert rs2.rules[5].target == dom((:[4:4], (:v,)))
@assert query(rs2.wm, dom((:[1:1], (:v,)))).root.value.value == 0.0
step_rule!(rs2, 4)
step_rule!(rs2, 1)
@assert query(rs2.wm, dom((:[1:1], (:v,)))).root.value.value == Hyper(5.0,1)
@assert query(rs2.wm, dom((:[2:2], (:v,)))).root.value.value == 0
@assert query(rs2.wm, dom((:[3:3], (:v,)))).root.value.value == 0.0
@assert query(rs2.wm, dom((:[4:4], (:v,)))).root.value.value == 0.0
step_rule!(rs2, 5)
step_rule!(rs2, 1)
step_rule!(rs2, 2)
step_rule!(rs2, 3)
@assert query(rs2.wm, dom((:[1:1], (:v,)))).root.value.value == Hyper(5.0,1)
@assert query(rs2.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs2.wm, dom((:[3:3], (:v,)))).root.value.value == Hyper(5.0,1)

resulting_mem = rs2.wm
old_init!(rs2)
run!(rs2, 30)
@assert epsilonequal(rs2.wm, resulting_mem)

rs3 = @rules begin
  f(x) = @sum 5 + i(x)
  g(x) = @sum 10
  h(x) = @sum f(x) + g(x)
  i(x) = @sum 0
  i(x) = @sum [1<y<4]
end

@assert rs3.rules[1].target == dom((:[1:1], (:v,)))
@assert rs3.rules[2].target == dom((:[2:2], (:v,)))
@assert rs3.rules[3].target == dom((:[3:3], (:v,)))
@assert rs3.rules[4].target == dom((:[4:4], (:v,)))
@assert rs3.rules[5].target == dom((:[4:4], (:v,)))
@assert query(rs3.wm, dom((:[1:1], (:v,)))).root.value.value == 0
step_rule!(rs3, 4)
step_rule!(rs3, 1)
@assert query(rs3.wm, dom((:[1:1], (:v,)))).root.value.value == 5.0
@assert query(rs3.wm, dom((:[2:2], (:v,)))).root.value.value == 0
@assert query(rs3.wm, dom((:[3:3], (:v,)))).root.value.value == 0
@assert query(rs3.wm, dom((:[4:4], (:v,)))).root.value.value == 0.0
step_rule!(rs3, 2)
@assert query(rs3.wm, dom((:[1:1], (:v,)))).root.value.value == 5.0
@assert query(rs3.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs3.wm, dom((:[3:3], (:v,)))).root.value.value == 0
@assert query(rs3.wm, dom((:[4:4], (:v,)))).root.value.value == 0.0
step_rule!(rs3, 3)
@assert query(rs3.wm, dom((:[1:1], (:v,)))).root.value.value == 5.0
@assert query(rs3.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs3.wm, dom((:[3:3], (:v,)))).root.value.value == 15.0
@assert query(rs3.wm, dom((:[4:4], (:v,)))).root.value.value == 0.0
step_rule!(rs3, 3)
@assert query(rs3.wm, dom((:[1:1], (:v,)))).root.value.value == 5.0
@assert query(rs3.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs3.wm, dom((:[3:3], (:v,)))).root.value.value == 15.0
@assert query(rs3.wm, dom((:[4:4], (:v,)))).root.value.value == 0.0
step_rule!(rs3, 5)
@assert query(rs3.wm, dom((:[1:1], (:v,)))).root.value.value == 5.0
@assert query(rs3.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs3.wm, dom((:[3:3], (:v,)))).root.value.value == 15.0
@assert query(rs3.wm, dom((:[4:4], (:v,)))).root.value.value == 3.0
step_rule!(rs3, 4)
@assert query(rs3.wm, dom((:[1:1], (:v,)))).root.value.value == 5.0
@assert query(rs3.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs3.wm, dom((:[3:3], (:v,)))).root.value.value == 15.0
@assert query(rs3.wm, dom((:[4:4], (:v,)))).root.value.value == 3.0
step_rule!(rs3, 1)
@assert query(rs3.wm, dom((:[1:1], (:v,)))).root.value.value == 8.0
@assert query(rs3.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs3.wm, dom((:[3:3], (:v,)))).root.value.value == 15.0
@assert query(rs3.wm, dom((:[4:4], (:v,)))).root.value.value == 3.0
step_rule!(rs3, 2)
@assert query(rs3.wm, dom((:[1:1], (:v,)))).root.value.value == 8.0
@assert query(rs3.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs3.wm, dom((:[3:3], (:v,)))).root.value.value == 15.0
@assert query(rs3.wm, dom((:[4:4], (:v,)))).root.value.value == 3.0
step_rule!(rs3, 3)
@assert query(rs3.wm, dom((:[1:1], (:v,)))).root.value.value == 8.0
@assert query(rs3.wm, dom((:[2:2], (:v,)))).root.value.value == 10.0
@assert query(rs3.wm, dom((:[3:3], (:v,)))).root.value.value == 18.0
@assert query(rs3.wm, dom((:[4:4], (:v,)))).root.value.value == 3.0

resulting_mem = rs3.wm
old_init!(rs3)
run!(rs3, 30)
@assert epsilonequal(rs3.wm, resulting_mem)

rs4 = @rules begin
  f(x) = @sum 5 + i(x)
  g(x) = @sum 10
  h(x) = @sum f(x)
  h(x) = @sum g(x)
  i(x) = @sum 0
  i(x) = @sum [1<y<4]
end

run!(rs4, 30)
@assert epsilonequal(rs3.wm, rs4.wm)


# test whether insert! and initialization create equivalent results
# the helper predicate g is not strictly necessary; it would be simpler to
# write a rule f(x,z) = @max f(x,y)*f(y,z). Seperating the operations out
# gives a little more granularity for debugging. By which I mean, there was a
# point at which it wasn't working, and I seperated things out as part of an
# attempt to get things working, though by the time it was working I could have
# put things back together, so seperating things out doesn't play a role in it
# working.

trans_with_init = @rules begin
  f(x,z) = @max g(x,y,z)
  f(x,y) = @max [1<=x<2]*[3<=y<4] + [3<=x<4]*[5<=y<6]
  g(x,y,z) = @max f(x,y)*f(y,z)
end

trans_without_init = @rules begin
  f(x,z) = @max g(x,y,z)
  f(x,y) = @max 0
  g(x,y,z) = @max f(x,y)*f(y,z)
end

square_1 = rect_region([1,3],[2,4])
square_2 = rect_region([3,5],[4,6])
square_3 = rect_region([1,5],[2,6])
sq_tree_1 = BSPTree(boundless_reg(2),unfoldboundary(BSPTree(square_1,LeafNode(1.0)),LeafNode(0.0)))
sq_tree_2 = BSPTree(boundless_reg(2),unfoldboundary(BSPTree(square_2,LeafNode(1.0)),LeafNode(0.0)))
sq_tree_3 = BSPTree(boundless_reg(2),unfoldboundary(BSPTree(square_3,LeafNode(1.0)),LeafNode(0.0)))
init_f_state = sq_tree_1 + sq_tree_2
final_f_state = sq_tree_1 + sq_tree_2 + sq_tree_3
f_num = trans_without_init.pred_nums[:f]
g_num = trans_without_init.pred_nums[:g]
f_sig = sig((:[$(f_num):$(f_num)],(:v,:v)))
g_sig = sig((:[$(g_num):$(g_num)],(:v,:v,:v)))
f_dom = Domain(f_sig, boundless_reg(2), standard_varmap(f_sig))
g_dom = Domain(g_sig, boundless_reg(2), standard_varmap(g_sig))
init_f_memtree = MemTree(f_dom, MemLeaf(init_f_state.root, standard_varmap(f_sig)))
final_f_memtree = MemTree(f_dom, MemLeaf(final_f_state.root, standard_varmap(f_sig)))

# fire the initializaion rule for trans_with_init
step_rule!(trans_with_init, 2)
# imitate the effects of firing such a rule for trans_without_init
trans_without_init.output_buffers[2] = insert(init_f_memtree, trans_without_init.output_buffers[2])
trans_without_init.wm = insert(init_f_memtree, trans_without_init.wm)
@assert epsilonequal(query(trans_with_init.output_buffers[2], f_dom), query(trans_without_init.output_buffers[2], f_dom))
step_rule!(trans_with_init, 3)
step_rule!(trans_without_init, 3)
@assert epsilonequal(query(trans_with_init.output_buffers[3], g_dom), query(trans_without_init.output_buffers[3], g_dom))
@assert epsilonequal(query(trans_with_init.wm, g_dom), query(trans_without_init.wm, g_dom))
step_rule!(trans_with_init, 1)
step_rule!(trans_without_init, 1)
@assert epsilonequal(query(trans_with_init.output_buffers[1], f_dom), query(trans_without_init.output_buffers[1], f_dom))
@assert epsilonequal(query(trans_with_init.wm, f_dom), query(trans_without_init.wm, f_dom))

@assert epsilonequal(query(trans_with_init.wm, f_dom), final_f_memtree)


# Ok, here is the simpler version of a transitive relation.

simple_trans = @rules begin
  f(x,z) = @max f(x,y)*f(y,z)
  f(x,y) = @max [1<=x<2]*[3<=y<4] + [3<=x<4]*[5<=y<6]
end

step_rule!(simple_trans, 2)
@assert epsilonequal(query(simple_trans.wm, f_dom), init_f_memtree)
step_rule!(simple_trans, 1)
@assert !epsilonequal(query(simple_trans.wm, f_dom), init_f_memtree)
@assert epsilonequal(query(simple_trans.wm, f_dom), final_f_memtree)



#insert!(init_f_memtree, trans_without_init)
#step_rule!(trans_with_init, 2)

#epsilonequal(trans_with_init.wm, trans_without_init.wm)
#q1 = query(trans_with_init.wm, f_dom)
#q2 = query(trans_without_init.wm, f_dom)
#epsilonequal(q1,q2)
#f_stage_sig = sig((:[2,2],(:[4,4],(:v,:v))))
#f_stage_dom = Domain(f_stage_sig, boundless_reg(2), standard_varmap(f_stage_sig))
#query(trans_with_init.wm, f_stage_dom) == query(trans_without_init.wm, f_stage_dom)


#run!(trans_with_init, 20)
#run!(trans_without_init, 20)

#trans_with_init.wm == trans_without_init.wm
#epsilonequal(trans_with_init.wm, trans_without_init.wm)
#q1 = query(trans_with_init.wm, f_dom)
#q2 = query(trans_without_init.wm, f_dom)
#epsilonequal(q1,q2)


# Here's a simple example involving averaging two numbers, but I'll
# progressively mix in more second order features.

# First-order version.

av1 = @rules begin
  a() = @just 1
  b() = @just 2
  av() = @sum (a() + b()) / 2
end

step_rule!(av1,1)
step_rule!(av1,2)
step_rule!(av1,3)
@assert epsilonequal(query(av1, :av), mt(dom((:[3:3], ())),ml(1.5)))
@assert !epsilonequal(query(av1, :av), mt(dom((:[3:3], ())),ml(1.0)))

# Second-order predicate determines which preds to average.

av2 = @rules begin
  a() = @just 1
  b() = @just 2
  to_average(P) = @just [[P == a]] + [[P == b]]
  av() = @sum to_average(P) * P() / 2
end

step_rule!(av2,1)
step_rule!(av2,2)
step_rule!(av2,3)
step_rule!(av2,4)
@assert epsilonequal(query(av2, :av), mt(dom((:[4:4], ())),ml(1.5)))
@assert !epsilonequal(query(av2, :av), mt(dom((:[4:4], ())),ml(-1.5)))

# Sum over the second-order predicate to determine the divisor.

av3 = @rules begin
  a() = @just 1
  b() = @just 2
  to_average(P) = @just [[P == a]] + [[P == b]]
  num_averaged() = @sum to_average(P)
  av() = @sum to_average(P) * P() / num_averaged()
end

@assert epsilonequal(query(av3, :a), mt(dom((:[1:1], ())), ml(0.0)))
@assert !epsilonequal(query(av3, :a), mt(dom((:[1:1], ())), ml(1.0)))
@assert epsilonequal(query(av3, :b), mt(dom((:[2:2], ())), ml(0.0)))
@assert !epsilonequal(query(av3, :b), mt(dom((:[2:2], ())), ml(1.0)))
@assert epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[0:5]))), ml(0.0)))
@assert !epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[0:5],))), ml(1.0)))
@assert epsilonequal(query(av3, :num_averaged), mt(dom((:[4:4], ())), ml(0.0)))
@assert !epsilonequal(query(av3, :num_averaged), mt(dom((:[4:4], ())), ml(1.0)))
@assert epsilonequal(query(av3, :av), mt(dom((:[5:5], ())), ml(0.0)))
@assert !epsilonequal(query(av3, :av), mt(dom((:[5:5], ())), ml(1.0)))

step_rule!(av3,1)

@assert epsilonequal(query(av3, :a), mt(dom((:[1:1], ())), ml(1.0)))
@assert !epsilonequal(query(av3, :a), mt(dom((:[1:1], ())), ml(-1.0)))
@assert epsilonequal(query(av3, :b), mt(dom((:[2:2], ())), ml(0.0)))
@assert !epsilonequal(query(av3, :b), mt(dom((:[2:2], ())), ml(1.0)))
@assert epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[0:5]))), ml(0.0)))
@assert !epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[0:5],))), ml(1.0)))
@assert epsilonequal(query(av3, :num_averaged), mt(dom((:[4:4], ())), ml(0.0)))
@assert !epsilonequal(query(av3, :num_averaged), mt(dom((:[4:4], ())), ml(1.0)))
@assert epsilonequal(query(av3, :av), mt(dom((:[5:5], ())), ml(0.0)))
@assert !epsilonequal(query(av3, :av), mt(dom((:[5:5], ())), ml(1.0)))

step_rule!(av3,2)

@assert epsilonequal(query(av3, :a), mt(dom((:[1:1], ())), ml(1.0)))
@assert !epsilonequal(query(av3, :a), mt(dom((:[1:1], ())), ml(-1.0)))
@assert epsilonequal(query(av3, :b), mt(dom((:[2:2], ())), ml(2.0)))
@assert !epsilonequal(query(av3, :b), mt(dom((:[2:2], ())), ml(1.0)))
@assert epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[0:5]))), ml(0.0)))
@assert !epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[0:5],))), ml(1.0)))
@assert epsilonequal(query(av3, :num_averaged), mt(dom((:[4:4], ())), ml(0.0)))
@assert !epsilonequal(query(av3, :num_averaged), mt(dom((:[4:4], ())), ml(1.0)))
@assert epsilonequal(query(av3, :av), mt(dom((:[5:5], ())), ml(0.0)))
@assert !epsilonequal(query(av3, :av), mt(dom((:[5:5], ())), ml(1.0)))

step_rule!(av3,3)

@assert epsilonequal(query(av3, :a), mt(dom((:[1:1], ())), ml(1.0)))
@assert !epsilonequal(query(av3, :a), mt(dom((:[1:1], ())), ml(-1.0)))
@assert epsilonequal(query(av3, :b), mt(dom((:[2:2], ())), ml(2.0)))
@assert !epsilonequal(query(av3, :b), mt(dom((:[2:2], ())), ml(1.0)))
@assert epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[1:2],))), ml(1.0)))
@assert !epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[1:2],))), ml(0.0)))
@assert epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[3:5],))), ml(0.0)))
@assert !epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[3:5],))), ml(1.0)))
@assert epsilonequal(query(av3, :num_averaged), mt(dom((:[4:4], ())), ml(0.0)))
@assert !epsilonequal(query(av3, :num_averaged), mt(dom((:[4:4], ())), ml(1.0)))
@assert epsilonequal(query(av3, :av), mt(dom((:[5:5], ())), ml(0.0)))
@assert !epsilonequal(query(av3, :av), mt(dom((:[5:5], ())), ml(1.0)))

step_rule!(av3,4)

@assert epsilonequal(query(av3, :a), mt(dom((:[1:1], ())), ml(1.0)))
@assert !epsilonequal(query(av3, :a), mt(dom((:[1:1], ())), ml(-1.0)))
@assert epsilonequal(query(av3, :b), mt(dom((:[2:2], ())), ml(2.0)))
@assert !epsilonequal(query(av3, :b), mt(dom((:[2:2], ())), ml(1.0)))
@assert epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[1:2],))), ml(1.0)))
@assert !epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[1:2],))), ml(0.0)))
@assert epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[3:5],))), ml(0.0)))
@assert !epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[3:5],))), ml(1.0)))
@assert epsilonequal(query(av3, :num_averaged), mt(dom((:[4:4], ())), ml(2.0)))
@assert !epsilonequal(query(av3, :num_averaged), mt(dom((:[4:4], ())), ml(1.0)))
@assert epsilonequal(query(av3, :av), mt(dom((:[5:5], ())), ml(0.0)))
@assert !epsilonequal(query(av3, :av), mt(dom((:[5:5], ())), ml(1.0)))

step_rule!(av3,5)

@assert epsilonequal(query(av3, :a), mt(dom((:[1:1], ())), ml(1.0)))
@assert !epsilonequal(query(av3, :a), mt(dom((:[1:1], ())), ml(-1.0)))
@assert epsilonequal(query(av3, :b), mt(dom((:[2:2], ())), ml(2.0)))
@assert !epsilonequal(query(av3, :b), mt(dom((:[2:2], ())), ml(1.0)))
@assert epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[1:2],))), ml(1.0)))
@assert !epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[1:2],))), ml(0.0)))
@assert epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[3:5],))), ml(0.0)))
@assert !epsilonequal(query(av3, :to_average), mt(dom((:[3:3], (:[3:5],))), ml(1.0)))
@assert epsilonequal(query(av3, :num_averaged), mt(dom((:[4:4], ())), ml(2.0)))
@assert !epsilonequal(query(av3, :num_averaged), mt(dom((:[4:4], ())), ml(1.0)))
@assert epsilonequal(query(av3, :av), mt(dom((:[5:5], ())),ml(1.5)))
@assert !epsilonequal(query(av3, :av), mt(dom((:[5:5], ())),ml(-1.5)))

# Here's a version which averages vectors, rather than single numbers. Starting
# with vectors holding uniform values, though.

av4 = @rules begin
  a(x) = @just 1
  b(x) = @just 2
  to_average(P) = @just [[P == a]] + [[P == b]]
  num_averaged() = @sum to_average(P)
  av(x) = @sum to_average(P) * P(x) / num_averaged()
end

step_rule!(av4,1)
step_rule!(av4,2)
step_rule!(av4,3)
step_rule!(av4,4)
step_rule!(av4,5)
@assert epsilonequal(query(av4, :av), mt(dom((:[5:5], (:v,))),ml(1.5)))
@assert !epsilonequal(query(av4, :av), mt(dom((:[5:5], (:v,))),ml(-1.5)))

# Now with nontrivial vector entries.

av5 = @rules begin
  a(x) = @just [1<x<=2] + [2<x<=3]
  b(x) = @just [2<x<=3] + [3<x<=4]
  to_average(P) = @just [[P == a]] + [[P == b]]
  num_averaged() = @sum to_average(P)
  av(x) = @sum to_average(P) * P(x) / num_averaged()
  to_compare(x) = @just 0.5*[1<x<=2] + [2<x<=3] + 0.5*[3<x<=4]
end

step_rule!(av5,1)
step_rule!(av5,2)
step_rule!(av5,3)
step_rule!(av5,4)
step_rule!(av5,5)
step_rule!(av5,6)
@assert epsilonequal(query(av5, :av), query(av5, :to_compare))
av_dom = query(av5, :av).domain
@assert epsilonequal(query(av5, :av), MemTree(av_dom, query(av5, :to_compare).root))
@assert !epsilonequal(query(av5, :av), MemTree(av_dom, 1-query(av5, :to_compare).root))
@assert epsilonequal(integrate(query(av5, :av),[1]), integrate(query(av5, :to_compare),[1]))
@assert !epsilonequal(integrate(query(av5, :av),[1]), 1-integrate(query(av5, :to_compare),[1]))



# Now we want to tuple matching.
# First, here's a pure first-order marginalization.

match1 = @rules begin
  a(x,y) = @sum [0<x<4]*[0<y<1] + [0<x<1]*[0<y<4]
  b(x) = @sum a(x,y)
  to_compare(x) = @just [0<x<4] + 4*[0<x<1]
end

step_rule!(match1, 1)
step_rule!(match1, 2)
step_rule!(match1, 3)
@assert epsilonequal(integrate(query(match1, :b),[1]), integrate(query(match1, :to_compare),[1]))
@assert !epsilonequal(integrate(query(match1, :b),[1]), integrate(1-query(match1, :to_compare),[1]))

# Adding a match table to tell us what marginalizes what.

# The following is a broken version; the tuple variable _t_ should be capturing
# all the arguments: P(_t_) should be P(_t_...). However, the broken version
# helped me debug some things.

match2 = @rules begin
  a(x,y) = @sum [0<x<4]*[0<y<1] + [0<x<1]*[0<y<4]
  b(x) = @sum 0 # Now we just initialize b w/o doing anything else.
  match(P,Q,(x,y),(x,)) = @sum [[P == a]]*[[Q == b]]
  P(_t_) = @sum Q(_u_) * match(P,Q,_t_,_u_)
end

@assert epsilonequal(query(match2, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match2, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
# @assert epsilonequal(query(match2, sig((:[3,3], (:[1,3], :[1,3], (:v, :v), (:v,))))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match2, 1)
@assert !epsilonequal(query(match2, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match2, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1,1], (:v, :v)))))
@assert epsilonequal(query(match2, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
# @assert epsilonequal(query(match2, sig((:[3,3], (:[1,3], :[1,3], (:v, :v), (:v,))))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match2, 2)
@assert epsilonequal(query(match2, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1,1], (:v, :v)))))
@assert epsilonequal(query(match2, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
# @assert epsilonequal(query(match2, sig((:[3,3], (:[1,3], :[1,3], (:v, :v), (:v,))))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match2, 3)
@assert epsilonequal(query(match2, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1,1], (:v, :v)))))
@assert epsilonequal(query(match2, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match2, sig((:[3:3], (:[1:3], :[1:3], (:v, :v), (:v,))))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match2, 4)
b_dom = dom((:[2:2], ((:v,),)))
# @assert epsilonequal(query(match2, sig((:[2,2], ((:v,),)))), MemTree(b_dom, query(match1, :to_compare).root))
# @assert epsilonequal(integrate(query(match2, :b),[1]), integrate(query(match1, :to_compare),[1]))
# @assert epsilonequal(query(match2, :b), query(match1, :b))
# Running more just to catch errors which occur when I do that.
step_rule!(match2, 1)
step_rule!(match2, 2)
step_rule!(match2, 3)
step_rule!(match2, 4)

# Now, this version **should** work... if matched first-order variables within
# patterns (particularly, within the head pattern) works.

hyper(x,y) = Hyper(x,y)

match3 = @rules begin
  a(x,y) = @sum [0<x<4]*[0<y<1] + [0<x<1]*[0<y<4]
  b(x) = @sum 0
  match(P,Q,(x,y),(x,)) = @sum [[P == a]]*[[Q == b]]*hyper(1,1)/1.4142135623730951
  Q(_u_...) = @sum P(_t_...) * match(P,Q,_t_,_u_)
end

match_pred_nums = match3.pred_nums
preds = Set(keys(match_pred_nums))
vl = get_variable_locs(:(match(P,Q,(x,y),(x,))), preds)
(match_reg, match_map) = first_order_constraints(match_pred_nums, vl)
match_dom = Domain(sig((:[3:3], (:[1:3], :[1:3], (:v, :v), (:v,)))), match_reg, match_map)
broad_match_dom = Domain(sig((:[3:3], (:[1:3], :[1:3], (:v, :v), (:v,)))))
@assert epsilonequal(query(match3, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
@assert epsilonequal(query(match3, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
@assert epsilonequal(query(match3.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
@assert epsilonequal(query(match3.wm, broad_match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3.wm, broad_match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
step_rule!(match3, 1)
@assert !epsilonequal(query(match3, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match3, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1:1], (:v, :v)))))
@assert epsilonequal(query(match3, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
@assert epsilonequal(query(match3.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
@assert epsilonequal(query(match3.wm, broad_match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3.wm, broad_match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
step_rule!(match3, 2)
@assert !epsilonequal(query(match3, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match3, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1:1], (:v, :v)))))
@assert epsilonequal(query(match3, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
@assert epsilonequal(query(match3.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
@assert epsilonequal(query(match3.wm, broad_match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3.wm, broad_match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
step_rule!(match3, 3)
@assert !epsilonequal(query(match3, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match3, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1,1], (:v, :v)))))
@assert epsilonequal(query(match3, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
@assert !epsilonequal(query(match3.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
@assert !epsilonequal(query(match3.wm, broad_match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match3.wm, broad_match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(1.0))))
@assert epsilonequal(
        query(match3.wm, Domain(sig((:[3:3], (:[1:1], :[2:2], (:v, :v), (:v,)))), match_reg, match_map)),
        MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(Hyper(1/1.4142135623730951,1)))))
@assert epsilonequal(
        query(match3.wm, Domain(sig((:[3:3], (:[1:1], :[2:2], (:v, :v), (:v,)))))),
        MemTree(
          Domain(sig((:[3:3], (:[1:1], :[2:2], (:v, :v), (:v,))))),
          MemLeaf(
            delta_slice(
              LinSplit([-1.0,1.0,0.0],0.0),
              LeafNode(Hyper(1/1.4142135623730951,1))),
            Dict([2,3,1]=>1,[2,4,1]=>2,[2,3,2]=>3))))
step_rule!(match3, 4)
b_dom = dom((:[2:2], (:v,)))
@assert epsilonequal(query(match3, sig((:[2:2], (:v,)))), MemTree(b_dom, query(match1, :to_compare).root))
@assert epsilonequal(integrate(query(match3, :b),[1]), integrate(query(match1, :to_compare),[1]))
@assert epsilonequal(query(match3, sig((:[2:2], (:v,)))), query(match1, sig((:[2:2], (:v,)))))
# Running more just to catch errors which occur when I do that.
step_rule!(match3, 1)
step_rule!(match3, 2)
step_rule!(match3, 3)
step_rule!(match3, 4)
# Should still have the desired result.
@assert epsilonequal(query(match3, sig((:[2:2], (:v,)))), MemTree(b_dom, query(match1, :to_compare).root))
@assert epsilonequal(integrate(query(match3, :b),[1]), integrate(query(match1, :to_compare),[1]))
@assert epsilonequal(query(match3, sig((:[2:2], (:v,)))), query(match1, sig((:[2:2], (:v,)))))

# Now, using tuple constraints. This version currently doesn't work because of
# an issue integrating out more complicated default variables. More or less, you
# can't use multiple tuple constraints at once until that issue is fixed.

match4 = @rules begin
  a(x,y) = @sum [0<x<4]*[0<y<1] + [0<x<1]*[0<y<4]
  b(x) = @sum 0
  match(P,Q,_t_,_u_) = @sum [[P == a]]*[[Q == b]]*[[_t_ == (x,y)]]*[[_u_ == (x,)]]
  P(_t_...) = @sum Q(_u_...) * match(P,Q,_t_,_u_)
end

@assert epsilonequal(query(match4, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match4, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match4, sig((:[3:3], (:[1:3], :[1:3], (:v, :v), (:v,))))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match4, 1)
@assert !epsilonequal(query(match4, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match4, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1:1], (:v, :v)))))
@assert epsilonequal(query(match4, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match4, sig((:[3:3], (:[1:3], :[1:3], (:v, :v), (:v,))))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match4, 2)
@assert epsilonequal(query(match4, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1:1], (:v, :v)))))
@assert epsilonequal(query(match4, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match4, sig((:[3:3], (:[1:3], :[1:3], (:v, :v), (:v,))))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match4, 3)
@assert epsilonequal(query(match4, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1:1], (:v, :v)))))
@assert epsilonequal(query(match4, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match4, sig((:[3:3], (:[1:3], :[1:3], (:v, :v), (:v,))))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
# step_rule!(match4, 4)
# b_dom = dom((:[2,2], (:v,)))
# @assert epsilonequal(query(match4, sig((:[2,2], (:v,)))), MemTree(b_dom, query(match1, :to_compare).root))
# @assert epsilonequal(integrate(query(match4, :b),[1]), integrate(query(match1, :to_compare),[1]))
# @assert epsilonequal(query(match4, :b), query(match1, :b))

# Now let's check that the second-order rule only applies when the match table
# says.

match5 = @rules begin
  a(x,y) = @sum [0<x<4]*[0<y<1] + [0<x<1]*[0<y<4]
  b(x) = @sum 0
  c(x) = @sum 0
  d(x,y) = @sum [0<x<2]*[0<y<1.5]
  match(P,Q,(x,y),(x,)) = @sum [[P == a]]*[[Q == b]]*hyper(1,1)/1.4142135623730951
  Q(_u_...) = @sum P(_t_...) * match(P,Q,_t_,_u_)
end

match_pred_nums = match5.pred_nums
preds = Set(keys(match_pred_nums))
vl = get_variable_locs(:(match(P,Q,(x,y),(x,))), preds)
(match_reg, match_map) = first_order_constraints(match_pred_nums, vl)
match_dom = Domain(sig((:[5:5], (:[1:5], :[1:5], (:v, :v), (:v,)))), match_reg, match_map)
@assert epsilonequal(query(match5, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[3:3], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[4:4], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match5, 1)
@assert !epsilonequal(query(match5, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1:1], (:v, :v)))))
@assert epsilonequal(query(match5, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[3:3], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[4:4], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match5, 2)
@assert !epsilonequal(query(match5, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1:1], (:v, :v)))))
@assert epsilonequal(query(match5, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[3:3], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[4:4], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match5, 3)
@assert !epsilonequal(query(match5, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1:1], (:v, :v)))))
@assert epsilonequal(query(match5, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[3:3], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[4:4], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match5, 4)
@assert !epsilonequal(query(match5, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1:1], (:v, :v)))))
@assert epsilonequal(query(match5, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[3:3], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match5, sig((:[4:4], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(integrate(query(match5, sig((:[4:4], (:v, :v)))), [1]), integrate(query(match1, sig((:[1:1], (:v, :v)))), [1]))
@assert epsilonequal(query(match5.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match5, 5)
@assert !epsilonequal(query(match5, sig((:[1:1], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[1:1], (:v, :v)))), query(match1, sig((:[1:1], (:v, :v)))))
@assert epsilonequal(query(match5, sig((:[2:2], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert epsilonequal(query(match5, sig((:[3:3], (:v,)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(query(match5, sig((:[4:4], (:v, :v)))), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
@assert !epsilonequal(integrate(query(match5, sig((:[4:4], (:v, :v)))), [1]), integrate(query(match1, sig((:[1:1], (:v, :v)))), [1]))
@assert !epsilonequal(query(match5.wm, match_dom), MemTree(Domain(UnspecifiedTSig()), MemLeaf(LeafNode(0.0))))
step_rule!(match5, 6)
b_dom = dom((:[2:2], (:v,)))
@assert epsilonequal(query(match5, sig((:[2:2], (:v,)))), MemTree(b_dom, query(match1, :to_compare).root))
@assert epsilonequal(integrate(query(match5, :b),[1]), integrate(query(match1, :to_compare),[1]))
@assert epsilonequal(query(match5, sig((:[2:2], (:v,)))), query(match1, sig((:[2:2], (:v,)))))
# Running more just to catch errors which occur when I do that.
step_rule!(match5, 1)
step_rule!(match5, 2)
step_rule!(match5, 3)
step_rule!(match5, 4)
# Should still have the desired result.
@assert epsilonequal(query(match5, sig((:[2:2], (:v,)))), MemTree(b_dom, query(match1, :to_compare).root))
@assert epsilonequal(integrate(query(match5, :b),[1]), integrate(query(match1, :to_compare),[1]))
@assert epsilonequal(query(match5, sig((:[2:2], (:v,)))), query(match1, sig((:[2:2], (:v,)))))


recursion = @rules begin
  f(x,y) = @sum 1
  f(x,_t_) = @sum f(_t_...)
end


pred_const = @rules begin
  a(x) = @sum 1
  b(a) = @sum 3
end























#      ;D                                                                                                                                                                                                                                                                                                                                                                                                                          :)
