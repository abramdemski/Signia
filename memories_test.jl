
include("memories.jl")

# using Base.Test

# seed the random number generator to ensure consistent results
using Random
srand(x) = Random.seed!(x)
srand(1)

sig1 = ESig()
sig2 = VSig()
sig3 = UnspecifiedTSig()
sig4 = SpecifiedTSig([VSig(), VSig()])
sig5 = SpecifiedTSig([UnspecifiedTSig(), UnspecifiedTSig()])
sig6 = SpecifiedTSig([SpecifiedTSig([VSig(), VSig()]), UnspecifiedTSig()])
sig7 = PSig([1:10])
sig8 = PSig([1:10, 2:20])

sig1_ = sig(:e)
sig2_ = sig(:v)
sig3_ = sig(:t)
sig4_ = sig((:v, :v))
sig5_ = sig((:t, :t))
sig6_ = sig(((:v, :v), :t))
sig7_ = sig(:[1:10])
sig8_ = sig(:[1:10, 2:20])

@assert sig1_ == sig1
@assert sig2_ == sig2
@assert sig3_ == sig3
@assert sig4_ == sig4
@assert sig5_ == sig5
@assert sig6_ == sig6
@assert sig7_ == sig7
@assert sig8_ == sig8

@assert sig1_ != sig2
@assert sig2_ != sig3
@assert sig3_ != sig4
@assert sig4_ != sig5
@assert sig5_ != sig6
@assert sig6_ != sig7
@assert sig7_ != sig1

@assert sig(sigv(sig1)) == sig1
@assert sig(sigv(sig2)) == sig2
@assert sig(sigv(sig3)) == sig3
@assert sig(sigv(sig4)) == sig4
@assert sig(sigv(sig5)) == sig5
@assert sig(sigv(sig6)) == sig6
@assert sig(sigv(sig7)) == sig7


@assert dom((:[1:2], [1,2], sig5, [1,2])) ==
  Domain(sig((:[1:2], :v, sig5, :v)),
    rect_region([1,1], [2,2]),
    Dict([2]=>1, [4]=>2))

dom((:[1:2], [1,2], sig5, [1,2]))
dom((:[1:2], [1,2], [1,2]))
dom(([1,2], sig5, [1,2]))
dom(sig5)
dom((:t, :t))


@assert access_defined(sig(:v), Int[])
@assert access_defined(sig6, [1])
@assert access_defined(sig6, [2])
@assert !access_defined(sig6, [3])
@assert !access_defined(sig6, [0])
@assert access_defined(sig6, [1,1])
@assert access_defined(sig6, [1,2])
@assert !access_defined(sig6, [1,3])
@assert !access_defined(sig6, [2,1])
@assert !access_defined(sig6, [2,2,2])
@assert access_defined(sig8, [1])
@assert access_defined(sig8, [2])
@assert !access_defined(sig8, [3])
@assert !access_defined(sig8, [1,1])



@assert specialize_sig(sig5, [1], sig4) == sig6
@assert specialize_sig(sig6, [1,1], sig(:[1:2])) == ESig()
@assert specialize_sig(sig5, [1], sig((:[1:10],))) == sig(((:[1:10],), :t))

sig9_ = specialize_sig(sig5, [1], sig5)
specialize_sig(sig9_, [1,1], sig9_)== sig(((((:t, :t), :t), :t), :t))

@assert specialize_sig(PSig(1,10), Int[], PSig(-1,2)) == PSig(1,2)
@assert specialize_sig(PSig(1,10), Int[], PSig(2,20)) == PSig(2,10)
@assert specialize_sig(sig((:v, :[1:10])), [2], PSig(-1,2)) == sig((:v, :[1:2]))
@assert specialize_sig(sig((:v, :[1:10])), [2], PSig(2,20)) == sig((:v, :[2:10]))
@assert specialize_sig(sig((:v, :[1:10, 2:20, 3:30])), [2,3], 5:50) == sig((:v, :[1:10, 2:20, 5:30]))

sig9 = SpecifiedTSig([UnspecifiedTSig(),
                      UnspecifiedTSig(Set((Signature[VSig()],)))],
                     Set((Signature[SpecifiedTSig(Signature[PSig(1,2)]),SpecifiedTSig(Signature[PSig(1,2)])],)))
@assert specialize_sig(sig9, [2], SpecifiedTSig(Signature[VSig()])) == ESig()
sig10 = specialize_sig(sig9, [2], sig((:[1,2],),))
@assert sig10 != ESig()
@assert specialize_sig(sig10, [1], sig((:[1,2],),)) == ESig()

@assert intersection(sig(:[0:10]), sig(:[-5:5])) == sig(:[0:5])
@assert intersection(sig(:[1:10]), sig(:t)) == ESig()
@assert intersection(sig5, sig8) == ESig()
@assert intersection(sig((:v, :[1:10, 2:20, 3:30])), sig((:v, :[2:10, 10:20]))) == sig((:v, :[2:10, 10:20, 3:30]))


@assert intersection(sig((:[1:3],)), sig(:t)) == sig((:[1:3],))
@assert intersection(sig((:t, (:[1,3],))), sig(((:[1,3],), :t))) == sig(((:[1,3],), (:[1,3],)))

@assert intersection(sig9, sig((:t, :v))) == ESig()
@assert intersection(sig10, sig((:[1,2], :t))) == ESig()
@assert intersection(sig9, sig(((:[1,2],), :t))) != ESig()
@assert intersection(sig9, sig9) != ESig()
@assert intersection(sig10, sig10) != ESig()

@assert intersection(USig(1:20), USig(2:10)) == USig(2:10)
@assert intersection(USig(2:20), USig(1:10)) == USig(2:10)
@assert intersection(USig(1:20), USig(0:30)) == USig(1:20)

vm1 = Dict([1]=>1, [2]=>2, [3]=>3)
vm2 = Dict([3]=>1, [1]=>2, [2]=>3)
vm3 = Dict([1]=>1, [3]=>2, [2]=>3)
vm4 = Dict([1,1]=>1, [2,1]=>2, [3,1]=>3)
vm5 = Dict([4]=>1, [3]=>2)

@assert varmatches(vm1, vm2) == Dict(1=>2, 2=>3, 3=>1)
@assert varmatches(vm1, vm3) == Dict(1=>1, 2=>3, 3=>2)
@assert varmatches(vm1, vm4) == Dict{Int, Int}()

d1 = Dict(1=>2, 2=>3, 3=>1)
@assert reorder_dict_to_reorder_vect(d1,3)[1] == d1[1]
@assert reorder_dict_to_reorder_vect(d1,3)[2] == d1[2]
@assert reorder_dict_to_reorder_vect(d1,3)[3] == d1[3]

@assert find_varmap_match_reordering(vm1,vm2) == Dict(2=>1, 3=>2, 1=>3)
@assert find_varmap_match_reordering(vm1,vm3) == Dict(1=>1, 3=>2, 2=>3)
@assert find_varmap_match_reordering(vm1,vm5) == Dict(2=>3, 1=>4)

vm6 = Dict([1]=>1,[2]=>2, [4]=>4)
vm7 = Dict([1]=>100, [2]=>200, [3]=>300, [5]=>1)
vm_ro = find_varmap_match_reordering(vm6,vm7)
# find_varmap_match_reordering should always have an entry for each dim-num in the second argument
@assert all((k -> haskey(vm_ro, k)), values(vm7))
# find_varmap_match_reordering should not map a dim-num onto an already existing dim-num in the target, if it didn't match
@assert all((p -> in(p,varmatches(vm7,vm6)) ? true : (in(p[2], values(vm6)) ? false : true)), vm_ro)


dom1 = dom((([1,10],),([1,20],),:t))
dom2 = dom((:t,([2,30],),([3,30],)))
dom3 = intersection(dom1,dom2)
@assert dom3 == dom((([1,10],),([2,20],),([3,30],)))


@assert subset(sig(((:v,), (:v,))), SpecifiedTSig(Signature[sig(:t), sig(:t)]))
@assert !subset(sig(((:v,), (:v,))), SpecifiedTSig(Signature[sig(:t), sig(:t)], Set((Signature[sig(:t), sig((:v,))],))))


@assert subset(dom(:[1:2]), dom(:[1:2]))
@assert subset(dom(:[1:2]), dom(:[1:3]))
@assert !subset(dom(:[1:3]), dom(:[1:2]))
@assert subset(dom([1,2]), dom([1,2]))
@assert subset(dom([1,2]), dom([1,3]))
@assert !subset(dom([1,3]), dom([1,2]))
@assert !subset(dom((:[1:2],[1,2])), dom(([1,2], :[1:2])))
@assert subset(dom((:[1:2],[1,2])), dom((:[1:3], [0,2])))
@assert subset(dom((:[1:2],[1,2])), dom((:[1:2], [1,2])))
@assert !subset(dom((:[1:3],[1,2])), dom((:[1:2], [1,3])))
@assert !subset(dom((:t, :t)), dom((:t, ([1,2],))))
@assert !subset(dom((:t, [1,2])), dom((:t, :t)))
@assert subset(dom((:t, ([1,2],))), dom((:t, :t)))
@assert !subset(dom((:[1:1], :t)), dom((:[1:1], (:t, :t))))
@assert subset(Domain(sig((:v, :v, :v)),
                    reorder(rect_region([0.1,10.1], [0.9, 10.9]), [2,1], 3),
                    Dict([2]=>1, [1]=>2, [3]=>3)),
            Domain(sig((:v, :v, :v)), rect_region([0,10],[1,11]), Dict([1]=>1, [2]=>2)))
@assert subset(Domain(sig((:v, (:v, :v))),
                    reorder(rect_region([0.1,10.1], [0.9, 10.9]), [2,1], 3),
                    Dict([2]=>1, [1]=>2, [3]=>3)),
            Domain(sig((:v, :t)), rect_region([0],[1]), Dict([1]=>1)))


mt1 = MemTree(dom((:t, :t)),
  TSplit([1],
    Dict(sig((:v,))=>
      MemLeaf(LeafNode(1.0), Dict([1,1]=>1))),
      MemLeaf(LeafNode(0.0),
        Dict{Array{Int64,1},Int64}())))
mt2 = follow_tuple_branch(mt1, [mt1.root.branches...][1])
@assert mt2.domain.sig == sig(((:v,), :t))
@assert mt2.root.value.value == 1.0
mt3 = follow_tuple_default(mt1)
@assert mt3.domain.sig != sig((:t, :t))
@assert subset(mt3.domain.sig, sig((:t, :t)))
@assert !subset(sig((:t, :t)), mt3.domain.sig)
@assert intersection(mt3.domain.sig, mt2.domain.sig) == ESig()
@assert mt3.domain.sig != spec_only(mt3.domain.sig)
@assert spec_only(mt3.domain.sig) == spec_only(sig((:t, :t)))
@assert mt3.root.value.value == 0.0
mt4 = MemTree(dom((:[1:10],)),
  PSplit(
    [1, 1],
    2,
    MemLeaf(LeafNode(0.0), Dict{VarLoc,Int}()),
    MemLeaf(LeafNode(1.0), Dict{VarLoc,Int}())))
mt5 = takeneg(mt4)
@assert mt5.domain == dom((:[1:1],))
@assert mt5.root.value.value == 0.0
mt6 = takepos(mt4)
@assert mt6.domain == dom((:[2:10],))
@assert mt6.root.value.value == 1.0


@assert flatten_signature(sig(())) == sig(())
@assert flatten_signature(sig((:t, :t))) == sig((:t, :t))
@assert flatten_signature(sig(:v)) == sig(:v)
# @assert flatten_signature(sig((:[1,2], (:v, :v), :v))) == sig((:[0,2], :t, :v))

@assert sig_vars(sig(:v)) == Set(([],))
@assert sig_vars(sig((:v,(:t,:v)))) == Set((Int[1], Int[2, 2]))

@assert trim(mt1) == mt1
@assert trim(mt1).domain == mt1.domain
@assert trim(mt1).root == mt1.root
@assert trim(mt2) == mt2
@assert trim(mt3) == mt3
@assert trim(mt1) != trim(mt2)
@assert trim(mt2) != trim(mt3)
@assert trim(mt4) == mt4
@assert trim(mt5) == mt5
@assert trim(mt6) == mt6


_mt7 = mt(dom((:[1,10], :t)), ps([1,1], 20, ml(0.0), ml(1.0)))
mt7 = MemTree(dom((:[1,10], :t)), PSplit([1,1], 20, MemLeaf(LeafNode(0.0)), MemLeaf(LeafNode(1.0))))
@assert _mt7 == mt7
_mt8 = mt(dom((:[1,10], :t)), ml(0.0))
mt8 = MemTree(dom((:[1,10], :t)), MemLeaf(LeafNode(0.0)))
@assert _mt8 == mt8
@assert trim(mt7) == mt8
_mt9 = mt(dom((:[1,10], :t)), ps([1,1], 0, ml(1.0), ml(0.0)))
mt9 = MemTree(dom((:[1,10], :t)), PSplit([1,1], 0, MemLeaf(1.0), MemLeaf(0.0)))
@assert mt9 == _mt9
@assert trim(mt9) == mt8

ts1 = ts([2], Dict(sig((:v,))=>ml(0.0), sig((:v,:v))=>ml(1.0)), ml(2.0))
m10 = mt(dom((:t, :t)), ts1)
m11 = mt(dom((:t, (:v,))), ts1)
m12 = mt(dom((:t, (:v, :v))), ts1)
m13 = mt(dom((:t, (:v, :v, :v))), ts1)
@assert trim(m10) == m10
@assert trim(m11) == mt(dom((:t, (:v,))), ml(0.0))

untrimmed_wm_1 = MemTree(Domain(SpecifiedTSig(Signature[PSig(1,5),UnspecifiedTSig(Set{Array{Signature,1}}())],Set{Array{Signature,1}}()),
                                LinRegion(LinBound[],0),Dict{Array{Int64,1},Int64}()),
                         PSplit([1,1],
                                2,
                                MemLeaf(LeafNode(0),Dict{Array{Int64,1},Int64}()),
                                PSplit([1,1],
                                       3,
                                       MemLeaf(LeafNode(0),Dict{Array{Int64,1},Int64}()),
                                       PSplit([1,1],
                                              4,
                                              MemLeaf(LeafNode(1),Dict{Array{Int64,1},Int64}()),
                                              MemLeaf(None(),Dict{Array{Int64,1},Int64}())))))
trimmed_wm_1 = trim(untrimmed_wm_1)
@assert untrimmed_wm_1 == trimmed_wm_1


ml1 = MemLeaf(unfoldboundary(BSPTree(rect_region([1.9, 0.9],[4.1, 3.1]), LeafNode(0.9))), Dict([1]=>2, [2]=>1))
m14 = MemTree(Domain(sig((:v, :v)), rect_region([1,2],[3,4]), Dict([1]=>1, [2]=>2)), ml1)
@assert trim(m14).root.value.value == 0.9
ml2 = MemLeaf(unfoldboundary(BSPTree(rect_region([1.0,2.0],[3.0,4.0]), LeafNode(1.0))), Dict([1]=>2, [2,1]=>1))
ts2 = TSplit([2], Dict(sig((:v,))=>ml2), MemLeaf(None(), Dict([1]=>1, [2,1]=>2)))
m15 = MemTree(Domain(sig((:v, :t)), rect_region([2.1],[3.9]), Dict([1]=>1)), ts2)
r15 = reorder(rect_region([1],[3]), [2, 1], 2)
ml3 = MemLeaf(unfoldboundary(BSPTree(r15, LeafNode(1.0))), Dict([1]=>1, [2,1]=>2))
ts3 = TSplit([2], Dict(sig((:v,))=>ml3), MemLeaf(None(), Dict([1]=>1)))
m16 = MemTree(m15.domain, ts3)
@assert m16==trim(m16)
@assert trim(m15) == m16

# @assert query(m16, sig((:v, (:v,)))) == MemTree(fix_dom_dims(Domain(sig((:v, (:v,))), m15.domain.reg, m15.domain.map)), ml3)
@assert query(m15, dom(([2,4], ([1,3],)))).root.value.value == 1.0

# querying a trimmed mem should be the same as querying the untrimmed version
# example from whole system test
untrimmed_wm_2 = MemTree(Domain(SpecifiedTSig(Signature[PSig(1,5),UnspecifiedTSig(Set{Array{Signature,1}}())],Set{Array{Signature,1}}()),
                                LinRegion(LinBound[],0),Dict{Array{Int64,1},Int64}()),
                         PSplit([1,1],
                                2,
                                MemLeaf(LeafNode(0),Dict{Array{Int64,1},Int64}()),
                                PSplit([1,1],
                                       3,
                                       MemLeaf(LeafNode(0),Dict{Array{Int64,1},Int64}()),
                                       PSplit([1,1],
                                              4,
                                              MemLeaf(LeafNode(1),Dict{Array{Int64,1},Int64}()),
                                              MemLeaf(None(),Dict{Array{Int64,1},Int64}())))))
trimmed_wm_2 = trim(untrimmed_wm_2)
@assert query(untrimmed_wm_2, untrimmed_wm_2.domain) == query(trimmed_wm_2, untrimmed_wm_2.domain)
f_sig = sig((:[4,4],(:v,:v)))
f_dom = Domain(f_sig, boundless_reg(2), standard_varmap(f_sig))
f_stage_sig = sig((:[2,2],(:[4,4],(:v,:v))))
f_stage_dom = Domain(f_stage_sig, boundless_reg(2), standard_varmap(f_stage_sig))
@assert query(untrimmed_wm_2, f_dom) == query(trimmed_wm_2, f_dom)
@assert query(untrimmed_wm_2, f_stage_dom) == query(trimmed_wm_2, f_stage_dom)
# a superset of f_stage_dom:
f_query_dom = Domain(SpecifiedTSig(Signature[PSig(2,2),
                                             SpecifiedTSig(Signature[PSig(1,5),
                                                                     UnspecifiedTSig(Set{Array{Signature,1}}())],
                                                           Set{Array{Signature,1}}())],
                                   Set{Array{Signature,1}}()),
                     LinRegion(LinBound[],0),Dict{Array{Int64,1},Int64}())
@assert intersection(f_stage_dom, f_query_dom) == f_stage_dom
@assert query(trimmed_wm_2, f_stage_dom) == query(trimmed_wm_2, intersection(f_stage_dom, f_query_dom))
@assert query(trimmed_wm_2, f_stage_dom) == query(query(trimmed_wm_2, f_query_dom), f_stage_dom)
@assert query(trimmed_wm_2, f_stage_dom) == query(query(trimmed_wm_2, f_stage_dom), f_query_dom)
@assert query(query(trimmed_wm_2, f_stage_dom), f_query_dom) == query(query(trimmed_wm_2, f_query_dom), f_stage_dom)
@assert query(query(trimmed_wm_2, f_stage_dom), f_query_dom) == query(trimmed_wm_2, intersection(f_query_dom, f_stage_dom))
untrimmed_wm_3 =  MemTree(Domain(SpecifiedTSig(Signature[PSig(1,5),UnspecifiedTSig(Set{Array{Signature,1}}())],Set{Array{Signature,1}}()),LinRegion(LinBound[],0),Dict{Array{Int64,1},Int64}()),PSplit([1,1],2,TSplit([2],Dict{SpecifiedTSig,MemNode}(SpecifiedTSig(Signature[PSig(4,4),UnspecifiedTSig(Set{Array{Signature,1}}()),VSig()],Set{Array{Signature,1}}())=>TSplit([2,2],Dict{SpecifiedTSig,MemNode}(SpecifiedTSig(Signature[VSig(),VSig()],Set{Array{Signature,1}}())=>MemLeaf(LeafNode(0),Dict([2,2,2]=>2,[2,2,1]=>1,[2,3]=>3))),MemLeaf(LeafNode(0),Dict([2,3]=>1)))),MemLeaf(LeafNode(0),Dict{Array{Int64,1},Int64}())),PSplit([1,1],3,TSplit([2],Dict{SpecifiedTSig,MemNode}(SpecifiedTSig(Signature[PSig(4,4),UnspecifiedTSig(Set{Array{Signature,1}}())],Set{Array{Signature,1}}())=>TSplit([2,2],Dict{SpecifiedTSig,MemNode}(SpecifiedTSig(Signature[VSig(),VSig()],Set{Array{Signature,1}}())=>MemLeaf(SplitNode(LinSplit([1.0,-0.0],1.0),LeafNode(0.0),SplitNode(LinSplit([-1.0,-0.0],-2.0),SplitNode(LinSplit([-0.0,1.0],1.0),LeafNode(0.0),SplitNode(LinSplit([-0.0,-1.0],-2.0),LeafNode(0.0),SplitNode(LinSplit([1.0,-0.0],3.0),LeafNode(0.0),SplitNode(LinSplit([-1.0,-0.0],-4.0),LeafNode(0.0),LeafNode(1.0))))),SplitNode(LinSplit([-0.0,1.0],3.0),LeafNode(0.0),SplitNode(LinSplit([-0.0,-1.0],-4.0),LeafNode(0.0),LeafNode(1.0))))),Dict([2,2,2]=>2,[2,2,1]=>1))),MemLeaf(LeafNode(0),Dict{Array{Int64,1},Int64}()))),MemLeaf(LeafNode(0),Dict{Array{Int64,1},Int64}())),PSplit([1,1],4,TSplit([2],Dict{SpecifiedTSig,MemNode}(SpecifiedTSig(Signature[PSig(5,5),UnspecifiedTSig(Set{Array{Signature,1}}())],Set{Array{Signature,1}}())=>TSplit([2,2],Dict{SpecifiedTSig,MemNode}(SpecifiedTSig(Signature[VSig(),VSig(),VSig()],Set{Array{Signature,1}}())=>PSplit([2,1,1],6,PSplit([2,1,1],5,MemLeaf(LeafNode(1),Dict{Array{Int64,1},Int64}()),MemLeaf(LeafNode(1),Dict{Array{Int64,1},Int64}())),MemLeaf(LeafNode(1),Dict{Array{Int64,1},Int64}()))),MemLeaf(LeafNode(1),Dict{Array{Int64,1},Int64}()))),MemLeaf(LeafNode(1),Dict{Array{Int64,1},Int64}())),MemLeaf(None(),Dict{Array{Int64,1},Int64}())))))
trimmed_wm_3 = trim(untrimmed_wm_3)
trimmed_wm_3 == untrimmed_wm_3
@assert query(untrimmed_wm_3, untrimmed_wm_3.domain) == query(trimmed_wm_3, untrimmed_wm_3.domain)
@assert query(untrimmed_wm_3, f_dom) == query(trimmed_wm_3, f_dom)
@assert query(untrimmed_wm_3, f_stage_dom) == query(trimmed_wm_3, f_stage_dom)
@assert query(trimmed_wm_3, f_stage_dom) == query(trimmed_wm_3, intersection(f_query_dom, f_stage_dom))
@assert query(trimmed_wm_3, f_stage_dom) == query(query(trimmed_wm_3, f_query_dom), f_stage_dom)
@assert query(trimmed_wm_3, f_stage_dom) == query(query(trimmed_wm_3, f_stage_dom), f_query_dom)
@assert query(query(trimmed_wm_3, f_stage_dom), f_query_dom) == query(query(trimmed_wm_3, f_query_dom), f_stage_dom)
@assert query(query(trimmed_wm_3, f_stage_dom), f_query_dom) == query(trimmed_wm_3, intersection(f_query_dom, f_stage_dom))





m17 = MemTree(dom(:t), MemLeaf(1.0))
m18 = MemTree(dom(:t), TSplit([], Dict(sig((:v,))=>MemLeaf(1.0, Dict([1]=>1))), MemLeaf(1.0)))
@assert epsilonequal(m17, m18)
@assert epsilonequal(m18, m17)
@assert !epsilonequal(m18, mt(dom(:t), ts(Int[], Dict(sig((:v,))=>ml(1.0)), ml(0.0))))
@assert !epsilonequal(mt(dom(:t), ts(Int[], Dict(sig((:v,))=>ml(0.0)), ml(1.0))), m18)
@assert epsilonequal(m18, mt(dom(:e), ml(0.0)))
@assert epsilonequal(mt(dom(:e), ml(0.0)), m17)
@assert epsilonequal(mt(dom((:[0,10], :t)), ps([1], 3, ml(1.0), ml(1.0))), m18)
@assert epsilonequal(m18, mt(dom((:[0,10], :t)), ps([1], 3, ml(1.0), ml(1.0))))

# Testing that epsilonequal gets previous tests with == right
@assert epsilonequal(query(m16, sig((:v, (:v,)))), MemTree(Domain(sig((:v, (:v,))), m15.domain.reg, m15.domain.map), ml3))
@assert epsilonequal(MemTree(Domain(sig((:v, (:v,))), m15.domain.reg, m15.domain.map), ml3), query(m16, sig((:v, (:v,)))))
@assert epsilonequal(trim(m15), m16)
@assert epsilonequal(m16, trim(m15))
@assert epsilonequal(m16,m15)
@assert epsilonequal(m15,m16)
@assert epsilonequal(trim(m11), mt(dom((:t, (:v,))), ml(0.0)))
@assert epsilonequal(mt(dom((:t, (:v,))), ml(0.0)), trim(m11))
@assert epsilonequal(trim(m10), m10)
@assert epsilonequal(mt9, mt8)
@assert epsilonequal(mt8, mt9)
@assert epsilonequal(mt9, _mt9)

rulespace_domain_2 = Domain(SpecifiedTSig(Signature[PSig(1,3),SpecifiedTSig(Signature[VSig(),VSig(),PSig(1,9223372036854775807),VSig()],Set{Array{Signature,1}}())],Set{Array{Signature,1}}()),LinRegion(LinBound[],3),Dict([2,1]=>1,[2,2]=>2,[2,4]=>3))
m19 = mt(rulespace_domain_2, ps([1,1], 1, ml(0.0), ps([1,1], 2, ml(0.0), ml(1.0))))
m20 = mt(rulespace_domain_2, ps([1,1], 1, ml(1.0), ps([1,1], 2, ml(0.0), ml(1.0))))
@assert epsilonequal(m19, m20)

#insert
# Testing different types for the root split of the source.
@assert epsilonequal(mt(dom(:t), ml(1.0)), insert(mt(dom((:[0:10], :v)), ps([1,1], 3, ml(1.0), ml(1.0))), mt(dom(:t), ml(1.0))))
@assert !epsilonequal(mt(dom(:t), ml(1.0)), insert(mt(dom((:[0:10], :v)), ps([1,1], 3, ml(1.0), ml(1.0))), mt(dom(:t), ml(2.0))))
@assert !epsilonequal(mt(dom(:t), ml(1.0)), insert(mt(dom((:[0:10], :v)), ps([1,1], 3, ml(1.0), ml(2.0))), mt(dom(:t), ml(1.0))))
@assert !epsilonequal(mt(dom(:t), ml(1.0)), insert(mt(dom((:[0:10], :v)), ps([1,1], 3, ml(2.0), ml(1.0))), mt(dom(:t), ml(1.0))))
@assert epsilonequal(mt(dom(:t), ml(1.0)), insert(mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(1.0))), mt(dom(:t), ml(1.0))))
@assert !epsilonequal(mt(dom(:t), ml(1.0)), insert(mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(2.0)), ml(1.0))), mt(dom(:t), ml(1.0))))
@assert !epsilonequal(mt(dom(:t), ml(1.0)), insert(mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(2.0))), mt(dom(:t), ml(1.0))))
@assert !epsilonequal(mt(dom(:t), ml(1.0)), insert(mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(1.0))), mt(dom(:t), ml(2.0))))
@assert epsilonequal(mt(dom(:t), ml(1.0)), insert(mt(dom((:[0:10], :t)), ml(1.0)), mt(dom(:t), ml(1.0))))
@assert !epsilonequal(mt(dom(:t), ml(1.0)), insert(mt(dom((:[0:10], :t)), ml(2.0)), mt(dom(:t), ml(1.0))))
@assert !epsilonequal(mt(dom(:t), ml(1.0)), insert(mt(dom((:[0:10], :t)), ml(1.0)), mt(dom(:t), ml(2.0))))
# Testing insertions with different target root type.
@assert epsilonequal(mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(1.0))), insert(mt(dom((:[0:10], (:v, :v))), ml(1.0)), mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(1.0)))))
@assert !epsilonequal(mt(dom((:[0:10], :t)), ps([1,1], 3, ml(10.0), ml(1.0))), insert(mt(dom((:[0:10], (:v, :v))), ml(1.0)), mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(1.0)))))
@assert !epsilonequal(mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(10.0))), insert(mt(dom((:[0:10], (:v, :v))), ml(1.0)), mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(1.0)))))
@assert !epsilonequal(mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(1.0))), insert(mt(dom((:[0:10], (:v, :v))), ml(10.0)), mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(1.0)))))
@assert !epsilonequal(mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(1.0))), insert(mt(dom((:[0:10], (:v, :v))), ml(1.0)), mt(dom((:[0:10], :t)), ps([1,1], 3, ml(10.0), ml(1.0)))))
@assert !epsilonequal(mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(1.0))), insert(mt(dom((:[0:10], (:v, :v))), ml(1.0)), mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(10.0)))))
@assert epsilonequal(mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(1.0))), insert(mt(dom((:[0:10], (:v, :v))), ml(1.0)), mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(1.0)))))
@assert !epsilonequal(mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(10.0)), ml(1.0))), insert(mt(dom((:[0:10], (:v, :v))), ml(1.0)), mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(1.0)))))
@assert !epsilonequal(mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(10.0))), insert(mt(dom((:[0:10], (:v, :v))), ml(1.0)), mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(1.0)))))
@assert !epsilonequal(mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(1.0))), insert(mt(dom((:[0:10], (:v, :v))), ml(10.0)), mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(1.0)))))
@assert !epsilonequal(mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(1.0))), insert(mt(dom((:[0:10], (:v, :v))), ml(1.0)), mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(10.0)), ml(1.0)))))
@assert !epsilonequal(mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(1.0))), insert(mt(dom((:[0:10], (:v, :v))), ml(1.0)), mt(dom((:[0:10], :t)), ts([2], Dict(sig((:v,))=>ml(1.0)), ml(10.0)))))
# TODO Testing insertions with different source signature types.
# TODO Testing insertions with different source signature types.
# TODO Testing insertions with different target signature types.
@assert epsilonequal(mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(1.0))), insert(mt(dom((:[0:10], :t)), ml(1.0)), mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(1.0)))))
@assert epsilonequal(mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(1.0))), insert(mt(dom(:t), ml(1.0)), mt(dom((:[0:10], :t)), ps([1,1], 3, ml(1.0), ml(1.0)))))
# Testing inserting things in different orders.
# The domains of source1 and source2 are mutually exclusive, but source3 partially overlaps both.
source1 = mt(dom((:[1:5], :t)), ps([1,1], 3, ml(2.0), ml(3.0)))
source2 = mt(dom((:[6:10], :t)), ts([2], Dict(sig((:v,))=>ml(4.0)), ml(5.0)))
source3 = mt(dom((:[0:10], (:v, :v))), ml(6.0))
target1 = mt(dom(:t), ml(1.0))
target2 = mt(dom((:[1:10], :t)), ml(1.0))
target3 = mt(dom((:[2:6], :t)), ml(1.0))
target4 = mt(dom((:[2:6], (:v, :v))), ml(1.0))
@assert epsilonequal(insert(source1, insert(source2, target1)), insert(source2, insert(source1, target1)))
@assert !epsilonequal(insert(source1, insert(source3, target1)), insert(source3, insert(source1, target1)))
@assert !epsilonequal(insert(source2, insert(source3, target1)), insert(source3, insert(source2, target1)))
order1 = insert(source1, insert(source2, target1))
order2 = insert(source2, insert(source1, target1))
@assert epsilonequal(order1, source1)
@assert epsilonequal(source1, order1)
@assert epsilonequal(source2, order1)
@assert epsilonequal(order1, source2)
@assert epsilonequal(order2, source1)
@assert epsilonequal(source1, order2)
@assert epsilonequal(source2, order2)
@assert epsilonequal(order2, source2)
@assert epsilonequal(insert(source1, insert(source2, target2)), insert(source2, insert(source1, target2)))
@assert !epsilonequal(insert(source1, insert(source3, target2)), insert(source3, insert(source1, target2)))
@assert !epsilonequal(insert(source2, insert(source3, target2)), insert(source3, insert(source2, target2)))
@assert epsilonequal(insert(source1, insert(source2, target3)), insert(source2, insert(source1, target3)))
@assert !epsilonequal(insert(source1, insert(source3, target3)), insert(source3, insert(source1, target3)))
@assert !epsilonequal(insert(source2, insert(source3, target3)), insert(source3, insert(source2, target3)))
@assert epsilonequal(insert(source1, insert(source2, target4)), insert(source2, insert(source1, target4)))
@assert !epsilonequal(insert(source1, insert(source3, target4)), insert(source3, insert(source1, target4)))
@assert !epsilonequal(insert(source2, insert(source3, target4)), insert(source3, insert(source2, target4)))
# TODO Test something involving a nontrivial BSPTree insertion. Test whether the variable ordering at MemLeafs is working.

# The following example was encountered in whole-system testing.
working_mem_state_1 = MemTree(Domain(SpecifiedTSig(Signature[PSig(1:5),UnspecifiedTSig(Set{Array{Signature,1}}())],
                                                   Set{Array{Signature,1}}()),
                                     LinRegion(LinBound[],0),Dict{Array{Int64,1},Int64}()),
                              PSplit([1,1],2,MemLeaf(LeafNode(0),Dict{Array{Int64,1},Int64}()),PSplit([1,1],3,MemLeaf(LeafNode(0),Dict{Array{Int64,1},Int64}()),MemLeaf(LeafNode(1),Dict{Array{Int64,1},Int64}()))))
rule_output_1 = MemTree(Domain(SpecifiedTSig(Signature[PSig(1:1),SpecifiedTSig(Signature[PSig(4:4),SpecifiedTSig(Signature[VSig(),VSig()],Set{Array{Signature,1}}()),VSig()],Set{Array{Signature,1}}())],
                                             Set{Array{Signature,1}}()),
                               LinRegion(LinBound[],0),Dict{Array{Int64,1},Int64}()),
                        MemLeaf(None(),Dict([2,2,2]=>2,[2,2,1]=>1,[2,3]=>3)))
# Since the rule output has no contents in the memleaf, insertion should not change any values.
@assert epsilonequal(working_mem_state_1, insert(rule_output_1, working_mem_state_1))

test_domain = Domain(SpecifiedTSig(Signature[PSig(1,1),SpecifiedTSig(Signature[VSig(),VSig(),VSig(),VSig(),VSig()],Set{Array{Signature,1}}())]),
                            LinRegion(LinBound[],0),
                            Dict{VarLoc, Int64}())
csts8_clone = MemTree(test_domain,
                      MemLeaf(SplitNode(LinSplit([-1.0,-0.0,-0.0,-0.0,-0.0],-5.0),
                                        LeafNode(0.0),
                                        LeafNode(1.0)),
                              Dict{VarLoc,Int64}([2,1]=>1,[2,2]=>2,[2,5]=>5,[2,4]=>4,[2,3]=>3)))
csts8_simplified = MemTree(test_domain,
                      MemLeaf(SplitNode(LinSplit([-1.0,0.0,0.0,0.0,0.0],-5.0),
                                        LeafNode(0.0),
                                        LeafNode(1.0)),
                              Dict{VarLoc,Int64}([2,1]=>1,[2,2]=>2,[2,5]=>5,[2,4]=>4,[2,3]=>3)))
@assert epsilonequal(csts8_simplified, csts8_simplified)
@assert epsilonequal(csts8_clone, csts8_clone)

# Testing the various reorder functions.

# Reordering on varlocs alone.

@assert reorder(Dict([2]=>[3]), [2]) == [3]
@assert reorder(Dict([2]=>[3]), [2, 1]) == [3, 1]
@assert reorder(Dict([2]=>[3]), [1]) == [1]
@assert reorder(Dict([2]=>[3, 1]), [2]) == [3, 1]
@assert reorder(Dict([2]=>[3], [2, 1]=>[1]), [2, 1]) == [3, 1]
@assert reorder(Dict([2]=>[3], Int[]=>[4,1,1]), [2]) == [4,1,1,2]

# Signature reordering.

@assert reorder(Dict([1]=>[2], [2]=>[3], [3]=>[1]), sig((:t, :t, :t)), sig(((:t, :t), (:v,), (:[0:10],)))) == sig(((:[0:10],), (:t, :t), (:v,)))
@assert reorder(Dict([1, 1]=>[2, 2], [1, 2]=>[2, 1], [2]=>[3], [3]=>[1]), sig((:t, (:v, :t), :t)),
              sig(((:t, :v), (:v,), (:[0:10],)))) == sig(((:[0:10],), (:v, :t), (:v,)))

# Domain reordering.

@assert reorder(Dict([1]=>[2], [2]=>[3], [3]=>[1]),
        sig((:v, :[1:2], :[1:2])),
        dom((:[1:5], :[1:4], :v))) == dom((:v, :[1:2], :[1:2]))

# Memnode and memtree reordering.

@assert trim(reorder(Dict([1]=>[2, 1], [2, 1]=>[2, 2], [2, 2]=>[1]),
        sig((:v, (:t, :[1:10]))),
        mt(dom((:t, (:[1:10], :v))),
           ps([2, 1, 1], 5,
              ts([1], Dict(sig((:v,))=>ml(1.0), sig((:t, :t))=>ml(2.0)), ml(3.0)),
              ml(4.0))))) ==
        mt(dom((:v, (:t, :[1:10]))),
           ps([2, 2, 1], 5,
              ts([2,1], Dict(sig((:v,))=>ml(1.0), sig((:t, :t))=>ml(2.0)), ml(3.0)),
              ml(4.0)))

@assert trim(mt(dom((:v, :[1:10])), ts(Int[], Dict(sig((:v, :[1:10]))=>ml(1.0)), ml(2.0)))) == mt(dom((:v, :[1:10])), ml(1.0))
@assert trim(mt(dom((:v, :[1:10])), ts(Int[], Dict(sig((:v, :[1:11]))=>ml(1.0)), ml(2.0)))) == mt(dom((:v, :[1:10])), ml(1.0))
@assert trim(mt(dom((:v, :[1:10])), ts(Int[], Dict(sig((:v, :[1:11]))=>ml(1.0), sig((:v, :[1:12]))=>ml(1.0)), ml(2.0)))) == mt(dom((:v, :[1:10])), ml(1.0))

# Memarithmetic testing. Running through each function/case in the macro.

# MemNode, Number
@assert mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(4.0)), ml(3.0))).root - 1.0 == mt(dom((:[0,10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(3.0)), ml(2.0))).root
@assert mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(4.0), ml(5.0))).root - 1.0 == mt(dom((:[0,10], :t, :v)), ps([1,1], 5, ml(3.0), ml(4.0))).root
@assert mt(dom((:[0:10], :v)), ml(2.0)).root - 1.0 == mt(dom((:[0,10], :v)), ml(1.0)).root
@assert mt(dom((:[0:10], :v)), ml(2.0)).root + 2.0 == mt(dom((:[0,10], :v)), ml(4.0)).root
@assert mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(4.0)), ml(3.0))).root - 1 == mt(dom((:[0,10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(3.0)), ml(2.0))).root
@assert mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(4.0), ml(5.0))).root - 1 == mt(dom((:[0,10], :t, :v)), ps([1,1], 5, ml(3.0), ml(4.0))).root
@assert mt(dom((:[0:10], :v)), ml(2.0)).root - 1 == mt(dom((:[0,10], :v)), ml(1.0)).root
@assert mt(dom((:[0:10], :v)), ml(2.0)).root + 2 == mt(dom((:[0,10], :v)), ml(4.0)).root
# Number, MemNode
@assert 1.0 - mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(4.0)), ml(3.0))).root == mt(dom((:[0,10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(-3.0)), ml(-2.0))).root
@assert 1.0 - mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(4.0), ml(5.0))).root == mt(dom((:[0,10], :t, :v)), ps([1,1], 5, ml(-3.0), ml(-4.0))).root
@assert 1 - mt(dom((:[0:10], :v)), ml(2.0)).root == mt(dom((:[0,10], :v)), ml(-1.0)).root
@assert 2 + mt(dom((:[0:10], :v)), ml(2.0)).root == mt(dom((:[0,10], :v)), ml(4.0)).root
# The same tests, but now combining trees.
@assert mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(4.0)), ml(3.0))) - 1.0 == mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(3.0)), ml(2.0)))
@assert mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(4.0), ml(5.0))) - 1.0 == mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(3.0), ml(4.0)))
@assert mt(dom((:[0:10], :v)), ml(2.0)) - 1.0 == mt(dom((:[0:10], :v)), ml(1.0))
@assert mt(dom((:[0:10], :v)), ml(2.0)) + 2.0 == mt(dom((:[0:10], :v)), ml(4.0))
@assert mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(4.0)), ml(3.0))) - 1 == mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(3.0)), ml(2.0)))
@assert mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(4.0), ml(5.0))) - 1 == mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(3.0), ml(4.0)))
@assert mt(dom((:[0:10], :v)), ml(2.0)) - 1 == mt(dom((:[0:10], :v)), ml(1.0))
@assert mt(dom((:[0:10], :v)), ml(2.0)) + 2 == mt(dom((:[0:10], :v)), ml(4.0))
@assert 1.0 - mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(4.0)), ml(3.0))) == mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(-3.0)), ml(-2.0)))
@assert 1.0 - mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(4.0), ml(5.0))) == mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(-3.0), ml(-4.0)))
@assert 1 - mt(dom((:[0:10], :v)), ml(2.0)) == mt(dom((:[0:10], :v)), ml(-1.0))
@assert 2 + mt(dom((:[0:10], :v)), ml(2.0)) == mt(dom((:[0:10], :v)), ml(4.0))
# Memtree combination.
@assert epsilonequal(mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(4.0)), ml(3.0))) - mt(dom((:[4:6], (:v, :v), :v)), ml(1.0)),
  mt(dom((:[4:6], (:v, :v), :v)), ts([2], Dict(sig((:v, :v))=>ml(3.0)), ml(2.0))))
@assert epsilonequal(mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(4.0), ml(5.0))) - mt(dom((:[4:6], (:v, :v), :v)), ml(1.0)),
  mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(3.0), ml(4.0))))
@assert epsilonequal(mt(dom((:[0:10], :v)), ml(2.0)) - mt(dom((:[4:6], (:v, :v), :v)), ml(1.0)),
  mt(dom((:[0:10], :v)), ml(1.0)))
@assert epsilonequal(mt(dom((:[0:10], :v)), ml(2.0)) + mt(dom((:[4:6], (:v, :v), :v)), ml(2.0)),
  mt(dom((:[0:10], :v)), ml(4.0)))
@assert epsilonequal(mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(4.0)), ml(3.0)))- mt(dom((:[4:6], (:v, :v), :v)), ml(1.0)),
  mt(dom((:[0,10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(3.0)), ml(2.0))))
@assert epsilonequal(mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(4.0), ml(5.0))) - mt(dom((:[4:6], (:v, :v), :v)), ml(1.0)),
  mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(3.0), ml(4.0))))
@assert epsilonequal(mt(dom((:[0:10], :v)), ml(2.0)) - mt(dom((:[4:6], (:v, :v), :v)), ml(1.0)),
  mt(dom((:[0:10], :v)), ml(1.0)))
@assert epsilonequal(mt(dom((:[0:10], :v)), ml(2.0)) + mt(dom((:[4:6], (:v, :v), :v)), ml(2.0)),
  mt(dom((:[0:10], :v)), ml(4.0)))
@assert epsilonequal(mt(dom((:[4:6], (:v, :v), :v)), ml(1.0)) - mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(4.0)), ml(3.0))),
  mt(dom((:[0:10], :t, :v)), ts([2], Dict(sig((:v, :v))=>ml(-3.0)), ml(-2.0))))
@assert epsilonequal(mt(dom((:[4:6], (:v, :v), :v)), ml(1.0)) - mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(4.0), ml(5.0))),
  mt(dom((:[0:10], :t, :v)), ps([1,1], 5, ml(-3.0), ml(-4.0))))
@assert epsilonequal(mt(dom((:[4:6], (:v, :v), :v)), ml(1.0)) - mt(dom((:[0:10], :v)), ml(2.0)), mt(dom((:[0:10], :v)), ml(-1.0)))
@assert epsilonequal(mt(dom((:[4:6], (:v, :v), :v)), ml(2.0)) + mt(dom((:[0:10], :v)), ml(2.0)), mt(dom((:[0:10], :v)), ml(4.0)))

# MemLeaf, MemTree case. Mainly testing the reordering code.
# TODO

# Memsummary testing.
# TODO



so_tree = mt(dom(([0,2], :[1:2], ([0,2], :[0:10], [0,2]))), ps([2,1], 2, ml(1/2), ml(0.0)))
@assert epsilonequal(so_tree, normalize(so_tree)*44)
remap = Dict([1,1]=>[1,1], [1,2]=>[1,2], [2,2]=>[2,2])
remrem = remap_remap(remap, [2,1])
@assert remrem == Dict([1,1]=>[1,1], [1,2]=>[1,2], [2,1]=>[2,2])
(just_so, rem) = integrate_fo(so_tree)
@assert rem == Dict([1]=>[2], [2,1]=>[3,2])
normalized = normalize_fo(so_tree)
@assert epsilonequal(normalized*4, so_tree)


susd = Domain(SpecifiedTSig(Signature[PSig(UnitRange{Int64}[7:7]), SpecifiedTSig(Signature[PSig(UnitRange{Int64}[0:100]), PSig(UnitRange{Int64}[0:100]), VSig()], Set(Array{Signature,1}[[PSig(UnitRange{Int64}[0:4611686018427387903]), PSig(UnitRange{Int64}[0:4611686018427387903]), VSig()]]))], Set{Array{Signature,1}}()), LinRegion(LinBound[], 1), Dict([2, 3] => 1))
@assert !sig_allowed(susd.sig)
