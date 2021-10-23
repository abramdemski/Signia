
include("trees.jl")

using Profile

using Random

srand(x) = Random.seed!(x)

# seed the random number generator to ensure consistent results
srand(1)

# Testing hperreal numbers.

@assert Hyper(1.0,-1)==Hyper(1.0,-1)
@assert Hyper(1.0,0)==1.0
@assert Hyper(1.0,0) - 1 == Hyper(0.0,0)
@assert Hyper(1,1) == Hyper(1.0,1)
@assert Hyper(Hyper(2,1),2) == Hyper(2.0,3)
@assert convert(Hyper,Hyper(1.0,1)) == Hyper(1.0,1)
@assert simplify(Hyper(1.0,1)) !== 1.0
@assert simplify(Hyper(1.0,0)) == 1.0
@assert simplify(Hyper(0.0,1)) !== 1.0
@assert simplify(Hyper(0.0,1)) == 0.0
@assert simplify(1) == 1
@assert Hyper(1.0,1) + 1 == Hyper(1.0,1)
@assert Hyper(1.0,-1) + 1 == 1
@assert Hyper(1.0,0) + 1 == 2
@assert Hyper(1.0,1) - 1 == Hyper(1.0,1)
@assert Hyper(1.0,-1) - 1 == 1
@assert Hyper(1.0,0) - 1 == 0
@assert Hyper(2.0,1) * Hyper(2.0,0) == Hyper(4.0,1)
@assert Hyper(2.0,1) * Hyper(2.0,1) == Hyper(4.0,2)
@assert Hyper(2.0,1) * Hyper(2.0,-1) == 4.0
@assert 4.0 / Hyper(2.0,-1) == Hyper(2.0,1)
@assert Hyper(2.0,1) < Hyper(4.0,1)
@assert Hyper(2.0,1) < Hyper(4.0,2)
@assert Hyper(2.0,1) < Hyper(1.0,2)
@assert max(Hyper(2.0,1), Hyper(4.0,1)) == Hyper(4.0,1)
@assert max(Hyper(2.0,1), Hyper(4.0,2)) == Hyper(4.0,2)
@assert max(Hyper(2.0,1), Hyper(1.0,2)) == Hyper(1.0,2)
@assert max(Hyper(4.0,1), Hyper(2.0,1)) == Hyper(4.0,1)
@assert max(Hyper(4.0,2), Hyper(2.0,1)) == Hyper(4.0,2)
@assert max(Hyper(1.0,2), Hyper(2.0,1)) == Hyper(1.0,2)
@assert min(Hyper(2.0,1), Hyper(4.0,1)) == Hyper(2.0,1)
@assert min(Hyper(2.0,1), Hyper(4.0,2)) == Hyper(2.0,1)
@assert min(Hyper(2.0,1), Hyper(1.0,2)) == Hyper(2.0,1)
@assert min(Hyper(4.0,1), Hyper(2.0,1)) == Hyper(2.0,1)
@assert min(Hyper(4.0,2), Hyper(2.0,1)) == Hyper(2.0,1)
@assert min(Hyper(1.0,2), Hyper(2.0,1)) == Hyper(2.0,1)

@assert simplify(Hyper(1.0,1)) == Hyper(1.0,1)
@assert simplify(Hyper(1.0,0)) == 1.0
@assert epsilonequal(Hyper(1.0,0), 1.0)
@assert simplify(Hyper(Inf, 0)) == Inf
@assert simplify(Hyper(Inf, 1)) == Inf
@assert simplify(Hyper(Inf, -1)) == Inf
@assert simplify(Hyper(-Inf, 1)) == -Inf
@assert simplify(Hyper(-Inf, 0)) == -Inf
@assert simplify(Hyper(-Inf, -1)) == -Inf

@assert epsilonequal(Inf, Inf)
@assert epsilonequal(-Inf, -Inf)
@assert !epsilonequal(-Inf, Inf)
@assert epsilonequal(Inf, Inf+1)
@assert Inf == Inf
@assert -Inf == -Inf
@assert Inf != -Inf
@assert -Inf < Inf
@assert Hyper(1,1) < Inf
@assert Hyper(30,30) < Inf
@assert -Inf < Hyper(30,30)
@assert -Inf < Hyper(-30,30)
@assert -Inf < Hyper(30,-30)
@assert !epsilonequal(Inf, Hyper(1,1))

@assert max(Inf, Hyper(1,20)) == Inf
@assert epsilonequal(max(Inf, Hyper(Inf,1)), Inf)
@assert epsilonequal(min(-Inf, Hyper(-Inf, 1)), -Inf)

@assert Hyper(3,4)^2 == Hyper(9,8)

# test regsat and regvalid.
reg1 = rect_region([1,1,1],[2,2,2])
reg2 = rect_region([1,1,1],[1,1,1])
reg3 = rect_region([1,1,1],[0,0,0])
bound1 = LinBound(LinSplit([1,1,1],3), false)
reg4 = LinRegion(vcat(reg1.bounds, bound1), 3)
reg5 = LinRegion(vcat(reg2.bounds, bound1), 3)
reg6 = LinRegion(vcat(reg3.bounds, bound1), 3)
@assert regsat(makemodel(reg1))
@assert regvalid(reg1)
@assert regsat(makemodel(reg2))
@assert !regvalid(reg2)
@assert !regsat(makemodel(reg3))
@assert !regvalid(reg3)
@assert regsat(makemodel(reg4))
@assert !regvalid(reg4)
@assert regsat(makemodel(reg5))
@assert !regvalid(reg5)
@assert !regsat(makemodel(reg6))
@assert !regvalid(reg6)

# test regvalid with all negative constraints.
bound2 = LinBound(LinSplit([1.0, 0.0],1.0), false) # x strictly below 1
bound3 = LinBound(LinSplit([-1.0, 0.0],-1.0), false) # -x strictly below -1; so x>1
reg7 = LinRegion([bound1, bound2, bound3], 3)
@assert regsat(makemodel(reg7))
@assert !regvalid(reg7)
# test regvalid with all positive constraints.
bound4 = LinBound(LinSplit([1.0, 0.0],1.0), true) # x>=1
bound5 = LinBound(LinSplit([-1.0, 0.0],0.0), true) # -x>=0, so x<=0
bound6 = LinBound(LinSplit([1.0, 1.0],0.0), true) # the sum is positive
reg8 = LinRegion([bound4, bound5, bound6], 3)
@assert !regsat(makemodel(reg8))
@assert !regvalid(reg8)

# test region equality.
@assert rect_region([1,1,1],[2,2,2]).bounds == rect_region([1,1,1],[2,2,2]).bounds
@assert rect_region([1,1,1],[2,2,2]) !== rect_region([1,2,3],[4,5,6])
# test regvalid.
rr0 = rect_region([1,1,1],[2,2,2])
rs = rect_split(2,1.5,3)
@assert takepos(rr0,rs) == rect_region([1,1.5,1],[2,2,2])
@assert regvalid(rr0)
@assert !(regvalid(rect_region([2, 2, 2], [1, 1, 1])))
rr1 = rect_region([0, 0], [1, 1])
rr2 = rect_region([2, 0], [3, 1])
@assert !(regvalid(intersection(rr1, rr2)))
rr3 = rect_region([0, 0], [2, 2])
@assert regvalid(intersection(rr1, rr3))

for i=1:50
  @assert regvalid(randomrect(10))
end

for i=1:10
  @assert regvalid(randomrect())
end

r1 = LinRegion([LinBound(LinSplit([0.0],1.0),true)],1)
@assert !regvalid(r1)
@assert trim_region(r1)==r1
r2 = LinRegion([LinBound(LinSplit([0.0],1.0),false)],1)
@assert regvalid(r2)
@assert trim_region(r2) == LinRegion(LinBound[],1)
r3 = LinRegion([LinBound(LinSplit([0.0],0.0),true)],1)
@assert regvalid(r3)
r4 = LinRegion([LinBound(LinSplit([0.0],0.0),false)],1)
@assert !regvalid(r4)
r5 = LinRegion([LinBound(LinSplit([0.0],-1.0),true)],1)
@assert regvalid(r5)
r6 = LinRegion([LinBound(LinSplit([],-1.0),true)],1)
@assert regvalid(r6)
@assert trim_region(r6) == boundless_reg(1)
r7 = LinRegion([LinBound(LinSplit([1.0],1.0),true),LinBound(LinSplit([1.0],1.0),false)],1)
@assert !regvalid(r7)
r8 = LinRegion([LinBound(LinSplit([1.0],1.0),true),LinBound(LinSplit([-1.0],-1.0),true)],1)
@assert regvalid(r8)
r9 = LinRegion([LinBound(LinSplit([1.0],1.0),true),LinBound(LinSplit([-1.0],-1.0),false)],1)
@assert regvalid(r9)
r10 = LinRegion([LinBound(LinSplit([1.0],1.0),false),LinBound(LinSplit([-1.0],-1.0),false)],1)
@assert !regvalid(r10)


testree_a = BSPTree(LinRegion(LinBound[],5),SplitNode(LinSplit([-1.0,0.0,0.0,0.0,0.0],-5.0),LeafNode(0.0),LeafNode(1.0)))
@assert epsilonequal(testree_a, testree_a)
testree_b = takepos(testree_a)
@assert epsilonequal(testree_a, testree_b)
@assert epsilonequal(testree_b, testree_a)
@assert epsilonequal(testree_b, testree_b)
testree_c = takeneg(testree_a)
@assert epsilonequal(testree_a, testree_c)
@assert epsilonequal(testree_c, testree_a)
@assert epsilonequal(testree_c, testree_c)
@assert epsilonequal(testree_b, testree_c)
@assert epsilonequal(testree_c, testree_b)
@assert regvalid(intersection(testree_a.boundary, testree_a.boundary))
@assert regvalid(intersection(testree_a.boundary, testree_b.boundary))
@assert regvalid(intersection(testree_b.boundary, testree_a.boundary))
@assert regvalid(intersection(testree_a.boundary, testree_c.boundary))
@assert regvalid(intersection(testree_c.boundary, testree_a.boundary))
@assert !regvalid(intersection(testree_b.boundary, testree_c.boundary))
@assert !regvalid(intersection(testree_c.boundary, testree_b.boundary))

# regions whose dimensionality is larger than the number of dimensions in their bounds should be OK
dim_mismatch = LinRegion([LinBound(LinSplit([1.0,-0.0],1.0),true)],3)
@assert regvalid(dim_mismatch)
non_rect_dim_mismatch = LinRegion([LinBound(LinSplit([1.1,-0.5],1.0),true)],3)
@assert regvalid(non_rect_dim_mismatch)


n1 = SplitNode(rect_split(1, 1.0, 2), LeafNode(1.0), LeafNode(0.0))

n2 = SplitNode(rect_split(1, 3.0, 2), LeafNode(3.0), LeafNode(2.0))

rr0 = rect_region([0, 0], [4, 4])

n3 = SplitNode(rect_split(1, 2.0, 2), n2, n1)

# n1, n2, and n3 define 2-dimensional functions, although
# one dimension would really be sufficient. Call the dims x,y.
# n1 takes value 0 for x>1, and 1 for x<1. n2 takes value
# 2 for x>3, and 3 for x<3. Now, n3 takes the values of n1
# for x>2, and n2 for x<2. This should make it 0 for x>2,
# and 3 for x<2. The trim function should be able to make
# this explicit.

tt = trim(BSPTree(rr0, n3))
tt2 = s_trim(BSPTree(rr0, n3))
tt3 = cheap_trim(BSPTree(rr0, n3))
tt4 = two_part_trim(BSPTree(rr0, n3))
tt5 = modified_trim(BSPTree(rr0, n3))
sn0 = SplitNode(rect_split(1, 2.0,2), LeafNode(3.0), LeafNode(0.0))

# TODO: re-understand the isequal vs == distinction, explain here

@assert ==(tt.root, sn0)
@assert ==(tt2.root, sn0)
@assert ==(tt3.root, sn0)
@assert ==(tt4.root, sn0)
@assert ==(tt5.root, sn0)


function random_rects_test(n)
  for i=1:n
    srand(i)
    dims = rand(1:5)
    a = BSPTree(randomrect(dims), randomtree(dims, rand(1:4)))
    @assert epsilonequal(a,a)
    @assert epsilonequal(a, a + 0.00000001, 0.0000001)
    @assert !epsilonequal(a, a + 0.1, 0.0000001)
  end
end

random_rects_test(50)

function random_splits_test(n)
  for i in collect(1:n)
    srand(i)
    s1=randomsplit(2)
    b1=convert(Bool,rand(0:1))
    lb1 = LinBound(s1,b1)
    s2=randomsplit(2)
    b2=convert(Bool,rand(0:1))
    lb2 = LinBound(s2,b2)
    s3=randomsplit(2)
    b3=convert(Bool,rand(0:1))
    lb3 = LinBound(s3,b3)
    if lb1<lb2 && lb2<lb3
      @assert lb1 < lb3
    end
  end
end

random_splits_test(100)

@assert sup_in_direction(makemodel(rr0),[0.0,1.0]) == 4.0
@assert sup_in_direction(makemodel(rr0),[1.0,0.0]) == 4.0
@assert sup_in_direction(makemodel(rr0),[0.0,-1.0]) == 0.0
@assert sup_in_direction(makemodel(rr0),[1.0,1.0]) == 8.0
@assert sup_in_direction(makemodel(rr0),[0.1,1.0]) == 4.4
@assert sup_in_direction(makemodel(rr0),[0.1,1.0],true) == [4.0,4.0]

@assert regvalid(LinRegion([
  LinBound(LinSplit([1.0],0.0),true),
  LinBound(LinSplit([-1.0],0.0),true)], 1))

@assert regvalid(LinRegion([
  LinBound(LinSplit([1.0,0.0],0.0),true),
  LinBound(LinSplit([-1.0,0.0],0.0),true)], 2))

@assert !regvalid(LinRegion([
  LinBound(LinSplit([1.0,0.0],0.0),true),
  LinBound(LinSplit([1.0,0.0],0.0),false)], 2))

@assert regvalid(LinRegion([], 2))

@assert !intersects(
  rect_region([0.0,0.0],[1.1,1.1]),
  rect_region([1.1,1.1],[2.2,2.2]))

@assert rect_region([0.0,0.0],[1.0,1.0]) ==
 LinRegion([
  LinBound(LinSplit([1.0,0.0],0.0),true),
  LinBound(LinSplit([0.0,1.0],0.0),true),
  LinBound(LinSplit([1.0,0.0],1.0),false),
  LinBound(LinSplit([0.0,1.0],1.0),false),
  LinBound(LinSplit([1.0,1.0],0.0),true)],
  2)

lre = LinRegion([
   LinBound(LinSplit([1.0,0.0],0.0),true),
   LinBound(LinSplit([0.0,1.0],0.0),true),
   LinBound(LinSplit([1.0,0.0],1.0),false),
   LinBound(LinSplit([0.0,1.0],1.0),false),
   LinBound(LinSplit([1.0,1.0],0.0),true),
   LinBound(LinSplit([-1.0,1.0],-1.0),true),
   LinBound(LinSplit([1.0,-1.0],-1.0),true),
   LinBound(LinSplit([-1.0,-1.0],-2.0),true)],
   2)

@assert trim_region(lre)==rect_region([0.0,0.0],[1.0,1.0])

@assert intersects(closure(sqtree([0.0,0.0]).boundary),closure(sqtree([1.0,1.0]).boundary))

@assert subset(rect_region([0.0,0.0],[1.0,1.0]),closure(rect_region([0.0,0.0],[1.0,1.0])))

@assert !subset(closure(sqtree([0.0,0.0]).boundary),closure(sqtree([1.0,1.0]).boundary))


for i=1:10
  srand(i)
  dims = rand(1:4)
  a = randomtree(dims, rand(1:4))
  b = randomtree(dims, rand(1:4))
  @assert isequal(a, a) && isequal(b, b)
  atree = trim(BSPTree(randomrect(dims), a))
  btree = trim(BSPTree(randomrect(dims), b))
  rtree = BSPTree(randomrect(dims), LeafNode(rand()))
  # now we put insert rtree into atree, query it back out,
  # and check that the two are equal.
  inserted = insert(rtree, atree)
  queried = query(inserted, rtree.boundary)
  @assert epsilonequal(rtree, queried)
end

@assert isequal(reorder([10, 20, 30, 40, 50, 60], [4, 5, 6, 1, 2, 3], 6), [40, 50, 60, 10, 20, 30])
@assert isequal(reorder([10, 20, 30, 40, 50, 60], [2, 3, 4, 5, 6, 1], 6), [60, 10, 20, 30, 40, 50])

@assert isequal(reorder(rect_split(1, 0, 4), [4, 3, 2, 1], 4),rect_split(4, 0, 4))

@assert ==(reorder(rect_region([1.0,2.0,3.0],[4.0,5.0,6.0]), [2,3,1], 3), rect_region([3.0,1.0,2.0],[6.0,4.0,5.0]))


@assert !not_in([1,2,3],1)
@assert !not_in([1,2,3],2)
@assert !not_in([1,2,3],3)
@assert not_in([1,2,3],4)

@assert find_first([1,2,3],1)==1
@assert find_first([1,2,3],2)==2
@assert find_first([1,2,3],3)==3
@assert find_first([2,1,3],1)==2

@assert isequal(unreorder([40, 50, 60, 10, 20, 30], [4, 5, 6, 1, 2, 3]), [10, 20, 30, 40, 50, 60])
@assert isequal(unreorder([10, 20, 30, 40, 50, 60], [2, 3, 4, 5, 6, 1]), [20, 30, 40, 50, 60, 10])

@assert isequal(findreorder([1, 2, 3, 4], [2, 3, 4, 1]), [4, 1, 2, 3])
@assert isequal(reorder([3, 4, 1, 2],
                      findreorder([3, 4, 1, 2], [4, 3, 2, 1]), 4),
              [4, 3, 2, 1])


@assert convert_dims(None(), 1) == None()
@assert convert_dims(LeafNode(1.0), 3) == LeafNode(1.0)
@assert convert_dims(LinSplit([1.0,2.0,3.0],4.0),1) == LinSplit([1.0],4.0)


function test_rect_addition(n)
  for i=1:n
    srand(i)
    boundary = randomrect(3)
    atree = BSPTree(boundary, random_rect_tree(3, 3))
    btree = BSPTree(boundary, random_rect_tree(3, 3))
    @assert epsilonequal(treemap((x -> x+4), atree), atree+4)
    @assert !epsilonequal(treemap((x -> x-4), atree), atree+4)
    @assert epsilonequal(atree + btree, btree + atree, 0.00001)
    @assert !epsilonequal(atree + btree, btree + atree + 1, 0.00001)
  end
end

test_rect_addition(100)

function time_epsilonequal_and_addition(n)
  @time test_rect_addition(n)
end

function profile_epeq_add(n)
  @profile test_rect_addition(n)
end


tree1 = SplitNode(rect_split(1, .5, 2), LeafNode(.25), LeafNode(.75))

tree2 = SplitNode(rect_split(2, .5, 2), LeafNode(.25), LeafNode(.75))

tree3 = SplitNode(rect_split(1, .5, 2),
                  SplitNode(rect_split(2, .5, 2),
                            LeafNode(.5),
                            LeafNode(1.0)),
                  SplitNode(rect_split(2, .5, 2),
                            LeafNode(1.0),
                            LeafNode(1.5)))

@assert tree3.pos.pos.value == .75 + .75
@assert tree3.neg.neg.value == .25 + .25
@assert tree3.neg.pos.value == .75 + .25

frame = rect_region([0.0, 0.0], [1.0, 1.0])
@assert epsilonequal(BSPTree(frame, tree3), BSPTree(frame, tree1) + BSPTree(frame, tree2))
@assert !epsilonequal(BSPTree(frame, tree3), BSPTree(frame, tree1) + BSPTree(frame, tree2) + 2)

tree4 = treemap((x -> x+1), tree1)

@assert tree4.pos.value == 1.75
@assert tree4.neg.value == 1.25


tree5 = SplitNode(rect_split(1, .5, 2),
                  SplitNode(rect_split(2, .5, 2),
                            LeafNode(1.0),
                            LeafNode(.25/.75)),
                  SplitNode(rect_split(2, .5, 2),
                            LeafNode(.75/.25),
                            LeafNode(1.0)))

@assert epsilonequal(BSPTree(frame, tree5), BSPTree(frame, tree1) / BSPTree(frame, tree2))

# Testing each case in treearithmetic
@assert LeafNode(5.0) - 3 == LeafNode(2.0)
@assert None() + 4 == LeafNode(4.0)
@assert SplitNode(rect_split(1, 2.0, 1), LeafNode(1.0), LeafNode(2.0)) - 1 == SplitNode(rect_split(1, 2.0, 1), LeafNode(0.0), LeafNode(1.0))
@assert 3 - LeafNode(5.0) == LeafNode(-2.0)
@assert 4 / None() == LeafNode(4.0)
@assert 1 - SplitNode(rect_split(1, 2.0, 1), LeafNode(1.0), LeafNode(2.0)) == SplitNode(rect_split(1, 2.0, 1), LeafNode(0.0), LeafNode(-1.0))
@assert epsilonequal((BSPTree(rect_region([1.0,1.0],[0.0,0.0]), LeafNode(2.0)) +
      BSPTree(rect_region([1.0,1.0],[0.0,0.0]), LeafNode(2.0))),
      BSPTree(rect_region([1.0,1.0],[0.0,0.0]), None()))
@assert epsilonequal(BSPTree(rect_region([0.0,0.0],[1.0,1.0]), LeafNode(2.0)) +
      BSPTree(rect_region([0.0,0.0],[1.0,1.0]), LeafNode(3.0)),
      BSPTree(rect_region([0.0,0.0],[1.0,1.0]), LeafNode(5.0)))
@assert epsilonequal(BSPTree(rect_region([0.0,0.0],[1.0,1.0]),
              SplitNode(rect_split(1, 0.5, 2),
                        LeafNode(0.0),
                        LeafNode(1.0))) +
      BSPTree(rect_region([0.0,0.0],[1.0,1.0]), LeafNode(2.0)),
      BSPTree(rect_region([0.0,0.0],[1.0,1.0]),
                    SplitNode(rect_split(1, 0.5, 2),
                              LeafNode(2.0),
                              LeafNode(3.0))))
@assert epsilonequal(BSPTree(rect_region([0.0,0.0],[1.0,1.0]),
              SplitNode(rect_split(1, 1.5, 2),
                        LeafNode(0.0),
                        LeafNode(1.0))) +
      BSPTree(rect_region([0.0,0.0],[1.0,1.0]), LeafNode(2.0)),
      BSPTree(rect_region([0.0,0.0],[1.0,1.0]), LeafNode(2.0)))
@assert epsilonequal(BSPTree(rect_region([0.0,0.0],[1.0,1.0]),
              SplitNode(rect_split(1, -1.5, 2),
                        LeafNode(0.0),
                        LeafNode(1.0))) +
      BSPTree(rect_region([0.0,0.0],[1.0,1.0]), LeafNode(2.0)),
      BSPTree(rect_region([0.0,0.0],[1.0,1.0]), LeafNode(3.0)))


#@assert convert_dims(project_region(rect_region([0.0,0.0],[1.0,1.0]),1), 1) == project_region(rect_region([0.0],[1.0]),1)
@assert convert_dims(project_region(rect_region([0.0,0.0],[1.0,1.0]),2), 1) == rect_region([0.0],[1.0])


r = LinRegion([LinBound(LinSplit([1.0,1.0],-1.0),true),
               LinBound(LinSplit([-1.0,1.0],-1.0),true),
               LinBound(LinSplit([1.0,-1.0],-1.0),true),
               LinBound(LinSplit([-1.0,-1.0],-1.0),true)], 2)

@assert convert_dims(project_region(r,2),1) == LinRegion([LinBound(LinSplit([1.0],-1.0),true),LinBound(LinSplit([-1.0],-1.0),true)], 1)


r2 = LinRegion([LinBound(LinSplit([1.0,1.0],1.0),false),
               LinBound(LinSplit([-1.0,1.0],1.0),false),
               LinBound(LinSplit([1.0,-1.0],1.0),false),
               LinBound(LinSplit([-1.0,-1.0],1.0),false)], 2)

@assert r == closure(r2)

@assert convert_dims(project_region(r2,2),1) == LinRegion([LinBound(LinSplit([1.0],1.0),false),LinBound(LinSplit([-1.0],1.0),false)], 1)

@assert length(trim_region(r).bounds) == 4

@assert regvalid(
  LinRegion(
    LinBound[
      LinBound(LinSplit([1.0, 1.0], -1.0), true),
      LinBound(LinSplit([-1.0, 1.0], -1.0), true),
      LinBound(LinSplit([1.0, -1.0], -1.0), true),
      LinBound(LinSplit([-1.0, -1.0], -1.0), false)], 2))

@assert regvalid(
  trim_region(
    LinRegion(
      LinBound[
        LinBound(LinSplit([1.0, 1.0], -1.0), true),
        LinBound(LinSplit([-1.0, 1.0], -1.0), true),
        LinBound(LinSplit([1.0, -1.0], -1.0), true),
        LinBound(LinSplit([-1.0, -1.0], -1.0), false)], 2)))

@assert !regvalid(
  LinRegion(
    LinBound[
      LinBound(LinSplit([1.0, 1.0], 1.0), true),
      LinBound(LinSplit([-1.0, 1.0], 1.0), true),
      LinBound(LinSplit([1.0, -1.0], 1.0), true),
      LinBound(LinSplit([1.0, 1.0], 1.0), true)], 2))


r3 = rect_region([-1,-2,-3],[1,2,3])

@assert convert_dims(project_region(project_region(r3,3),2),1) == convert_dims(r3,1)

@assert length(faces(rect_region([0.0,0.0],[1.0,1.0])))==4

@assert upper_face(1, LinBound(LinSplit([1.0,0.0],1.5),false)) == true

@assert lower_face(1, LinBound(LinSplit([1.0, -1.0], 1.0), true))

@assert face_difference(1, LinSplit([-1,-1],0), LinSplit([1,1],0), project_region(rect_region([0,0],[1,1]),1)).root.value == Hyper(sqrt(2),-1)

@assert face_difference(1, LinSplit([1,1],1), LinSplit([1,1],0), project_region(rect_region([0,0],[1,1]),1)).root.value == 1.0

@assert face_difference(1, LinSplit([1,-1],0), LinSplit([1,0],0), project_region(rect_region([0,0],[1,1]),1)).root.value == .5


@assert trim(leaf_integrate(BSPTree(rect_region([0,0],[1.5,1.5]),LeafNode(2)),1)).root.value == 3.0

@assert epsilonequal(
  integrate(BSPTree(rect_region([0,0],[1,1]),delta_slice(LinSplit([2.0,-1.0],0.5))),2),
  BSPTree(rect_region([0],[1]),
          SplitNode(LinSplit([2.0],1.5),
          SplitNode(LinSplit([2.0],0.5),
          LeafNode(0.0),LeafNode(2.23606797749979)),LeafNode(0.0))))


s = LinSplit([1.0,-1.0],0.0)
ds = delta_slice(s, 1.0)
dr = delta_reg(s)
@assert trim(BSPTree(dr,ds)) == BSPTree(dr, LeafNode(1.0))





function random_small_rect(n)
  mins = rand(n)*9
  maxs = rand(n)+mins
  return rect_region(mins,maxs)
end

function rand_first_two()
  mins = [rand(2); 0.0] * 9
  maxs = [rand(2); 10.0] + mins
  return rect_region(mins,maxs)
end

function rand_second_two()
  mins = [0.0; rand(2)] * 9
  maxs = [10.0; rand(2)] + mins
  return rect_region(mins,maxs)
end

function rand_first_grid(n)
  node = LeafNode(0.0)
  for i=1:n
    new_rect = rand_first_two()
    new_val = LeafNode(rand())
    new_item = unfoldboundary(BSPTree(new_rect, new_val))
    node = insert(new_item, node)
  end
  return BSPTree(rect_region([0,0,0], [10,10,10]), node)
end

function rand_second_grid(n)
  node = LeafNode(0.0)
  for i=1:n
    new_rect = rand_second_two()
    new_val = LeafNode(rand())
    new_item = unfoldboundary(BSPTree(new_rect, new_val))
    node = insert(new_item, node)
  end
  return BSPTree(rect_region([0,0,0], [10,10,10]), node)
end

function trim_eq_check(n)
  p = rand_first_grid(n)
  p1 = orig_trim(p)
  p2 = s_trim(p)
  p3 = two_part_trim(p)
  p4 = two_part_trim_2(p)
  p5 = modified_trim(p)
  p6 = g_trim(p)
  q1 = cheap_trim(p)
  q2 = leaf_merge_trim(p)
  @assert epsilonequal(p, p1)
  @assert epsilonequal(p, p2)
  @assert epsilonequal(p, p3)
  @assert epsilonequal(p, p4)
  @assert epsilonequal(p, p5)
  @assert epsilonequal(p, q1)
  @assert epsilonequal(p, q2)
end

trim_eq_check(15)

function trim_speed_test_one()
  @time g_trim(rand_first_grid(15))
  return true
end

function trim_speed_test_two()
  @time g_trim(rand_first_grid(30))
  return true
end

function arithmetic_trim_test(n)
  for i=1:n
    a = rand_first_grid(15)
    b = rand_second_grid(15)
    c = g_trim(g_trim(a)*g_trim(b))
  end
end

function trim_speed_test_three()
  @time arithmetic_trim_test(50)
end

function trim_speed_test_four(n)
  a = [modified_trim(rand_first_grid(15)) for x=1:n]
  b = [modified_trim(rand_second_grid(15)) for x=1:n]
  @time for i=1:n
    a[n]*b[n]
  end
end


function merge_speed_test(n)
  a = [trim(rand_first_grid(15)) for x=1:n]
  b = [trim(rand_second_grid(15)) for x=1:n]
  c = Vector{BSPTree}(n)
  for i=1:n
    c[n] = a[n]*b[n]
  end
  @time for i=1:n
    merge_bottom_up(c[n])
  end
end


function arith_speed_1(n)
  a = [trim(rand_first_grid(6)) for x=1:n]
  b = [trim(rand_second_grid(6)) for x=1:n]
  @time for i=1:n
    (a[n]*b[n])+a[n]
  end
end

function repeat_test_1(n)
  for i=1:n
    arith_speed_1(100)
  end
end

function arith_speed_2(n)
  a = [trim(rand_first_grid(6)) for x=1:n]
  b = [trim(rand_second_grid(6)) for x=1:n]
  @time for i=1:n
    integrate(trim(a[n]*b[n]), 2)
  end
end

function repeat_test_2(n)
  for i=1:n
    arith_speed_2(5)
  end
end

# TODO querybox, computeresult, and processchange have been
# tested as components in larger computations but don't have
# individual tests written


# TODO varordering, predordering, findsourcemaps, treecomb,
# and compilecombofun have been tested as components of
# larger computations but don't have individual tests written
