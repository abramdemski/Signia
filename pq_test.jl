
include("pq.jl")

numbered_number = HeapEntry{Int}(12, 1)

number_pq = PQ(Int)

enqueue!(number_pq, numbered_number.contents, numbered_number.priority)

@assert number_pq.heap[1] == numbered_number

number_pq_2 = PQ(Int)

@assert number_pq_2.size == 0
enqueue!(number_pq_2,1,1)
@assert number_pq_2.size == 1
@assert number_pq_2.heap[1] == HeapEntry{Int}(1,1)
enqueue!(number_pq_2,2,2)
@assert number_pq_2.size == 2
@assert number_pq_2.heap[2] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[1] == HeapEntry{Int}(2,2)
enqueue!(number_pq_2,3,3)
@assert number_pq_2.size == 3
@assert number_pq_2.heap[3] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[2] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[1] == HeapEntry{Int}(3,3)
enqueue!(number_pq_2,4,4)
@assert number_pq_2.size == 4
@assert number_pq_2.heap[4] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[3] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[2] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[1] == HeapEntry{Int}(4,4)
enqueue!(number_pq_2,5,5)
@assert number_pq_2.size == 5
@assert number_pq_2.heap[5] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[4] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[3] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[2] == HeapEntry{Int}(4,4)
@assert number_pq_2.heap[1] == HeapEntry{Int}(5,5)
enqueue!(number_pq_2,6,6)
@assert number_pq_2.size == 6
@assert number_pq_2.heap[6] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[5] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[4] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[3] == HeapEntry{Int}(5,5)
@assert number_pq_2.heap[2] == HeapEntry{Int}(4,4)
@assert number_pq_2.heap[1] == HeapEntry{Int}(6,6)
enqueue!(number_pq_2,7,7)
@assert number_pq_2.size == 7
@assert number_pq_2.heap[7] == HeapEntry{Int}(5,5)
@assert number_pq_2.heap[6] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[5] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[4] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[3] == HeapEntry{Int}(6,6)
@assert number_pq_2.heap[2] == HeapEntry{Int}(4,4)
@assert number_pq_2.heap[1] == HeapEntry{Int}(7,7)
enqueue!(number_pq_2,8,8)
@assert number_pq_2.size == 8
@assert number_pq_2.heap[8] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[7] == HeapEntry{Int}(5,5)
@assert number_pq_2.heap[6] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[5] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[4] == HeapEntry{Int}(4,4)
@assert number_pq_2.heap[3] == HeapEntry{Int}(6,6)
@assert number_pq_2.heap[2] == HeapEntry{Int}(7,7)
@assert number_pq_2.heap[1] == HeapEntry{Int}(8,8)
enqueue!(number_pq_2,7,7)
@assert number_pq_2.size == 9
@assert number_pq_2.heap[9] == HeapEntry{Int}(4,4)
@assert number_pq_2.heap[8] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[7] == HeapEntry{Int}(5,5)
@assert number_pq_2.heap[6] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[5] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[4] == HeapEntry{Int}(7,7)
@assert number_pq_2.heap[3] == HeapEntry{Int}(6,6)
@assert number_pq_2.heap[2] == HeapEntry{Int}(7,7)
@assert number_pq_2.heap[1] == HeapEntry{Int}(8,8)
enqueue!(number_pq_2,6,6)
@assert number_pq_2.size == 10
@assert number_pq_2.heap[10] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[9] == HeapEntry{Int}(4,4)
@assert number_pq_2.heap[8] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[7] == HeapEntry{Int}(5,5)
@assert number_pq_2.heap[6] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[5] == HeapEntry{Int}(6,6)
@assert number_pq_2.heap[4] == HeapEntry{Int}(7,7)
@assert number_pq_2.heap[3] == HeapEntry{Int}(6,6)
@assert number_pq_2.heap[2] == HeapEntry{Int}(7,7)
@assert number_pq_2.heap[1] == HeapEntry{Int}(8,8)

number_pq_2 = PQ(HeapEntry{Int}[], 0, 0)

@assert number_pq_2.size == 0
enqueue!(number_pq_2,1,1)
@assert number_pq_2.size == 1
@assert number_pq_2.heap[1] == HeapEntry{Int}(1,1)
enqueue!(number_pq_2,2,2)
@assert number_pq_2.size == 2
@assert number_pq_2.heap[2] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[1] == HeapEntry{Int}(2,2)
enqueue!(number_pq_2,3,3)
@assert number_pq_2.size == 3
@assert number_pq_2.heap[3] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[2] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[1] == HeapEntry{Int}(3,3)
enqueue!(number_pq_2,4,4)
@assert number_pq_2.size == 4
@assert number_pq_2.heap[4] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[3] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[2] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[1] == HeapEntry{Int}(4,4)
enqueue!(number_pq_2,5,5)
@assert number_pq_2.size == 5
@assert number_pq_2.heap[5] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[4] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[3] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[2] == HeapEntry{Int}(4,4)
@assert number_pq_2.heap[1] == HeapEntry{Int}(5,5)
enqueue!(number_pq_2,6,6)
@assert number_pq_2.size == 6
@assert number_pq_2.heap[6] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[5] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[4] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[3] == HeapEntry{Int}(5,5)
@assert number_pq_2.heap[2] == HeapEntry{Int}(4,4)
@assert number_pq_2.heap[1] == HeapEntry{Int}(6,6)
enqueue!(number_pq_2,7,7)
@assert number_pq_2.size == 7
@assert number_pq_2.heap[7] == HeapEntry{Int}(5,5)
@assert number_pq_2.heap[6] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[5] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[4] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[3] == HeapEntry{Int}(6,6)
@assert number_pq_2.heap[2] == HeapEntry{Int}(4,4)
@assert number_pq_2.heap[1] == HeapEntry{Int}(7,7)
enqueue!(number_pq_2,8,8)
@assert number_pq_2.size == 8
@assert number_pq_2.heap[8] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[7] == HeapEntry{Int}(5,5)
@assert number_pq_2.heap[6] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[5] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[4] == HeapEntry{Int}(4,4)
@assert number_pq_2.heap[3] == HeapEntry{Int}(6,6)
@assert number_pq_2.heap[2] == HeapEntry{Int}(7,7)
@assert number_pq_2.heap[1] == HeapEntry{Int}(8,8)
enqueue!(number_pq_2,7,7)
@assert number_pq_2.size == 9
@assert number_pq_2.heap[9] == HeapEntry{Int}(4,4)
@assert number_pq_2.heap[8] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[7] == HeapEntry{Int}(5,5)
@assert number_pq_2.heap[6] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[5] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[4] == HeapEntry{Int}(7,7)
@assert number_pq_2.heap[3] == HeapEntry{Int}(6,6)
@assert number_pq_2.heap[2] == HeapEntry{Int}(7,7)
@assert number_pq_2.heap[1] == HeapEntry{Int}(8,8)
enqueue!(number_pq_2,6,6)
@assert number_pq_2.size == 10
@assert number_pq_2.heap[10] == HeapEntry{Int}(3,3)
@assert number_pq_2.heap[9] == HeapEntry{Int}(4,4)
@assert number_pq_2.heap[8] == HeapEntry{Int}(1,1)
@assert number_pq_2.heap[7] == HeapEntry{Int}(5,5)
@assert number_pq_2.heap[6] == HeapEntry{Int}(2,2)
@assert number_pq_2.heap[5] == HeapEntry{Int}(6,6)
@assert number_pq_2.heap[4] == HeapEntry{Int}(7,7)
@assert number_pq_2.heap[3] == HeapEntry{Int}(6,6)
@assert number_pq_2.heap[2] == HeapEntry{Int}(7,7)
@assert number_pq_2.heap[1] == HeapEntry{Int}(8,8)

dequeue!(number_pq_2) == 8
@assert number_pq_2.size == 9

number_pq_3 = PQ(Int)

number_ordering = [2, 5, 8, 1, 4, 7, 3, 6, 9]

for i=1:length(number_ordering)
    enqueue!(number_pq_3, number_ordering[i], number_ordering[i])
end

for i=1:length(number_ordering)
    n = length(number_pq_3)
    @assert dequeue!(number_pq_3) == n
end
