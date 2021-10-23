
# == Priority Queue Implementation == #

# A parametric struct for a heap entry. This just wraps a type T with a priocity
# value.

struct HeapEntry{T}
    contents::T
    priority::Float64
end

# A parametric type for a priority queue.

mutable struct PQ{T}
    # The heap in which we keep everything quasi-sorted.
    heap::Vector{HeapEntry{T}}
    # The current number of valid objects in the heap.
    size::Int
    # The current max size of the heap array.
    current_max::Int
end

# Initialization for the heap. I'll start it at 16 so we don't have to expand
# its size a bunch of times right off.
function PQ(T::DataType)
    return PQ{T}(Vector{HeapEntry{T}}(undef, 16), 0, 16)
end

import Base.length

length(pq::PQ) = pq.size

# Heaps in Julia are a little annoying because Julia arrays start at 1 instead
# of 0. Here's a heap:
#
#                    root
#          l                     r
#    ll         lr         rl         rr
# lll  llr   lrl  lrr   rll  rlr   rrl  rrr
#
# Here's the array version of that same heap:
#
#    root l r ll lr rl rr lll llr ...
#    1    2 3 4  5  6  7  8   9
#
# Node      Left Child   Right Child
# root (1)  l (2)        r (3)
# l (2)     ll (4)       lr (5)
# r (3)     rl (6)       rr (7)
# ll (4)    lll (8)      llr (9)
# ...
#
# So the formula for the two children is 2x, 2x+1. The formula for finding the
# parent of a given node is Int(floor(x/2)).
#
# WELL, OK, these formulas seem strictly less annoying... never mind. Anyway.
# So we insert things at the next un-used slot, and then we swap with parents
# to bubble up so long as the heap property is violated.

heap_parent(i::Int) = Int(floor(i/2))
left_child(i::Int) = i*2
right_child(i::Int) = i*2+1
upward_heap_violation(pq::PQ, i::Int) = !(i==1) && pq.heap[i].priority > pq.heap[heap_parent(i)].priority
left_heap_violation(pq::PQ, i::Int) = !(left_child(i) > pq.size) &&  pq.heap[left_child(i)].priority > pq.heap[i].priority
right_heap_violation(pq::PQ, i::Int) = !(right_child(i) > pq.size) &&  pq.heap[right_child(i)].priority > pq.heap[i].priority

function enqueue!(pq::PQ, item, weight::Float64)
    # check if there's a new spot to put something in; if not, expand the array
    if pq.size == pq.current_max
        new_max = 2*max(pq.size,1)
        new_array = Vector{HeapEntry{typeof(item)}}(undef, new_max)
        for i=1:pq.size
            new_array[i] = pq.heap[i]
        end
        pq.heap = new_array
        pq.current_max = new_max
    end
    # put the item in the next unused slot
    item_location = pq.size + 1
    pq.heap[item_location] = HeapEntry(item, weight)
    pq.size = item_location
    # bubble up as necessary
    while upward_heap_violation(pq, item_location)
        hold = pq.heap[item_location]
        pq.heap[item_location] = pq.heap[heap_parent(item_location)]
        pq.heap[heap_parent(item_location)] = hold
        item_location = heap_parent(item_location)
    end
    return pq
end

enqueue!(pq::PQ, item, weight::Int) = enqueue!(pq, item, convert(Float64, weight))

function dequeue!(pq::PQ)
    # check whether empty
    if pq.size == 0
        error("Attempted to dequeue emply PQ.")
    end
    # store the top item outside the heap
    result = pq.heap[1]
    # put the last item of the heap in the top position
    pq.heap[1] = pq.heap[pq.size]
    # decrease the size of the heap
    pq.size = pq.size - 1
    # restore the heap property by pushing the top item down, as necessary
    current_location = 1
    while left_heap_violation(pq, current_location) || right_heap_violation(pq, current_location)
        if pq.heap[left_child(current_location)].priority >= pq.heap[right_child(current_location)].priority # left child is biggest
            # swap with left child
            hold = pq.heap[current_location]
            pq.heap[current_location] = pq.heap[left_child(current_location)]
            pq.heap[left_child(current_location)] = hold
            # change current location to the child
            current_location = left_child(current_location)
        else # right child is biggest
            # swap with right child
            hold = pq.heap[current_location]
            pq.heap[current_location] = pq.heap[right_child(current_location)]
            pq.heap[right_child(current_location)] = hold
            # change current location to the child
            current_location = right_child(current_location)
        end
    end
    # return the top item we stored earlier
    return result.contents
end

function peek(pq::PQ)
    return pq.heap[1].contents
end



















#
