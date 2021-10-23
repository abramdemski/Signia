
# I need hyperreal values in order to implement delta functions.
# However, I only need very approximate hyperreals. Anything
# infinitesimal compared to the largest infinity is discarded.
# Therefore, I store a float (value) along with an int (mantissa)
# which tells what power of infinity is involved.

struct Hyper <: Number
  value::Float64
  mantissa::Int
end

# If a hyper is given as the argument of a hyper, unpack.
Hyper(v::Hyper,i) = Hyper(v.value,convert(Int,i)+v.mantissa)
# Otherwise, try to convert things to the right type.
Hyper(v,i) = Hyper(convert(Float64,v), convert(Int, i))

# an alias for use inside Signia programs, since capitalization would make it a
# predicate variable.
hyper(x,y) = Hyper(x,y)


# Define type conversion from other numeric types.

import Base.convert

# Finite values are hyperreal values with mantissa 0.
convert(::Type{Hyper}, x::Float64) = Hyper(x, 0)
convert(::Type{Hyper}, x::Number) = Hyper(x, 0)

# I'll want to de-convert back to floats whenever possible.

simplify(h::Hyper) = h.value == -Inf ? -Inf : (h.value == Inf ? Inf : (h.mantissa == 0 ? h.value : (h.value == 0 ? 0 : h)))
simplify(h::Number) = h

# Now I need to implement basic arithmetic ops for this.

import Base.+

function +(a::Hyper,b::Hyper)
  if a.mantissa == b.mantissa
    return simplify(Hyper(a.value+b.value, a.mantissa))
  elseif a.value == 0.0
    return b
  elseif b.value == 0.0
    return a
  elseif a.mantissa < b.mantissa
    return simplify(b)
  else
    return simplify(a)
  end
end

+(a::Hyper, b::Number) = a + convert(Hyper, b)
+(a::Number, b::Hyper) = convert(Hyper, a) + b

import Base.-

function -(a::Hyper, b::Hyper)
  if a.mantissa == b.mantissa
    return simplify(Hyper(a.value - b.value, a.mantissa))
  elseif a.mantissa < b.mantissa
    return simplify(b)
  else
    return simplify(a)
  end
end

-(a::Hyper, b::Number) = a - convert(Hyper, b)
-(a::Number, b::Hyper) = convert(Hyper, a) - b

# Multiplication for hyperreals.

import Base.*

# All we have to do is multiply the coefficients and add the exponents.
*(a::Hyper, b::Hyper) = simplify(Hyper(a.value*b.value, a.mantissa+b.mantissa))

*(a::Bool, b::Hyper) = a ? b : a
*(a::Hyper, b::Number) = simplify(Hyper(a.value*b, a.mantissa))
*(a::Number, b::Hyper) = simplify(Hyper(b.value*a, b.mantissa))

import Base./

/(a::Hyper, b::Hyper) = simplify(Hyper(a.value/b.value, a.mantissa-b.mantissa))

/(a::Hyper, b::Number) = simplify(Hyper(a.value/b, a.mantissa))
/(a::Number, b::Hyper) = simplify(Hyper(a/b.value, -b.mantissa))

import Base.^

function ^(a::Hyper, b::Hyper)
  @warn("I'm being asked to compute something of the form Hyper^Hyper. I'll do it, but the output is meaningless because I don't really have an appropriate value for that.")
  return simplify(Hyper(a.value^b.value, floor(a.mantissa*b.value) + b.mantissa))
end

^(a::Hyper, b::Rational) = simplify(Hyper(a.value^b, floor(a.mantissa*b)))
^(a::Hyper, b::Integer) = simplify(Hyper(a.value^b, a.mantissa*b))
# can't exponentiate the mantissa if b isn't an int
^(a::Hyper, b::Number) = simplify(Hyper(a.value^b, a.mantissa*b))

function ^(a::Irrational{:e}, b::Hyper)
  @warn("I'm being asked to compute something of the form Number^Hyper. I'll do it, but the output is meaningless because I don't really have an appropriate value for that.")
  return simplify(Hyper(a^b.value, b.mantissa))
end

function ^(a::Number, b::Hyper)
  @warn("I'm being asked to compute something of the form Number^Hyper. I'll do it, but the output is meaningless because I don't really have an appropriate value for that.")
  return simplify(Hyper(a^b.value, b.mantissa))
end


import Base.==

==(a::Hyper, b::Hyper) = a.mantissa == b.mantissa && a.value == b.value

#function ==(a::Hyper, b::Number)
#  if b == Inf
#    return a == Hyper(1.0,1)
#  if b == -Inf
#    return a == Hyper(-1.0, 1)
#  else
#  return a == convert(Hyper, b)
#end

==(a::Hyper, b::Number) = a == convert(Hyper, b)

==(a::Number, b::Hyper) = convert(Hyper, a) == b


# isless makes a variety of comparisons work.
# Note that Inf is greater than any hyper, and -Inf is less. This allows me to
# use those values as identity values for the min and max ops.

import Base.isless

function isless(a::Hyper, b::Hyper)
  if a.value == Inf
    return false
  elseif b.value == Inf
    return true
  elseif b.value == -Inf
    return false
  elseif a.value == -Inf
    return true
  elseif a.mantissa < b.mantissa
    return true
  elseif b.mantissa < a.mantissa
    return false
  elseif a.value < b.value
    return true
  else
    return false
  end
end

function isless(a::Number, b::Hyper)
  if a == Inf
    return false
  elseif b.value == Inf
    return true
  elseif b.value == -Inf
    return false
  elseif a == -Inf
    return true
  elseif b.mantissa < 0
    if a > 0
      return true
    elseif a <= 0
      return false
    else
      throw("isless doesn't know how to compare $a with $b")
    end
  elseif b.mantissa > 0
    return true
  else # mantissa == 0
    return isless(a, b.value)
  end
end

function isless(a::Hyper, b::Number)
  if a.value == Inf
    return false
  elseif b == Inf
    return true
  elseif b == -Inf
    return false
  elseif a.value == -Inf
    return true
  elseif a.mantissa < 0
    if b > 0
      return true
    elseif b <= 0
      return false
    else
      throw("isless doesn't know how to compare $a with $b")
    end
  elseif a.mantissa > 0
    return false
  else # mantissa == 0
    return isless(a.value, b)
  end
end

import Base.max

function max(a::Hyper, b::Hyper)
  if a > b
    return a
  else
    return b
  end
end

import Base.min

function min(a::Hyper, b::Hyper)
  if a < b
    return a
  else
    return b
  end
end






#=


# I need hyperreal values in order to implement delta functions.

# The Hyper type holds an array of floats, and an int, the
# mantissa. Like a floating-point mantissa, the Hyper mantissa
# tells us what power of the base is used at the most significant
# digit. In this case, however, "digits" are real numbers and the
# "base" is infinity. A mantissa of 0 means that the largest value
# of the hyperreal is a finite one. -1 indicates a simple
# infinitesimal. And so on. Delta values will generally be +1.

# Warning: when an immutable type contains a mutable type such
# as a vector, the mutable type is still mutable. So, although
# Hyper is conceptually immutable and is supposed to be treated
# as such, it is possible for the values of the vector to be
# edited.

immutable Hyper
  values::Vector{Float64}
  mantissa::Int
end

Hyper(v,i) = Hyper(convert(Vector{Float64},v), convert(Int, i))

# Define type conversion from other numeric types.

import Base.convert

convert(::Type{Hyper}, x::Float64) = Hyper([x], 0)
convert(::Type{Hyper}, x::Number) = Hyper([convert(Float64,x)], 0)

# Now I need to implement basic arithmetic ops for this.

import Base.+

function +(a::Hyper,b::Hyper)
  # We need to find which has the larger order of infinity; the new number will start there.
  larger = (a.mantissa > b.mantissa) ? a : b
  smaller = (a.mantissa <= b.mantissa) ? a : b
  largermant = larger.mantissa
  smallermant = smaller.mantissa
  # The difference gives us the array offset for comparable values.
  offset = largermant - smallermant
  # smaller_end is the location of the last item in smaller.values *relative to* the array indices of larger.values.
  # This may or may not fall inside the array bounds of larger.values.
  smaller_end = length(smaller.values) + offset
  len = max(length(larger.values),smaller_end)
  values = Vector{Float64}(len)
  # First, the portion where only the larger is defined.
  # Here, we simply copy the values.
  for i = 1:(offset)
    values[i] = larger.values[i]
  end
  # Then, for the portion where both are defined, add them.
  last_common = min(length(larger.values),smaller_end)
  for i = (offset + 1):last_common
    values[i] = larger.values[i] + smaller.values[i-offset]
  end
  # The final portion could belong to either the smaller or the larger, depending on which stretches further.
  larger_later = (length(larger.values) > smaller_end) ? true : false
  if larger_later
    for i = (last_common+1):length(larger.values)
      values[i] = larger.values[i]
    end
  else
    for i = (last_common+1):(smaller_end)
      values[i] = smaller.values[i-offset]
    end
  end
  return Hyper(values,largermant)
end

+(a::Hyper, b::Number) = a + convert(Hyper, b)
+(a::Number, b::Hyper) = convert(Hyper, a) + b

# Multiplication for hyperreals.

import Base.*

function *(a::Hyper, b::Hyper)
  # The largest power of infinity in the result is the sum of the two mantissas.
  mantissa = a.mantissa+b.mantissa
  # The power of the smallest power of infinity needed.
  smallest = mantissa-length(a.values)-length(b.values)+2
  values = Vector{Float64}(mantissa-smallest+1)
  for i = 1:length(a.values)
    for j = 1:length(b.values)
      values[i+j-1] = a.values[i] * b.values[j]
    end
  end
  return Hyper(values, mantissa)
end

# If multiplied by a number, try to convert it to a float and multiply the
# individual components.

function *(a::Hyper, b::Number)
  c = convert(Float64, b)
  return Hyper([c*x for x=a.values], a.mantissa)
end

*(a::Number, b::Hyper) = b*a

import Base.max

function trim(h::Hyper)
  i=1
  lim=length(h.values)+1
  while i < lim || h.values[i] == 0.0
    i+=1
  end
  if i>1
    return Hyper(h.values[i:length(h.values)], h.mantissa-i+1)
  else
    return h
  end
end

function max(a::Hyper, b::Hyper)
  trimmed_a = trim(a)
  trimmed_b = trim(b)
  if trimmed_a.mantissa > trimmed_b.mantissa
    return trimmed_a
  elseif trimmed_b.mantissa > trimmed_a.mantissa
    return trimmed_b
  elseif trimmed_a.values[1] > trimmed_b.values[1]
    return trimmed_a
  else
    return trimmed_b
  end
end

import Base.min

function max(a::Hyper, b::Hyper)
  trimmed_a = trim(a)
  trimmed_b = trim(b)
  if trimmed_a.mantissa < trimmed_b.mantissa
    return trimmed_a
  elseif trimmed_b.mantissa < trimmed_a.mantissa
    return trimmed_b
  elseif trimmed_a.values[1] < trimmed_b.values[1]
    return trimmed_a
  else
    return trimmed_b
  end
end

# TODO: division
# TODO: subtraction


=#
