# This file is a part of Julia. License is MIT: http://julialang.org/license

## from base/boot.jl:
#
# immutable String <: AbstractString
#     data::Vector{UInt8}
# end
#

## basic UTF-8 decoding & iteration ##

is_surrogate_lead(c::Unsigned) = ((c & ~0x003ff) == 0xd800)
is_surrogate_trail(c::Unsigned) = ((c & ~0x003ff) == 0xdc00)
is_surrogate_codeunit(c::Unsigned) = ((c & ~0x007ff) == 0xd800)
is_valid_continuation(c) = ((c & 0xc0) == 0x80)

const utf8_offset = [
    0x00000000, 0x00003080,
    0x000e2080, 0x03c82080,
    0xfa082080, 0x82082080,
]

const utf8_trailing = [
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2, 3,3,3,3,3,3,3,3,4,4,4,4,5,5,5,5,
]

## required core functionality ##

@inline unsafe_codeunit(s::String, i::Integer) = unsafe_load(pointer(s),i)

function codeunit(s::String, i::Integer)
    if i < 1 || i > s.len
        throw(BoundsError(s,i))
    end
    unsafe_codeunit(s, i)
end

bytes(s::String) = (unsafe_codeunit(s,i) for i in 1:s.len)

function endof(s::String)
    p = pointer(s)
    i = s.len
    while i > 0 && is_valid_continuation(unsafe_load(p,i))
        i -= 1
    end
    i
end

function length(s::String)
    p = pointer(s)
    cnum = 0
    for i = 1:s.len
        cnum += !is_valid_continuation(unsafe_load(p,i))
    end
    cnum
end

@noinline function slow_utf8_next(p::Ptr{UInt8}, b::UInt8, i::Int, l::Int)
    if is_valid_continuation(b)
        throw(UnicodeError(UTF_ERR_INVALID_INDEX, i, unsafe_load(p,i)))
    end
    trailing = utf8_trailing[b + 1]
    if l < i + trailing
        return '\ufffd', i+1
    end
    c::UInt32 = 0
    for j = 1:(trailing + 1)
        c <<= 6
        c += unsafe_load(p,i)
        i += 1
    end
    c -= utf8_offset[trailing + 1]
    return Char(c), i
end

@inline function next(s::String, i::Int)
    # function is split into this critical fast-path
    # for pure ascii data, such as parsing numbers,
    # and a longer function that can handle any utf8 data
    if i < 1 || i > s.len
        throw(BoundsError(s,i))
    end
    p = pointer(s)
    b = unsafe_load(p, i)
    if b < 0x80
        return Char(b), i + 1
    end
    return slow_utf8_next(p, b, i, s.len)
end

function first_utf8_byte(ch::Char)
    c = UInt32(ch)
    b = c < 0x80    ? c%UInt8 :
        c < 0x800   ? ((c>>6)  | 0xc0)%UInt8 :
        c < 0x10000 ? ((c>>12) | 0xe0)%UInt8 :
                      ((c>>18) | 0xf0)%UInt8
    return b
end

function reverseind(s::String, i::Integer)
    j = s.len + 1 - i
    p = pointer(s)
    while is_valid_continuation(unsafe_load(p,j))
        j -= 1
    end
    return j
end

## overload methods for efficiency ##

sizeof(s::String) = s.len

isvalid(s::String, i::Integer) =
    (1 <= i <= s.len) && !is_valid_continuation(unsafe_load(pointer(s),i))

const empty_utf8 = String(UInt8[])

function getindex(s::String, r::UnitRange{Int})
    isempty(r) && return empty_utf8
    i, j = first(r), last(r)
    l = s.len
    if i < 1 || i > l
        throw(BoundsError(s, i))
    end
    if is_valid_continuation(unsafe_codeunit(s,i))
        throw(UnicodeError(UTF_ERR_INVALID_INDEX, i, unsafe_codeunit(s,i)))
    end
    if j > l
        throw(BoundsError())
    end
    j = nextind(s,j)-1
    String(pointer(s,i), j-i+1)
end

function search(s::String, c::Char, i::Integer = 1)
    if i < 1 || i > sizeof(s)
        i == sizeof(s) + 1 && return 0
        throw(BoundsError(s, i))
    end
    if is_valid_continuation(codeunit(s,i))
        throw(UnicodeError(UTF_ERR_INVALID_INDEX, i, codeunit(s,i)))
    end
    c < Char(0x80) && return search(s, c%UInt8, i)
    while true
        i = search(s, first_utf8_byte(c), i)
        (i==0 || s[i] == c) && return i
        i = next(s,i)[2]
    end
end

function search(a::String, b::Union{Int8,UInt8}, i::Integer = 1)
    if i < 1
        throw(BoundsError(a, i))
    end
    n = a.len
    if i > n
        return i == n+1 ? 0 : throw(BoundsError(a, i))
    end
    p = pointer(a)
    q = ccall(:memchr, Ptr{UInt8}, (Ptr{UInt8}, Int32, Csize_t), p+i-1, b, n-i+1)
    q == C_NULL ? 0 : Int(q-p+1)
end

function rsearch(s::String, c::Char, i::Integer = s.len)
    c < Char(0x80) && return rsearch(s, c%UInt8, i)
    b = first_utf8_byte(c)
    while true
        i = rsearch(s, b, i)
        (i==0 || s[i] == c) && return i
        i = prevind(s,i)
    end
end

function rsearch(a::String, b::Union{Int8,UInt8}, i::Integer = s.len)
    if i < 1
        return i == 0 ? 0 : throw(BoundsError(a, i))
    end
    n = a.len
    if i > n
        return i == n+1 ? 0 : throw(BoundsError(a, i))
    end
    p = pointer(a)
    q = ccall(:memrchr, Ptr{UInt8}, (Ptr{UInt8}, Int32, Csize_t), p, b, i)
    q == C_NULL ? 0 : Int(q-p+1)
end

function string(a::String...)
    if length(a) == 1
        return a[1]::String
    end
    n = 0
    for str in a
        n += str.len
    end
    out = ccall(:jl_alloc_string, Ref{String}, (Csize_t,), n)
    offs = 1
    for str in a
        unsafe_copy!(pointer(out,offs), pointer(str), str.len)
        offs += str.len
    end
    return out
end

# UTF-8 encoding length of a character
function codelen(d::Char)
    c = UInt32(d::Char)
    if c < 0x80
        return 1
    elseif c < 0x800
        return 2
    elseif c < 0x10000
        return 3
    elseif c < 0x110000
        return 4
    end
    return 3  # '\ufffd'
end

function string(a::Union{String,Char}...)
    n = 0
    for d in a
        if isa(d,Char)
            n += codelen(d::Char)
        else
            n += (d::String).len
        end
    end
    out = ccall(:jl_alloc_string, Ref{String}, (Csize_t,), n)
    offs = 1
    p = pointer(out)
    for d in a
        if isa(d,Char)
            c = UInt32(d::Char)
            if c < 0x80
                unsafe_store!(p, offs, c%UInt8); offs += 1
            elseif c < 0x800
                unsafe_store!(p, offs, (( c >> 6          ) | 0xC0)%UInt8); offs += 1
                unsafe_store!(p, offs, (( c        & 0x3F ) | 0x80)%UInt8); offs += 1
            elseif c < 0x10000
                unsafe_store!(p, offs, (( c >> 12         ) | 0xE0)%UInt8); offs += 1
                unsafe_store!(p, offs, (((c >> 6)  & 0x3F ) | 0x80)%UInt8); offs += 1
                unsafe_store!(p, offs, (( c        & 0x3F ) | 0x80)%UInt8); offs += 1
            elseif c < 0x110000
                unsafe_store!(p, offs, (( c >> 18         ) | 0xF0)%UInt8); offs += 1
                unsafe_store!(p, offs, (((c >> 12) & 0x3F ) | 0x80)%UInt8); offs += 1
                unsafe_store!(p, offs, (((c >> 6)  & 0x3F ) | 0x80)%UInt8); offs += 1
                unsafe_store!(p, offs, (( c        & 0x3F ) | 0x80)%UInt8); offs += 1
            else
                # '\ufffd'
                unsafe_store!(p, offs, 0xef); offs += 1
                unsafe_store!(p, offs, 0xbf); offs += 1
                unsafe_store!(p, offs, 0xbd); offs += 1
            end
        else
            l = (d::String).len
            unsafe_copy!(pointer(out,offs), pointer(d::String), l)
            offs += l
        end
    end
    return out
end

function reverse(s::String)
    dat = convert(Vector{UInt8},s)
    n = length(dat)
    n <= 1 && return s
    buf = Vector{UInt8}(n)
    out = n
    pos = 1
    @inbounds while out > 0
        ch = dat[pos]
        if ch > 0xdf
            if ch < 0xf0
                (out -= 3) < 0 && throw(UnicodeError(UTF_ERR_SHORT, pos, ch))
                buf[out + 1], buf[out + 2], buf[out + 3] = ch, dat[pos + 1], dat[pos + 2]
                pos += 3
            else
                (out -= 4) < 0 && throw(UnicodeError(UTF_ERR_SHORT, pos, ch))
                buf[out+1], buf[out+2], buf[out+3], buf[out+4] = ch, dat[pos+1], dat[pos+2], dat[pos+3]
                pos += 4
            end
        elseif ch > 0x7f
            (out -= 2) < 0 && throw(UnicodeError(UTF_ERR_SHORT, pos, ch))
            buf[out + 1], buf[out + 2] = ch, dat[pos + 1]
            pos += 2
        else
            buf[out] = ch
            out -= 1
            pos += 1
        end
    end
    String(buf)
end

write(io::IO, s::String) = write(io, pointer(s), s.len)

pointer(s::String) = convert(Ptr{UInt8}, pointer_from_objref(s)+sizeof(Int))
pointer(x::String, i::Integer) = pointer(x)+(i-1)

convert(::Type{String}, s::String) = s
convert(::Type{String}, v::Vector{UInt8}) = String(v)
