# Finite integer functions on the plane; missing dictionary key = outside domain.
const Site = Complex{BigInt}
const Tile = Dict{Site,BigInt}
pt(x::Integer, y::Integer) = complex(BigInt(x), BigInt(y))
_exactint(x::Integer) = BigInt(x)
function _exactint(x::Rational)
    denominator(x) == 1 || throw(ArgumentError("nonintegral lattice component: $x"))
    return BigInt(numerator(x))
end
_site(z::Number) = pt(_exactint(real(z)), _exactint(imag(z)))
function _require_nonempty(t::Tile, which::AbstractString)
    isempty(t) && throw(ArgumentError("empty tile: $which"))
    return t
end
# Rectangular origin and lexicographic anchors are deliberately DIFFERENT.
function ll(t::Tile)
    _require_nonempty(t, "LL")
    return argmin(z -> (imag(z),real(z)), keys(t))
end
function ur(t::Tile)
    _require_nonempty(t, "UR")
    return argmax(z -> (imag(z),real(z)), keys(t))
end
"""Translate the full support by v; add the affine slope at the destination coordinate."""
function place(t::Tile, v, slope)
    _require_nonempty(t,"place")
    w = _site(v); a = _site(slope)
    out = Tile(); sizehint!(out,length(t))
    if iszero(a)
        for (z,h) in t
            out[z+w] = h
        end
    else
        ax,ay = real(a),imag(a)
        for (z,h) in t
            u=z+w
            out[u] = h + ax*real(u) + ay*imag(u)
        end
    end
    return out
end
"""Rectangular-bounding-box minimum at zero; heights unchanged."""
function trim(t::Tile)
    _require_nonempty(t,"trim")
    return place(t,-pt(minimum(real,keys(t)), minimum(imag,keys(t))),0)
end
"""Actual bottom-row leftmost site at zero; heights unchanged."""
llcenter(t::Tile) = place(t,-ll(t),0)
function maxzero(t::Tile)
    _require_nonempty(t,"maxzero")
    m=maximum(values(t))
    return Tile(z => h-m for (z,h) in t)
end
"""Lower the incoming tile until it touches the old one; take their pointwise minimum.
Queries only their true intersection. If it is empty, no relative gauge is defined."""
function touch(old::Tile, incoming::Tile; context="")
    _require_nonempty(old,"old in $context"); _require_nonempty(incoming,"incoming in $context")
    delta = nothing
    small = length(old) < length(incoming) ? old : incoming
    for z in keys(small)
        if haskey(old,z) && haskey(incoming,z)
            v=incoming[z]-old[z]
            if isnothing(delta) || v<delta
                delta=v
            end
        end
    end
    isnothing(delta) && throw(ArgumentError("disjoint required tile overlap: $context"))
    # With this normalization the old value wins at EVERY old site in the overlap.
    # Hence only insert fresh sites. This is exactly the ordered min_nan rule.
    out=copy(old)
    for (z,h) in incoming
        if !haskey(out,z)
            out[z]=h-delta
        end
    end
    return out
end
"""Write exact integer heights in legacy export convention: sorted (x,y) relative
to the occupied bottom row's leftmost point; never subtract a height gauge."""
function write_tile(io::IO,t::Tile)
    a=ll(t)
    println(io,"# x\ty\theight; LL anchor = (0,0); exact integers")
    for z in sort!(collect(keys(t));by=z->(real(z),imag(z)))
        u=z-a
        println(io,real(u),'\t',imag(u),'\t',t[z])
    end
    return nothing
end
