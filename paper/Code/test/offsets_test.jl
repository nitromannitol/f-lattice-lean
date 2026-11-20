using Test
module ExactOffsets
include("../src/offsets.jl")
end
module OriginalOffsets
const ROOT=get(ENV,"F_LATTICE_ORIGINAL",normpath(joinpath(@__DIR__,"../../recovery_20261101_0745/f_lattice_original_algorithm/final_code")))
count_full(s,c)=count(==(c),s)
all2(s)=isempty(s)||(!occursin('1',s)&&!occursin('3',s))
all3(s)=isempty(s)||(!occursin('1',s)&&!occursin('2',s))
isOdd(p)=isodd(numerator(p)+denominator(p));isEven(p)=!isOdd(p)
vf(p)=(denominator(p)+numerator(p)*im,(numerator(p)-denominator(p))+(numerator(p)+denominator(p))*im)
function af(p)
 n,d=numerator(p),denominator(p)
 mat=(1//(d*d+2*d*n-n*n))*[-n*n d*n;d*n -d*d]
 a,b=mat*[d,n],mat*[n-d,n+d]
 return a[1]+im*a[2],b[1]+im*b[2]
end
getChildren(o,e)=((numerator(e)+numerator(o))//(denominator(e)+denominator(o)),(numerator(e)+2*numerator(o))//(denominator(e)+2*denominator(o)))
include(joinpath(ROOT,"rational_recursion.jl"))
include(joinpath(ROOT,"tile_decomp/tile_offsets.jl"))
end
const E=ExactOffsets;const O=OriginalOffsets
words=[""]
for n in 1:5
 append!(words,[w*string(c) for w in copy(words) if length(w)==n-1 for c in '1':'3'])
end
@testset "literal original source offsets" begin
 for w in words
  @test E.getFracs(w)==O.getFracs(w)
  @test all(x->x isa Rational{BigInt},E.getFracs(w))
  for name in (:getOddTileFull,:getEvenTileFull,:getAltOddTileFull,:getAltEvenTileFull,
    :getOddTileOffSets,:getEvenTileOffSets,:getAltOddTileOffSets,:getAltEvenTileOffSets,
    :getOddTileAffine,:getEvenTileAffine,:getAltOddTileAffine,:getAltEvenTileAffine)
   a=getfield(E,name)(w);b=getfield(O,name)(w)
   @test a==b
   flat=first(a) isa Tuple ? (a[1]...,a[2]...) : a
   @test all(x->x isa Complex{BigInt},flat)
  end
  if !isempty(w)
   for name in (:get_even_l_offsets,:get_odd_l_offsets), flip in (false,true)
    a=getfield(E,name)(w,flip)
    @test a==getfield(O,name)(w,flip)
    @test all(x->x isa Complex{BigInt},a)
   end
   for p in E.getFracs(w)[1:2]
    op=Int(numerator(p))//Int(denominator(p))
    @test E.get_alt_full_offset(p,w)==O.get_alt_full_offset(op,w)
    @test E.translate_alts(p)==O.translate_alts(op)
    rw,f=E.rational_approximation(p,1)
    @test rw==w
    @test p in f[1:2]
   end
  end
 end
end
@testset "unbounded exact history and rotations" begin
 for w in (repeat("1",100),repeat("2",1100),repeat("3",1100),repeat("123",40))
  for p in E.getFracs(w)[1:2]
   @test E.rational_approximation(p,1)[1]==w
   @test E.getModFareyParents(p)==E.getFracs(w)[3:4]
  end
  @test all(x->x isa Complex{BigInt},E.getAffine(w))
 end
 @test denominator(E.getFracs(repeat("1",100))[1])>typemax(Int64)
 for n in -3:3,d in -3:3
  z=Complex{BigInt}(n,d)
  @test E.rotccw(E.Rot(z))==z
 end
 @test_throws DomainError E.rational_approximation(big(0)//big(1))
 @test_throws DomainError E.rational_approximation(big(1)//big(1))
 @test_throws ArgumentError E.getFracs("14")
 @test E.all2("") && E.all3("")
end
