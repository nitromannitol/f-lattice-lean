# Run: julia --project=. test/clipping_demo.jl [archived final_code directory]
# No large dense allocation. Executes the ORIGINAL scalar translator on a 3x3
# canvas; the helper replay below uses exact sparse emulation of its fixed canvas.
using FLatticeExact, Test
const E=FLatticeExact
module OriginalScalar end
original=isempty(ARGS) ? joinpath(@__DIR__,"../../recovery_20261101_0745/f_lattice_original_algorithm/final_code") : ARGS[1]
text=read(joinpath(original,"build_odometers_init.jl"),String)
a=findfirst("function translate_v(G,v)",text).start
b=findfirst("## AFFINE FUNCTIONS",text).start
Base.include_string(OriginalScalar,text[a:b-1],"original_scalar_translate")
@testset "enormous displacement: original fixed canvas versus exact support" begin
    A=fill(NaN,3,3); A[2,2]=7
    huge=big(10)^100; v=E.pt(huge,-huge); slope=E.pt(3,-2)
    clipped=OriginalScalar.translate_va(A,v,slope)
    @test all(isnan,clipped)
    placed=E.place(Tile(E.pt(1,1)=>big(7)),v,slope)
    @test length(placed)==1
    @test placed[E.pt(1,1)+v]==8+5huge
    println("scalar demo: original support=0; sparse support=1; exact height=8+5*10^100")
end

# Independent ordered pointwise-min implementation, NOT E.touch.
function merge_min(old,new)
    overlap=intersect(keys(old),keys(new))
    isempty(overlap) && error("required overlap vanished under clipping")
    shift=minimum(new[z]-old[z] for z in overlap)
    out=copy(old)
    for (z,h) in new
        value=h-shift
        out[z]=haskey(out,z) ? min(out[z],value) : value
    end
    out
end
function replay(m,a,k; clip=false)
    current="1"*"2"^k
    m=map(E.llcenter,m); a=map(E.llcenter,a)
    alltiles=(m...,a...)
    xmin=minimum(minimum(real,keys(t)) for t in alltiles)
    xmax=maximum(maximum(real,keys(t)) for t in alltiles)
    ymin=minimum(minimum(imag,keys(t)) for t in alltiles)
    ymax=maximum(maximum(imag,keys(t)) for t in alltiles)
    # center_mats joint unpad has one empty row/column on every side.
    # Then get_l_correct pads ALL eight once and selected three once again.
    nx=xmax-xmin+3; ny=ymax-ymin+3
    origin=E.pt(1-xmin+cld(6nx,4)-1+cld(36nx,4)-1,
                1-ymin+cld(6ny,4)-1+cld(36ny,4)-1)
    inside(z)=0<=real(z+origin)<36nx && 0<=imag(z+origin)<36ny
    pa,qa=E.translate_alts((m[3],m[4],a[3],a[4]),current)
    g1,g2,g3=m[4],m[3],qa
    k1,k2,k3,k4,a1,a2,a3,a4=E.get_odd_l_offsets("1",true)
    vs,aa=E.getOddTileFull(current); v=vs[4]; slope=aa[4]
    removed=0
    function offer(t,v,b)
        out=Tile()
        for (z,h) in t
            u=z+v
            if !clip || inside(u)
                out[u]=h+real(b)*real(u)+imag(b)*imag(u)
            else
                removed+=1
            end
        end
        out
    end
    out=offer(g1,v,slope)
    for i in 1:k
        v+=k1; slope+=a1; out=merge_min(out,offer(g1,v,slope))
    end
    v+=k2; slope+=a2; out=merge_min(out,offer(g2,v,slope))
    v+=k3; slope+=a3
    for i in 1:2(k+1) # LONG, not SHORT
        v+=k4; slope+=a4; out=merge_min(out,offer(g3,v,slope))
    end
    out=E.maxzero(out)
    out,removed,(36nx,36ny),origin
end
m,a=E.get_odometers("1") # TRUE full eight-register ancestor, not root/base substitutes.
@testset "consumed corrected helper: ancestor1, odd flipped LONG" begin
    for k in (78,200)
        current="1"*"2"^k
        # Next letter2 consumes ancestor2=1, selecting LONG for corrected odd ALT.
        full,_,canvas,origin=replay(m,a,k)
        got=E.get_l_correct(m,a,"1",current;getOdd=true,isFlip=true,isLong=true)
        @test E.trim(full)==got
        if k==200
            # The fixed canvas loses a required overlap before completion.
            # Original Float64 min/NaN machinery instead proceeds to its later
            # BoundsError (separate direct dense run, not executed here).
            @test length(full)==9670
            @test_throws ErrorException replay(m,a,k;clip=true)
            println("k=200 next=2 odd_ALT_LONG=true canvas=$canvas full=$(length(full)) fixed_canvas_required_overlap_lost=true")
            continue
        end
        clipped,lost,_,_=replay(m,a,k;clip=true)
        shared=intersect(keys(full),keys(clipped))
        differences=Set(full[z]-clipped[z] for z in shared)
        println("k=$k next=2 odd_ALT_LONG=true canvas=$canvas full=$(length(full)) clipped=$(length(clipped)) discarded_placement_entries=$lost common_height_differences=$(sort!(collect(differences)))")
        @test (length(full),length(clipped),lost)==(3814,3799,15)
        @test differences==Set([big(0)])
    end
end
# Scope: equality with direct sparse helper and a separately implemented exact
# fixed-canvas emulation. Direct original dense helper comparison is a separate
# test/run; do not mislabel this emulation as independent dense execution.
