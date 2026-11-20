using FLatticeExact
using Test

# Quotient coordinates are obtained from the adjugate of the actual deck basis.
# This independently checks each finite native support, physical height consistency
# and binary Laplacian. It says nothing about recurrence.
# A trimmed/reanchored tile has no declared physical origin parity. Test both phases.
# Usage from the Julia package root: julia --project=. audits/check_native_deck.jl 3
det2(z,w)=real(z)*imag(w)-imag(z)*real(w)
dot2(z,w)=real(z)*real(w)+imag(z)*imag(w)
pnt=FLatticeExact.pt

function check_deck(tile,p; odd, label)
    n,d=numerator(p),denominator(p)
    U=(odd ? 2 : 1)*pnt(d,n); V=pnt(n-d,n+d); W=pnt(n,-d)
    det=det2(U,V)
    key(z)=(mod(det2(z,V),det),mod(det2(U,z),det))
    rep=Dict{Tuple{BigInt,BigInt},Tuple{Site,BigInt}}()
    equations=Tuple{BigInt,BigInt,BigInt}[]
    function shift(z,u)
        j,rj=divrem(det2(U,u-z),det)
        i,ri=divrem(det2(u-z,V),det)
        @test ri==0 && rj==0
        return i,j,j*dot2(W,z)+div(j*(j-1),2)*dot2(W,V)
    end
    for (z,h) in tile
        k=key(z)
        if haskey(rep,k)
            u,g=rep[k]
            i,j,q=shift(u,z)
            push!(equations,(i,j,h-g-q))
        else
            rep[k]=(z,h)
        end
    end
    @test length(rep)==det
    isempty(equations) && return false
    a,b,c=equations[1]
    k=findfirst(e->a*e[2]-b*e[1]!=0,equations)
    isnothing(k) && return false
    e,f,g=equations[k]
    den=a*f-b*e
    alpha=(c*f-b*g)//den; beta=(a*g-c*e)//den
    @test denominator(alpha)==denominator(beta)==1
    @test all(eq->eq[1]*alpha+eq[2]*beta==eq[3],equations)
    function at(z)
        u,g=rep[key(z)]; i,j,q=shift(u,z)
        g+i*alpha+j*beta+q
    end
    outcomes=[count(values(rep)) do (z,h)
        v=isodd(real(z)+imag(z)+phase) ? pnt(0,1) : pnt(1,0)
        !((at(z+v)+at(z-v)-2h) in (-1,0))
    end for phase in (0,1)]
    if minimum(outcomes) != 0
        println("FAIL STAR: ",label," fraction=",p," failures=",outcomes)
    end
    @test minimum(outcomes)==0
    return true
end

function main(depth)
    words=[""]; n=0; nfull=0
    @testset "Native quotient and exact physical binary stars" begin
        for _ in 0:depth
            for w in words
                std,alt=get_odometers(w)
                p,q=getFracs(w)[1:2]
                for (j,t) in enumerate((std,alt)), (i,f) in enumerate((p,q))
                    n+=1
                    nfull+=check_deck(t[i],f;odd=i==1,label=(w,j,i))
                end
            end
            words=[w*c for w in words for c in "123"]
        end
    end
    println("outputs=",n,", complete deck and binary-star checks=",nfull)
end

main(isempty(ARGS) ? 3 : parse(Int,only(ARGS)))
