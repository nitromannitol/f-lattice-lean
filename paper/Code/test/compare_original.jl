# Independently run the archived dense Julia functions. Pass /path/to/final_code.
using FLatticeExact
using Test
module Legacy
using LinearAlgebra
end
function load_original(dir)
    for file in ("helper_functions.jl","build_odometers_init.jl","rational_recursion.jl",
                 "tile_decomp/tile_offsets.jl","base_case.jl","odometer_recursion.jl","get_l_correction.jl")
        path=joinpath(dir,file)
        # Only remove the plotting import; none of the plotting functions are called.
        src=replace(read(path,String),r"(?m)^using Plots[^\S\n]*$"=>"# drawing disabled for this test")
        Base.include_string(Legacy,src,path)
    end
end
function dense_tile(A)
    anchor=Legacy.get_lower_left_vertex(A)
    isnothing(anchor) && error("legacy returned an empty/nonfinite field")
    out=Tile()
    for idx in CartesianIndices(A)
        h=A[idx]; isnan(h) && continue
        isfinite(h) && isinteger(h) && abs(h)<big(2)^53 || error("legacy value is not a safe integer")
        out[FLatticeExact.pt(idx[1]-anchor[1],idx[2]-anchor[2])]=BigInt(h)
    end
    out
end
function compare_words(words)
    countarrays=entries=0
    @testset "Julia exact sparse versus archival dense original: every native key and absolute height" begin
        for w in words
            olds=Legacy.get_odometers(w)
            news=FLatticeExact.get_odometers(w)
            n=0
            for k in 1:2, s in 1:4
                want=dense_tile(olds[k][s]); got=FLatticeExact.llcenter(news[k][s])
                @test want == got
                n+=length(want); countarrays+=1
            end
            entries+=n
            println("word=",repr(w)," fields=8 finite_sites=",n); flush(stdout)
            GC.gc()
        end
    end
    println("TOTAL words=",length(words)," arrays=",countarrays," finite_sites=",entries)
end
isempty(ARGS) && error("usage: julia --project=. test/compare_original.jl /path/to/final_code [WORD ...]")
load_original(abspath(ARGS[1]))
compare_words(length(ARGS)>1 ? ARGS[2:end] : ["","1","2","3","11","12","13","21","22","23","31","32","33","113","123","232","323"])
