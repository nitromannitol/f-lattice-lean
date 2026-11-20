# From the Code folder: julia --project=. audits/check_patterns.jl 4
using FLatticeExact

function verify_depth(maxdepth)
    maxdepth >= 0 || throw(ArgumentError("depth must be nonnegative"))
    words = [""]
    total = 0
    sites = big(0)
    for depth in 0:maxdepth
        for word in words
            mats,alts = get_odometers(word)
            fractions = getFracs(word)
            for family in (mats,alts), i in 1:2
                t = family[i]
                p = periodic_pattern(t,fractions[i])
                @assert length(p.labels)==p.area
                @assert all(periodic_height(p,z)==h for (z,h) in t)
                sites += p.area
                total += 1
            end
        end
        println("depth=",depth," words=",length(words)," cumulative_patterns=",total," cumulative_period_classes=",sites)
        depth < maxdepth && (words = [w*c for w in words for c in "123"])
    end
end

length(ARGS)<=1 || error("usage: check_patterns.jl [depth]")
verify_depth(isempty(ARGS) ? 4 : parse(Int,only(ARGS)))
