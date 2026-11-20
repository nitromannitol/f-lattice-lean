# Julia code for the F-lattice odometers

Julia 1.7 or later is required. The package uses the Julia standard library. Run the following commands from this directory.

~~~sh
julia --project=. run_code.jl 3312 patterns.svg
julia --project=. examples/export.jl 23 alt odd > word23.tsv
julia --project=. test/runtests.jl
~~~

The first command draws the two standards and the two alternates. Black is Laplacian −1, gray is 0, and white is outside the finite tile. The program evaluates incoming neighbors across period boundaries. The second command exports exact integer heights relative to the leftmost occupied point of the bottom row. The empty word is written as two quotes. [Example for word 3312](examples/3312.svg)

In a fresh interactive Julia session, `include("run_code.jl")` also draws the original example. Use `render("23","word23.svg")` to draw another word.

## Tile and pattern interface

~~~julia
using FLatticeExact
standards, alternates = get_odometers("23")
p, q, p_parent, q_parent = getFracs("23")
odd_alt = alternates[1]
field = periodic_pattern(odd_alt, p)

odd_alt[0 + 0im]             # exact height at the native anchor
periodic_height(field, 4im)  # exact extended height in this tile's coordinates
pattern_value(field, 4im)    # F-lattice Laplacian at that site
~~~

Each family returns four tiles in the order current odd, current even, retained odd parent and retained even parent. A tile maps integer lattice coordinates to integer heights using arbitrary precision. A missing key denotes a position outside the tile. Each tile has its own local coordinate frame. Reanchoring changes the coordinates and preserves the absolute heights.

The constructor translates every occupied point, adds the affine slope at its destination and takes the prescribed minimum at each successive contact. Both lengths of an L-correction use the saved ancestor from the preceding word. The parent registers, insertion order and normalization are the same as in the paper. [Constructor details](RECURSION_IMPLEMENTATION.md)

The pattern calculation obtains the two additive period constants from repeated sites, checks every repeated height, and requires the tile to cover its period quotient. It evaluates both possible checkerboards over a whole period to recover the physical incoming directions in the local frame. The optional keyword *horizontal_parity* fixes a known horizontal-input parity, 0 or 1. Inconsistent data or an unresolved checkerboard produce an error. The returned field exposes its periods as *u* and *v* and its period area as *area*. [Exact period arithmetic](src/pattern.jl)

## Matrix interface

A script using the original, unqualified constructor can load the matrix interface in a fresh Julia session.

~~~julia
include("init.jl")
mats, alt_mats = get_odometers("3312")
p, q, p_parent, q_parent = getFracs("3312")
~~~

This returns the same eight registers as matrices. The first dimension is the horizontal coordinate. Finite entries retain their exact integer heights. Empty entries and the one-site border are NaN. Matrices are allocated at the final output size, after the complete sparse computation.

## Clipping regression

At the word consisting of 1 and 37 twos, the odd alternate at 39/116 has 82,028 occupied sites and covers all 41,966 period classes. The old published output lost the five points from (123,217) through (123,221), each the only representative of its class. The tests check those points, deliberately remove them, and verify that the period reconstruction detects the incomplete tile. The tests also construct both standards and both alternates at 44 twos. [Regression and matrix tests](test/pattern_test.jl)
