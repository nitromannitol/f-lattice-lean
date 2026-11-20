# Exact offset module audit

Implemented `src/offsets.jl` directly from original `final_code/tile_decomp/tile_offsets.jl`, retaining every original table branch, including even affine `ap1+2ap2`, saved-last2 L corrections, and pure3 restoration's extra `im`. Mechanical changes are Rational{BigInt}, AbstractString, and explicit Complex{BigInt} zero values. No array recursion was included.

Farey helpers use Rational{BigInt} from their initial values. `vf` and `af` return Complex{BigInt}; the latter simplifies the original rational matrix product identically to `(0, n-di)`. Exact inverse history compares rationals by equality and uses the original three interval choices with no search cap. The optional legacy depth argument is accepted but ignored. Only 0<x<1 has a creation word; endpoint inverse requests raise DomainError. Invalid word digits raise ArgumentError. No floating input method is supplied.

Inverse search is the original mediant subdivision of the current adjacent Farey interval. Every strict nonterminal step increases an endpoint denominator while both endpoints bracketing a fixed rational have denominator at most that rational's denominator; therefore exact rational search terminates. This is not a 999-step or floating-tolerance approximation.

Additional helpers supplied: getChildren, getNextFrac, getModFareyParents, getParents, isEven, count_full, all standard/alternate OffSets and Affine variants, getTileOffSets, getAltTileOffSets, get_even_offset/get_odd_offset and affine mates, get_alt_offset/get_alt_affine, one-argument translate_alts, Rot (clockwise), rotccw, arithmetic_dual. The restoration helper returns its original positive offset; the caller applies the negative translation as in the original.

Unit tests load the ORIGINAL Julia rational_recursion and tile_offsets sources in an independent module, using the original rational-matrix affine calculation. For every word through length five they compare all ordinary/alternate slot lists, both flips of both helper tables, primitive restoration, and exact inverse histories. All returned coordinates and slopes are checked to be Complex{BigInt}. Further tests exercise inverse histories beyond 999 steps, fractions exceeding Int64, exact physical rotations and rejected endpoints/digits.

Fresh execution with Julia 1.10.13:
- literal original source offsets: 15,272 / 15,272 PASS;
- unbounded exact history and rotations: 74 / 74 PASS.

Command: julia --startup-file=no astra_exact_julia_20261119/test/offsets_test.jl

The tests are regression/source-equivalence evidence. They do not establish recurrence, native recognition, or execution of the array constructor.
