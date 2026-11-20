# Sparse high-level constructor transcription

`src/recursion.jl` transcribes the literal final_code `odometer_recursion.jl`
and `get_l_correction.jl`, not the proposed analytic atlas.

Preserved:
- six natural slots, their actual odd/even standard and alternate permutations;
- seventh uncorrected alternate source inserted immediately after natural slot0;
- current-phase UR choice, including the terminal3 special branch;
- actual pure helper G2-only adjustments (they do not update the running G3 origin);
- k+1 scans, one bridge, 2k+1 SHORT / 2k+2 LONG heads;
- every chronological exact touch/min, including clipped collisions;
- helper-only max-zero normalization;
- two separate saved ancestor records and updates on 1/3 versus 1/2.

Helpers are evaluated lazily at the previous current word immediately before
consumption. Only the branch selected by next digit2 or3, SHORT and LONG, is
built. Root/unused helpers are never called. This is equivalent to the literal
cache for consumed calls, without pretending unused invalid helpers exist.

Restoration uses the first birth prefix along the actual lineage, with no
999-step cutoff. A test compares this against the separately implemented exact
rational inverse for both parent types through length4.

## Coordinates and gauge

Constructor input tiles have their lexicographic (y,x) LL at0. Returns of each
new constructor are trimmed by rectangular coordinate minima, with heights
unchanged. Carried parent entries in the four-tuple have LL at0, which is the
internal common frame; normalize their support coordinates for comparisons to
arbitrary padded legacy matrices. No public height max-zero is applied.
`place` must evaluate its affine slope on the translated site, not its local
source site. `ur` must be lexicographic max(y,x), not independent coordinate
maxima. Shared-frame displacement of all operands changes each placed source
by a scalar; chronological touch removes every such relative scalar. In all
four literal offset tables the first source slope is zero, so no new absolute
height gauge is introduced at the outer merge. Helpers subsequently max-zero.
The public return LL-centers all eight registers, without changing heights.
Genuine Julia TSV and live direct regression results are in VALIDATION.md.

## Executed tests

Julia1.10.13, independent minimal exact sparse core:17 constructor smoke words
through `1122`,`1133` all completed with nonempty touches. Test file
`test/recursion_test.jl`:252/252 assertions passed, including invalid alphabet
rejection, exact BigInt heights, regression support counts, and independent
birth-history agreement. Support-count expectations record this implementation's
smoke results; they are NOT independent original-array fidelity certificates.
The separate integration tests compare the actual package against original Julia output.
