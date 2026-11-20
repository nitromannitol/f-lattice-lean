# Deterministic clipping evidence

`clipping_demo.jl` runs without large dense allocations. Run with Julia and this
project; optional argument supplies the archived `final_code` directory.

1. The actual archived scalar `translate_va`/`translate_v` definitions are loaded
   verbatim into an isolated module. A single finite site in a 3x3 array translated
   by `(10^100,-10^100)` vanishes. Sparse `place` retains the one point and the
   exact BigInt affine height `8+5*10^100`.
2. The true full ancestor is word `1` (all eight standard/alternate registers).
   Current prefix is `1` followed by k copies of `2`. Its saved ancestor2 remains
   `1`; appending the next `2` really consumes the odd flipped LONG helper for the
   corrected odd alternate. This is not an empty-root or artificial input.
3. At k78 the unbounded helper has 3814 sites. An independently implemented
   ordered pointwise-min replay with the original fixed 684x576 canvas has3799
   sites, losing15 placement entries. All retained physical values agree exactly,
   after the common final max-zero convention. This example demonstrates SUPPORT
   clipping, NOT a discrepancy in surviving heights.
4. At k200 the unbounded helper has9670 sites and agrees exactly with that
   independently implemented unbounded min replay. The canvas-restricted replay
   loses a required overlap. It deliberately errors there rather than emulating
   Float64 Inf/NaN propagation.

A separate direct run of the original Julia code measured 3,799 at k=78 and a
BoundsError at k200. Those dense executions are not performed or independently
claimed by this script. The fixed-canvas emulation is independently implemented,
not a second copy of the optimized sparse `touch` routine. All original sources
remain unchanged. These tests do not prove later constructor correctness or
recurrence.
