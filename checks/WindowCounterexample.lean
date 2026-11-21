import FLatticePaper.Tiles.WindowCounterexample

/-! Checks for the strict counterexample to the window bound (task 26): the tile `T0` is an admissible simple tile,
the Cramer-numerator window fails on it, packing holds, and the two global inputs and the tiling conclusion hold. -/

open FLatticePaper.Tiles

#print axioms w1₀_admissible
#print axioms w2₀_admissible
#print axioms T0_simple
#print axioms T0_window_fails
#print axioms T0_packing
#print axioms T0_global
#print axioms T0_almost_tiling
