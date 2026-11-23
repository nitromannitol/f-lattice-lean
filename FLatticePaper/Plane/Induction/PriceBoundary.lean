import FLatticePaper.Plane.Induction.PriceH
import FLatticePaper.Plane.Induction.BaseRange

/-! # The boundary price bound `hbd` from its four sides (task 110, step (1))

`hbd` of `priceRange_of_conjugate` asks `P z ≤ c₀` at every `z` with `OnBoundary E z`, where `OnBoundary E z` is an outward unit direction
leaving `E` at `z`. The boundary splits into four sides by that direction. This file proves the combinator: the four side bounds give `hbd`.

The side bounds are the traces of Q13's insertion, named here with their claimed content:
* bottom (outward `(0,−1)`): on the native H arc, `P(H_0) = c₀` and `P(H_j) = c₀ − 1` for `j > 0` (`PriceH.price_arc_W0/W1`); the
  non-spectrum bottom points are deck translates of free ones (`outside_SI_free`), which needs the deck price drift;
* top (outward `(0,1)`): the zero price drift translate of the bottom H trace (named);
* left (outward `(−1,0)`): the native V trace at `c₀` (the whole star agrees with the harmonic field before and after the price shift; named);
* right (outward `(1,0)`): the right V trace at `c₀ − 1` (the primary drift; named). -/

namespace FLatticePaper.PriceBoundary

open FLatticePaper FLatticePaper.Induction

/-- **`hbd` from its four sides.** If the price is at most `c` at every boundary point leaving `E` in each of the four directions, then it
is at most `c` at every `OnBoundary E` point. -/
theorem hbd_of_sides {E : Set Site} {P : Site → ℤ} {c : ℤ}
    (hbot : ∀ z, OutwardDir E (0, -1) z → P z ≤ c)
    (htop : ∀ z, OutwardDir E (0, 1) z → P z ≤ c)
    (hleft : ∀ z, OutwardDir E (-1, 0) z → P z ≤ c)
    (hright : ∀ z, OutwardDir E (1, 0) z → P z ≤ c) :
    ∀ z, OnBoundary E z → P z ≤ c := by
  rintro z (h | h | h | h)
  · exact htop z h
  · exact hbot z h
  · exact hright z h
  · exact hleft z h

end FLatticePaper.PriceBoundary
