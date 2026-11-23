import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.AlternateMidpoint

/-! # The strong estimates of a standard field (task 49, step 0)

The induction of the I1 and I2 comparisons (fixes/Q4-strips.md) uses, at the strictly earlier word `u` (the swapped birth prefix),
the packet of its standard field together with the two price ranges, the short-slip range, and the unit increments and no-cross
stars of the slip and of the primitive price. This file states these as one structure `StrongEstimates u`, with the notions taken
from `Potentials.lean` (`slip`, `price`, `cutPrice`, `shortShift`) and `AlternateMidpoint.lean` (`HasUnitSlip`, `NoEvenSlipSaddle`).

Not yet in this structure (their notions are not defined in Lean yet): F2 (the signed policies of the field and of its chain mate,
monotone on their retained edges), F3 (the signed retained graph with an integer rank for every pair of positive weights), F4
(the reflected graph of the chain mate, its black and white quotas and opposite rank increments), and the even-parity extension of
the odd zero strip (NO_ODD_SLIP_AUDIT §§2–4). They are added when their definitions exist.
-/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The primitive price increment over an input edge: `P(input) − P(center)`. -/
def priceIncrement (frame : ChildFrame) (F : Field) (center input : Site) : ℤ :=
  frame.price F input - frame.price F center

/-- F1 for the primitive price: its increments over the edges are in `{−1, 0, 1}`. -/
def HasUnitPrice (frame : ChildFrame) (F : Field) : Prop :=
  ∀ center input, Edge input center →
    -1 ≤ priceIncrement frame F center input ∧ priceIncrement frame F center input ≤ 1

/-- F1 for the primitive price, no-cross stars: at a star the two input increments are not opposite nonzero steps. -/
def NoPriceSaddle (frame : ChildFrame) (F : Field) : Prop :=
  ∀ site,
    let neg := priceIncrement frame F site (incomingNeg site)
    let pos := priceIncrement frame F site (incomingPos site)
    ¬ ((neg = -1 ∧ pos = 1) ∨ (neg = 1 ∧ pos = -1))

/-- The strong estimates of the standard field of a word `u`, the earlier word of an induction step. -/
structure StrongEstimates (u : Word) : Prop where
  /-- The packet of the standard field: periods, strips, reflection, binarity. -/
  packet : (frameAt u).Packet (standardField u)
  /-- The short-slip range `0 ≤ D_1 ≤ 2` on the closed polygon, with `D_η(z) = F(z) − F(z + ησ)`. -/
  slipRange : ∀ z ∈ (frameAt u).closedPolygon,
    0 ≤ (frameAt u).slip (standardField u) 1 z ∧ (frameAt u).slip (standardField u) 1 z ≤ 2
  /-- The primitive-price range `c_0 − 1 ≤ P ≤ c_0` on the closed polygon, with `c_0 = cutPrice`. -/
  priceRange : ∀ z ∈ (frameAt u).closedPolygon,
    (frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) z ∧
      (frameAt u).price (standardField u) z ≤ (frameAt u).cutPrice
  /-- F1, the slip: unit increments of `F` against its σ-translate on every edge. -/
  F1_unitSlip : HasUnitSlip (standardField u) (fun z => standardField u (z + (frameAt u).shortShift))
  /-- F1, the slip: no-cross stars. -/
  F1_noSlipSaddle : NoEvenSlipSaddle (standardField u) (fun z => standardField u (z + (frameAt u).shortShift))
  /-- F1, the primitive price: unit increments on every edge. -/
  F1_unitPrice : HasUnitPrice (frameAt u) (standardField u)
  /-- F1, the primitive price: no opposite nonzero increments at a star (no-cross primitive stars). -/
  F1_noPriceSaddle : NoPriceSaddle (frameAt u) (standardField u)

namespace StrongEstimates

variable {u : Word}

/-- The short-slip range, from the structure. -/
theorem slip_mem_range (h : StrongEstimates u) {z : Site} (hz : z ∈ (frameAt u).closedPolygon) :
    0 ≤ (frameAt u).slip (standardField u) 1 z ∧ (frameAt u).slip (standardField u) 1 z ≤ 2 :=
  h.slipRange z hz

/-- The primitive-price range, from the structure. -/
theorem price_mem_range (h : StrongEstimates u) {z : Site} (hz : z ∈ (frameAt u).closedPolygon) :
    (frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) z ∧
      (frameAt u).price (standardField u) z ≤ (frameAt u).cutPrice :=
  h.priceRange z hz

end StrongEstimates

end FLatticePaper.Induction
