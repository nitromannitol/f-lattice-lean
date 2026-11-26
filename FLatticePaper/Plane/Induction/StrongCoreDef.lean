import FLatticePaper.Plane.Induction.StrongEstimates

/-! # The core of the strong estimates

`StrongCore u` is `StrongEstimates u` without the policy field `F2F3_policy`, with the same field names. A lemma that uses only these
fields takes `StrongCore u`; a `StrongEstimates u` is coerced to its core (`StrongEstimates.toCore`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The strong estimates of `u` without the policy field `F2F3_policy`. -/
structure StrongCore (u : Word) : Prop where
  packet : (frameAt u).Packet (standardField u)
  slipRange : ∀ z ∈ (frameAt u).closedPolygon,
    0 ≤ (frameAt u).slip (standardField u) 1 z ∧ (frameAt u).slip (standardField u) 1 z ≤ 2
  priceRange : ∀ z ∈ (frameAt u).closedPolygon,
    (frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) z ∧
      (frameAt u).price (standardField u) z ≤ (frameAt u).cutPrice
  priceDrift : ∀ z,
    (frameAt u).price (standardField u) (z + (frameAt u).child.modifiedDeck.kernel) -
        (frameAt u).price (standardField u) z = -1 ∧
      (frameAt u).price (standardField u) (z + (frameAt u).child.modifiedDeck.transverse) -
        (frameAt u).price (standardField u) z = 0
  slipDrift : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ z,
    (frameAt u).slip (standardField u) η (z + (frameAt u).child.modifiedDeck.kernel) -
        (frameAt u).slip (standardField u) η z = 0 ∧
      (frameAt u).slip (standardField u) η (z + (frameAt u).child.modifiedDeck.transverse) -
        (frameAt u).slip (standardField u) η z = 2 * η
  zeroStripInterval : ∀ x : Site,
    1 - parentD u ≤ parentN u * x.1 - parentD u * x.2 →
      parentN u * x.1 - parentD u * x.2 ≤ parentN u + 2 * parentD u - 1 →
        quarterTurnField (standardField u) x = 0
  zeroEvenLine : ∀ x : Site, (x.1 + x.2) % 2 = 0 →
    parentN u * x.1 - parentD u * x.2 = -parentD u → quarterTurnField (standardField u) x = 0
  F1_unitSlip : HasUnitSlip (standardField u) (fun z => standardField u (z + (frameAt u).shortShift))
  F1_noSlipSaddle : NoEvenSlipSaddle (standardField u) (fun z => standardField u (z + (frameAt u).shortShift))
  F1_unitPrice : HasUnitPrice (frameAt u) (standardField u)
  F1_noPriceSaddle : NoPriceSaddle (frameAt u) (standardField u)

/-- The fields of the strong estimates other than the policy. -/
theorem StrongEstimates.toCore {u : Word} (h : StrongEstimates u) : StrongCore u :=
  { packet := h.packet
    slipRange := h.slipRange
    priceRange := h.priceRange
    priceDrift := h.priceDrift
    slipDrift := h.slipDrift
    zeroStripInterval := h.zeroStripInterval
    zeroEvenLine := h.zeroEvenLine
    F1_unitSlip := h.F1_unitSlip
    F1_noSlipSaddle := h.F1_noSlipSaddle
    F1_unitPrice := h.F1_unitPrice
    F1_noPriceSaddle := h.F1_noPriceSaddle }

instance {u : Word} : Coe (StrongEstimates u) (StrongCore u) := ⟨StrongEstimates.toCore⟩

end FLatticePaper.Induction
