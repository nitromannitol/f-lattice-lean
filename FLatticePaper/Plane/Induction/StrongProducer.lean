import FLatticePaper.Plane.Induction.StrongEstimates

/-! Task 39, step 2: the open part of `StrongEstimates u`.

`StrongProducer u` is every field of `StrongEstimates u` except the packet. The packet of the standard field is not a producer
obligation: it is supplied by the word induction (`packet_standardField`), once the sheet and star inputs hold at every proper
word. The eleven fields are the open part; their status is recorded in the task report (proved modulo the stated inputs,
or open), and each is checked numerically at the proper words of length at most four.

`StrongEstimates.of_producer` assembles the strong estimates from the packet and the producer. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The open part of the strong estimates of a standard field: the fields other than the packet. -/
structure StrongProducer (u : Word) : Prop where
  /-- The short-slip range `0 ≤ D_1 ≤ 2` on the closed polygon, with `D_η(z) = F(z) − F(z + ησ)`. -/
  slipRange : ∀ z ∈ (frameAt u).closedPolygon,
    0 ≤ (frameAt u).slip (standardField u) 1 z ∧ (frameAt u).slip (standardField u) 1 z ≤ 2
  /-- The primitive-price range `c_0 − 1 ≤ P ≤ c_0` on the closed polygon, with `c_0 = cutPrice`. -/
  priceRange : ∀ z ∈ (frameAt u).closedPolygon,
    (frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) z ∧
      (frameAt u).price (standardField u) z ≤ (frameAt u).cutPrice
  /-- The drifts of the primitive price on the generators `U` (kernel) and `V` (transverse) of the earlier child:
  `P(z + U) − P(z) = −1` and `P(z + V) − P(z) = 0` (checked numerically on the standard fields of the proper words of length
  at most three). -/
  priceDrift : ∀ z,
    (frameAt u).price (standardField u) (z + (frameAt u).child.modifiedDeck.kernel) -
        (frameAt u).price (standardField u) z = -1 ∧
      (frameAt u).price (standardField u) (z + (frameAt u).child.modifiedDeck.transverse) -
        (frameAt u).price (standardField u) z = 0
  /-- The drifts of the short slip `D_η` for `η = ±1`: `0` along `U` and `2η` along `V` (checked numerically as above). -/
  slipDrift : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ z,
    (frameAt u).slip (standardField u) η (z + (frameAt u).child.modifiedDeck.kernel) -
        (frameAt u).slip (standardField u) η z = 0 ∧
      (frameAt u).slip (standardField u) η (z + (frameAt u).child.modifiedDeck.transverse) -
        (frameAt u).slip (standardField u) η z = 2 * η
  /-- The zero strip of the quarter-turned earlier field in the parent transverse coordinate `t_p = N x₁ − D x₂`:
  `f = h₀ + F_u(Z ·) = quarterTurnField (standardField u)` vanishes for `1 − D ≤ t_p ≤ N + 2D − 1` (fix Q4-strips, the zero
  region). Checked numerically on the proper words of length at most three. -/
  zeroStripInterval : ∀ x : Site,
    1 - parentD u ≤ parentN u * x.1 - parentD u * x.2 →
      parentN u * x.1 - parentD u * x.2 ≤ parentN u + 2 * parentD u - 1 →
        quarterTurnField (standardField u) x = 0
  /-- The even-parity extension of the zero strip at `t_p = −D`: `f = 0` at the even sites with `t_p = −D` (fix Q4-strips,
  `f_even(−D) = 0`). Checked numerically on the proper words of length at most three. -/
  zeroEvenLine : ∀ x : Site, (x.1 + x.2) % 2 = 0 →
    parentN u * x.1 - parentD u * x.2 = -parentD u → quarterTurnField (standardField u) x = 0
  /-- F1, the slip: unit increments of `F` against its σ-translate on every edge. -/
  F1_unitSlip : HasUnitSlip (standardField u) (fun z => standardField u (z + (frameAt u).shortShift))
  /-- F1, the slip: no-cross stars. -/
  F1_noSlipSaddle : NoEvenSlipSaddle (standardField u) (fun z => standardField u (z + (frameAt u).shortShift))
  /-- F1, the primitive price: unit increments on every edge. -/
  F1_unitPrice : HasUnitPrice (frameAt u) (standardField u)
  /-- F1, the primitive price: no opposite nonzero increments at a star (no-cross primitive stars). -/
  F1_noPriceSaddle : NoPriceSaddle (frameAt u) (standardField u)
  /-- F2 and F3 for the standard field: a signed policy that is a quota policy, along whose retained edges the field does not
  increase, and for every pair of positive weights `(a, c)` a rank with increments `λ(−a, cη)` on the generators `U′`, `V′`
  (`U′`, `V′` the kernel and the transverse period of the earlier child, `η = ε`). -/
  F2F3_policy : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ policy : Site → Site → Prop,
    RetainQuota (standardField u) policy ∧
      NonincreasingAlong ((frameAt u).chainPotential (standardField u) η) policy ∧
      ∀ a c : ℤ, 0 < a → 0 < c →
        RankWithIncrements policy (frameAt u).child.modifiedDeck.kernel (frameAt u).child.modifiedDeck.transverse
          (-a) (c * η)


/-- **The strong estimates from the packet and the producer.** -/
theorem StrongEstimates.of_producer {u : Word} (hpk : (frameAt u).Packet (standardField u))
    (P : StrongProducer u) : StrongEstimates u :=
  { packet := hpk
    slipRange := P.slipRange
    priceRange := P.priceRange
    priceDrift := P.priceDrift
    slipDrift := P.slipDrift
    zeroStripInterval := P.zeroStripInterval
    zeroEvenLine := P.zeroEvenLine
    F1_unitSlip := P.F1_unitSlip
    F1_noSlipSaddle := P.F1_noSlipSaddle
    F1_unitPrice := P.F1_unitPrice
    F1_noPriceSaddle := P.F1_noPriceSaddle
    F2F3_policy := P.F2F3_policy }

end FLatticePaper.Induction
