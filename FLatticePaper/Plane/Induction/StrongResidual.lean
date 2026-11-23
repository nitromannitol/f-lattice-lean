import FLatticePaper.Plane.Induction.SlipFields
import FLatticePaper.Plane.Induction.WeightPolicy

/-! Task 40, step 2: the residual of the strong estimates after the slip fields.

`StrongResidual u` is the part of `StrongEstimates u` that is not yet proved at `u` from its own data and the conjugate's strong
data: the price range, the price unit and no-saddle conditions, the price and slip drifts, the zero strip and its even line, and
the per-phase policy with ranks. The packet, the slip range and the slip unit and no-saddle fields are proved in `SlipFields`
(`i3_slipFields_of_strong`) from the star-zone inputs of `u`, the strong data of `conjWord u` and the arc inputs of `u`.

`StrongEstimates.of_residual` assembles the strong estimates of `u` from the packet, these inputs and the residual. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The residual of the strong estimates of a standard field (the fields not yet proved from the strong data of the conjugate). -/
structure StrongResidual (u : Word) : Prop where
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


/-- The residual with the reduced policy field (task 43): one strict rank with increments `(−1, η)` on the child's generators, and a
quota policy along which `Φ_η`, the price `P` and the rounded slip `J_η` do not increase. The other fields are those of
`StrongResidual`. -/
structure StrongResidualReduced (u : Word) : Prop where
  /-- The primitive-price range, as in `StrongResidual`. -/
  priceRange : ∀ z ∈ (frameAt u).closedPolygon,
    (frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) z ∧
      (frameAt u).price (standardField u) z ≤ (frameAt u).cutPrice
  /-- The drifts of the primitive price, as in `StrongResidual`. -/
  priceDrift : ∀ z,
    (frameAt u).price (standardField u) (z + (frameAt u).child.modifiedDeck.kernel) -
        (frameAt u).price (standardField u) z = -1 ∧
      (frameAt u).price (standardField u) (z + (frameAt u).child.modifiedDeck.transverse) -
        (frameAt u).price (standardField u) z = 0
  /-- The drifts of the short slip, as in `StrongResidual`. -/
  slipDrift : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ z,
    (frameAt u).slip (standardField u) η (z + (frameAt u).child.modifiedDeck.kernel) -
        (frameAt u).slip (standardField u) η z = 0 ∧
      (frameAt u).slip (standardField u) η (z + (frameAt u).child.modifiedDeck.transverse) -
        (frameAt u).slip (standardField u) η z = 2 * η
  /-- The zero strip, as in `StrongResidual`. -/
  zeroStripInterval : ∀ x : Site,
    1 - parentD u ≤ parentN u * x.1 - parentD u * x.2 →
      parentN u * x.1 - parentD u * x.2 ≤ parentN u + 2 * parentD u - 1 →
        quarterTurnField (standardField u) x = 0
  /-- The even line, as in `StrongResidual`. -/
  zeroEvenLine : ∀ x : Site, (x.1 + x.2) % 2 = 0 →
    parentN u * x.1 - parentD u * x.2 = -parentD u → quarterTurnField (standardField u) x = 0
  /-- F1, the primitive price: unit increments on every edge. -/
  F1_unitPrice : HasUnitPrice (frameAt u) (standardField u)
  /-- F1, the primitive price: no opposite nonzero increments at a star. -/
  F1_noPriceSaddle : NoPriceSaddle (frameAt u) (standardField u)
  /-- The reduced F2F3: for `η = ±1` a quota policy along which `Φ_η`, the price and the rounded slip do not increase, and one
  strict rank with increments `(−1, η)` on the child's generators. -/
  F2F3_reduced : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ policy : Site → Site → Prop,
    RetainQuota (standardField u) policy ∧
      NonincreasingAlong ((frameAt u).chainPotential (standardField u) η) policy ∧
      NonincreasingAlong ((frameAt u).price (standardField u)) policy ∧
      NonincreasingAlong ((frameAt u).roundedSlip (standardField u) η) policy ∧
      RankWithIncrements policy (frameAt u).child.modifiedDeck.kernel (frameAt u).child.modifiedDeck.transverse (-1) η

/-- The determinant of the child's modified deck is nonzero (it is positive). -/
theorem child_det_ne_zero (u : Word) :
    (frameAt u).child.modifiedDeck.kernel.1 * (frameAt u).child.modifiedDeck.transverse.2 -
      (frameAt u).child.modifiedDeck.kernel.2 * (frameAt u).child.modifiedDeck.transverse.1 ≠ 0 := by
  have hint : (frameAt u).child.InUnitInterval :=
    Fraction.Interior.inUnitInterval ((parentsAt_valid u).current_interior .even)
  have h := Fraction.det_modifiedDeck_pos hint
  unfold PeriodDeck.det at h
  exact h.ne'

/-- The old policy field, from the reduced one: the `(a, c)`-family of ranks follows from the rank at `(1, 1)` and the monotone
price and rounded slip (`rankWithIncrements_of_monotone_hull`). -/
theorem StrongResidualReduced.F2F3_policy {u : Word} (R : StrongResidualReduced u) :
    ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ policy : Site → Site → Prop,
      RetainQuota (standardField u) policy ∧
        NonincreasingAlong ((frameAt u).chainPotential (standardField u) η) policy ∧
        ∀ a c : ℤ, 0 < a → 0 < c →
          RankWithIncrements policy (frameAt u).child.modifiedDeck.kernel (frameAt u).child.modifiedDeck.transverse
            (-a) (c * η) := by
  intro η hη
  obtain ⟨policy, hq, hΦ, hP, hJ, hrank⟩ := R.F2F3_reduced η hη
  refine ⟨policy, hq, hΦ, fun a c ha hc => ?_⟩
  refine rankWithIncrements_of_monotone_hull (child_det_ne_zero u) hη ?_ ?_ ?_ ?_
    (fun x y h => ⟨hP x y h, hJ x y h⟩) hrank a c ha hc
  · intro z
    have := (R.priceDrift z).1
    linarith
  · intro z
    have := (R.priceDrift z).2
    linarith
  · intro z
    have := (R.slipDrift η hη z).1
    unfold ChildFrame.roundedSlip
    omega
  · intro z
    have := (R.slipDrift η hη z).2
    unfold ChildFrame.roundedSlip
    omega

/-- **The old residual from the reduced one**: the policy field is derived, so `StrongResidual` and everything downstream of it are
unchanged. -/
theorem StrongResidual.of_reduced {u : Word} (R : StrongResidualReduced u) : StrongResidual u :=
  { priceRange := R.priceRange
    priceDrift := R.priceDrift
    slipDrift := R.slipDrift
    zeroStripInterval := R.zeroStripInterval
    zeroEvenLine := R.zeroEvenLine
    F1_unitPrice := R.F1_unitPrice
    F1_noPriceSaddle := R.F1_noPriceSaddle
    F2F3_policy := R.F2F3_policy }

/-- **The strong estimates of a proper word from the conjugate's strong data, the star-zone inputs, the arc inputs and the residual.** -/
theorem StrongEstimates.of_residual {u : Word} (hw : ∃ x ∈ u, x ≠ Digit.three)
    (hpk : (frameAt u).Packet (standardField u)) (hstar : StarZoneInputs u)
    (arcs : VArcInputs (frameAt u) (standardField u)) (h : StrongEstimates (conjWord u))
    (R : StrongResidual u) : StrongEstimates u :=
  { packet := hpk
    slipRange := (i3_slipFields_of_strong hw h hstar arcs).2.2
    priceRange := R.priceRange
    priceDrift := R.priceDrift
    slipDrift := R.slipDrift
    zeroStripInterval := R.zeroStripInterval
    zeroEvenLine := R.zeroEvenLine
    F1_unitSlip := (i3_slipFields_of_strong hw h hstar arcs).1
    F1_noSlipSaddle := (i3_slipFields_of_strong hw h hstar arcs).2.1
    F1_unitPrice := R.F1_unitPrice
    F1_noPriceSaddle := R.F1_noPriceSaddle
    F2F3_policy := R.F2F3_policy }

end FLatticePaper.Induction
