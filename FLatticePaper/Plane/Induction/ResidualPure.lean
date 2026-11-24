import FLatticePaper.Plane.Induction.StrongResidual
import FLatticePaper.Plane.Induction.W1ZeroStrip
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.SlipBase
import FLatticePaper.Plane.Induction.NoSaddle
import FLatticePaper.Plane.Induction.PriceRange
import FLatticePaper.Plane.Induction.PureBaseUnitPrice
import FLatticePaper.Plane.Induction.PureBasePrice
import FLatticePaper.Plane.Induction.W1BaseSeeds

/-! `StrongResidual` at the pure word `3^k`, except the policy field `F2F3_policy`, which is a hypothesis.

The zero strip is `zeroStripInterval_of_packet` at the reciprocal packet. The even line is `zeroEvenLine_field`, whose inputs are the
price range and drifts (`PriceRange`, `PureBasePrice`) and the odd seed `F w = harmonicGrid w` on `sGrade = 2 − 3d + 1`. The seed
holds on the whole line: its odd points are `(0,−3) + n·T`, `F(0,−3) = −1 = harmonicGrid(0,−3)` (`reciprocal_neg_three`), and both
`F` and `harmonicGrid` change by the same amount `w₁ − d w₂ + cV` under `T`. -/

namespace FLatticePaper.Induction

open Farey Construction FLatticePaper

/-- The harmonic grid changes along the transverse period `T = (1−d, 1+d)` by `w₁ − d w₂ + cV`, `cV = −d(d+3)/2`. -/
theorem harmonicGrid_T_threes (k : ℕ) (w : Site) :
    harmonicGrid (w + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) =
      harmonicGrid w + (w.1 - (2 * (k : ℤ) + 3) * w.2) + stairEvenConstantV (2 * (k : ℤ) + 3) := by
  have hc : (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3 + 3) / 2 = (2 * (k : ℤ) + 3) * ((k : ℤ) + 3) := by
    rw [show (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3 + 3) = 2 * ((2 * (k : ℤ) + 3) * ((k : ℤ) + 3)) by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [stairEvenConstantV_eq, hc]
  unfold harmonicGrid
  simp only [Prod.fst_add, Prod.snd_add]
  have hp : (w.1 + (1 - (2 * (k : ℤ) + 3)) + (w.2 + (1 + (2 * (k : ℤ) + 3)))) % 2 = (w.1 + w.2) % 2 := by
    omega
  rw [hp]
  have key : (w.1 + (1 - (2 * (k : ℤ) + 3))) ^ 2 + 2 * (w.1 + (1 - (2 * (k : ℤ) + 3))) * (w.2 + (1 + (2 * (k : ℤ) + 3)))
      - (w.2 + (1 + (2 * (k : ℤ) + 3))) ^ 2 - 2 * (w.2 + (1 + (2 * (k : ℤ) + 3))) - (w.1 + w.2) % 2
      = (w.1 ^ 2 + 2 * w.1 * w.2 - w.2 ^ 2 - 2 * w.2 - (w.1 + w.2) % 2)
        + 4 * (w.1 - (2 * (k : ℤ) + 3) * w.2 - (2 * (k : ℤ) + 3) * ((k : ℤ) + 3)) := by
    ring
  rw [key, Int.add_mul_ediv_left _ _ (by norm_num : (4 : ℤ) ≠ 0)]
  ring

/-- `F = harmonicGrid` is transported along the transverse period, in both directions. -/
theorem reciprocalField_harmonic_step (k : ℕ) (z : Site) :
    reciprocalField k z = harmonicGrid z ↔
      reciprocalField k (z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) =
        harmonicGrid (z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) := by
  rw [reciprocalField_T, harmonicGrid_T_threes]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    linarith

/-- The seed line `F = harmonicGrid` on `(0,−3) + n·T`. -/
theorem reciprocalField_harmonic_line (k : ℕ) (n : ℤ) :
    reciprocalField k ((0, -3) + (n * (1 - (2 * (k : ℤ) + 3)), n * (1 + (2 * (k : ℤ) + 3)))) =
      harmonicGrid ((0, -3) + (n * (1 - (2 * (k : ℤ) + 3)), n * (1 + (2 * (k : ℤ) + 3)))) := by
  refine Int.induction_on n ?_ ?_ ?_
  · have e0 : ((0 : ℤ), (-3 : ℤ)) + ((0 : ℤ) * (1 - (2 * (k : ℤ) + 3)), (0 : ℤ) * (1 + (2 * (k : ℤ) + 3))) = (0, -3) := by
      ext <;> simp
    rw [e0, FLatticePaper.W1BaseSeeds.reciprocal_neg_three k]
    unfold harmonicGrid
    norm_num
  · intro i ih
    have e : ((0 : ℤ), (-3 : ℤ)) + (((i : ℤ) + 1) * (1 - (2 * (k : ℤ) + 3)), ((i : ℤ) + 1) * (1 + (2 * (k : ℤ) + 3))) =
        ((0, -3) + ((i : ℤ) * (1 - (2 * (k : ℤ) + 3)), (i : ℤ) * (1 + (2 * (k : ℤ) + 3)))) +
          (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add]
      all_goals ring
    rw [e]
    exact (reciprocalField_harmonic_step k _).mp ih
  · intro i ih
    have e : ((0 : ℤ), (-3 : ℤ)) + ((-(i : ℤ) - 1) * (1 - (2 * (k : ℤ) + 3)), (-(i : ℤ) - 1) * (1 + (2 * (k : ℤ) + 3))) +
        (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) =
        ((0, -3) + (-(i : ℤ) * (1 - (2 * (k : ℤ) + 3)), -(i : ℤ) * (1 + (2 * (k : ℤ) + 3)))) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add]
      all_goals ring
    have h := (reciprocalField_harmonic_step k ((0, -3) + ((-(i : ℤ) - 1) * (1 - (2 * (k : ℤ) + 3)), (-(i : ℤ) - 1) * (1 + (2 * (k : ℤ) + 3))))).mpr
    rw [e] at h
    exact h ih

/-- The odd seed on the line `(d+1) w₁ + (d−1) w₂ = 3 − 3d`: `F w = harmonicGrid w` (the line is `(0,−3) + n·T` at odd sites). -/
theorem reciprocalField_harmonic_odd_line (k : ℕ) (w : Site) (hodd : (w.1 + w.2) % 2 = 1)
    (hline : (2 * (k : ℤ) + 3 + 1) * w.1 + (2 * (k : ℤ) + 3 - 1) * w.2 = 2 - 3 * (2 * (k : ℤ) + 3) + 1) :
    reciprocalField k w = harmonicGrid w := by
  have E : ((k : ℤ) + 2) * w.1 + ((k : ℤ) + 1) * (w.2 + 3) = 0 := by
    linarith
  obtain ⟨j, hj⟩ : ∃ j : ℤ, -(w.1 + w.2 + 3) = 2 * j := ⟨-(w.1 + w.2 + 3) / 2, by omega⟩
  have h1 : w.1 = ((k : ℤ) + 1) * (-(w.1 + w.2 + 3)) := by linear_combination E
  have h2 : w.2 + 3 = -((k : ℤ) + 2) * (-(w.1 + w.2 + 3)) := by linear_combination (-1 : ℤ) * E
  have hw : w = (0, -3) + ((-j) * (1 - (2 * (k : ℤ) + 3)), (-j) * (1 + (2 * (k : ℤ) + 3))) := by
    rw [hj] at h1 h2
    ext
    · simp only [Prod.fst_add]
      linear_combination h1
    · simp only [Prod.snd_add]
      linear_combination h2
  rw [hw]
  exact reciprocalField_harmonic_line k (-j)

/-- The seed hypothesis of `zeroEvenLine_field` at `3^k`. -/
theorem standardField_threes_harmonic_seed (k : ℕ) :
    ∀ w : Site, ¬ FLatticePaper.EvenSite w →
      (frameAt (List.replicate k Digit.three)).sGrade w =
        2 - 3 * (frameAt (List.replicate k Digit.three)).child.den +
          (frameAt (List.replicate k Digit.three)).child.num →
        standardField (List.replicate k Digit.three) w = harmonicGrid w := by
  intro w hw hs
  rw [standardField_threes]
  have hc := frameAt_threes_child k
  unfold ChildFrame.sGrade at hs
  rw [hc] at hs
  simp only at hs
  apply reciprocalField_harmonic_odd_line k w
  · unfold FLatticePaper.EvenSite at hw
    omega
  · linarith

/-- **`StrongResidual` at the pure word `3^k`, with the policy field as a hypothesis.** -/
theorem strongResidual_threes_of_policy (k : ℕ)
    (hpol : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ policy : Site → Site → Prop,
      RetainQuota (standardField (List.replicate k Digit.three)) policy ∧
        NonincreasingAlong ((frameAt (List.replicate k Digit.three)).chainPotential
          (standardField (List.replicate k Digit.three)) η) policy ∧
        ∀ a c : ℤ, 0 < a → 0 < c →
          RankWithIncrements policy (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel
            (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse (-a) (c * η)) :
    StrongResidual (List.replicate k Digit.three) where
  priceRange := priceRange_threes k
  priceDrift := fun z => (strongResidual_priceDrift_threes k z)
  slipDrift := strongResidual_slipDrift_threes k
  zeroStripInterval := FLatticePaper.W1ZeroStrip.zeroStripInterval_of_packet (List.replicate k Digit.three) (reciprocal_packet k)
  zeroEvenLine := FLatticePaper.W1ZeroStrip.zeroEvenLine_field (List.replicate k Digit.three) (reciprocal_packet k) (priceRange_threes k)
    (fun z => by have h := (strongResidual_priceDrift_threes k z).1; linarith)
    (fun z => by have h := (strongResidual_priceDrift_threes k z).2; linarith)
    (standardField_threes_harmonic_seed k)
  F1_unitPrice := hasUnitPrice_threes k
  F1_noPriceSaddle := noPriceSaddle_threes k
  F2F3_policy := hpol

end FLatticePaper.Induction
