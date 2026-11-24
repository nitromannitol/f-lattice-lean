import FLatticePaper.Plane.Induction.BaseFields
import FLatticePaper.Plane.Induction.SlipBase

/-! The base slip of the pure word `3^k` (`BaseSlip`): unit slip, no even slip saddle, and the slip range.

The slip of `frameAt 3^k` is `slipD k` (`slip_threes_eq`). Its star facts are proved at the raw centres (`slip_star_raw`,
from the even and odd neighbour values of `SlipBase`), and every centre is translated to a raw centre by `raw_cover_rep` and the
translation law `slipD_combine` (the incoming sites translate with the centre, `incomingNeg_add`). -/

namespace FLatticePaper.Induction

open Farey Construction FLatticePaper

/-- The star facts at a raw centre: the two incoming differences of `D` lie in `[−1, 1]`, and at an even centre `D` (with even
value) admits no saddle. -/
theorem slip_star_raw (k : ℕ) (y : Site) (hy : y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    (-1 ≤ slipD k (incomingNeg y) - slipD k y ∧ slipD k (incomingNeg y) - slipD k y ≤ 1) ∧
    (-1 ≤ slipD k (incomingPos y) - slipD k y ∧ slipD k (incomingPos y) - slipD k y ≤ 1) ∧
    (slipD k y % 2 = 0 →
      ¬ ((slipD k (incomingNeg y) - slipD k y = -1 ∧ slipD k (incomingPos y) - slipD k y = 1) ∨
        (slipD k (incomingNeg y) - slipD k y = 1 ∧ slipD k (incomingPos y) - slipD k y = -1))) := by
  obtain ⟨x, w⟩ := y
  have hyR : RawMem (2 * (k : ℤ) + 3) x w := (raw_mem_site (2 * (k : ℤ) + 3) (x, w)).mp hy
  rw [slipD_raw_Dcf k x w hyR]
  by_cases hpar : (x + w) % 2 = 0
  · have hE : FLatticePaper.EvenSite (x, w) := hpar
    have hN : incomingNeg (x, w) = (x - 1, w) := by
      unfold incomingNeg
      rw [if_pos hE]
    have hP : incomingPos (x, w) = (x + 1, w) := by
      unfold incomingPos
      rw [if_pos hE]
    rw [hN, hP, slip_val_even_minus k x w hyR hpar, slip_val_even_plus k x w hyR hpar]
    obtain ⟨hL1, hL2⟩ := slipLeft_bounds k x w hyR hpar
    obtain ⟨hR1, hR2⟩ := slipRight_bounds k x w hyR hpar
    exact ⟨⟨hL1, hL2⟩, ⟨hR1, hR2⟩, even_no_saddle k x w hyR hpar⟩
  · have hO : ¬ FLatticePaper.EvenSite (x, w) := hpar
    have hpar' : (x + w) % 2 = 1 := by
      unfold FLatticePaper.EvenSite at hO
      simp only at hO
      omega
    have hN : incomingNeg (x, w) = (x, w - 1) := by
      unfold incomingNeg
      rw [if_neg hO]
    have hP : incomingPos (x, w) = (x, w + 1) := by
      unfold incomingPos
      rw [if_neg hO]
    rw [hN, hP, slip_val_odd_down k x w hyR hpar', slip_val_odd_up k x w hyR hpar']
    obtain ⟨hD1, hD2⟩ := slipDown_bounds k x w hyR hpar'
    obtain ⟨hU1, hU2⟩ := slipUp_bounds k x w hyR hpar'
    exact ⟨⟨hD1, hD2⟩, ⟨hU1, hU2⟩, odd_no_saddle k x w hyR hpar'⟩

/-- The star facts at an arbitrary centre (translated from a raw centre). -/
theorem slip_star_all (k : ℕ) (c : Site) :
    (-1 ≤ slipD k (incomingNeg c) - slipD k c ∧ slipD k (incomingNeg c) - slipD k c ≤ 1) ∧
    (-1 ≤ slipD k (incomingPos c) - slipD k c ∧ slipD k (incomingPos c) - slipD k c ≤ 1) ∧
    (slipD k c % 2 = 0 →
      ¬ ((slipD k (incomingNeg c) - slipD k c = -1 ∧ slipD k (incomingPos c) - slipD k c = 1) ∨
        (slipD k (incomingNeg c) - slipD k c = 1 ∧ slipD k (incomingPos c) - slipD k c = -1))) := by
  obtain ⟨y, hyR, i, j, hc⟩ := raw_cover_rep k c
  subst hc
  obtain ⟨t, ht⟩ := combine_even k i j
  have hyS : y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites := (raw_mem_site _ y).mpr hyR
  obtain ⟨h1, h2, h3⟩ := slip_star_raw k y hyS
  rw [incomingNeg_add y _ t ht, incomingPos_add y _ t ht, slipD_combine, slipD_combine, slipD_combine]
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · intro hev
    have hev' : slipD k y % 2 = 0 := by omega
    have := h3 hev'
    omega

/-- The slip increment of the pure word is the difference of `D`. -/
theorem slipIncrement_threes (k : ℕ) (center input : Site) :
    slipIncrement (standardField (List.replicate k Digit.three))
        (fun z => standardField (List.replicate k Digit.three) (z + (frameAt (List.replicate k Digit.three)).shortShift))
        center input = slipD k input - slipD k center := by
  unfold slipIncrement slipD
  rw [frameAt_threes_shortShift, standardField_threes]

/-- **`F1_unitSlip` at `3^k`.** -/
theorem hasUnitSlip_threes (k : ℕ) :
    HasUnitSlip (standardField (List.replicate k Digit.three))
      (fun z => standardField (List.replicate k Digit.three) (z + (frameAt (List.replicate k Digit.three)).shortShift)) := by
  intro center input hE
  have hin : input = incomingNeg center ∨ input = incomingPos center := hE
  rw [slipIncrement_threes]
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, _⟩ := slip_star_all k center
  rcases hin with h | h
  · rw [h]
    exact ⟨a1, a2⟩
  · rw [h]
    exact ⟨b1, b2⟩

/-- **`F1_noSlipSaddle` at `3^k`.** -/
theorem noEvenSlipSaddle_threes (k : ℕ) :
    NoEvenSlipSaddle (standardField (List.replicate k Digit.three))
      (fun z => standardField (List.replicate k Digit.three) (z + (frameAt (List.replicate k Digit.three)).shortShift)) := by
  intro site hev
  have hev' : slipD k site % 2 = 0 := by
    have h := hev
    simp only [frameAt_threes_shortShift, standardField_threes] at h
    unfold slipD
    exact h
  obtain ⟨_, _, h3⟩ := slip_star_all k site
  have := h3 hev'
  simp only [slipIncrement_threes]
  exact this

/-- **`BaseSlip` of the pure word `3^k`.** -/
theorem baseSlip_threes (k : ℕ) : BaseSlip (List.replicate k Digit.three) where
  F1_unitSlip := hasUnitSlip_threes k
  F1_noSlipSaddle := noEvenSlipSaddle_threes k
  slipRange := by
    intro z hz
    rw [slip_threes_eq]
    exact slipD_raw_range k z ((raw_mem_site _ z).mpr (closedPolygon_threes_raw k z hz))

end FLatticePaper.Induction
