import FLatticePaper.Construction.AlternateStaircaseSeams

namespace FLatticePaper.Construction

open Farey

/-- The even sites of charge one in B3, as in formula (5). -/
abbrev StairEvenAltEvenBlack (den : ℤ) (point : Site) : Prop :=
  (1 ≤ point.2 ∧ point.2 ≤ den - 1 ∧
    (point.1 = 2 - den ∨ point.1 = 2 ∨ point.1 + point.2 = 2)) ∨
  (point.1 = 1 - den ∧ point.2 = 0) ∨ (point.1 = 3 ∧ point.2 = den)

/-- The odd sites of charge zero in B3, as in formula (6). -/
abbrev StairEvenAltOddWhite (den : ℤ) (point : Site) : Prop :=
  point.2 = -1 ∨ point.2 = den + 1 ∨
  (point.2 = 0 ∧ 1 ≤ point.1) ∨ (point.2 = den ∧ point.1 ≤ 3 - den) ∨
  (point.1 + point.2 = 2 - den ∧ 1 ≤ point.2 ∧ point.2 ≤ den - 2) ∨
  (point.1 + point.2 = den + 2 ∧ 2 ≤ point.2 ∧ point.2 ≤ den - 1) ∨
  (point.1 + point.2 = 1 ∧ 0 ≤ point.2 ∧ point.2 ≤ den - 2) ∨
  (point.1 + point.2 = 3 ∧ 2 ≤ point.2 ∧ point.2 ≤ den)

local macro "staircase_charge" : tactic => `(tactic|
  (simp (disch := omega) only [if_pos, if_neg]
   repeat' first | omega | (split <;> rename_i hclause <;>
     simp only [true_and, and_true, true_or, or_true, false_and, and_false, false_or, or_false,
       not_true_eq_false, not_false_eq_true] at hclause)))

set_option maxHeartbeats 850000 in
private theorem stairEvenAlt_laplacian_even {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (point : Site) (hmem : point ∈ (BaseMask.stairEvenAlt.raw den).sites) (he : EvenSite point) :
    laplacian (stairEvenAltField den standard) point =
      if StairEvenAltEvenBlack den point then -1 else 0 := by
  have hmin := hden.1
  have hd := hden.2
  have href := (reflectStairEvenAlt_mem_iff den point).mpr hmem
  have hpar := evenSite_reflectStairEvenAlt_iff den point
  rw [laplacian_stairEvenAltField_eq_background_add_residual, laplacian_stairEvenAltBackground,
    stairEvenAltResidual_on_raw hden hagree hperiod hmem,
    stairEvenAltResidual_incomingPos_reflect hden hagree hperiod]
  obtain ⟨x, y⟩ := point
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hmem
  dsimp only at hx hy hshape
  have hxy : (x + y) % 2 = 0 := he
  rw [if_pos he, stairEvenAltResidual_incomingNeg_even hden hagree hperiod hmem he,
    stairEvenAltResidual_incomingNeg_even hden hagree hperiod href (hpar.mpr he)]
  simp only [StairEvenAltEvenBlack, reflectStairEvenAlt, Prod.fst_sub, Prod.snd_sub,
    BaseMask.StairEvenAltBump]
  rcases hshape with hbody | hl | hu | hl | hr
  · by_cases hy0 : y = 0
    · by_cases hdiag : x + y = 2 <;> staircase_charge
    · by_cases hyd : y = den
      · by_cases hdiag : x + y = 2 <;> staircase_charge
      · by_cases hdiag : x + y = 2 <;> staircase_charge
  · by_cases hrail : x = 2 - den <;> staircase_charge
  · by_cases hrail : x = 2 <;> staircase_charge
  · staircase_charge
  · staircase_charge

set_option maxHeartbeats 850000 in
private theorem stairEvenAlt_laplacian_odd {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (point : Site) (hmem : point ∈ (BaseMask.stairEvenAlt.raw den).sites) (he : ¬ EvenSite point) :
    laplacian (stairEvenAltField den standard) point =
      if StairEvenAltOddWhite den point then 0 else -1 := by
  have hmin := hden.1
  have hd := hden.2
  have href := (reflectStairEvenAlt_mem_iff den point).mpr hmem
  have hpar := evenSite_reflectStairEvenAlt_iff den point
  rw [laplacian_stairEvenAltField_eq_background_add_residual, laplacian_stairEvenAltBackground,
    stairEvenAltResidual_on_raw hden hagree hperiod hmem,
    stairEvenAltResidual_incomingPos_reflect hden hagree hperiod]
  obtain ⟨x, y⟩ := point
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hmem
  dsimp only at hx hy hshape
  have hxy : (x + y) % 2 ≠ 0 := he
  rw [if_neg he, stairEvenAltResidual_incomingNeg_odd hden hagree hperiod hmem he,
    stairEvenAltResidual_incomingNeg_odd hden hagree hperiod href (fun h => he (hpar.mp h))]
  simp only [StairEvenAltOddWhite, reflectStairEvenAlt, Prod.fst_sub, Prod.snd_sub,
    BaseMask.StairEvenAltBump]
  rcases hshape with hbody | hl | hu | hl | hr
  · let neg := (y = 0 ∧ 3 ≤ x) ∨ (x + y = 2 - den ∧ 1 ≤ y ∧ y ≤ den - 2) ∨
        (x + y = 3 ∧ 2 ≤ y ∧ y ≤ den)
    let pos := (y = den ∧ x ≤ 1 - den) ∨ (x + y = den + 2 ∧ 2 ≤ y ∧ y ≤ den - 1) ∨
        (x + y = 1 ∧ 0 ≤ y ∧ y ≤ den - 2)
    have hcenter : ¬ BaseMask.StairEvenAltBump den (x, y) := by
      dsimp only [BaseMask.StairEvenAltBump]
      omega
    have hexclusive : ¬ (neg ∧ pos) := by unfold neg pos; omega
    have hwhite : StairEvenAltOddWhite den (x, y) ↔ neg ∨ pos := by
      unfold neg pos
      dsimp only [StairEvenAltOddWhite]
      by_cases h0 : y = 0
      · omega
      · by_cases hd' : y = den <;> omega
    have hneg : (if x = 1 - den ∧ y = -1 then (2 : ℤ)
        else if y = -1 ∨ (y = 0 ∧ 3 ≤ x) ∨
          (x + y = 2 - den ∧ 1 ≤ y ∧ y ≤ den - 2) ∨
          (x + y = 3 ∧ 2 ≤ y ∧ y ≤ den) ∨ (x = 3 ∧ y = den + 1)
        then 1 else 0) = if neg then 1 else 0 := by
      rw [if_neg (by omega)]
      apply if_congr ?_ rfl rfl
      unfold neg
      omega
    have hpos : (if 4 - den - x = 1 - den ∧ den - y = -1 then (2 : ℤ)
        else if den - y = -1 ∨ (den - y = 0 ∧ 3 ≤ 4 - den - x) ∨
          ((4 - den - x) + (den - y) = 2 - den ∧ 1 ≤ den - y ∧ den - y ≤ den - 2) ∨
          ((4 - den - x) + (den - y) = 3 ∧ 2 ≤ den - y ∧ den - y ≤ den) ∨
          (4 - den - x = 3 ∧ den - y = den + 1)
        then 1 else 0) = if pos then 1 else 0 := by
      clear hneg
      rw [if_neg (by omega)]
      apply if_congr ?_ rfl rfl
      unfold pos
      omega
    rw [hneg]
    erw [hpos]
    rw [if_neg hcenter, if_congr hwhite rfl rfl]
    by_cases hn : neg
    · have hp : ¬ pos := fun hp => hexclusive ⟨hn, hp⟩
      simp [hn, hp]
    · by_cases hp : pos <;> simp [hn, hp]
  · by_cases htip : x = 1 - den <;> staircase_charge
  · by_cases htip : x = 3 <;> staircase_charge
  · omega
  · omega

/-- The B3 Laplacian on the occupied raw mask in the physical chart. -/
theorem stairEvenAlt_laplacian_on_raw {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (point : Site) (hmem : point ∈ (BaseMask.stairEvenAlt.raw den).sites) :
    laplacian (stairEvenAltField den standard) point =
      if EvenSite point then (if StairEvenAltEvenBlack den point then -1 else 0)
      else (if StairEvenAltOddWhite den point then 0 else -1) := by
  by_cases he : EvenSite point
  · simpa only [if_pos he] using stairEvenAlt_laplacian_even hden hagree hperiod point hmem he
  · simpa only [if_neg he] using stairEvenAlt_laplacian_odd hden hagree hperiod point hmem he

theorem stairEvenAlt_binary_laplacian {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (point : Site) : laplacian (stairEvenAltField den standard) point = -1 ∨
      laplacian (stairEvenAltField den standard) point = 0 := by
  have hinterval : (Fraction.mk 1 den).InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  obtain ⟨site, hsite, hspan⟩ := stairEvenAlt_raw_cover hden point
  have h := laplacian_periodic_of_generatorPeriods hinterval (stairEvenAltField_periods hperiod) hspan site
  rw [show site + (point - site) = point by rw [add_comm, sub_add_cancel],
    stairEvenAlt_laplacian_on_raw hden hagree hperiod site hsite] at h
  rw [h]
  split <;> split <;> simp

end FLatticePaper.Construction
