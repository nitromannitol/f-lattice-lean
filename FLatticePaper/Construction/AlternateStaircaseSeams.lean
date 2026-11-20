import FLatticePaper.Construction.AlternateStaircaseReflection

namespace FLatticePaper.Construction

open Farey

/-- The discrepancy from the B3 background, also at sites just outside the raw support. -/
def stairEvenAltResidual (den : ℤ) (standard : Field) (point : Site) : ℤ :=
  stairEvenAltField den standard point - BaseMask.stairEvenAltBackground den point

private theorem standard_kernel_period {den : ℤ} {standard : Field} (hodd : den % 2 = 1)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (multiple : ℤ) : Function.Periodic standard (multiple * den, multiple) := by
  have hU : Function.Periodic standard (den, 1) := by
    intro point
    have h := hperiod.1 point
    change standard (point + (reciprocalEvenDeck den).kernel) = _ at h
    simpa only [reciprocalEvenDeck_eq hodd, add_zero] using h
  have heq : multiple • ((den, 1) : Site) = (multiple * den, multiple) := by
    apply Prod.ext <;> simp
  simpa only [heq] using hU.zsmul multiple

private theorem standard_at_raw {den : ℤ} {standard : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    {point : Site} (hpoint : point ∈ (BaseMask.stairEven.raw den).sites) :
    standard point = BaseMask.stairEvenValue den point := by
  have h := hagree ⟨point, hpoint⟩
  rw [BaseMask.stairEven_raw_height, add_zero] at h
  exact h.symm

private theorem standard_value_from_kernel {den : ℤ} {standard : Field}
    (hodd : den % 2 = 1) (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (point representative : Site) (index : ℤ)
    (hrep : representative ∈ (BaseMask.stairEven.raw den).sites)
    (heq : representative = point + (index * den, index)) :
    standard point = BaseMask.stairEvenValue den representative := by
  have h := standard_at_raw hagree hrep
  rw [heq, standard_kernel_period hodd hperiod index point] at h
  simpa only [heq] using h

private theorem standard_value_from_transverse {den : ℤ} {standard : Field}
    (hodd : den % 2 = 1) (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (point representative : Site) (index : ℤ)
    (hrep : representative ∈ (BaseMask.stairEven.raw den).sites)
    (heq : representative = (point + (1 - den, 1 + den)) + (index * den, index)) :
    standard point = BaseMask.stairEvenValue den representative +
      (Fraction.mk 1 den).transverseGrade point - stairEvenConstantV den := by
  have h := standard_at_raw hagree hrep
  have hV := hperiod.2 point
  change standard (point + (reciprocalEvenDeck den).transverse) = _ at hV
  rw [reciprocalEvenDeck_eq hodd] at hV
  have hval : standard representative = standard point - (Fraction.mk 1 den).transverseGrade point +
      stairEvenConstantV den := by
    rw [heq, standard_kernel_period hodd hperiod index, hV]
  omega

private theorem marker_zero_above {den : ℤ} {point : Site} (hmin : 3 ≤ den)
    (hlo : 1 - den < staircaseLevel den point) (hhi : staircaseLevel den point ≤ 2 * den) :
    stairEvenAltMarker den point = 0 := by
  have hbound : 3 - den - (Fraction.mk 1 den).periodDenominator ≤ staircaseLevel den point := by
    simp only [Fraction.periodDenominator]
    nlinarith only [hmin, hlo, sq_nonneg den]
  rw [stairEvenAltMarker_eq_of_level_bounds hmin point hbound hhi, if_neg]
  rintro ⟨row, hrow, heq⟩
  have h := mul_le_mul_of_nonneg_left (Finset.mem_Ico.mp hrow).1 (show 0 ≤ den + 1 by omega)
  rw [mul_one] at h
  omega

private theorem marker_zero_below {den : ℤ} {point : Site} (hmin : 3 ≤ den)
    (hlo : 3 - den - (Fraction.mk 1 den).periodDenominator ≤ staircaseLevel den point)
    (hhi : staircaseLevel den point < 3 - den ^ 2) : stairEvenAltMarker den point = 0 := by
  have hbound : staircaseLevel den point ≤ 2 * den := by nlinarith only [hmin, hhi, sq_nonneg den]
  rw [stairEvenAltMarker_eq_of_level_bounds hmin point hlo hbound, if_neg]
  rintro ⟨row, hrow, heq⟩
  have h := mul_le_mul_of_nonneg_left (show row ≤ den - 1 by have := (Finset.mem_Ico.mp hrow).2; omega)
    (show 0 ≤ den + 1 by omega)
  nlinarith only [h, hhi, heq]

private theorem chooseTwo_row_succ (row : ℤ) : chooseTwo (row + 1) = chooseTwo row + row := by
  simpa [chooseTwo] using chooseTwo_add row 1

private theorem chooseTwo_eq_quotient (row : ℤ) : chooseTwo row = row * (row - 1) / 2 := rfl

private theorem triangular_row (row : ℤ) : row * (row + 1) / 2 = chooseTwo (row + 1) := by
  unfold chooseTwo
  rw [show row * (row + 1) = (row + 1) * (row + 1 - 1) by ring]

private theorem leftmost_residual {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) {standard : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den)) :
    stairEvenAltResidual den standard (3 - 2 * den, den - 1) = 0 := by
  have hmin := hden.1
  have hp : (2 - den, den) ∈ (BaseMask.stairEven.raw den).sites := by
    apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
  have hs := standard_value_from_kernel hden.2 hagree hperiod (2 - 2 * den, den - 1) (2 - den, den) 1 hp
    (by apply Prod.ext <;> dsimp <;> omega)
  have hmarker : stairEvenAltMarker den (3 - 2 * den, den - 1) = 0 := by
    apply marker_zero_below hmin <;> simp only [staircaseLevel, Fraction.periodDenominator] <;> nlinarith only [hmin]
  have hcorner : ¬ BaseMask.StairEvenCorner den (2 - den, den) := by
    simp only [BaseMask.StairEvenCorner]
    omega
  simp only [stairEvenAltResidual, stairEvenAltField, BaseMask.stairEvenAltBackground,
    Prod.mk_sub_mk, sub_zero, hmarker, add_zero, triangular_row]
  rw [show 3 - 2 * den - 1 = 2 - 2 * den by omega, hs]
  simp only [BaseMask.stairEvenValue, if_neg hcorner, add_zero, ← chooseTwo_eq_quotient]
  rw [show den - 1 + 1 = den by omega, min_eq_left (by omega : 2 - den - 1 ≤ 0),
    min_eq_left (by omega : 0 ≤ 2 - (3 - 2 * den)), min_eq_right (by omega : den - 2 + (3 - 2 * den) ≤ 0),
    max_eq_right (by omega : 3 - 2 * den + (den - 1) - 2 ≤ 0)]
  omega

private theorem left_corner_residual {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) {standard : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den)) :
    stairEvenAltResidual den standard (-den, 0) = 1 := by
  have hmin := hden.1
  have hp : (den - 1, 2) ∈ (BaseMask.stairEven.raw den).sites := by
    apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
  have hs := standard_value_from_kernel hden.2 hagree hperiod (-den - 1, 0) (den - 1, 2) 2 hp
    (by
      apply Prod.ext
      · dsimp; omega
      · rfl)
  have hmarker : stairEvenAltMarker den (-den, 0) = 0 := by
    rw [stairEvenAltMarker_eq_of_level_bounds hmin _ (by
      simp only [staircaseLevel, Fraction.periodDenominator]
      nlinarith only [hmin, sq_nonneg den]) (by simp only [staircaseLevel]; omega), if_neg]
    rintro ⟨row, hrow, heq⟩
    simp only [staircaseLevel, mul_zero, sub_zero] at heq
    by_cases hr : row = 1
    · rw [hr, mul_one] at heq
      omega
    · have := mul_le_mul_of_nonneg_left (show 2 ≤ row by have := (Finset.mem_Ico.mp hrow).1; omega)
        (show 0 ≤ den + 1 by omega)
      nlinarith only [this, hmin, heq]
  have hcorner : ¬ BaseMask.StairEvenCorner den (den - 1, 2) := by
    simp only [BaseMask.StairEvenCorner]
    omega
  simp only [stairEvenAltResidual, stairEvenAltField, BaseMask.stairEvenAltBackground, BaseMask.stairEvenValue,
    Prod.mk_sub_mk, sub_zero, hmarker, add_zero, hs, if_neg hcorner]
  rw [min_eq_right (by omega : 0 ≤ den - 1 - 1), min_eq_left (by omega : 0 ≤ 2 - -den),
    min_eq_right (by omega : den - 2 + -den ≤ 0), max_eq_right (by omega : -den - 2 ≤ 0)]
  omega

private theorem lower_diagonal_residual {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) {standard : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (row : ℤ) (hlo : 2 ≤ row) (hhi : row ≤ den - 2) :
    stairEvenAltResidual den standard (2 - den - row, row - 1) = 1 := by
  have hp : (1 - row, row) ∈ (BaseMask.stairEven.raw den).sites := by
    apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
  have hs := standard_value_from_kernel hden.2 hagree hperiod (2 - den - row - 1, row - 1) (1 - row, row) 1 hp
    (by apply Prod.ext <;> dsimp <;> omega)
  have hmarker : stairEvenAltMarker den (2 - den - row, row - 1) = 1 := by
    unfold stairEvenAltMarker
    rw [if_pos]
    refine ⟨row, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    congr 1
    simp only [staircaseLevel]
    ring
  have hcorner : ¬ BaseMask.StairEvenCorner den (1 - row, row) := by
    simp only [BaseMask.StairEvenCorner]
    omega
  simp only [stairEvenAltResidual, stairEvenAltField, BaseMask.stairEvenAltBackground, BaseMask.stairEvenValue,
    Prod.mk_sub_mk, sub_zero, hmarker, hs, if_neg hcorner, add_zero, triangular_row]
  rw [show row - 1 + 1 = row by omega, min_eq_left (by omega : 1 - row - 1 ≤ 0),
    min_eq_left (by omega : 0 ≤ 2 - (2 - den - row)),
    min_eq_right (by omega : den - 2 + (2 - den - row) ≤ 0),
    max_eq_right (by omega : 2 - den - row + (row - 1) - 2 ≤ 0)]
  simp only [← chooseTwo_eq_quotient]
  omega

private theorem lower_tip_residual {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) {standard : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den)) :
    stairEvenAltResidual den standard (1, -1) = 0 := by
  have hmin := hden.1
  have hp : (1, den + 1) ∈ (BaseMask.stairEven.raw den).sites := by
    apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
  have hs := standard_value_from_transverse hden.2 hagree hperiod (0, -1) (1, den + 1) 1 hp
    (by apply Prod.ext <;> dsimp <;> omega)
  have hmarker : stairEvenAltMarker den (1, -1) = 0 := by
    apply marker_zero_above hmin <;> simp only [staircaseLevel] <;> omega
  have hcorner : ¬ BaseMask.StairEvenCorner den (1, den + 1) := by simp [BaseMask.StairEvenCorner]
  simp only [stairEvenAltResidual, stairEvenAltField, BaseMask.stairEvenAltBackground,
    Prod.mk_sub_mk, sub_zero, hmarker, add_zero, show (1 : ℤ) - 1 = 0 by decide, hs,
    BaseMask.stairEvenValue, if_neg hcorner, stairEvenConstantV, Fraction.transverseGrade]
  rw [min_eq_left (by omega : 0 ≤ den - 2 + 1)]
  simp only [← chooseTwo_eq_quotient]
  omega

private theorem lower_row_residual {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) {standard : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (x : ℤ) (hlo : 3 ≤ x) (hhi : x ≤ den) : stairEvenAltResidual den standard (x, -1) = 1 := by
  have hp : (x - den, den) ∈ (BaseMask.stairEven.raw den).sites := by
    apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
  have hs := standard_value_from_transverse hden.2 hagree hperiod (x - 1, -1) (x - den, den) 0 hp
    (by apply Prod.ext <;> dsimp <;> omega)
  have hmarker : stairEvenAltMarker den (x, -1) = 0 := by
    apply marker_zero_above hden.1 <;> simp only [staircaseLevel] <;> omega
  have hcorner : ¬ BaseMask.StairEvenCorner den (x - den, den) := by
    simp only [BaseMask.StairEvenCorner]
    omega
  simp only [stairEvenAltResidual, stairEvenAltField, BaseMask.stairEvenAltBackground,
    Prod.mk_sub_mk, sub_zero, hmarker, add_zero, hs, BaseMask.stairEvenValue, if_neg hcorner,
    stairEvenConstantV, Fraction.transverseGrade]
  rw [min_eq_left (by omega : x - den - 1 ≤ 0), min_eq_right (by omega : 2 - x ≤ 0),
    min_eq_left (by omega : 0 ≤ den - 2 + x), max_eq_left (by omega : 0 ≤ x + -1 - 2)]
  simp only [← chooseTwo_eq_quotient, chooseTwo_row_succ den]
  omega

private theorem bottom_rail_residual {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) {standard : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (x : ℤ) (hlo : 3 - den ≤ x) (hhi : x ≤ 0) : stairEvenAltResidual den standard (x, -2) = 1 := by
  have hmin := hden.1
  have hp : (x, den) ∈ (BaseMask.stairEven.raw den).sites := by
    apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
  have hs := standard_value_from_transverse hden.2 hagree hperiod (x - 1, -2) (x, den) 1 hp
    (by apply Prod.ext <;> dsimp <;> omega)
  have hmarker : stairEvenAltMarker den (x, -2) = 0 := by
    apply marker_zero_above hmin <;> simp only [staircaseLevel] <;> omega
  have hcorner : ¬ BaseMask.StairEvenCorner den (x, den) := by simp only [BaseMask.StairEvenCorner]; omega
  simp only [stairEvenAltResidual, stairEvenAltField, BaseMask.stairEvenAltBackground,
    Prod.mk_sub_mk, sub_zero, hmarker, add_zero, hs, BaseMask.stairEvenValue, if_neg hcorner,
    stairEvenConstantV, Fraction.transverseGrade]
  rw [min_eq_left (by omega : x - 1 ≤ 0), min_eq_left (by omega : 0 ≤ 2 - x),
    min_eq_left (by omega : 0 ≤ den - 2 + x), max_eq_right (by omega : x + -2 - 2 ≤ 0)]
  simp only [← chooseTwo_eq_quotient, chooseTwo_row_succ den]
  omega

private theorem bottom_corner_residual {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) {standard : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den)) :
    stairEvenAltResidual den standard (1 - den, -2) = 2 := by
  have hmin := hden.1
  have hp : (1, den + 1) ∈ (BaseMask.stairEven.raw den).sites := by
    apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
  have hs := standard_value_from_transverse hden.2 hagree hperiod (-den, -2) (1, den + 1) 2 hp
    (by apply Prod.ext <;> dsimp <;> omega)
  have hmarker : stairEvenAltMarker den (1 - den, -2) = 0 := by
    apply marker_zero_above hmin <;> simp only [staircaseLevel] <;> omega
  have hcorner : ¬ BaseMask.StairEvenCorner den (1, den + 1) := by simp [BaseMask.StairEvenCorner]
  simp only [stairEvenAltResidual, stairEvenAltField, BaseMask.stairEvenAltBackground,
    Prod.mk_sub_mk, sub_zero, hmarker, add_zero, show 1 - den - 1 = -den by omega, hs,
    BaseMask.stairEvenValue, if_neg hcorner, stairEvenConstantV, Fraction.transverseGrade]
  rw [min_eq_left (by omega : 0 ≤ 2 - (1 - den)), min_eq_right (by omega : den - 2 + (1 - den) ≤ 0),
    max_eq_right (by omega : 1 - den + -2 - 2 ≤ 0)]
  simp only [← chooseTwo_eq_quotient]
  omega

/-- The seven source values for a left or lower exit of a B3 incoming star. -/
theorem stairEvenAltResidual_incomingNeg_of_notMem {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (point : Site) (hmem : point ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hexit : incomingNeg point ∉ (BaseMask.stairEvenAlt.raw den).sites) :
    stairEvenAltResidual den standard (incomingNeg point) =
      if EvenSite point then (if point.1 = 1 - den ∧ point.2 = 0 then 1 else 0)
      else if point.1 = 1 ∧ point.2 = 0 then 0
      else if point.1 = 1 - den ∧ point.2 = -1 then 2 else 1 := by
  obtain ⟨x, y⟩ := point
  have hcases := (stairEvenAlt_incomingNeg_notMem_iff hden (x, y) hmem).mp hexit
  have hmin := hden.1
  have hodd := hden.2
  by_cases he : EvenSite (x, y)
  · simp only [incomingNeg, if_pos he] at hcases ⊢
    rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · change x = 4 - 2 * den at hx
      change y = den - 1 at hy
      rw [hx, hy, if_neg (by omega), show 4 - 2 * den - 1 = 3 - 2 * den by omega]
      exact leftmost_residual hden hagree hperiod
    · change x = 1 - den at hx
      change y = 0 at hy
      rw [hx, hy, if_pos (by exact ⟨rfl, rfl⟩), show 1 - den - 1 = -den by omega]
      exact left_corner_residual hden hagree hperiod
  · have hp : (x + y) % 2 ≠ 0 := he
    simp only [incomingNeg, if_neg he] at hcases ⊢
    rcases hcases with ⟨hsum, hlo, hhi⟩ | ⟨hy, hlo, hhi⟩ | hy
    · have hx : x = 2 - den - y := by omega
      rw [if_neg (by omega), if_neg (by omega), hx]
      exact lower_diagonal_residual hden hagree hperiod y hlo hhi
    · change y = 0 at hy
      subst y
      by_cases htip : x = 1
      · subst x
        simpa using lower_tip_residual hden hagree hperiod
      · rw [if_neg (fun h => htip h.1), if_neg (by omega)]
        exact lower_row_residual hden hagree hperiod x (by omega) hhi
    · change y = -1 at hy
      subst y
      rw [if_neg (by omega : ¬ (x = 1 ∧ (-1 : ℤ) = 0))]
      by_cases htip : x = 1 - den
      · subst x
        simpa using bottom_corner_residual hden hagree hperiod
      · rw [if_neg (fun h => htip h.1)]
        have hbounds : 1 - den ≤ x ∧ x ≤ 0 := by
          obtain ⟨_, _, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hmem
          dsimp at hshape
          omega
        exact bottom_rail_residual hden hagree hperiod x (by omega) hbounds.2

theorem stairEvenAltResidual_on_raw {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    {point : Site} (hmem : point ∈ (BaseMask.stairEvenAlt.raw den).sites) :
    stairEvenAltResidual den standard point = if BaseMask.StairEvenAltBump den point then 1 else 0 := by
  have h := stairEvenAltField_agrees hden hagree hperiod ⟨point, hmem⟩
  rw [BaseMask.stairEvenAlt_raw_height, add_zero] at h
  change BaseMask.stairEvenAltBackground den point + (if BaseMask.StairEvenAltBump den point then 1 else 0) =
    stairEvenAltField den standard point at h
  change stairEvenAltField den standard point - BaseMask.stairEvenAltBackground den point = _
  omega

theorem stairEvenAltResidual_incomingNeg_even {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    {point : Site} (hmem : point ∈ (BaseMask.stairEvenAlt.raw den).sites) (heven : EvenSite point) :
    stairEvenAltResidual den standard (incomingNeg point) =
      if (point.1 = 1 - den ∧ point.2 = 0) ∨ (point.1 = 2 - den ∧ point.2 = -1) then 1 else 0 := by
  obtain ⟨x, y⟩ := point
  have hp : (x + y) % 2 = 0 := heven
  have hmin := hden.1
  have hodd := hden.2
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hmem
  have hcases := stairEvenAlt_incomingNeg_notMem_iff hden (x, y) hmem
  simp only [if_pos heven] at hcases
  by_cases hin : incomingNeg (x, y) ∈ (BaseMask.stairEvenAlt.raw den).sites
  · rw [stairEvenAltResidual_on_raw hden hagree hperiod hin]
    simp only [incomingNeg, if_pos heven, BaseMask.StairEvenAltBump]
    apply if_congr ?_ rfl rfl
    have hnot : ¬ ((x = 4 - 2 * den ∧ y = den - 1) ∨ (x = 1 - den ∧ y = 0)) :=
      fun h => hcases.mpr h hin
    omega
  · rw [stairEvenAltResidual_incomingNeg_of_notMem hden hagree hperiod _ hmem hin, if_pos heven]
    apply if_congr ?_ rfl rfl
    have hout := hcases.mp hin
    omega

theorem stairEvenAltResidual_incomingNeg_odd {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    {point : Site} (hmem : point ∈ (BaseMask.stairEvenAlt.raw den).sites) (hodd : ¬ EvenSite point) :
    stairEvenAltResidual den standard (incomingNeg point) =
      if point.1 = 1 - den ∧ point.2 = -1 then 2
      else if point.2 = -1 ∨ (point.2 = 0 ∧ 3 ≤ point.1) ∨
        (point.1 + point.2 = 2 - den ∧ 1 ≤ point.2 ∧ point.2 ≤ den - 2) ∨
        (point.1 + point.2 = 3 ∧ 2 ≤ point.2 ∧ point.2 ≤ den) ∨
        (point.1 = 3 ∧ point.2 = den + 1) then 1 else 0 := by
  obtain ⟨x, y⟩ := point
  have hp : (x + y) % 2 ≠ 0 := hodd
  have hmin := hden.1
  have hd := hden.2
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hmem
  have hcases := stairEvenAlt_incomingNeg_notMem_iff hden (x, y) hmem
  simp only [if_neg hodd] at hcases
  by_cases hin : incomingNeg (x, y) ∈ (BaseMask.stairEvenAlt.raw den).sites
  · have hnot : ¬ ((x + y = 2 - den ∧ 2 ≤ y ∧ y ≤ den - 2) ∨
        (y = 0 ∧ 1 ≤ x ∧ x ≤ den) ∨ y = -1) := fun h => hcases.mpr h hin
    have hrail : ¬ (x = 1 - den ∧ y = -1) := by omega
    rw [stairEvenAltResidual_on_raw hden hagree hperiod hin, if_neg hrail]
    simp only [incomingNeg, if_neg hodd, BaseMask.StairEvenAltBump]
    apply if_congr ?_ rfl rfl
    rcases hshape with h | h | h | h | h <;> omega
  · have hout := hcases.mp hin
    rw [stairEvenAltResidual_incomingNeg_of_notMem hden hagree hperiod _ hmem hin, if_neg hodd]
    rcases hout with h | h | h
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    · by_cases htip : x = 1
      · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    · by_cases htip : x = 1 - den
      · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]

/-- Right and upper input heights use the same table at the reflected center. -/
theorem stairEvenAltResidual_incomingPos_reflect {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (point : Site) : stairEvenAltResidual den standard (incomingPos point) =
      stairEvenAltResidual den standard (incomingNeg (reflectStairEvenAlt den point)) := by
  rw [(incomingStar_reflectStairEvenAlt den point).1]
  exact (stairEvenAltField_residual_reflection hden hagree hperiod (incomingPos point)).symm

theorem laplacian_stairEvenAltField_eq_background_add_residual (den : ℤ) (standard : Field) (point : Site) :
    laplacian (stairEvenAltField den standard) point =
      laplacian (BaseMask.stairEvenAltBackground den) point +
        stairEvenAltResidual den standard (incomingNeg point) +
        stairEvenAltResidual den standard (incomingPos point) - 2 * stairEvenAltResidual den standard point := by
  simp only [laplacian, stairEvenAltResidual]
  ring

end FLatticePaper.Construction
