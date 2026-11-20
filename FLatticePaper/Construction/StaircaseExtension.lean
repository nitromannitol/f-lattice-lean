import FLatticePaper.Construction.PeriodExtension
import FLatticePaper.Construction.StaircaseCoverage
import FLatticePaper.Plane.QuadraticGrowth

namespace FLatticePaper.Construction

open Farey

/-- The transverse period constant in the raw B1 coordinates. -/
def stairEvenConstantV (den : ℤ) : ℤ := -chooseTwo (den + 1) - den

theorem stairEvenConstantV_eq (den : ℤ) :
    stairEvenConstantV den = -(den * (den + 3) / 2) := by
  unfold stairEvenConstantV chooseTwo
  rw [show den * (den + 3) = (den + 1) * (den + 1 - 1) + den * 2 by ring,
    Int.add_mul_ediv_right _ _ (by decide)]
  omega

/-- Two occupied raw B1 sites in one deck class coincide or differ by one
of the signed generators. The argument uses their actual coordinate bounds. -/
theorem stairEven_overlap_indices {den : ℤ} (hden : BaseMask.stairEven.Valid den)
    {first second : Site} (hfirst : first ∈ (BaseMask.stairEven.raw den).sites)
    (hsecond : second ∈ (BaseMask.stairEven.raw den).sites) {i j : ℤ}
    (hshift : second = first + (reciprocalEvenDeck den).combine i j) :
    (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) ∨ (i = -1 ∧ j = 0) ∨
      (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = -1) := by
  obtain ⟨hmin, hodd⟩ := hden
  obtain ⟨hx, hy, _⟩ := BaseMask.mem_stairEven_raw_iff.mp hfirst
  obtain ⟨hx', hy', _⟩ := BaseMask.mem_stairEven_raw_iff.mp hsecond
  rw [reciprocalEvenDeck_eq hodd] at hshift
  have hcol : second.1 - first.1 = i * den + j * (1 - den) := by
    have h := congrArg Prod.fst hshift
    simp only [Prod.fst_add, PeriodDeck.combine] at h
    omega
  have hrow : second.2 - first.2 = i + j * (den + 1) := by
    have h := congrArg Prod.snd hshift
    simp only [Prod.snd_add, PeriodDeck.combine, mul_one, add_comm 1 den] at h
    omega
  let determinant := den ^ 2 + 2 * den - 1
  have hdet : 0 < determinant := by dsimp [determinant]; nlinarith only [hmin, sq_nonneg (den - 1)]
  have hgrade : determinant * j = den * (second.2 - first.2) - (second.1 - first.1) := by
    rw [hcol, hrow]
    dsimp [determinant]
    ring
  have hdyLo : -(den + 1) ≤ second.2 - first.2 := by omega
  have hdyHi : second.2 - first.2 ≤ den + 1 := by omega
  have hmulLo := mul_le_mul_of_nonneg_left hdyLo (by omega : 0 ≤ den)
  have hmulHi := mul_le_mul_of_nonneg_left hdyHi (by omega : 0 ≤ den)
  have hwidth : den * (den + 1) + 2 * den - 2 < 2 * determinant := by
    dsimp [determinant]
    nlinarith only [hmin, sq_nonneg (den - 1)]
  have hjLo : -1 ≤ j := by
    by_contra! h
    have hmult := mul_le_mul_of_nonneg_left (show j ≤ -2 by omega) hdet.le
    nlinarith only [hgrade, hmult, hmulLo, hwidth, show second.1 - first.1 ≤ 2 * den - 2 by omega]
  have hjHi : j ≤ 1 := by
    by_contra! h
    have hmult := mul_le_mul_of_nonneg_left (show 2 ≤ j by omega) hdet.le
    nlinarith only [hgrade, hmult, hmulHi, hwidth, show 2 - 2 * den ≤ second.1 - first.1 by omega]
  have hbound (a : ℤ) (hlo : 2 - 2 * den ≤ a * den) (hhi : a * den ≤ 2 * den - 2) :
      -1 ≤ a ∧ a ≤ 1 := by
    constructor
    · by_contra! h
      have := mul_le_mul_of_nonneg_right (show a ≤ -2 by omega) (show 0 ≤ den by omega)
      omega
    · by_contra! h
      have := mul_le_mul_of_nonneg_right (show 2 ≤ a by omega) (show 0 ≤ den by omega)
      omega
  obtain hj | hj | hj : j = -1 ∨ j = 0 ∨ j = 1 := by omega
  all_goals subst j
  · simp only [neg_mul, one_mul] at hrow hcol
    have hi : 0 ≤ i := by omega
    have hzero : i = 0 := by
      by_contra! h
      have := mul_le_mul_of_nonneg_right (show 1 ≤ i by omega) (show 0 ≤ den by omega)
      omega
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hzero, rfl⟩)))
  · simp only [zero_mul, add_zero] at hcol
    have := hbound i (by omega) (by omega)
    omega
  · have hi : i ≤ 0 := by simp only [one_mul] at hrow; omega
    have hzero : i = 0 := by
      by_contra! h
      have := mul_le_mul_of_nonneg_right (show i ≤ -1 by omega) (show 0 ≤ den by omega)
      simp only [one_mul] at hcol
      omega
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hzero, rfl⟩)))

private theorem stairEven_value_kernel {den : ℤ} (hmin : 3 ≤ den) {point : Site}
    (hp : point ∈ (BaseMask.stairEven.raw den).sites)
    (hq : point + (den, 1) ∈ (BaseMask.stairEven.raw den).sites) :
    BaseMask.stairEvenValue den (point + (den, 1)) = BaseMask.stairEvenValue den point := by
  obtain ⟨hx, hy, hs⟩ := BaseMask.mem_stairEven_raw_iff.mp hp
  obtain ⟨hx', hy', hs'⟩ := BaseMask.mem_stairEven_raw_iff.mp hq
  simp only [Prod.fst_add, Prod.snd_add] at hx' hy'
  have hbinom : chooseTwo (point.2 + 1) = chooseTwo point.2 + point.2 := by
    simpa [chooseTwo] using chooseTwo_add point.2 1
  unfold BaseMask.stairEvenValue
  simp only [Prod.fst_add, Prod.snd_add]
  rw [show (point.2 + 1) * (point.2 + 1 - 1) / 2 = chooseTwo (point.2 + 1) from rfl,
    show point.2 * (point.2 - 1) / 2 = chooseTwo point.2 from rfl, hbinom,
    min_eq_right (by omega : 0 ≤ point.1 + den - 1), min_eq_left (by omega : point.1 - 1 ≤ 0)]
  split <;> split <;> simp only [BaseMask.StairEvenCorner, Prod.fst_add, Prod.snd_add] at * <;> omega

private theorem stairEven_value_transverse {den : ℤ} (hmin : 3 ≤ den) {point : Site}
    (hp : point ∈ (BaseMask.stairEven.raw den).sites)
    (hq : point + (1 - den, den + 1) ∈ (BaseMask.stairEven.raw den).sites) :
    BaseMask.stairEvenValue den (point + (1 - den, den + 1)) =
      BaseMask.stairEvenValue den point - (Fraction.mk 1 den).transverseGrade point + stairEvenConstantV den := by
  obtain ⟨hx, hy, _⟩ := BaseMask.mem_stairEven_raw_iff.mp hp
  obtain ⟨hx', hy', _⟩ := BaseMask.mem_stairEven_raw_iff.mp hq
  simp only [Prod.fst_add, Prod.snd_add] at hx' hy'
  have hy0 : point.2 = 0 := by omega
  have hcorn₁ : ¬ BaseMask.StairEvenCorner den point := by
    unfold BaseMask.StairEvenCorner
    omega
  have hcorn₂ : ¬ BaseMask.StairEvenCorner den (point + (1 - den, den + 1)) := by
    simp only [BaseMask.StairEvenCorner, Prod.fst_add, Prod.snd_add]
    omega
  simp only [BaseMask.stairEvenValue, if_neg hcorn₁, if_neg hcorn₂, Prod.fst_add, Prod.snd_add,
    Fraction.transverseGrade, one_mul, hy0, add_zero, zero_mul, mul_zero, zero_add, Int.zero_ediv,
    neg_zero, zero_sub, stairEvenConstantV, chooseTwo]
  rw [min_eq_left (by omega : point.1 + (1 - den) - 1 ≤ 0),
    min_eq_right (by omega : 0 ≤ point.1 - 1)]
  omega

/-- Exact B1 height agreement on every occupied overlap for the stated constants. -/
theorem stairEven_respectsPeriods {den : ℤ} (hden : BaseMask.stairEven.Valid den) :
    (BaseMask.stairEven.raw den).RespectsPeriods (Fraction.mk 1 den) 0 (stairEvenConstantV den) := by
  intro first second i j hshift
  have hindices := stairEven_overlap_indices hden first.property second.property hshift
  rw [BaseMask.stairEven_raw_height, BaseMask.stairEven_raw_height]
  change second.val = first.val + (reciprocalEvenDeck den).combine i j at hshift
  rw [reciprocalEvenDeck_eq hden.2] at hshift
  rcases hindices with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [PeriodDeck.combine, periodIncrement, chooseTwo, show ((0, 0) : Site) = 0 from rfl]
      using congrArg (BaseMask.stairEvenValue den) hshift
  · have hpos : second.val = first.val + (den, 1) := by simpa [PeriodDeck.combine] using hshift
    have hmem := hpos ▸ second.property
    simpa [hpos, periodIncrement, chooseTwo] using stairEven_value_kernel hden.1 first.property hmem
  · have hpos : first.val = second.val + (den, 1) := by
      apply Prod.ext <;> dsimp [PeriodDeck.combine] at hshift ⊢
      · have := congrArg Prod.fst hshift
        dsimp at this
        omega
      · have := congrArg Prod.snd hshift
        dsimp at this
        omega
    have hmem := hpos ▸ first.property
    simpa [hpos, periodIncrement, chooseTwo] using (stairEven_value_kernel hden.1 second.property hmem).symm
  · have hpos : second.val = first.val + (1 - den, den + 1) := by
      simpa [PeriodDeck.combine, add_comm 1 den] using hshift
    have hmem := hpos ▸ second.property
    rw [hpos, stairEven_value_transverse hden.1 first.property hmem]
    simp [periodIncrement, chooseTwo]
    omega
  · have hpos : first.val = second.val + (1 - den, den + 1) := by
      apply Prod.ext <;> dsimp [PeriodDeck.combine] at hshift ⊢
      · have := congrArg Prod.fst hshift
        dsimp at this
        omega
      · have := congrArg Prod.snd hshift
        dsimp at this
        omega
    have hmem := hpos ▸ first.property
    have hvalue := stairEven_value_transverse hden.1 second.property hmem
    rw [← hpos] at hvalue
    have hgrade : (Fraction.mk 1 den).transverseGrade first.val =
        (Fraction.mk 1 den).transverseGrade second.val + (Fraction.mk 1 den).periodDenominator := by
      rw [hpos]
      simp only [Fraction.transverseGrade, Fraction.periodDenominator, Prod.fst_add, Prod.snd_add]
      ring
    simp [periodIncrement, chooseTwo, hgrade]
    omega

/-- The global B1 height in raw physical coordinates, with its exact
overlap law and source period constants. -/
theorem stairEven_exists_extension {den : ℤ} (hden : BaseMask.stairEven.Valid den) :
    ∃ field : Field, (BaseMask.stairEven.raw den).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).matrix := by
  obtain ⟨field, hagree, hperiod⟩ := HeightTile.exists_extension_of_respectsPeriods
    (stairEven_raw_cover hden) (stairEven_respectsPeriods hden)
  have hinterval : (Fraction.mk 1 den).InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  exact ⟨field, hagree, hperiod, generator_periods_growth hinterval hperiod⟩

end FLatticePaper.Construction
