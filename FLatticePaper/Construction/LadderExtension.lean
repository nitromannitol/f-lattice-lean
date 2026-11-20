import FLatticePaper.Construction.LadderCoverage
import FLatticePaper.Construction.StaircaseExtension

namespace FLatticePaper.Construction

open Farey

/-- Every overlap between occupied B5 points is a single signed generator or zero. -/
theorem ladderOdd_overlap_indices {den : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {first second : Site} (hfirst : first ∈ (BaseMask.ladderOdd.raw den).sites)
    (hsecond : second ∈ (BaseMask.ladderOdd.raw den).sites) {i j : ℤ}
    (hshift : second = first + (reciprocalLadderDeck den).combine i j) :
    (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) ∨ (i = -1 ∧ j = 0) ∨
      (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = -1) := by
  obtain ⟨hmin, heven⟩ := hden
  obtain ⟨hx, hy, _⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hfirst
  obtain ⟨hx', hy', _⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hsecond
  rw [reciprocalLadderDeck_eq heven] at hshift
  have hcol : second.1 - first.1 = i * (2 * den) + j * (1 - den) := by
    have h := congrArg Prod.fst hshift
    simp only [Prod.fst_add, PeriodDeck.combine] at h
    omega
  have hrow : second.2 - first.2 = 2 * i + j * (den + 1) := by
    have h := congrArg Prod.snd hshift
    simp only [Prod.snd_add, PeriodDeck.combine, mul_comm i 2, add_comm 1 den] at h
    omega
  let T := den ^ 2 + 2 * den - 1
  have hT : 0 < T := by dsimp [T]; nlinarith only [hmin, sq_nonneg (den - 1)]
  have hgrade : T * j = den * (second.2 - first.2) - (second.1 - first.1) := by
    rw [hcol, hrow]
    dsimp [T]
    ring
  have hxlo : 2 - 3 * den ≤ second.1 - first.1 := by omega
  have hxhi : second.1 - first.1 ≤ 3 * den - 2 := by omega
  have hylo : -(den + 2) ≤ second.2 - first.2 := by omega
  have hyhi : second.2 - first.2 ≤ den + 2 := by omega
  have hmulLo := mul_le_mul_of_nonneg_left hylo (show 0 ≤ den by omega)
  have hmulHi := mul_le_mul_of_nonneg_left hyhi (show 0 ≤ den by omega)
  have hwidth : den * (den + 2) + 3 * den - 2 < 2 * T := by
    dsimp [T]
    nlinarith only [hmin, sq_nonneg (den - 1)]
  have hjLo : -1 ≤ j := by
    by_contra! h
    have hmul := mul_le_mul_of_nonneg_left (show j ≤ -2 by omega) hT.le
    simp only [mul_neg] at hmul
    linarith
  have hjHi : j ≤ 1 := by
    by_contra! h
    have hmul := mul_le_mul_of_nonneg_left (show 2 ≤ j by omega) hT.le
    linarith
  have hdenPos : 0 ≤ 2 * den := by omega
  rcases (show j = -1 ∨ j = 0 ∨ j = 1 by omega) with rfl | rfl | rfl
  · have hi : 0 ≤ i := by simp only [neg_mul, one_mul] at hrow; omega
    have hi' : i = 0 := by
      by_contra! h
      have hmul := mul_le_mul_of_nonneg_right (show 1 ≤ i by omega) hdenPos
      simp only [neg_mul, one_mul] at hcol hmul
      omega
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hi', rfl⟩)))
  · simp only [zero_mul, add_zero] at hcol
    have hlo : -1 ≤ i := by
      by_contra! h
      have hmul := mul_le_mul_of_nonneg_right (show i ≤ -2 by omega) hdenPos
      omega
    have hhi : i ≤ 1 := by
      by_contra! h
      have hmul := mul_le_mul_of_nonneg_right (show 2 ≤ i by omega) hdenPos
      omega
    omega
  · have hi : i ≤ 0 := by simp only [one_mul] at hrow; omega
    have hi' : i = 0 := by
      by_contra! h
      have hmul := mul_le_mul_of_nonneg_right (show i ≤ -1 by omega) hdenPos
      simp only [neg_mul, one_mul] at hcol hmul
      omega
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hi', rfl⟩)))

private theorem ladderOdd_kernel_overlap {den : ℤ} (hmin : 4 ≤ den) {point : Site}
    (hp : point ∈ (BaseMask.ladderOdd.raw den).sites)
    (hq : point + (2 * den, 2) ∈ (BaseMask.ladderOdd.raw den).sites) :
    (point.1 = 0 ∧ point.2 = 0) ∨
      (1 ≤ point.2 ∧ point.2 ≤ den - 1 ∧ point.1 + point.2 = 1) ∨
      (point.1 = 2 - den ∧ point.2 = den) := by
  obtain ⟨hx, hy, hs⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hp
  obtain ⟨hx', hy', hs'⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hq
  simp only [BaseMask.LadderOddCorner, Prod.fst_add, Prod.snd_add] at hx' hy' hs hs'
  omega

private theorem ladderOdd_transverse_overlap {den : ℤ} {point : Site}
    (hp : point ∈ (BaseMask.ladderOdd.raw den).sites)
    (hq : point + (1 - den, den + 1) ∈ (BaseMask.ladderOdd.raw den).sites) :
    (point.2 = 0 ∧ 1 ≤ point.1 ∧ point.1 ≤ den - 1) ∨
      (point.2 = 1 ∧ den + 2 ≤ point.1 ∧ point.1 ≤ 2 * den) := by
  obtain ⟨hx, hy, hs⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hp
  obtain ⟨hx', hy', hs'⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hq
  simp only [BaseMask.LadderOddCorner, Prod.fst_add, Prod.snd_add] at hx' hy' hs hs'
  omega

local macro "ladder_height" : tactic => `(tactic|
  (simp (disch := omega) only [BaseMask.LadderOddBump, Prod.fst_add, Prod.snd_add, if_pos, if_neg,
    min_eq_left, min_eq_right, max_eq_left, max_eq_right]
   omega))

private theorem ladderOdd_value_kernel {den : ℤ} (hmin : 4 ≤ den) {point : Site}
    (hp : point ∈ (BaseMask.ladderOdd.raw den).sites)
    (hq : point + (2 * den, 2) ∈ (BaseMask.ladderOdd.raw den).sites) :
    BaseMask.ladderOddValue den (point + (2 * den, 2)) = BaseMask.ladderOddValue den point := by
  obtain ⟨x, y⟩ := point
  have hcase := ladderOdd_kernel_overlap hmin hp hq
  simp only [BaseMask.ladderOddValue, Prod.fst_add, Prod.snd_add,
    show ∀ n : ℤ, n * (n - 1) / 2 = chooseTwo n from fun _ => rfl, chooseTwo_add,
    show chooseTwo (2 : ℤ) = 1 by decide]
  clear hp hq
  dsimp only at hcase
  rcases hcase with h | h | h <;> ladder_height

private theorem ladderOdd_value_transverse {den : ℤ} (hmin : 4 ≤ den) {point : Site}
    (hp : point ∈ (BaseMask.ladderOdd.raw den).sites)
    (hq : point + (1 - den, den + 1) ∈ (BaseMask.ladderOdd.raw den).sites) :
    BaseMask.ladderOddValue den (point + (1 - den, den + 1)) =
      BaseMask.ladderOddValue den point - (Fraction.mk 1 den).transverseGrade point + stairEvenConstantV den := by
  obtain ⟨x, y⟩ := point
  have hcase := ladderOdd_transverse_overlap hp hq
  simp only [BaseMask.ladderOddValue, Prod.fst_add, Prod.snd_add, Fraction.transverseGrade, one_mul,
    stairEvenConstantV, show ∀ n : ℤ, n * (n - 1) / 2 = chooseTwo n from fun _ => rfl, chooseTwo_add]
  clear hp hq
  dsimp only at hcase
  rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · simp only [show chooseTwo (0 : ℤ) = 0 by decide, zero_mul]
    ladder_height
  · simp only [show chooseTwo (1 : ℤ) = 0 by decide, one_mul, mul_one]
    ladder_height

/-- Period compatibility on all actual B5 height overlaps. -/
theorem ladderOdd_respectsPeriods {den : ℤ} (hden : BaseMask.ladderOdd.Valid den) :
    (BaseMask.ladderOdd.raw den).RespectsPeriods (Fraction.mk 1 den) 0 (stairEvenConstantV den) := by
  intro first second i j hshift
  have hindices := ladderOdd_overlap_indices hden first.property second.property hshift
  rw [BaseMask.ladderOdd_raw_height, BaseMask.ladderOdd_raw_height]
  change second.val = first.val + (reciprocalLadderDeck den).combine i j at hshift
  rw [reciprocalLadderDeck_eq hden.2] at hshift
  rcases hindices with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [PeriodDeck.combine, periodIncrement, chooseTwo, show ((0, 0) : Site) = 0 from rfl]
      using congrArg (BaseMask.ladderOddValue den) hshift
  · have hpos : second.val = first.val + (2 * den, 2) := by simpa [PeriodDeck.combine] using hshift
    have hmem := hpos ▸ second.property
    simpa [hpos, periodIncrement, chooseTwo] using ladderOdd_value_kernel hden.1 first.property hmem
  · have hpos : first.val = second.val + (2 * den, 2) := by
      apply Prod.ext <;> dsimp [PeriodDeck.combine] at hshift ⊢
      · have h := congrArg Prod.fst hshift
        dsimp at h
        omega
      · have h := congrArg Prod.snd hshift
        dsimp at h
        omega
    have hmem := hpos ▸ first.property
    simpa [hpos, periodIncrement, chooseTwo] using (ladderOdd_value_kernel hden.1 second.property hmem).symm
  · have hpos : second.val = first.val + (1 - den, den + 1) := by
      simpa [PeriodDeck.combine, add_comm 1 den] using hshift
    have hmem := hpos ▸ second.property
    rw [hpos, ladderOdd_value_transverse hden.1 first.property hmem]
    simp [periodIncrement, chooseTwo]
    omega
  · have hpos : first.val = second.val + (1 - den, den + 1) := by
      apply Prod.ext <;> dsimp [PeriodDeck.combine] at hshift ⊢
      · have h := congrArg Prod.fst hshift
        dsimp at h
        omega
      · have h := congrArg Prod.snd hshift
        dsimp at h
        omega
    have hmem := hpos ▸ first.property
    have hvalue := ladderOdd_value_transverse hden.1 second.property hmem
    rw [← hpos] at hvalue
    have hgrade : (Fraction.mk 1 den).transverseGrade first.val =
        (Fraction.mk 1 den).transverseGrade second.val + (Fraction.mk 1 den).periodDenominator := by
      rw [hpos]
      simp only [Fraction.transverseGrade, Fraction.periodDenominator, Prod.fst_add, Prod.snd_add]
      ring
    simp [periodIncrement, chooseTwo, hgrade]
    omega

/-- The global B5 height with its prescribed literal values, periods and growth. -/
theorem ladderOdd_exists_extension {den : ℤ} (hden : BaseMask.ladderOdd.Valid den) :
    ∃ field : Field, (BaseMask.ladderOdd.raw den).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).matrix := by
  obtain ⟨field, hagree, hperiod⟩ := HeightTile.exists_extension_of_respectsPeriods
    (ladderOdd_raw_cover hden) (ladderOdd_respectsPeriods hden)
  have hinterval : (Fraction.mk 1 den).InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  exact ⟨field, hagree, hperiod, generator_periods_growth hinterval hperiod⟩

theorem evaluateNative_threes_odd_standard_extension (extra : ℕ) :
    let word := (BaseRun.threes extra).word
    let den : ℤ := 2 * (extra : ℤ) + 3 + 1
    let fraction := (parentsAt word).current .odd
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.standard.currentOdd.val.Agrees field 0 ∧
      HasGeneratorPeriods fraction field 0 (stairEvenConstantV den) ∧
      HasQuadraticGrowth field fraction.matrix := by
  dsimp only
  rw [threes_current_odd]
  have hvalid : BaseMask.ladderOdd.Valid (2 * (extra : ℤ) + 3 + 1) := by
    change 4 ≤ 2 * (extra : ℤ) + 3 + 1 ∧ (2 * (extra : ℤ) + 3 + 1) % 2 = 0
    omega
  obtain ⟨field, hagree, hperiod, hgrowth⟩ := ladderOdd_exists_extension hvalid
  exact ⟨(BaseRun.threes extra).registers.llCenter, field, evaluateNative_base _,
    BaseMask.ladderOdd_llCenter_agrees hvalid hagree, hperiod, hgrowth⟩

end FLatticePaper.Construction
