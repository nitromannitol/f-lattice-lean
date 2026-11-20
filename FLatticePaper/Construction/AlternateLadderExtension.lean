import FLatticePaper.Construction.LadderExtension

namespace FLatticePaper.Construction

open Farey

/-- The B7 transverse constant in the raw physical coordinates. -/
def ladderOddAltConstantV (den : ℤ) : ℤ := -chooseTwo (den + 1) - 2 * den + 1

theorem ladderOddAltConstantV_eq (den : ℤ) :
    ladderOddAltConstantV den = -((den ^ 2 + 5 * den - 2) / 2) := by
  unfold ladderOddAltConstantV chooseTwo
  rw [show den ^ 2 + 5 * den - 2 = (den + 1) * (den + 1 - 1) + (2 * den - 1) * 2 by ring,
    Int.add_mul_ediv_right _ _ (by decide)]
  omega

/-- The B7 mask admits the diagonal overlap in addition to the signed generators. -/
theorem ladderOddAlt_overlap_indices {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {first second : Site} (hfirst : first ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hsecond : second ∈ (BaseMask.ladderOddAlt.raw den).sites) {i j : ℤ}
    (hshift : second = first + (reciprocalLadderDeck den).combine i j) :
    (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) ∨ (i = -1 ∧ j = 0) ∨
      (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = -1) ∨ (i = 1 ∧ j = 1) ∨ (i = -1 ∧ j = -1) := by
  obtain ⟨hmin, heven⟩ := hden
  obtain ⟨hx, hy, _⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hfirst
  obtain ⟨hx', hy', _⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hsecond
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
  have hxlo : 3 - 3 * den ≤ second.1 - first.1 := by omega
  have hxhi : second.1 - first.1 ≤ 3 * den - 3 := by omega
  have hylo : -(den + 3) ≤ second.2 - first.2 := by omega
  have hyhi : second.2 - first.2 ≤ den + 3 := by omega
  have hmulLo := mul_le_mul_of_nonneg_left hylo (show 0 ≤ den by omega)
  have hmulHi := mul_le_mul_of_nonneg_left hyhi (show 0 ≤ den by omega)
  have hwidth : den * (den + 3) + 3 * den - 3 < 2 * T := by
    dsimp [T]
    nlinarith only [hmin, sq_nonneg (den - 2)]
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
  · have hi : -1 ≤ i := by simp only [neg_mul, one_mul] at hrow; omega
    have hi' : i ≤ 0 := by
      by_contra! h
      have hmul := mul_le_mul_of_nonneg_right (show 1 ≤ i by omega) hdenPos
      simp only [neg_mul, one_mul] at hcol hmul
      omega
    omega
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
  · have hi : i ≤ 1 := by simp only [one_mul] at hrow; omega
    have hi' : 0 ≤ i := by
      by_contra! h
      have hmul := mul_le_mul_of_nonneg_right (show i ≤ -1 by omega) hdenPos
      simp only [neg_mul, one_mul] at hcol hmul
      omega
    omega

theorem ladderOddAlt_kernel_overlap {den : ℤ} {point : Site}
    (hp : point ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hq : point + (2 * den, 2) ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    point.1 + point.2 = -1 ∧ 1 ≤ point.2 ∧ point.2 ≤ den - 2 := by
  obtain ⟨hx, hy, hs⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hp
  obtain ⟨hx', hy', hs'⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hq
  simp only [BaseMask.LadderOddAltCorner, Prod.fst_add, Prod.snd_add] at hx' hy' hs hs'
  omega

theorem ladderOddAlt_transverse_overlap {den : ℤ} {point : Site}
    (hp : point ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hq : point + (1 - den, den + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    (point.2 = -1 ∧ 0 ≤ point.1 ∧ point.1 ≤ den - 1) ∨
      (point.2 = 0 ∧ point.1 = den - 1) ∨
      (point.2 = 1 ∧ den - 1 ≤ point.1 ∧ point.1 ≤ 2 * den - 2) := by
  obtain ⟨hx, hy, hs⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hp
  obtain ⟨hx', hy', hs'⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hq
  simp only [BaseMask.LadderOddAltCorner, Prod.fst_add, Prod.snd_add] at hx' hy' hs hs'
  omega

theorem ladderOddAlt_diagonal_overlap {den : ℤ} {point : Site}
    (hp : point ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hq : point + (den + 1, den + 3) ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    point = (-1, -1) := by
  obtain ⟨hx, hy, hs⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hp
  obtain ⟨hx', hy', hs'⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hq
  simp only [BaseMask.LadderOddAltCorner, Prod.fst_add, Prod.snd_add] at hx' hy' hs hs'
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

local macro "alternate_ladder_height" : tactic => `(tactic|
  (simp (disch := omega) only [BaseMask.LadderOddAltCorner, BaseMask.LadderOddAltDiagonal,
    Prod.fst_add, Prod.snd_add, if_pos, if_neg, min_eq_left, min_eq_right, max_eq_left, max_eq_right]
   omega))

private theorem ladderOddAlt_value_kernel {den : ℤ} (hmin : 4 ≤ den) {point : Site}
    (hp : point ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hq : point + (2 * den, 2) ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    BaseMask.ladderOddAltValue den (point + (2 * den, 2)) = BaseMask.ladderOddAltValue den point - 1 := by
  obtain ⟨x, y⟩ := point
  have hcase := ladderOddAlt_kernel_overlap hp hq
  dsimp only at hcase
  have hquad : chooseTwo (y + 2 + 1) = chooseTwo (y + 1) + 2 * y + 3 := by
    rw [show y + 2 + 1 = y + 1 + 2 by omega, chooseTwo_add, show chooseTwo (2 : ℤ) = 1 by decide]
    omega
  simp only [BaseMask.ladderOddAltValue, Prod.fst_add, Prod.snd_add,
    show ∀ n : ℤ, n * (n + 1) / 2 = chooseTwo (n + 1) from fun n => by
      unfold chooseTwo
      rw [add_sub_cancel_right, mul_comm n], hquad]
  clear hp hq
  alternate_ladder_height

private theorem ladderOddAlt_value_transverse {den : ℤ} (hmin : 4 ≤ den) {point : Site}
    (hp : point ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hq : point + (1 - den, den + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    BaseMask.ladderOddAltValue den (point + (1 - den, den + 1)) =
      BaseMask.ladderOddAltValue den point - (Fraction.mk 1 den).transverseGrade point + ladderOddAltConstantV den := by
  obtain ⟨x, y⟩ := point
  have hcase := ladderOddAlt_transverse_overlap hp hq
  have hquad0 : chooseTwo (den + 2) = chooseTwo (den + 1) + den + 1 := by
    rw [show den + 2 = den + 1 + 1 by omega, chooseTwo_add, show chooseTwo (1 : ℤ) = 0 by decide]
    omega
  have hquad1 : chooseTwo (den + 3) = chooseTwo (den + 1) + 2 * den + 3 := by
    rw [show den + 3 = den + 1 + 2 by omega, chooseTwo_add, show chooseTwo (2 : ℤ) = 1 by decide]
    omega
  simp only [BaseMask.ladderOddAltValue, Prod.fst_add, Prod.snd_add, Fraction.transverseGrade,
    ladderOddAltConstantV, one_mul, show ∀ n : ℤ, n * (n + 1) / 2 = chooseTwo (n + 1) from fun n => by
      unfold chooseTwo
      rw [add_sub_cancel_right, mul_comm n]]
  clear hp hq
  dsimp only at hcase
  rcases hcase with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · simp only [show (-1 : ℤ) + (den + 1) + 1 = den + 1 by omega,
      show chooseTwo ((-1 : ℤ) + 1) = 0 by decide]
    alternate_ladder_height
  · simp only [show (0 : ℤ) + (den + 1) + 1 = den + 2 by omega,
      show chooseTwo ((0 : ℤ) + 1) = 0 by decide, hquad0]
    alternate_ladder_height
  · simp only [show (1 : ℤ) + (den + 1) + 1 = den + 3 by omega,
      show chooseTwo ((1 : ℤ) + 1) = 1 by decide, hquad1]
    alternate_ladder_height

private theorem ladderOddAlt_value_diagonal {den : ℤ} (hmin : 4 ≤ den) {point : Site}
    (hp : point ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hq : point + (den + 1, den + 3) ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    BaseMask.ladderOddAltValue den (point + (den + 1, den + 3)) =
      BaseMask.ladderOddAltValue den point - 1 - (Fraction.mk 1 den).transverseGrade point + ladderOddAltConstantV den := by
  have hcorner := ladderOddAlt_diagonal_overlap hp hq
  subst point
  have htarget : ((-1, -1) : Site) + (den + 1, den + 3) = (den, den + 2) :=
    Prod.ext (by dsimp; omega) (by dsimp; omega)
  rw [htarget]
  have hquad1 : chooseTwo (den + 2 + 1) = chooseTwo (den + 1) + 2 * den + 3 := by
    rw [show den + 2 + 1 = den + 1 + 2 by omega, chooseTwo_add, show chooseTwo (2 : ℤ) = 1 by decide]
    omega
  have ha : BaseMask.LadderOddAltCorner den (-1, -1) ∨ BaseMask.LadderOddAltDiagonal den (-1, -1) :=
    Or.inl (Or.inl ⟨rfl, rfl⟩)
  have hb : BaseMask.LadderOddAltCorner den (den, den + 2) ∨ BaseMask.LadderOddAltDiagonal den (den, den + 2) :=
    Or.inl (Or.inr ⟨rfl, rfl⟩)
  simp only [BaseMask.ladderOddAltValue, Fraction.transverseGrade, one_mul,
    ladderOddAltConstantV, if_pos ha, if_pos hb,
    show ∀ n : ℤ, n * (n + 1) / 2 = chooseTwo (n + 1) from fun n => by
      unfold chooseTwo
      rw [add_sub_cancel_right, mul_comm n], hquad1, show chooseTwo ((-1 : ℤ) + 1) = 0 by decide]
  simp (disch := omega) only [min_eq_left, min_eq_right, max_eq_left, max_eq_right]
  omega

private theorem ladderOddAlt_positive_period {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    (first second : (BaseMask.ladderOddAlt.raw den).sites) {i j : ℤ}
    (hshift : second.val = first.val + (Fraction.mk 1 den).modifiedDeck.combine i j)
    (hindex : (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 1)) :
    BaseMask.ladderOddAltValue den second.val = BaseMask.ladderOddAltValue den first.val +
      periodIncrement (Fraction.mk 1 den) (-1) (ladderOddAltConstantV den) first.val i j := by
  change second.val = first.val + (reciprocalLadderDeck den).combine i j at hshift
  rw [reciprocalLadderDeck_eq hden.2] at hshift
  rcases hindex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hpos : second.val = first.val + (2 * den, 2) := by simpa [PeriodDeck.combine] using hshift
    have h := ladderOddAlt_value_kernel hden.1 first.property (hpos ▸ second.property)
    rw [← hpos] at h
    simp [periodIncrement, chooseTwo]
    omega
  · have hpos : second.val = first.val + (1 - den, den + 1) := by
      simpa [PeriodDeck.combine, add_comm 1 den] using hshift
    have h := ladderOddAlt_value_transverse hden.1 first.property (hpos ▸ second.property)
    rw [← hpos] at h
    simp [periodIncrement, chooseTwo]
    omega
  · have hpos : second.val = first.val + (den + 1, den + 3) := by
      rw [hshift]
      apply congrArg (first.val + ·)
      apply Prod.ext <;> simp only [PeriodDeck.combine, one_mul] <;> omega
    have h := ladderOddAlt_value_diagonal hden.1 first.property (hpos ▸ second.property)
    rw [← hpos] at h
    simp [periodIncrement, chooseTwo]
    omega

/-- Compatibility uses the signed generators and the one additional corner pair. -/
theorem ladderOddAlt_respectsPeriods {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den) :
    (BaseMask.ladderOddAlt.raw den).RespectsPeriods (Fraction.mk 1 den) (-1) (ladderOddAltConstantV den) := by
  intro first second i j hshift
  let fraction := Fraction.mk 1 den
  let constantV := ladderOddAltConstantV den
  have hindices := ladderOddAlt_overlap_indices hden first.property second.property hshift
  rw [BaseMask.ladderOddAlt_raw_height, BaseMask.ladderOddAlt_raw_height]
  have hnegative {p q : ℤ}
      (hmove : second.val = first.val + fraction.modifiedDeck.combine (-p) (-q))
      (hpositive : (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 1)) :
      BaseMask.ladderOddAltValue den second.val = BaseMask.ladderOddAltValue den first.val +
        periodIncrement fraction (-1) constantV first.val (-p) (-q) := by
    have hswap : first.val = second.val + fraction.modifiedDeck.combine p q := by
      rw [hmove]
      apply Prod.ext <;> simp only [PeriodDeck.combine, Prod.fst_add, Prod.snd_add] <;> ring
    have hvalue := ladderOddAlt_positive_period hden second first hswap hpositive
    change BaseMask.ladderOddAltValue den first.val = BaseMask.ladderOddAltValue den second.val +
      periodIncrement fraction (-1) constantV second.val p q at hvalue
    have hzero : periodIncrement fraction (-1) constantV second.val 0 0 = 0 := by
      simp [periodIncrement, chooseTwo]
    have hadd := periodIncrement_add fraction (-1) constantV second.val p q (-p) (-q)
    rw [add_neg_cancel, add_neg_cancel, hzero, ← hswap] at hadd
    omega
  rcases hindices with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [PeriodDeck.combine, periodIncrement, chooseTwo, show ((0, 0) : Site) = 0 from rfl]
      using congrArg (BaseMask.ladderOddAltValue den) hshift
  · exact ladderOddAlt_positive_period hden first second hshift (Or.inl ⟨rfl, rfl⟩)
  · exact hnegative (p := 1) (q := 0) hshift (Or.inl ⟨rfl, rfl⟩)
  · exact ladderOddAlt_positive_period hden first second hshift (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact hnegative (p := 0) (q := 1) hshift (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact ladderOddAlt_positive_period hden first second hshift (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact hnegative (p := 1) (q := 1) hshift (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem ladderOddAlt_exists_extension {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den) :
    ∃ field : Field, (BaseMask.ladderOddAlt.raw den).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).matrix := by
  obtain ⟨field, hagree, hperiod⟩ := HeightTile.exists_extension_of_respectsPeriods
    (ladderOddAlt_raw_cover hden) (ladderOddAlt_respectsPeriods hden)
  have hinterval : (Fraction.mk 1 den).InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  exact ⟨field, hagree, hperiod, generator_periods_growth hinterval hperiod⟩

theorem evaluateNative_threes_odd_alternate_extension (extra : ℕ) :
    let word := (BaseRun.threes extra).word
    let den : ℤ := 2 * (extra : ℤ) + 3 + 1
    let fraction := (parentsAt word).current .odd
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧
      registers.alternate.currentOdd.val.Agrees (fun site => field (site + (-1, -1))) 0 ∧
      HasGeneratorPeriods fraction field (-1) (ladderOddAltConstantV den) ∧
      HasQuadraticGrowth field fraction.matrix := by
  dsimp only
  rw [threes_current_odd]
  have hvalid : BaseMask.ladderOddAlt.Valid (2 * (extra : ℤ) + 3 + 1) := by
    change 4 ≤ 2 * (extra : ℤ) + 3 + 1 ∧ (2 * (extra : ℤ) + 3 + 1) % 2 = 0
    omega
  obtain ⟨field, hagree, hperiod, hgrowth⟩ := ladderOddAlt_exists_extension hvalid
  exact ⟨(BaseRun.threes extra).registers.llCenter, field, evaluateNative_base _,
    BaseMask.ladderOddAlt_llCenter_agrees hvalid hagree, hperiod, hgrowth⟩

end FLatticePaper.Construction
