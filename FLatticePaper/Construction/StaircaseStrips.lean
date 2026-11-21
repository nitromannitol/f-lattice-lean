import FLatticePaper.Construction.StaircaseExtension

namespace FLatticePaper.Construction

open Farey

private theorem stairEven_value_zero_of_grade {den : ℤ} (hden : 3 ≤ den) {point : Site}
    (hpoint : point ∈ (BaseMask.stairEven.raw den).sites) (hgrade : 1 - den ≤ point.1 - den * point.2) :
    BaseMask.stairEvenValue den point = 0 := by
  obtain ⟨x, y⟩ := point
  obtain ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩, hbody⟩ := BaseMask.mem_stairEven_raw_iff.mp hpoint
  have hy : y ≤ 1 := by
    change 1 - den ≤ x - den * y at hgrade
    by_contra! h
    have hmul := mul_le_mul_of_nonneg_left (show 2 ≤ y by omega) (show 0 ≤ den by omega)
    linarith only [hmul, hxhi, hgrade]
  change 0 ≤ y at hylo
  rcases hbody with hcorner | hbody
  · rcases hcorner with ⟨hx, hy₀⟩ | ⟨hx, hy₁⟩
    · change x = 0 at hx
      change y = 0 at hy₀
      subst x
      subst y
      have hcorner : BaseMask.StairEvenCorner den (0, 0) := Or.inl ⟨rfl, rfl⟩
      simp only [BaseMask.stairEvenValue, if_pos hcorner]
      decide
    · change y = den + 1 at hy₁
      omega
  · have hx : 1 ≤ x := by
      change 1 ≤ x + y ∧ x + y ≤ den + 2 at hbody
      rcases show y = 0 ∨ y = 1 by omega with hy₀ | hy₁
      · omega
      · change 1 - den ≤ x - den * y at hgrade
        rw [hy₁, mul_one] at hgrade
        omega
    have hcorner : ¬ BaseMask.StairEvenCorner den (x, y) := by
      simp only [BaseMask.StairEvenCorner]
      omega
    simp only [BaseMask.stairEvenValue, if_neg hcorner, min_eq_right (show 0 ≤ x - 1 by omega), add_zero]
    rcases show y = 0 ∨ y = 1 by omega with hy₀ | hy₁
    · rw [hy₀]
      decide
    · rw [hy₁]
      decide

private theorem stairEven_value_sub_transverse_of_grade {den : ℤ} (hden : 3 ≤ den) {point : Site}
    (hpoint : point ∈ (BaseMask.stairEven.raw den).sites)
    (hgrade : point.1 - den * point.2 + (den ^ 2 + 2 * den - 1) ≤ 2 * den) :
    BaseMask.stairEvenValue den point = point.1 - den * point.2 + (den ^ 2 + 2 * den - 1) +
      stairEvenConstantV den := by
  obtain ⟨x, y⟩ := point
  obtain ⟨⟨hxlo, _⟩, ⟨_, hyhi⟩, hbody⟩ := BaseMask.mem_stairEven_raw_iff.mp hpoint
  change x - den * y + (den ^ 2 + 2 * den - 1) ≤ 2 * den at hgrade
  change 2 - den ≤ x at hxlo
  change y ≤ den + 1 at hyhi
  have hylo : den ≤ y := by
    by_contra! h
    have hmul := mul_le_mul_of_nonneg_left (show y ≤ den - 1 by omega) (show 0 ≤ den by omega)
    nlinarith only [hmul, hgrade, hxlo]
  have hchoose : chooseTwo (den + 1) = chooseTwo den + den := by simpa [chooseTwo] using chooseTwo_add den 1
  rcases show y = den ∨ y = den + 1 by omega with hrow | hrow
  · subst y
    have hx : x ≤ 1 := by nlinarith only [hgrade]
    have hcorner : ¬ BaseMask.StairEvenCorner den (x, den) := by
      simp only [BaseMask.StairEvenCorner]
      omega
    simp only [BaseMask.stairEvenValue, if_neg hcorner, min_eq_left (show x - 1 ≤ 0 by omega), add_zero]
    change -chooseTwo den + (x - 1) = x - den * den + (den ^ 2 + 2 * den - 1) + stairEvenConstantV den
    rw [stairEvenConstantV, hchoose]
    ring
  · subst y
    rcases hbody with hcorner | hbody
    · have hx : x = 2 := by
        simp only [BaseMask.StairEvenCorner] at hcorner
        omega
      subst x
      simp only [BaseMask.stairEvenValue, if_pos hcorner]
      change -chooseTwo (den + 1) + min (2 - 1) 0 + 1 = _
      rw [show min ((2 : ℤ) - 1) 0 = 0 by decide, stairEvenConstantV]
      ring
    · change 1 ≤ x + (den + 1) ∧ x + (den + 1) ≤ den + 2 at hbody
      have hx : x ≤ 1 := by omega
      have hcorner : ¬ BaseMask.StairEvenCorner den (x, den + 1) := by
        simp only [BaseMask.StairEvenCorner]
        omega
      simp only [BaseMask.stairEvenValue, if_neg hcorner, min_eq_left (show x - 1 ≤ 0 by omega), add_zero]
      change -chooseTwo (den + 1) + (x - 1) = x - den * (den + 1) + (den ^ 2 + 2 * den - 1) + stairEvenConstantV den
      rw [stairEvenConstantV]
      ring

/-- The entire zero strip of the pure reciprocal even standard, including
the two occupied corners of the literal mask and the root at denominator three. -/
theorem stairEven_eq_zero_of_transverse {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (site : Site) (hlo : 1 - den ≤ site.1 - den * site.2) (hhi : site.1 - den * site.2 ≤ 2 * den) :
    field site = 0 := by
  let transverse : Site := (1 - den, den + 1)
  let kernel : Site := (den, 1)
  let denom := den ^ 2 + 2 * den - 1
  obtain ⟨point, hpoint, ⟨i, j, hstep⟩⟩ := stairEven_raw_cover hden site
  have heq := reciprocalEvenDeck_eq hden.2
  change site - point = (reciprocalEvenDeck den).combine i j at hstep
  rw [heq] at hstep
  have hsite : site = (point + j • transverse) + i • kernel := by
    apply Prod.ext
    · have h := congrArg Prod.fst hstep
      simp [PeriodDeck.combine, transverse, kernel] at h ⊢
      omega
    · have h := congrArg Prod.snd hstep
      simp [PeriodDeck.combine, transverse, kernel, add_comm 1 den] at h ⊢
      omega
  have hkernel : Function.Periodic field kernel := by
    intro site
    have h := hperiod.1 site
    change field (site + (reciprocalEvenDeck den).kernel) = field site + 0 at h
    rw [heq, add_zero] at h
    exact h
  have hs : site.1 - den * site.2 = point.1 - den * point.2 - j * denom := by
    rw [hsite]
    simp [transverse, kernel, denom]
    ring
  have ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩, _⟩ := BaseMask.mem_stairEven_raw_iff.mp hpoint
  have hd := hden.1
  have hbound : 1 - denom ≤ point.1 - den * point.2 ∧ point.1 - den * point.2 ≤ den := by
    have hmul := mul_le_mul_of_nonneg_left hyhi (show 0 ≤ den by omega)
    have hnonneg := mul_nonneg (show 0 ≤ den by omega) hylo
    dsimp [denom]
    constructor <;> nlinarith only [hmul, hnonneg, hxlo, hxhi]
  have hdenom : 2 * den < denom := by dsimp [denom]; nlinarith only [mul_nonneg (by omega : 0 ≤ den - 3) (by omega : 0 ≤ den + 3)]
  have hjhi : j ≤ 0 := by
    by_contra! h
    have hmul := mul_le_mul_of_nonneg_right (show 1 ≤ j by omega) (show 0 ≤ denom by omega)
    linarith only [hmul, hs, hlo, hbound.2, hdenom]
  have hjlo : -1 ≤ j := by
    by_contra! h
    have hmul := mul_le_mul_of_nonneg_right (show j ≤ -2 by omega) (show 0 ≤ denom by omega)
    linarith only [hmul, hs, hhi, hbound.1, hdenom]
  have hraw := hagree ⟨point, hpoint⟩
  rw [BaseMask.stairEven_raw_height, add_zero] at hraw
  rw [hsite, (hkernel.zsmul i) (point + j • transverse)]
  rcases show j = 0 ∨ j = -1 by omega with hj | hj
  · rw [hj, zero_zsmul, add_zero, ← hraw]
    rw [hj, zero_mul, sub_zero] at hs
    exact stairEven_value_zero_of_grade hd hpoint (hs ▸ hlo)
  · have hgrade : point.1 - den * point.2 + (den ^ 2 + 2 * den - 1) ≤ 2 * den := by
      rw [hj, neg_one_mul, sub_neg_eq_add] at hs
      exact hs ▸ hhi
    have hvalue := stairEven_value_sub_transverse_of_grade hd hpoint hgrade
    rw [hj, neg_one_zsmul, ← sub_eq_add_neg]
    have htrans := hperiod.2 (point - transverse)
    change field (point - transverse + (reciprocalEvenDeck den).transverse) = _ at htrans
    rw [heq, add_comm 1 den] at htrans
    change field (point - transverse + transverse) = _ at htrans
    rw [sub_add_cancel, ← hraw] at htrans
    simp only [Fraction.transverseGrade, one_mul, Prod.fst_sub, Prod.snd_sub, transverse] at htrans
    linear_combination hvalue - htrans

end FLatticePaper.Construction
