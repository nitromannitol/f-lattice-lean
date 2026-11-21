import FLatticePaper.Construction.StaircaseExtension
import FLatticePaper.Construction.QuarterTurnCorrection
import Mathlib.Tactic.IntervalCases

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

private theorem centeredCorrection_add_chooseTwo (x y : ℤ) :
    centeredQuarterTurnCorrection (x, y) + chooseTwo y =
      x + chooseTwo (x + y) - (x + y + 1) ^ 2 / 4 := by
  have hp : (x + y + 1) % 2 = 1 - (x + y) % 2 := by omega
  have hc := four_mul_centeredQuarterTurnCorrection (x, y)
  apply (mul_right_inj' (show (4 : ℤ) ≠ 0 by decide)).mp
  dsimp only at hc
  linear_combination hc + 2 * two_mul_chooseTwo y - 2 * two_mul_chooseTwo (x + y) +
    four_mul_square_div_four (x + y + 1) - hp

private theorem centeredCorrection_reciprocal_transverse (den : ℤ) :
    centeredQuarterTurnCorrection (1 - den, den + 1) = stairEvenConstantV den := by
  have hc := four_mul_centeredQuarterTurnCorrection (1 - den, den + 1)
  have hp : (1 - den + (den + 1)) % 2 = 0 := by omega
  change 4 * centeredQuarterTurnCorrection (1 - den, den + 1) =
    (1 - den) ^ 2 + 2 * (1 - den) * (den + 1) - (den + 1) ^ 2 - 2 * (den + 1) -
      (1 - den + (den + 1)) % 2 at hc
  rw [hp] at hc
  apply (mul_right_inj' (show (4 : ℤ) ≠ 0 by decide)).mp
  unfold stairEvenConstantV
  linear_combination hc + 2 * two_mul_chooseTwo (den + 1)

private theorem stairEven_eq_correction_on_native {den : ℤ} (hden : 3 ≤ den) {point : Site}
    (hpoint : point ∈ (BaseMask.stairEven.raw den).sites)
    (hgrade : (den + 1) * point.1 + (den - 1) * point.2 ≤ 2 * den + 1) :
    BaseMask.stairEvenValue den point = centeredQuarterTurnCorrection point := by
  obtain ⟨x, y⟩ := point
  obtain ⟨_, ⟨hy₀, hy₁⟩, hbody⟩ := BaseMask.mem_stairEven_raw_iff.mp hpoint
  change (den + 1) * x + (den - 1) * y ≤ 2 * den + 1 at hgrade
  change 0 ≤ y at hy₀
  change y ≤ den + 1 at hy₁
  have hk : x + y ≤ 3 := by
    by_contra! h
    have hm := mul_le_mul_of_nonneg_left (show 4 ≤ x + y by omega) (show 0 ≤ den + 1 by omega)
    nlinarith only [hm, hy₁, hgrade]
  rcases hbody with hcorner | ⟨hk₀, hk₁⟩
  · rcases hcorner with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · change x = 0 at hx
      change y = 0 at hy
      subst x
      subst y
      have hzero : BaseMask.StairEvenCorner den (0, 0) := Or.inl ⟨rfl, rfl⟩
      simp only [BaseMask.stairEvenValue, if_pos hzero]
      decide
    · change x = 2 at hx
      change y = den + 1 at hy
      omega
  · change 1 ≤ x + y at hk₀
    change x + y ≤ den + 2 at hk₁
    have hx : x ≤ 1 := by
      by_contra! h
      have hsum : 2 ≤ x + y := by omega
      have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ den - 1 by omega)
      nlinarith only [hm, h, hgrade]
    have hcorner : ¬ BaseMask.StairEvenCorner den (x, y) := by
      simp only [BaseMask.StairEvenCorner]
      omega
    have hsmall (sum : ℤ) (hlo : 1 ≤ sum) (hhi : sum ≤ 3) : chooseTwo sum - (sum + 1)^2 / 4 = -1 := by
      interval_cases sum <;> decide
    have h := centeredCorrection_add_chooseTwo x y
    have h' := hsmall (x + y) hk₀ hk
    simp only [BaseMask.stairEvenValue, if_neg hcorner, min_eq_left (show x - 1 ≤ 0 by omega), add_zero]
    change -chooseTwo y + (x - 1) = centeredQuarterTurnCorrection (x, y)
    omega

private theorem stairEven_eq_correction_sub_kernel {den : ℤ} (hden : 3 ≤ den) {point : Site}
    (hpoint : point ∈ (BaseMask.stairEven.raw den).sites)
    (hgrade : den ^ 2 ≤ (den + 1) * point.1 + (den - 1) * point.2) :
    BaseMask.stairEvenValue den point = centeredQuarterTurnCorrection (point - (den, 1)) := by
  obtain ⟨x, y⟩ := point
  obtain ⟨⟨_, hx₁⟩, ⟨hy₀, hy₁⟩, hbody⟩ := BaseMask.mem_stairEven_raw_iff.mp hpoint
  change den ^ 2 ≤ (den + 1) * x + (den - 1) * y at hgrade
  change x ≤ den at hx₁
  change 0 ≤ y at hy₀
  change y ≤ den + 1 at hy₁
  have hlo : den ≤ x + y := by
    by_contra! h
    have hx : x ≤ den - 1 := by omega
    have hm := mul_le_mul_of_nonneg_left (show x + y ≤ den - 1 by omega) (show 0 ≤ den - 1 by omega)
    nlinarith only [hm, hx, hgrade]
  have hx : 1 ≤ x := by
    by_contra! h
    have hm := mul_le_mul_of_nonneg_left hy₁ (show 0 ≤ den - 1 by omega)
    have hn := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ den + 1 by omega) (show x ≤ 0 by omega)
    nlinarith only [hm, hn, hgrade]
  let sum := x + y - den - 1
  have hcornerFormula : centeredQuarterTurnCorrection (x - den, y - 1) + chooseTwo y =
      sum + chooseTwo sum - (sum + 1) ^ 2 / 4 := by
    have hz := centeredCorrection_add_chooseTwo (x - den) (y - 1)
    have heq : x - den + (y - 1) = sum := by dsimp [sum]; ring
    rw [heq] at hz
    have hy := chooseTwo_add (y - 1) 1
    rw [sub_add_cancel, show chooseTwo 1 = 0 by decide, add_zero, mul_one] at hy
    dsimp only [sum] at hz ⊢
    omega
  change BaseMask.stairEvenValue den (x, y) = centeredQuarterTurnCorrection (x - den, y - 1)
  rcases hbody with hcorner | ⟨_, hkhi⟩
  · have htop : x = 2 ∧ y = den + 1 := by
      simp only [BaseMask.StairEvenCorner] at hcorner
      omega
    have hsum : sum = 2 := by dsimp [sum]; omega
    rw [hsum] at hcornerFormula
    have hnum : (2 : ℤ) + chooseTwo 2 - (2 + 1)^2 / 4 = 1 := by decide
    rw [hnum] at hcornerFormula
    simp only [BaseMask.stairEvenValue, if_pos hcorner, min_eq_right (show 0 ≤ x - 1 by omega), add_zero]
    change -chooseTwo y + 1 = centeredQuarterTurnCorrection (x - den, y - 1)
    omega
  · change x + y ≤ den + 2 at hkhi
    have hlo' : -1 ≤ sum := by dsimp [sum]; omega
    have hhi' : sum ≤ 1 := by dsimp [sum]; omega
    have hsmall (sum : ℤ) (hlo : -1 ≤ sum) (hhi : sum ≤ 1) : sum + chooseTwo sum - (sum + 1)^2 / 4 = 0 := by
      interval_cases sum <;> decide
    rw [hsmall sum hlo' hhi'] at hcornerFormula
    have hcorner : ¬ BaseMask.StairEvenCorner den (x, y) := by simp only [BaseMask.StairEvenCorner]; omega
    simp only [BaseMask.stairEvenValue, if_neg hcorner, min_eq_right (show 0 ≤ x - 1 by omega), add_zero]
    change -chooseTwo y = centeredQuarterTurnCorrection (x - den, y - 1)
    omega

/-- The entire harmonic strip of the actual reciprocal even standard.
Subtracting the physical harmonic correction removes the transverse period jet. -/
theorem stairEven_eq_harmonic_of_longitudinal {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (site : Site) (hlo : 1 - 2 * den ≤ (den + 1) * site.1 + (den - 1) * site.2)
    (hhi : (den + 1) * site.1 + (den - 1) * site.2 ≤ 2 * den + 1) :
    field site = centeredQuarterTurnCorrection site := by
  let transverse : Site := (1 - den, den + 1)
  let kernel : Site := (den, 1)
  let denom := den ^ 2 + 2 * den - 1
  let grade (point : Site) := (den + 1) * point.1 + (den - 1) * point.2
  let difference (point : Site) := field point - centeredQuarterTurnCorrection point
  obtain ⟨point, hpoint, ⟨i, j, hstep⟩⟩ := stairEven_raw_cover hden site
  have heq := reciprocalEvenDeck_eq hden.2
  change site - point = (reciprocalEvenDeck den).combine i j at hstep
  rw [heq] at hstep
  have hsite : site = (point + i • kernel) + j • transverse := by
    apply Prod.ext
    · have h := congrArg Prod.fst hstep
      simp [PeriodDeck.combine, transverse, kernel] at h ⊢
      omega
    · have h := congrArg Prod.snd hstep
      simp [PeriodDeck.combine, transverse, kernel, add_comm 1 den] at h ⊢
      omega
  have hV : Function.Periodic difference transverse := by
    intro site
    have hf := hperiod.2 site
    change field (site + (reciprocalEvenDeck den).transverse) = _ at hf
    rw [heq, add_comm 1 den] at hf
    have hv : EvenSite transverse := by change (1 - den + (den + 1)) % 2 = 0; omega
    have hc := centeredQuarterTurnCorrection_add site hv
    rw [centeredCorrection_reciprocal_transverse,
      show (transverse.1 + transverse.2) / 2 = 1 by dsimp [transverse]; omega,
      show (transverse.1 - transverse.2) / 2 = -den by dsimp [transverse]; omega] at hc
    simp only [Fraction.transverseGrade, one_mul] at hf
    dsimp only [difference]
    linear_combination hf - hc
  have hU : Function.Periodic field kernel := by
    intro site
    have h := hperiod.1 site
    change field (site + (reciprocalEvenDeck den).kernel) = field site + 0 at h
    rw [heq, add_zero] at h
    exact h
  have hgrade : grade site = grade point + i * denom := by
    rw [hsite]
    simp [grade, transverse, kernel, denom]
    ring
  change 1 - 2 * den ≤ grade site at hlo
  change grade site ≤ 2 * den + 1 at hhi
  obtain ⟨⟨hxlo, hxhi⟩, _, hbody⟩ := BaseMask.mem_stairEven_raw_iff.mp hpoint
  have hd := hden.1
  have hbound : 3 - den ≤ grade point ∧ grade point ≤ den ^ 2 + 3 * den - 2 := by
    rcases hbody with hcorner | ⟨hbodyLo, hbodyHi⟩
    · rcases hcorner with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> simp [grade, hx, hy] <;>
        constructor <;> nlinarith only [hd, sq_nonneg den]
    · have hlow := mul_le_mul_of_nonneg_left hbodyLo (show 0 ≤ den - 1 by omega)
      have hhigh := mul_le_mul_of_nonneg_left hbodyHi (show 0 ≤ den - 1 by omega)
      simp only [grade]
      constructor <;> nlinarith only [hxlo, hxhi, hlow, hhigh]
  have hdenom : 0 ≤ denom := by
    dsimp [denom]
    nlinarith only [hd, sq_nonneg den]
  have hipo : i ≤ 0 := by
    by_contra! h
    have hm := mul_le_mul_of_nonneg_right (show 1 ≤ i by omega) hdenom
    dsimp [denom] at hm hgrade
    nlinarith only [hm, hgrade, hhi, hbound.1, hd, mul_nonneg (by omega : 0 ≤ den - 3) (by omega : 0 ≤ den + 3)]
  have hilo : -1 ≤ i := by
    by_contra! h
    have hm := mul_le_mul_of_nonneg_right (show i ≤ -2 by omega) hdenom
    dsimp [denom] at hm hgrade
    nlinarith only [hm, hgrade, hlo, hbound.2, hd, mul_nonneg (by omega : 0 ≤ den - 3) (by omega : 0 ≤ den + 3)]
  have hraw := hagree ⟨point, hpoint⟩
  rw [BaseMask.stairEven_raw_height, add_zero] at hraw
  apply sub_eq_zero.mp
  change difference site = 0
  rw [hsite, (hV.zsmul j) (point + i • kernel)]
  dsimp only [difference]
  rw [(hU.zsmul i) point, ← hraw]
  rcases show i = 0 ∨ i = -1 by omega with hi | hi
  · rw [hi, zero_zsmul, add_zero]
    rw [hi, zero_mul, add_zero] at hgrade
    have hlocal : grade point ≤ 2 * den + 1 := hgrade ▸ hhi
    exact sub_eq_zero.mpr (stairEven_eq_correction_on_native hd hpoint hlocal)
  · rw [hi, neg_one_zsmul, ← sub_eq_add_neg]
    rw [hi, neg_one_mul] at hgrade
    have hlocal : den ^ 2 ≤ grade point := by dsimp [denom] at hgrade; linarith only [hgrade, hlo]
    exact sub_eq_zero.mpr (stairEven_eq_correction_sub_kernel hd hpoint hlocal)

end FLatticePaper.Construction
