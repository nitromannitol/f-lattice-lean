import FLatticePaper.Construction.AlternateLadderExtension

namespace FLatticePaper.Construction

open Farey

def reflectLadderOddAlt (den : ℤ) (point : Site) : Site := (den - 1, den + 1) - point

def ladderOddAltBackground (den : ℤ) (point : Site) : ℤ :=
  -chooseTwo (point.2 + 1) + min point.1 0 + max (point.1 + point.2 - den) 0 + min (den - point.1 - 1) 0

abbrev LadderOddAltBump (den : ℤ) (point : Site) : Prop :=
  BaseMask.LadderOddAltCorner den point ∨ BaseMask.LadderOddAltDiagonal den point

theorem ladderOddAltValue_eq_background_add_bump (den : ℤ) (point : Site) :
    BaseMask.ladderOddAltValue den point = ladderOddAltBackground den point +
      (if LadderOddAltBump den point then 1 else 0) := by
  simp only [BaseMask.ladderOddAltValue, ladderOddAltBackground, chooseTwo, add_sub_cancel_right,
    mul_comm (point.2 + 1) point.2]

theorem reflectLadderOddAlt_mem_iff (den : ℤ) (point : Site) :
    reflectLadderOddAlt den point ∈ (BaseMask.ladderOddAlt.raw den).sites ↔
      point ∈ (BaseMask.ladderOddAlt.raw den).sites := by
  simp only [BaseMask.mem_ladderOddAlt_raw_iff, BaseMask.LadderOddAltCorner, reflectLadderOddAlt,
    Prod.fst_sub, Prod.snd_sub]
  omega

theorem evenSite_reflectLadderOddAlt_iff (den : ℤ) (point : Site) :
    EvenSite (reflectLadderOddAlt den point) ↔ EvenSite point := by
  simp only [EvenSite, reflectLadderOddAlt, Prod.fst_sub, Prod.snd_sub]
  omega

theorem ladderOddAltBump_reflect_iff (den : ℤ) (point : Site) :
    LadderOddAltBump den (reflectLadderOddAlt den point) ↔ LadderOddAltBump den point := by
  simp only [LadderOddAltBump, BaseMask.LadderOddAltCorner, BaseMask.LadderOddAltDiagonal,
    reflectLadderOddAlt, Prod.fst_sub, Prod.snd_sub]
  omega

theorem ladderOddAltBackground_reflection (den : ℤ) (point : Site) :
    ladderOddAltBackground den (reflectLadderOddAlt den point) = ladderOddAltBackground den point +
      (Fraction.mk 1 den).transverseGrade point + point.2 - chooseTwo (den + 1) - 1 := by
  obtain ⟨x, y⟩ := point
  have hquad : -chooseTwo (den + 2 - y) = -chooseTwo (y + 1) + (den + 2) * y - chooseTwo (den + 2) := by
    apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide)
    linear_combination -two_mul_chooseTwo (den + 2 - y) + two_mul_chooseTwo (y + 1) +
      two_mul_chooseTwo (den + 2)
  have hsum : chooseTwo (den + 2) = chooseTwo (den + 1) + den + 1 := by
    have h := chooseTwo_add (den + 1) 1
    simp only [show chooseTwo (1 : ℤ) = 0 by decide, add_zero, mul_one] at h
    simpa [add_assoc] using h
  have hmax (s : ℤ) : max (-s) 0 = max s 0 - s := by omega
  simp only [ladderOddAltBackground, reflectLadderOddAlt, Prod.fst_sub, Prod.snd_sub,
    Fraction.transverseGrade, one_mul]
  rw [show den + 1 - y + 1 = den + 2 - y by omega, hquad, hsum,
    show den - (den - 1 - x) - 1 = x by omega, show den - 1 - x = den - x - 1 by omega,
    show den - x - 1 + (den + 1 - y) - den = -(x + y - den) by omega, hmax]
  ring

theorem ladderOddAlt_agrees_value {den : ℤ} {field : Field}
    (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0) {point : Site}
    (hpoint : point ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    field point = BaseMask.ladderOddAltValue den point := by
  have h := hagree ⟨point, hpoint⟩
  rw [BaseMask.ladderOddAlt_raw_height, add_zero] at h
  exact h.symm

theorem ladderOddAltField_reflection {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den) {field : Field}
    (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den))
    (point : Site) : field (reflectLadderOddAlt den point) = field point +
      (Fraction.mk 1 den).transverseGrade point + point.2 - chooseTwo (den + 1) - 1 := by
  let slope := Fraction.mk 1 den
  let reflected : Field := fun site =>
    field (reflectLadderOddAlt den site) - slope.transverseGrade site - site.2 + chooseTwo (den + 1) + 1
  have hinterval : slope.InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp [slope]; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp [slope]; omega⟩
  have hreflectAdd (site step : Site) :
      reflectLadderOddAlt den (site + step) + step = reflectLadderOddAlt den site := by
    apply Prod.ext <;> dsimp [reflectLadderOddAlt] <;> omega
  have hperiod' : HasGeneratorPeriods slope reflected (-1) (ladderOddAltConstantV den) := by
    constructor
    · intro site
      change reflected (site + (reciprocalLadderDeck den).kernel) = reflected site + (-1)
      rw [reciprocalLadderDeck_eq hden.2]
      have hp := hperiod.1 (reflectLadderOddAlt den (site + (2 * den, 2)))
      change field (reflectLadderOddAlt den (site + (2 * den, 2)) + (reciprocalLadderDeck den).kernel) = _ at hp
      rw [reciprocalLadderDeck_eq hden.2, hreflectAdd] at hp
      have hgrade : slope.transverseGrade (site + (2 * den, 2)) = slope.transverseGrade site := by
        dsimp [slope, Fraction.transverseGrade]
        ring
      simp only [reflected, hgrade, Prod.snd_add]
      omega
    · intro site
      change reflected (site + (reciprocalLadderDeck den).transverse) = reflected site -
        slope.transverseGrade site + ladderOddAltConstantV den
      rw [reciprocalLadderDeck_eq hden.2, add_comm 1 den]
      have hp := hperiod.2 (reflectLadderOddAlt den (site + (1 - den, den + 1)))
      change field (reflectLadderOddAlt den (site + (1 - den, den + 1)) + (reciprocalLadderDeck den).transverse) = _ at hp
      rw [reciprocalLadderDeck_eq hden.2, add_comm 1 den, hreflectAdd] at hp
      simp only [reflected, slope, Fraction.transverseGrade, reflectLadderOddAlt, Prod.fst_add, Prod.snd_add,
        Prod.fst_sub, Prod.snd_sub, one_mul, ladderOddAltConstantV] at hp ⊢
      linear_combination -hp + two_mul_chooseTwo (den + 1)
  have heq := eq_of_covered_generator_periods hinterval hperiod' hperiod (ladderOddAlt_raw_cover hden)
    (fun site hsite => by
      have hr := ladderOddAlt_agrees_value hagree ((reflectLadderOddAlt_mem_iff den site).mpr hsite)
      have hs := ladderOddAlt_agrees_value hagree hsite
      rw [ladderOddAltValue_eq_background_add_bump, ladderOddAltBackground_reflection,
        if_congr (ladderOddAltBump_reflect_iff den site) rfl rfl] at hr
      rw [ladderOddAltValue_eq_background_add_bump] at hs
      dsimp only [reflected, slope]
      omega)
  have hp := congrFun heq point
  dsimp only [reflected, slope] at hp
  omega

theorem incomingStar_reflectLadderOddAlt (den : ℤ) (point : Site) :
    incomingNeg (reflectLadderOddAlt den point) = reflectLadderOddAlt den (incomingPos point) ∧
      incomingPos (reflectLadderOddAlt den point) = reflectLadderOddAlt den (incomingNeg point) := by
  have hpar := evenSite_reflectLadderOddAlt_iff den point
  by_cases he : EvenSite point
  · simp only [incomingNeg, incomingPos, if_pos he, if_pos (hpar.mpr he)]
    constructor <;> apply Prod.ext <;> dsimp [reflectLadderOddAlt] <;> omega
  · have hnot : ¬ EvenSite (reflectLadderOddAlt den point) := fun h => he (hpar.mp h)
    simp only [incomingNeg, incomingPos, if_neg he, if_neg hnot]
    constructor <;> apply Prod.ext <;> dsimp [reflectLadderOddAlt] <;> omega

theorem laplacian_ladderOddAltField_reflection {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den) {field : Field}
    (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den))
    (point : Site) : laplacian field (reflectLadderOddAlt den point) = laplacian field point := by
  have hin := incomingStar_reflectLadderOddAlt den point
  simp only [laplacian, hin.1, hin.2, ladderOddAltField_reflection hden hagree hperiod]
  by_cases he : EvenSite point
  · simp only [incomingNeg, incomingPos, if_pos he, Fraction.transverseGrade, one_mul]
    ring
  · simp only [incomingNeg, incomingPos, if_neg he, Fraction.transverseGrade, one_mul]
    ring

end FLatticePaper.Construction
