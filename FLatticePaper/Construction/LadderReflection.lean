import FLatticePaper.Construction.LadderExtension

namespace FLatticePaper.Construction

open Farey

def reflectLadderOdd (den : ℤ) (point : Site) : Site := (den + 2, den + 2) - point

def ladderOddBackground (den : ℤ) (point : Site) : ℤ :=
  -chooseTwo point.2 + min 0 (point.1 - 1) + max (point.2 + point.1 - den - 2) 0 +
    min (den + 1 - point.1) 0

theorem ladderOddValue_eq_background_add_bump (den : ℤ) (point : Site) :
    BaseMask.ladderOddValue den point = ladderOddBackground den point +
      (if BaseMask.LadderOddBump den point then 1 else 0) := rfl

theorem reflectLadderOdd_mem_iff (den : ℤ) (point : Site) :
    reflectLadderOdd den point ∈ (BaseMask.ladderOdd.raw den).sites ↔
      point ∈ (BaseMask.ladderOdd.raw den).sites := by
  simp only [BaseMask.mem_ladderOdd_raw_iff, BaseMask.LadderOddCorner, reflectLadderOdd,
    Prod.fst_sub, Prod.snd_sub]
  omega

theorem evenSite_reflectLadderOdd_iff (den : ℤ) (point : Site) :
    EvenSite (reflectLadderOdd den point) ↔ EvenSite point := by
  simp only [EvenSite, reflectLadderOdd, Prod.fst_sub, Prod.snd_sub]
  omega

private theorem ladderOddBump_reflect_iff (den : ℤ) (point : Site) :
    BaseMask.LadderOddBump den (reflectLadderOdd den point) ↔ BaseMask.LadderOddBump den point := by
  simp only [BaseMask.LadderOddBump, reflectLadderOdd, Prod.fst_sub, Prod.snd_sub]
  omega

theorem ladderOddBackground_reflection (den : ℤ) (point : Site) :
    ladderOddBackground den (reflectLadderOdd den point) = ladderOddBackground den point +
      (Fraction.mk 1 den).transverseGrade point + (1 - chooseTwo (den + 1)) := by
  obtain ⟨x, y⟩ := point
  have hquad : -chooseTwo (den + 2 - y) = -chooseTwo y + (den + 1) * y - chooseTwo (den + 2) := by
    apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide)
    linear_combination -two_mul_chooseTwo (den + 2 - y) + two_mul_chooseTwo y + two_mul_chooseTwo (den + 2)
  have hsum : chooseTwo (den + 2) = chooseTwo (den + 1) + den + 1 := by
    have h := chooseTwo_add (den + 1) 1
    simp only [show chooseTwo (1 : ℤ) = 0 by decide, add_zero, mul_one] at h
    simpa [add_assoc] using h
  have hmax (s : ℤ) : max (-s) 0 = max s 0 - s := by omega
  simp only [ladderOddBackground, reflectLadderOdd, Prod.fst_sub, Prod.snd_sub,
    Fraction.transverseGrade, one_mul, hquad, hsum]
  rw [show den + 2 - x - 1 = den + 1 - x by omega,
    show den + 1 - (den + 2 - x) = x - 1 by omega,
    show den + 2 - y + (den + 2 - x) - den - 2 = -(y + x - den - 2) by omega, hmax,
    min_comm 0 (den + 1 - x), min_comm (x - 1) 0]
  ring

theorem ladderOdd_agrees_value {den : ℤ} {field : Field}
    (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0) {point : Site}
    (hpoint : point ∈ (BaseMask.ladderOdd.raw den).sites) :
    field point = BaseMask.ladderOddValue den point := by
  have h := hagree ⟨point, hpoint⟩
  rw [BaseMask.ladderOdd_raw_height, add_zero] at h
  exact h.symm

theorem ladderOddField_reflection {den : ℤ} (hden : BaseMask.ladderOdd.Valid den) {field : Field}
    (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (point : Site) : field (reflectLadderOdd den point) = field point +
      (Fraction.mk 1 den).transverseGrade point + (1 - chooseTwo (den + 1)) := by
  let slope := Fraction.mk 1 den
  let C := 1 - chooseTwo (den + 1)
  let reflected : Field := fun site => field (reflectLadderOdd den site) - slope.transverseGrade site - C
  have hinterval : slope.InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp [slope]; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp [slope]; omega⟩
  have hreflectAdd (site step : Site) :
      reflectLadderOdd den (site + step) + step = reflectLadderOdd den site := by
    apply Prod.ext <;> dsimp [reflectLadderOdd] <;> omega
  have hperiod' : HasGeneratorPeriods slope reflected 0 (stairEvenConstantV den) := by
    constructor
    · intro site
      change reflected (site + (reciprocalLadderDeck den).kernel) = reflected site + 0
      rw [reciprocalLadderDeck_eq hden.2]
      have hp := hperiod.1 (reflectLadderOdd den (site + (2 * den, 2)))
      change field (reflectLadderOdd den (site + (2 * den, 2)) + (reciprocalLadderDeck den).kernel) = _ at hp
      rw [reciprocalLadderDeck_eq hden.2, hreflectAdd, add_zero] at hp
      have hgrade : slope.transverseGrade (site + (2 * den, 2)) = slope.transverseGrade site := by
        dsimp [slope, Fraction.transverseGrade]
        ring
      dsimp only [reflected]
      rw [← hp, hgrade, add_zero]
    · intro site
      change reflected (site + (reciprocalLadderDeck den).transverse) =
        reflected site - slope.transverseGrade site + stairEvenConstantV den
      rw [reciprocalLadderDeck_eq hden.2, add_comm 1 den]
      have hp := hperiod.2 (reflectLadderOdd den (site + (1 - den, den + 1)))
      change field (reflectLadderOdd den (site + (1 - den, den + 1)) + (reciprocalLadderDeck den).transverse) = _ at hp
      rw [reciprocalLadderDeck_eq hden.2, add_comm 1 den, hreflectAdd] at hp
      dsimp only [reflected]
      simp only [slope, Fraction.transverseGrade, reflectLadderOdd, Prod.fst_add, Prod.snd_add,
        Prod.fst_sub, Prod.snd_sub, one_mul, stairEvenConstantV] at hp ⊢
      linear_combination -hp + two_mul_chooseTwo (den + 1)
  have heq := eq_of_covered_generator_periods hinterval hperiod' hperiod (ladderOdd_raw_cover hden)
    (fun site hsite => by
      have hr := ladderOdd_agrees_value hagree ((reflectLadderOdd_mem_iff den site).mpr hsite)
      have hs := ladderOdd_agrees_value hagree hsite
      rw [ladderOddValue_eq_background_add_bump, ladderOddBackground_reflection,
        if_congr (ladderOddBump_reflect_iff den site) rfl rfl] at hr
      rw [ladderOddValue_eq_background_add_bump] at hs
      change field (reflectLadderOdd den site) - slope.transverseGrade site - C = field site
      dsimp only [slope, C]
      omega)
  have hp := congrFun heq point
  change field (reflectLadderOdd den point) - (Fraction.mk 1 den).transverseGrade point -
    (1 - chooseTwo (den + 1)) = field point at hp
  omega

theorem incomingStar_reflectLadderOdd (den : ℤ) (point : Site) :
    incomingNeg (reflectLadderOdd den point) = reflectLadderOdd den (incomingPos point) ∧
      incomingPos (reflectLadderOdd den point) = reflectLadderOdd den (incomingNeg point) := by
  have hpar := evenSite_reflectLadderOdd_iff den point
  by_cases he : EvenSite point
  · simp only [incomingNeg, incomingPos, if_pos he, if_pos (hpar.mpr he)]
    constructor <;> apply Prod.ext <;> dsimp [reflectLadderOdd] <;> omega
  · have hnot : ¬ EvenSite (reflectLadderOdd den point) := fun h => he (hpar.mp h)
    simp only [incomingNeg, incomingPos, if_neg he, if_neg hnot]
    constructor <;> apply Prod.ext <;> dsimp [reflectLadderOdd] <;> omega

theorem laplacian_ladderOddField_reflection {den : ℤ} (hden : BaseMask.ladderOdd.Valid den) {field : Field}
    (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (point : Site) : laplacian field (reflectLadderOdd den point) = laplacian field point := by
  have hin := incomingStar_reflectLadderOdd den point
  simp only [laplacian, hin.1, hin.2, ladderOddField_reflection hden hagree hperiod]
  by_cases he : EvenSite point
  · simp only [incomingNeg, incomingPos, if_pos he, Fraction.transverseGrade, one_mul]
    ring
  · simp only [incomingNeg, incomingPos, if_neg he, Fraction.transverseGrade, one_mul]
    ring

end FLatticePaper.Construction
