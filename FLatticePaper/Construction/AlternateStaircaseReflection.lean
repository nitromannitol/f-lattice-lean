import FLatticePaper.Construction.AlternateStaircaseExtension
import FLatticePaper.Construction.StaircaseLaplacian

namespace FLatticePaper.Construction

open Farey

/-- The B3 reflection center is the sum of its paired corners. -/
def reflectStairEvenAlt (den : ℤ) (point : Site) : Site := (4 - den, den) - point

theorem reflectStairEvenAlt_mem_iff (den : ℤ) (point : Site) :
    reflectStairEvenAlt den point ∈ (BaseMask.stairEvenAlt.raw den).sites ↔
      point ∈ (BaseMask.stairEvenAlt.raw den).sites := by
  simp only [BaseMask.mem_stairEvenAlt_raw_iff, reflectStairEvenAlt, Prod.fst_sub, Prod.snd_sub]
  omega

theorem stairEvenAltBackground_reflection (den : ℤ) (point : Site) :
    BaseMask.stairEvenAltBackground den (reflectStairEvenAlt den point) =
      BaseMask.stairEvenAltBackground den point + (Fraction.mk 1 den).transverseGrade point +
        (2 - chooseTwo (den + 1)) := by
  let x := point.1
  let y := point.2
  have hchoose : chooseTwo (den - y + 1) = chooseTwo (y + 1) + chooseTwo (den + 1) - (den + 1) * y := by
    apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide)
    linear_combination two_mul_chooseTwo (den - y + 1) - two_mul_chooseTwo (y + 1) -
      two_mul_chooseTwo (den + 1)
  have hs (j : ℤ) : j * (j + 1) / 2 = chooseTwo (j + 1) := by
    unfold chooseTwo
    rw [show j * (j + 1) = (j + 1) * (j + 1 - 1) by ring]
  change -( (den - y) * (den - y + 1) / 2) + min 0 (2 - (4 - den - x)) +
    min 0 (den - 2 + (4 - den - x)) + max ((4 - den - x) + (den - y) - 2) 0 =
      -(y * (y + 1) / 2) + min 0 (2 - x) + min 0 (den - 2 + x) + max (x + y - 2) 0 +
        (den * y - 1 * x) + (2 - chooseTwo (den + 1))
  rw [hs (den - y), hs y, hchoose, show 2 - (4 - den - x) = den - 2 + x by omega,
    show den - 2 + (4 - den - x) = 2 - x by omega,
    show (4 - den - x) + (den - y) - 2 = -(x + y - 2) by omega]
  by_cases hsum : 0 ≤ x + y - 2
  · rw [max_eq_left hsum, max_eq_right (by omega : -(x + y - 2) ≤ 0)]
    ring
  · rw [max_eq_right (by omega : x + y - 2 ≤ 0), max_eq_left (by omega : 0 ≤ -(x + y - 2))]
    ring

theorem stairEvenAltMarker_reflect (den : ℤ) (point : Site) :
    stairEvenAltMarker den (reflectStairEvenAlt den point) = stairEvenAltMarker den point := by
  let period := (Fraction.mk 1 den).periodDenominator
  let level := point.1 - den * point.2
  let reflectionLevel := 4 - den * (den + 1)
  have hlevel : (reflectStairEvenAlt den point).1 - den * (reflectStairEvenAlt den point).2 =
      reflectionLevel - level := by
    simp only [reflectStairEvenAlt, Prod.fst_sub, Prod.snd_sub, reflectionLevel, level]
    ring
  have hflip (row : ℤ) : (reflectionLevel - level) % period = (2 - (den + 1) * row) % period ↔
      level % period = (2 - (den + 1) * (den - row)) % period := by
    simp only [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]
    rw [show reflectionLevel - level - (2 - (den + 1) * row) =
      -(level - (2 - (den + 1) * (den - row))) by dsimp [reflectionLevel]; ring, dvd_neg]
  change (if ∃ row ∈ Finset.Ico (1 : ℤ) den,
    ((reflectStairEvenAlt den point).1 - den * (reflectStairEvenAlt den point).2) % period =
      (2 - (den + 1) * row) % period then 1 else 0) =
    if ∃ row ∈ Finset.Ico (1 : ℤ) den, level % period = (2 - (den + 1) * row) % period then 1 else 0
  rw [hlevel]
  apply if_congr ?_ rfl rfl
  constructor
  · rintro ⟨row, hrow, hmod⟩
    have hrow' := Finset.mem_Ico.mp hrow
    exact ⟨den - row, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, (hflip row).mp hmod⟩
  · rintro ⟨row, hrow, hmod⟩
    have hrow' := Finset.mem_Ico.mp hrow
    refine ⟨den - row, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, (hflip (den - row)).mpr ?_⟩
    rwa [sub_sub_cancel]

/-- Central reflection of B3 has the actual affine height increment, obtained
from B1's reflection and the symmetry of the marked transverse classes. -/
theorem stairEvenAltField_reflection {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (point : Site) : stairEvenAltField den standard (reflectStairEvenAlt den point) =
      stairEvenAltField den standard point + (Fraction.mk 1 den).transverseGrade point +
        (2 - chooseTwo (den + 1)) := by
  have hreflect := stairEven_reflection hden hagree hperiod (point - (1, 0))
  have hkernel := hperiod.1 (reflectStairEvenAlt den point - (1, 0))
  change standard (reflectStairEvenAlt den point - (1, 0) + (reciprocalEvenDeck den).kernel) = _ at hkernel
  rw [reciprocalEvenDeck_eq hden.2, add_zero] at hkernel
  have heq : reflectStairEvenAlt den point - (1, 0) + (den, 1) = (2, den + 1) - (point - (1, 0)) := by
    apply Prod.ext <;> dsimp [reflectStairEvenAlt] <;> omega
  have hgrade : (Fraction.mk 1 den).transverseGrade (point - (1, 0)) =
      (Fraction.mk 1 den).transverseGrade point + 1 := by
    simp only [Fraction.transverseGrade, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [heq, hreflect, hgrade] at hkernel
  simp only [stairEvenAltField, stairEvenAltMarker_reflect]
  omega

/-- The correction to the B3 background is invariant under central reflection,
including on incoming sites outside the literal mask. -/
theorem stairEvenAltField_residual_reflection {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (point : Site) :
    stairEvenAltField den standard (reflectStairEvenAlt den point) -
      BaseMask.stairEvenAltBackground den (reflectStairEvenAlt den point) =
        stairEvenAltField den standard point - BaseMask.stairEvenAltBackground den point := by
  rw [stairEvenAltField_reflection hden hagree hperiod, stairEvenAltBackground_reflection]
  ring

end FLatticePaper.Construction
