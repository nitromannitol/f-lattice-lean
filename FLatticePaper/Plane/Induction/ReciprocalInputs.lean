import FLatticePaper.Plane.Induction.Bands
import FLatticePaper.Construction.StaircaseStrips
import FLatticePaper.Construction.StaircaseLaplacian
import FLatticePaper.Construction.StaircaseExtension
import FLatticePaper.Construction.QuarterTurnCorrection
import FLatticePaper.Construction.PeriodExtension
import FLatticePaper.Farey.EarlierChain

/-! The reciprocal standard field `1/(2k+3)` satisfies the three height inputs of the coherence step on its own
polygon (supplement Part I, base case). -/

namespace FLatticePaper.Induction

open Farey Construction

/-- The frame of the word `3^k`. -/
def reciprocalFrame (k : ℕ) : ChildFrame :=
  ⟨parentsAt (List.replicate k Digit.three), parentsAt_valid _⟩

theorem reciprocalFrame_child (k : ℕ) : (reciprocalFrame k).child = ⟨1, 2 * k + 3⟩ := by
  show (parentsAt (List.replicate k Digit.three)).current .even = _
  unfold parentsAt
  rw [Parents.walk_threes]
  simp only [Parents.current, Parents.combine, root]
  congr 1
  ring

theorem reciprocal_child_num (k : ℕ) : (reciprocalFrame k).child.num = 1 := by
  rw [reciprocalFrame_child]

theorem reciprocal_child_den (k : ℕ) : (reciprocalFrame k).child.den = 2 * (k : ℤ) + 3 := by
  rw [reciprocalFrame_child]

theorem reciprocal_tGrade (k : ℕ) (z : Site) :
    (reciprocalFrame k).tGrade z = z.1 - (2 * (k : ℤ) + 3) * z.2 := by
  unfold ChildFrame.tGrade
  rw [reciprocal_child_num, reciprocal_child_den]
  ring

theorem reciprocal_sGrade (k : ℕ) (z : Site) :
    (reciprocalFrame k).sGrade z = (2 * (k : ℤ) + 3 + 1) * z.1 + (2 * (k : ℤ) + 3 - 1) * z.2 := by
  unfold ChildFrame.sGrade
  rw [reciprocal_child_num, reciprocal_child_den]

theorem reciprocal_modifiedDeck (k : ℕ) :
    (reciprocalFrame k).child.modifiedDeck =
      ⟨(2 * (k : ℤ) + 3, 1), (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))⟩ := by
  rw [reciprocalFrame_child]
  have hmu : (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction).periodMultiplicity = 1 := by
    show (if (1 + (2 * (k : ℤ) + 3)) % 2 = 0 then (1 : ℤ) else 2) = 1
    rw [if_pos (by omega)]
  simp only [Fraction.modifiedDeck, Fraction.unmodifiedDeck, hmu, one_mul]

theorem reciprocal_centre (k : ℕ) : (reciprocalFrame k).centre = (2, 2 * (k : ℤ) + 3 + 1) := by
  unfold ChildFrame.centre
  rw [reciprocal_modifiedDeck]
  dsimp only
  exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)

theorem reciprocal_symmetryConstant (k : ℕ) :
    (reciprocalFrame k).symmetryConstant = 1 - chooseTwo (2 * (k : ℤ) + 3 + 1) := by
  have hc : 2 * chooseTwo (2 * (k : ℤ) + 3 + 1) = (2 * (k : ℤ) + 3 + 1) * (2 * (k : ℤ) + 3) := by
    rw [two_mul_chooseTwo]
    ring
  have hnum : (reciprocalFrame k).child.den + (reciprocalFrame k).child.num -
      (reciprocalFrame k).child.periodDenominator = 2 * (-2 * (k : ℤ) ^ 2 - 7 * k - 5) := by
    rw [reciprocal_child_num, reciprocal_child_den, reciprocalFrame_child]
    unfold Fraction.periodDenominator
    ring
  unfold ChildFrame.symmetryConstant
  rw [hnum, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  linarith

theorem reciprocal_harmonic_corner (k : ℕ) :
    harmonicGrid ((1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) + (1, -1)) =
      -(2 * (k : ℤ) + 5) * ((k : ℤ) + 1) := by
  have hsum : (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) + (1, -1) =
      (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) := by
    exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  rw [hsum]
  have h := harmonicGrid_exact (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3)
  dsimp only at h
  have hmod : (2 - (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3)) % 2 = 0 := by
    have e : (2 - (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3)) = 2 := by ring
    rw [e]
    norm_num
  rw [hmod] at h
  linarith

theorem reciprocal_chooseTwo (k : ℕ) :
    chooseTwo (2 * (k : ℤ) + 3 + 1) = ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) := by
  have hc : 2 * chooseTwo (2 * (k : ℤ) + 3 + 1) = (2 * (k : ℤ) + 3 + 1) * (2 * (k : ℤ) + 3) := by
    rw [two_mul_chooseTwo]
    ring
  linarith

/-- The reciprocal standard field satisfies the three height inputs on its own polygon. -/
theorem reciprocal_heightInputs (k : ℕ) {field : Field}
    (hagree : (BaseMask.stairEven.raw (2 * k + 3)).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * k + 3)) field 0 (stairEvenConstantV (2 * k + 3))) :
    (reciprocalFrame k).HeightInputs field := by
  have hden : BaseMask.stairEven.Valid (2 * (k : ℤ) + 3) := ⟨by omega, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨-, hH⟩
    simp only [reciprocal_tGrade, reciprocal_child_num, reciprocal_child_den] at hH
    by_cases hpar : EvenSite z
    · rw [if_pos hpar] at hH
      exact stairEven_eq_zero_of_transverse hden hagree hperiod z (by linarith [hH.1]) (by linarith [hH.2])
    · rw [if_neg hpar] at hH
      exact stairEven_eq_zero_of_transverse hden hagree hperiod z (by linarith [hH.1]) (by linarith [hH.2])
  · rintro z ⟨-, hV⟩
    simp only [reciprocal_sGrade, reciprocal_child_num, reciprocal_child_den] at hV
    by_cases hpar : EvenSite z
    · rw [if_pos hpar] at hV
      rw [stairEven_eq_harmonic_of_longitudinal hden hagree hperiod z (by linarith [hV.1])
        (by linarith [hV.2])]
      linarith [four_mul_centeredQuarterTurnCorrection z, harmonicGrid_exact z]
    · rw [if_neg hpar] at hV
      rw [stairEven_eq_harmonic_of_longitudinal hden hagree hperiod z (by linarith [hV.1])
        (by linarith [hV.2])]
      linarith [four_mul_centeredQuarterTurnCorrection z, harmonicGrid_exact z]
  · rintro z -
    have hR := stairEven_reflection hden hagree hperiod z
    rw [reciprocal_centre k, reciprocal_tGrade, reciprocal_symmetryConstant k, hR]
    simp only [Fraction.transverseGrade]
    ring

/-- The period constants of the reciprocal standard field are the coherent constants of its frame. -/
theorem reciprocal_coherentConstants (k : ℕ) :
    (reciprocalFrame k).coherentConstantU = 0 ∧
      (reciprocalFrame k).coherentConstantV = stairEvenConstantV (2 * k + 3) := by
  constructor
  · unfold ChildFrame.coherentConstantU
    rw [reciprocal_modifiedDeck]
    dsimp only
    rw [reciprocal_harmonic_corner k, reciprocal_tGrade, reciprocal_symmetryConstant k,
      reciprocal_chooseTwo k]
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  · unfold ChildFrame.coherentConstantV
    rw [reciprocal_modifiedDeck, reciprocal_centre k, reciprocal_symmetryConstant k]
    dsimp only
    rw [reciprocal_tGrade, reciprocal_tGrade, reciprocal_chooseTwo k]
    unfold stairEvenConstantV
    rw [reciprocal_chooseTwo k]
    ring

end FLatticePaper.Induction
