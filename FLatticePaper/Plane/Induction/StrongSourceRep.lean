import FLatticePaper.Plane.Induction.StrongVStar
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.TieReduce

/-! Task 70 (a): the source representative: the standard field at a site equals the sheet minimum at a kernel shift lying in `E`. -/

namespace FLatticePaper.StrongSourceRep

open Farey FLatticePaper FLatticePaper.Induction

/-- **(a) The source representative.** At a site `x` whose `t`-grade lies in the `t`-range of `E`, the standard field equals the sheet minimum
at some kernel shift of `x` lying in `E`: `F x = M (x + kU)`. -/
theorem standardField_eq_sheetMin_rep {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site)
    (hw : (EvenSite x → 2 - (frameAt word).child.periodDenominator ≤ (frameAt word).tGrade x ∧
        (frameAt word).tGrade x ≤ (frameAt word).child.den + (frameAt word).child.num - 2) ∧
      (¬ EvenSite x → (frameAt word).child.num - (frameAt word).child.periodDenominator ≤ (frameAt word).tGrade x ∧
        (frameAt word).tGrade x ≤ (frameAt word).child.den)) :
    ∃ k : ℤ, standardField word x =
      (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) (x + k • (frameAt word).child.modifiedDeck.kernel) := by
  obtain ⟨k, hk⟩ := StrongVStar.exists_kernel_mem_of_tWindow (frameAt word) x hw
  have hpk := packet_of_strong h hSE
  have hcU := (frameAt word).coherentConstantU_eq_zero
  have hper : ∀ w, standardField word (w + (frameAt word).child.modifiedDeck.kernel) = standardField word w := by
    intro w
    have := hpk.periods.1 w
    rw [this, hcU, add_zero]
  have hzs : ∀ m : ℤ, standardField word (x + m • (frameAt word).child.modifiedDeck.kernel) = standardField word x := by
    intro m
    induction m using Int.induction_on with
    | zero => simp
    | succ i ih =>
      rw [add_smul, one_smul, ← add_assoc, hper, ih]
    | pred i ih =>
      have e : x + (-(i : ℤ) - 1) • (frameAt word).child.modifiedDeck.kernel + (frameAt word).child.modifiedDeck.kernel =
          x + (-(i : ℤ)) • (frameAt word).child.modifiedDeck.kernel := by
        rw [sub_smul, one_smul]
        abel
      have h2 := hper (x + (-(i : ℤ) - 1) • (frameAt word).child.modifiedDeck.kernel)
      rw [e, ih] at h2
      exact h2.symm
  refine ⟨k, ?_⟩
  rw [← hzs k]
  exact standardField_eq_sheetMin_of_strong h hSE hk


end FLatticePaper.StrongSourceRep
