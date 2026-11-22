import FLatticePaper.Plane.Induction.EvenStep
import FLatticePaper.Plane.Induction.OddStep

/-! The plane facts of the even alternate `ĝ = roundedMidpoint g (g(· + σ))` of a standard field `g` (global_recurrence.tex,
the alternate odometer). `odometersTheoremAt_of_standard` proves these internally; here they are exposed one by one: the
periods (`eq:periodicity`), the quadratic growth, the binary Laplacian, superharmonicity and recurrence, and the
non-integer-affine difference from the standard field. -/

namespace FLatticePaper.Induction
open Farey

namespace ChildFrame

theorem alternate_facts (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (hperiod : HasGeneratorPeriods frame.child F cU cV)
    {α : Type*} [LinearOrder α] {rank : Site → α}
    (hstep : HasUnitSlip F (fun z => F (z + frame.shortShift)))
    (hnoSaddle : NoEvenSlipSaddle F (fun z => F (z + frame.shortShift)))
    (hrank : IsConstrainedBurningRank F rank
      (fun center input => slipIncrement F (fun z => F (z + frame.shortShift)) center input ≤ 0)) :
    SatisfiesPeriodicity frame.child (frame.alternate F) ∧
      HasQuadraticGrowth (frame.alternate F) frame.child.matrix ∧
      (∀ x, laplacian (frame.alternate F) x = -1 ∨ laplacian (frame.alternate F) x = 0) ∧
      Superharmonic (frame.alternate F) ∧ Recurrent (frame.alternate F) ∧
      ¬ IntegerAffine (fun x => frame.alternate F x - F x) := by
  have hint : frame.child.Interior := frame.valid.current_interior .even
  have hI : frame.child.InUnitInterval := hint.inUnitInterval
  obtain ⟨hnum, hden⟩ := hint
  -- the companion sheet is the standard shifted by the child's short slip
  have hcomp : (fun z => F (z + frame.shortShift)) =
      alternateCompanion F frame.child.num frame.child.den frame.parents.odd.num frame.parents.odd.den := by
    funext z
    unfold alternateCompanion
    rw [frame.shortShift_eq_alternateSlip]
  have hH : frame.alternate F =
      roundedMidpoint F (alternateCompanion F frame.child.num frame.child.den
        frame.parents.odd.num frame.parents.odd.den) := by
    unfold ChildFrame.alternate
    rw [hcomp]
  rw [hcomp] at hstep hnoSaddle hrank
  -- the odd parent's determinant is the unit ε
  have hdet : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = -1 ∨
      frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = 1 := by
    rw [← frame.eps_eq]
    rcases frame.eps_unit with h | h
    · exact Or.inr h
    · exact Or.inl h
  -- the standard's generator identities in the coordinates of the midpoint lemmas
  have hkernelF : ∀ site, F (site + (frame.child.den, frame.child.num)) = F site + cU := by
    intro site
    have h := hperiod.1 site
    rw [ChildFrame.child_modifiedDeck_kernel] at h
    exact h
  have hperiodV : ∀ site, F (site + (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) =
      F site + frame.child.num * site.1 - frame.child.den * site.2 + cV := by
    intro site
    have h := hperiod.2 site
    rw [ChildFrame.child_modifiedDeck_transverse] at h
    unfold Fraction.transverseGrade at h
    rw [h]
    ring
  -- the alternate's burning rank, from the companion theorem
  have hHrank := isBurningRank_alternateCompanion_midpoint (standard := F) (rank := rank)
    frame.child.num frame.child.den frame.parents.odd.num frame.parents.odd.den hstep hnoSaddle hrank
  rw [← hH] at hHrank
  -- the alternate's generator identities: H − F has increments 0 and −1 on the kernel and transverse
  have hHgen : HasGeneratorPeriods frame.child (frame.alternate F) cU (cV - 1) := by
    refine ⟨fun z => ?_, fun z => ?_⟩
    · rw [ChildFrame.child_modifiedDeck_kernel, hH]
      have h1 := roundedMidpoint_sub_standard_add_kernel F frame.child.num frame.child.den
        frame.parents.odd.num frame.parents.odd.den cU hkernelF z
      dsimp only at h1
      have h2 := hkernelF z
      linarith
    · have hP := hperiod.2 z
      rw [ChildFrame.child_modifiedDeck_transverse] at hP ⊢
      have h1 := roundedMidpoint_sub_standard_add_transverse F frame.child.num frame.child.den
        frame.parents.odd.num frame.parents.odd.den cV hdet hperiodV z
      dsimp only at h1
      rw [hH]
      unfold Fraction.transverseGrade at hP ⊢
      linarith
  -- the alternate differs from the standard by a non-affine function
  have hna := not_integerAffine_roundedMidpoint_sub_standard F frame.child.num frame.child.den
    frame.parents.odd.num frame.parents.odd.den cU cV hnum hden hdet hkernelF hperiodV
  refine ⟨satisfiesPeriodicity_of_generatorPeriods hI hHgen, generator_periods_growth hI hHgen, ?_,
    hHrank.superharmonic, hHrank.recurrent, ?_⟩
  · intro x
    rcases hHrank x with ⟨h, -, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  · rw [hH]
    exact hna

end ChildFrame

end FLatticePaper.Induction
