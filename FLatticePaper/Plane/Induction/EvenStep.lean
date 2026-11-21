import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.AlternatePeriods
import FLatticePaper.Plane.Recurrence
import FLatticePaper.Plane.OdometerTheorem

namespace FLatticePaper.Induction
open Farey

/-- The shift of the even alternate is the child's short slip `alternateSlip`. -/
theorem ChildFrame.shortShift_eq_alternateSlip (frame : ChildFrame) :
    frame.shortShift = alternateSlip frame.child.num frame.child.den
      frame.parents.odd.num frame.parents.odd.den := by
  have he := frame.eps_eq
  unfold ChildFrame.shortShift alternateSlip
  dsimp only
  rw [he]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> ring

namespace ChildFrame

/-- The even alternate `H = ⌈(F + F(· + σ))/2⌉`. -/
def alternate (frame : ChildFrame) (F : Field) : Field :=
  roundedMidpoint F (fun z => F (z + frame.shortShift))

theorem alternate_eq (frame : ChildFrame) (F : Field) (z : Site) :
    frame.alternate F z = F z - frame.slip F 1 z / 2 := by
  simp only [ChildFrame.alternate, roundedMidpoint, ChildFrame.slip, one_smul]

/-- `theorem:odometers` at an even child, from the standard field's generator identities and the three Part I
star estimates with a constrained rank. -/
theorem odometersTheoremAt_of_standard (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (hperiod : HasGeneratorPeriods frame.child F cU cV)
    {α : Type*} [LinearOrder α] {rank : Site → α}
    (hstep : HasUnitSlip F (fun z => F (z + frame.shortShift)))
    (hnoSaddle : NoEvenSlipSaddle F (fun z => F (z + frame.shortShift)))
    (hrank : IsConstrainedBurningRank F rank
      (fun center input => slipIncrement F (fun z => F (z + frame.shortShift)) center input ≤ 0)) :
    OdometersTheoremAt frame.child := by
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
  -- the standard is superharmonic and recurrent, from its rank
  have hstdRank : IsBurningRank F rank := hrank.toIsBurningRank
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
  refine ⟨F, frame.alternate F, ⟨hstdRank.superharmonic, hstdRank.recurrent,
      generator_periods_growth hI hperiod⟩,
    ⟨hHrank.superharmonic, hHrank.recurrent, generator_periods_growth hI hHgen⟩,
    satisfiesPeriodicity_of_generatorPeriods hI hperiod,
    satisfiesPeriodicity_of_generatorPeriods hI hHgen, ?_, ?_⟩
  · intro h
    apply hna
    refine ⟨(0, 0), 0, fun site => ?_⟩
    have hsite : roundedMidpoint F (alternateCompanion F frame.child.num frame.child.den
        frame.parents.odd.num frame.parents.odd.den) site = F site := by
      rw [← hH]
      exact (congrFun h site).symm
    simp [hsite]
  · rw [hH]
    exact hna

end ChildFrame

end FLatticePaper.Induction
