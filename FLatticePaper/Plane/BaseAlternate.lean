import FLatticePaper.MainTheorems
import FLatticePaper.Plane.Induction.AlternateFacts
import FLatticePaper.Plane.Induction.ReciprocalInputs
import FLatticePaper.Plane.Induction.StandardField
import FLatticePaper.Construction.AlternateStaircaseRotation
import FLatticePaper.Construction.AlternateStaircaseRank

/-! The alternate facts of a word, from its midpoint `frame.alternate (standardField u)`.

For a word whose standard field is an explicit base field (the reciprocal staircase `3^k`), the midpoint agrees, up to a
constant, with the explicit base alternate `stairEvenAltField`: then the binary Laplacian, the superharmonicity and the
recurrence come from the explicit burning rank of the base alternate (`stairEvenAlt_exists_burningRank`), which needs only the
agreement and the periods of the standard field, not the star estimates. -/

namespace FLatticePaper.BaseAlternate

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Induction

/-- The alternate facts of a word `u`: the generator identity of the midpoint `frame.alternate (standardField u)` (its transverse
constant lowered by one), `eq:periodicity`, the quadratic growth, the binary Laplacian, superharmonicity, recurrence, and the
non-integer-affine difference from the standard field. -/
def AlternateFactsWord (u : Word) : Prop :=
  HasGeneratorPeriods (frameAt u).child ((frameAt u).alternate (standardField u))
      (frameAt u).coherentConstantU ((frameAt u).coherentConstantV - 1) ∧
    SatisfiesPeriodicity (frameAt u).child ((frameAt u).alternate (standardField u)) ∧
    HasQuadraticGrowth ((frameAt u).alternate (standardField u)) (frameAt u).child.matrix ∧
    (∀ x, laplacian ((frameAt u).alternate (standardField u)) x = -1 ∨
      laplacian ((frameAt u).alternate (standardField u)) x = 0) ∧
    Superharmonic ((frameAt u).alternate (standardField u)) ∧
    Recurrent ((frameAt u).alternate (standardField u)) ∧
    ¬ IntegerAffine (fun x => (frameAt u).alternate (standardField u) x - standardField u x)

/-- The alternate facts of a word whose star estimates are known (the headline's route). -/
theorem alternateFactsWord_of_star (u : Word) (hpk : (frameAt u).Packet (standardField u))
    (hS : StarEstimates u) : AlternateFactsWord u := by
  obtain ⟨hU, hNS, rank, hrank⟩ := hS
  exact (frameAt u).alternate_facts hpk.periods hU hNS hrank

theorem not_integerAffine_add_const {G : Field} {c : ℤ} (h : ¬ IntegerAffine G) :
    ¬ IntegerAffine (fun x => G x + c) := by
  rintro ⟨g, d, hg⟩
  apply h
  refine ⟨g, d - c, fun x => ?_⟩
  have := hg x
  simp only at this
  linarith

theorem laplacian_add_const (A : Field) (c : ℤ) (x : Site) :
    laplacian (fun y => A y + c) x = laplacian A x := by
  simp only [laplacian]
  ring

theorem isBurningRank_add_const {α : Type*} [LT α] {A : Field} {rank : Site → α} (h : IsBurningRank A rank)
    (c : ℤ) : IsBurningRank (fun y => A y + c) rank := by
  unfold IsBurningRank at h ⊢
  intro x
  rw [laplacian_add_const]
  exact h x

/-- The alternate facts of a frame whose midpoint is a constant translate of an explicit base alternate `A`, with the explicit
burning rank of `A`, the generator identity of `A`, and the non-integer-affine difference of `A` from the standard field. -/
theorem alternateFacts_of_explicit (frame : ChildFrame) {F A : Field} {cU cV c : ℤ}
    (hA : HasGeneratorPeriods frame.child A cU (cV - 1)) (hint : frame.child.InUnitInterval)
    {rank : Site → ℤ} (hrank : IsBurningRank A rank)
    (hnot : ¬ IntegerAffine (fun x => A x - F x))
    (hid : ∀ x, frame.alternate F x = A x + c) :
    HasGeneratorPeriods frame.child (frame.alternate F) cU (cV - 1) ∧
      SatisfiesPeriodicity frame.child (frame.alternate F) ∧
      HasQuadraticGrowth (frame.alternate F) frame.child.matrix ∧
      (∀ x, laplacian (frame.alternate F) x = -1 ∨ laplacian (frame.alternate F) x = 0) ∧
      Superharmonic (frame.alternate F) ∧ Recurrent (frame.alternate F) ∧
      ¬ IntegerAffine (fun x => frame.alternate F x - F x) := by
  have hfun : frame.alternate F = fun y => A y + c := funext hid
  rw [hfun]
  have hper : HasGeneratorPeriods frame.child (fun y => A y + c) cU (cV - 1) := by
    refine ⟨fun x => ?_, fun x => ?_⟩
    · show A (x + frame.child.modifiedDeck.kernel) + c = (A x + c) + cU
      rw [hA.1 x]
      ring
    · show A (x + frame.child.modifiedDeck.transverse) + c =
        (A x + c) - frame.child.transverseGrade x + (cV - 1)
      rw [hA.2 x]
      ring
  have hR := isBurningRank_add_const hrank c
  refine ⟨hper, satisfiesPeriodicity_of_generatorPeriods hint hper, generator_periods_growth hint hper, ?_,
    hR.superharmonic, hR.recurrent, ?_⟩
  · intro x
    rcases hR x with ⟨h1, -, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · show ¬ IntegerAffine (fun x => A x + c - F x)
    have : (fun x => A x + c - F x) = fun x => (A x - F x) + c := by
      funext x
      ring
    rw [this]
    exact not_integerAffine_add_const hnot

/-- The alternate facts of the reciprocal word `3^k`, from the midpoint agreeing with the explicit base alternate up to a
constant (the base case of the alternate identification). -/
theorem reciprocal_alternateFactsWord (k : ℕ)
    (hid : ∃ c : ℤ, ∀ x, (frameAt (List.replicate k Digit.three)).alternate
        (standardField (List.replicate k Digit.three)) x =
      stairEvenAltField (2 * (k : ℤ) + 3) (standardField (List.replicate k Digit.three)) x + c) :
    AlternateFactsWord (List.replicate k Digit.three) := by
  obtain ⟨c, hc⟩ := hid
  have hstd : standardField (List.replicate k Digit.three) = reciprocalField k := standardField_threes k
  obtain ⟨hagree, hper⟩ := reciprocalField_spec k
  have hchild : (frameAt (List.replicate k Digit.three)).child = ⟨1, 2 * (k : ℤ) + 3⟩ :=
    reciprocalFrame_child k
  have hcU : (frameAt (List.replicate k Digit.three)).coherentConstantU = 0 :=
    (reciprocal_coherentConstants k).1
  have hcV : (frameAt (List.replicate k Digit.three)).coherentConstantV =
      stairEvenConstantV (2 * (k : ℤ) + 3) :=
    (reciprocal_coherentConstants k).2
  have hagreeF : (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).Agrees
      (standardField (List.replicate k Digit.three)) 0 := by
    rw [hstd]
    exact hagree
  have hperF : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 3))
      (standardField (List.replicate k Digit.three)) 0 (stairEvenConstantV (2 * (k : ℤ) + 3)) := by
    rw [hstd]
    exact hper
  have hden : BaseMask.stairEvenAlt.Valid (2 * (k : ℤ) + 3) := ⟨by omega, by omega⟩
  obtain ⟨correction, -, -, hrank⟩ := stairEvenAlt_exists_burningRank hden hagreeF hperF
  have hnot := stairEvenAltField_sub_standard_not_integerAffine (den := 2 * (k : ℤ) + 3) (by omega) hperF
  have hA := stairEvenAltField_periods hperF
  have hint : (Fraction.mk 1 (2 * (k : ℤ) + 3)).InUnitInterval :=
    ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  have hint' : (frameAt (List.replicate k Digit.three)).child.InUnitInterval := by
    rw [hchild]
    exact hint
  have hAframe : HasGeneratorPeriods (frameAt (List.replicate k Digit.three)).child
      (stairEvenAltField (2 * (k : ℤ) + 3) (standardField (List.replicate k Digit.three)))
      (frameAt (List.replicate k Digit.three)).coherentConstantU
      ((frameAt (List.replicate k Digit.three)).coherentConstantV - 1) := by
    rw [hchild, hcU, hcV]
    exact hA
  exact alternateFacts_of_explicit (frameAt (List.replicate k Digit.three)) hAframe hint' hrank hnot hc

end FLatticePaper.BaseAlternate
