import FLatticePaper.MainTheorems
import FLatticePaper.Plane.Induction.AlternateFacts
import FLatticePaper.Plane.Induction.ReciprocalInputs
import FLatticePaper.Plane.Induction.StandardField
import FLatticePaper.Construction.AlternateStaircaseRotation
import FLatticePaper.Construction.AlternateStaircaseRank
import FLatticePaper.Construction.AlternateLadderRank
import FLatticePaper.Construction.AlternateLadderRotation
import FLatticePaper.Plane.Induction.TwosPacket
import FLatticePaper.Plane.Induction.TwosPeriods
import FLatticePaper.Construction.PropBaseCases

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

/-- Adding a harmonic function preserves recurrence (the difference against a superharmonic competitor shifts). -/
theorem recurrent_add_harmonic {F L : Field} (hF : Recurrent F) (hL : ∀ x, laplacian L x = 0) :
    Recurrent (fun y => F y + L y) := by
  intro C hC sites h
  have hCL : Superharmonic (fun y => C y - L y) := by
    intro x
    have h1 := hC x
    have h2 := hL x
    simp only [laplacian] at h1 h2 ⊢
    linarith
  have key := hF (fun y => C y - L y) hCL sites h
  have e1 : maxDifference (fun y => F y + L y) C sites h.1 =
      maxDifference F (fun y => C y - L y) sites h.1 := by
    unfold maxDifference
    congr 2
    funext s
    ring
  have e2 : maxDifference (fun y => F y + L y) C (incomingBoundaryFinset sites)
      (incomingBoundaryFinset_nonempty h.1) =
      maxDifference F (fun y => C y - L y) (incomingBoundaryFinset sites)
        (incomingBoundaryFinset_nonempty h.1) := by
    unfold maxDifference
    congr 2
    funext s
    ring
  rw [e1, e2]
  exact key

/-- The alternate facts of a frame whose midpoint is a constant translate of an explicit base alternate `A`, with the explicit
burning rank of `A`, the generator identity of `A`, and the non-integer-affine difference of `A` from the standard field. -/
theorem alternateFacts_of_explicit (frame : ChildFrame) {F A : Field} {cU cV c : ℤ}
    (hA : HasGeneratorPeriods frame.child A cU (cV - 1)) (hint : frame.child.InUnitInterval)
    (hbin : ∀ x, laplacian A x = -1 ∨ laplacian A x = 0) (hsup : Superharmonic A) (hrec : Recurrent A)
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
  have hconst : ∀ x, laplacian (fun y => A y + c) x = laplacian A x := fun x => laplacian_add_const A c x
  have hrecShift : Recurrent (fun y => A y + c) := by
    have h := recurrent_add_harmonic hrec (L := fun _ => c) (fun x => by simp only [laplacian]; ring)
    exact h
  refine ⟨hper, satisfiesPeriodicity_of_generatorPeriods hint hper, generator_periods_growth hint hper, ?_,
    ?_, hrecShift, ?_⟩
  · intro x
    rw [hconst]
    exact hbin x
  · intro x
    rw [hconst]
    exact hsup x
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
  have hbin : ∀ x, laplacian (stairEvenAltField (2 * (k : ℤ) + 3) (standardField (List.replicate k Digit.three))) x =
      -1 ∨ laplacian (stairEvenAltField (2 * (k : ℤ) + 3) (standardField (List.replicate k Digit.three))) x = 0 := by
    intro x
    rcases hrank x with ⟨h1, -, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  exact alternateFacts_of_explicit (frameAt (List.replicate k Digit.three)) hAframe hint' hbin hrank.superharmonic
    hrank.recurrent hnot hc


/-- The explicit rotated alternate `rotateLadderAltField` in the form of the quarter turn: the Laplacian at a site is the
Laplacian of the base field at the mapped site. -/
theorem rotateLadderAltField_eq' (den : ℤ) (S : Field) :
    rotateLadderAltField den S = fun point => S (QuarterTurn.counterclockwise.mapSite (2 * den - 2, 1) point) +
      (centeredQuarterTurnCorrection point + (point.1 + 1)) := by
  funext point
  have hshift : QuarterTurn.counterclockwise.mapSite (2 * den, 1) point - (2, 0) =
      QuarterTurn.counterclockwise.mapSite (2 * den - 2, 1) point := by
    apply Prod.ext <;> dsimp [QuarterTurn.mapSite, QuarterTurn.turn] <;> omega
  simp only [rotateLadderAltField, rotateLadderField, hshift, add_assoc]

theorem harmonic_ladderAltCorrection' :
    Harmonic (fun point : Site => centeredQuarterTurnCorrection point + (point.1 + 1)) := by
  intro point
  have h := harmonic_centeredQuarterTurnCorrection point
  have hline : (incomingNeg point).1 + (incomingPos point).1 = 2 * point.1 := by
    by_cases he : EvenSite point
    · simp only [incomingNeg, incomingPos, if_pos he]
      omega
    · simp only [incomingNeg, incomingPos, if_neg he]
      omega
  simp only [laplacian] at h ⊢
  omega

/-- The binary Laplacian of the rotated alternate, from the binary Laplacian of its base field. -/
theorem rotateLadderAltField_binary {den : ℤ} {S : Field} (hS : ∀ x, laplacian S x = -1 ∨ laplacian S x = 0)
    (x : Site) : laplacian (rotateLadderAltField den S) x = -1 ∨ laplacian (rotateLadderAltField den S) x = 0 := by
  have hodd : ¬ EvenSite (2 * den - 2, 1) := by
    unfold EvenSite
    dsimp only
    omega
  have h := laplacian_quarterTurn_add_harmonic QuarterTurn.counterclockwise (2 * den - 2, 1) hodd S
    (fun point => centeredQuarterTurnCorrection point + (point.1 + 1)) harmonic_ladderAltCorrection' x
  rw [rotateLadderAltField_eq', h]
  exact hS _

/-- The twos standard field's alternate facts from the explicit rotated alternate: the base field of the ladder alternate
agrees with its raw tile and has the periods, and the midpoint agrees with the rotated alternate up to a constant. -/
theorem twos_alternateFactsWord (k : ℕ)
    (hid : ∃ S : Field, (BaseMask.ladderOddAlt.raw (2 * (k : ℤ) + 4)).Agrees S 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S (-1) (ladderOddAltConstantV (2 * (k : ℤ) + 4)) ∧
      ∃ c : ℤ, ∀ x, (frameAt (List.replicate (k + 1) Digit.two)).alternate
        (standardField (List.replicate (k + 1) Digit.two)) x =
        rotateLadderAltField (2 * (k : ℤ) + 4) S x + c) :
    AlternateFactsWord (List.replicate (k + 1) Digit.two) := by
  obtain ⟨S, hagreeS, hperS, c, hc⟩ := hid
  have hden : BaseMask.ladderOddAlt.Valid (2 * (k : ℤ) + 4) := ⟨by omega, by omega⟩
  have heven : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  obtain ⟨correction, -, -, hrankS⟩ := ladderOddAlt_exists_burningRank hden hagreeS hperS
  have hbinS : ∀ x, laplacian S x = -1 ∨ laplacian S x = 0 := by
    intro x
    rcases hrankS x with ⟨h1, -, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hA := rotateLadderAltField_periods heven hperS
  have hrot : (Fraction.mk 1 (2 * (k : ℤ) + 4)).rotate = (frameAt (List.replicate (k + 1) Digit.two)).child := by
    rw [twos_child_eq k, rotate_ladder_fraction]
  -- the standard field's periods, from an explicit base field of the ladder
  obtain ⟨Sstd, hagStd, hperStd, -, -, -⟩ := ladderOdd_exists_recurrent_extension hden
  have hstd := twos_standardField_periods k hagStd hperStd
  have hstd' : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)).rotate
      (standardField (List.replicate (k + 1) Digit.two)) 0 (ladderEvenConstantV (2 * (k : ℤ) + 4)) := by
    rw [hrot]
    exact hstd
  have hnot := ladderEvenAlt_sub_standard_not_integerAffine heven hstd' hA
  have hcoh := twos_coherentConstants k
  have hAframe : HasGeneratorPeriods (frameAt (List.replicate (k + 1) Digit.two)).child
      (rotateLadderAltField (2 * (k : ℤ) + 4) S) (frameAt (List.replicate (k + 1) Digit.two)).coherentConstantU
      ((frameAt (List.replicate (k + 1) Digit.two)).coherentConstantV - 1) := by
    rw [hcoh.1, hcoh.2, ← hrot]
    exact hA
  have hint : (frameAt (List.replicate (k + 1) Digit.two)).child.InUnitInterval := by
    rw [← hrot]
    exact ladder_rotate_inUnitInterval hden.1 hden.2
  obtain ⟨hsupA, hrecA⟩ := rotateLadderAltField_recurrent hrankS.recurrent hrankS.superharmonic
  exact alternateFacts_of_explicit (frameAt (List.replicate (k + 1) Digit.two)) hAframe hint
    (rotateLadderAltField_binary hbinS) hsupA hrecA hnot hc

end FLatticePaper.BaseAlternate
