import FLatticePaper.Construction.LadderCoverage

namespace FLatticePaper.Construction

open Farey

/-- Coverage is of the actual occupied sites in each of the eight native registers. -/
structure TileRegisters.Covers (registers : TileRegisters) (parents : Parents) : Prop where
  standardOdd : (parents.current .odd).modifiedDeck.Covers registers.standard.currentOdd.val.sites
  standardEven : (parents.current .even).modifiedDeck.Covers registers.standard.currentEven.val.sites
  alternateOdd : (parents.current .odd).modifiedDeck.Covers registers.alternate.currentOdd.val.sites
  alternateEven : (parents.current .even).modifiedDeck.Covers registers.alternate.currentEven.val.sites
  standardRetainedOdd : parents.odd.modifiedDeck.Covers registers.standard.retainedOdd.val.sites
  standardRetainedEven : parents.even.modifiedDeck.Covers registers.standard.retainedEven.val.sites
  alternateRetainedOdd : parents.odd.modifiedDeck.Covers registers.alternate.retainedOdd.val.sites
  alternateRetainedEven : parents.even.modifiedDeck.Covers registers.alternate.retainedEven.val.sites

/-- At the empty word, check both native child parities and both families
against the complete quotient test, including their literal retained atoms. -/
theorem empty_registers_cover : BaseRun.empty.registers.llCenter.Covers (parentsAt []) := by
  constructor <;> apply (PeriodDeck.covers_iff_square_codes_subset _ (by decide) _).mpr <;> decide +kernel

theorem evaluateNative_empty_covers :
    ∃ registers, evaluateNative [] = .ok registers ∧ registers.Covers (parentsAt []) :=
  ⟨BaseRun.empty.registers.llCenter, evaluateNative_base .empty, empty_registers_cover⟩

def EndpointAtom.fraction : EndpointAtom → Fraction
  | .zero => ⟨0, 1⟩
  | .one => ⟨1, 1⟩

private theorem EndpointAtom.atOrigin_covers (endpoint : EndpointAtom) :
    endpoint.fraction.modifiedDeck.Covers endpoint.atOrigin.val.sites := by
  cases endpoint <;> apply (PeriodDeck.covers_iff_square_codes_subset _ (by decide) _).mpr <;>
    decide +kernel

private theorem EndpointAtom.attach_covers (endpoint : EndpointAtom) (standard : NonemptyTile) :
    endpoint.fraction.modifiedDeck.Covers ((endpoint.attach standard).llCenter).val.sites :=
  covers_place (covers_trim (covers_place endpoint.atOrigin_covers _ _) _) _ _

private theorem threes_frame (extra : ℕ) :
    parentsAt (BaseRun.threes extra).word = ⟨⟨0, 1⟩, ⟨1, 2 * (extra : ℤ) + 3⟩⟩ := by
  rw [BaseRun.word, parentsAt_replicate_three]
  apply congrArg (Parents.mk ⟨0, 1⟩)
  apply Fraction.ext rfl
  simp [Nat.cast_add]

private theorem twos_frame (extra : ℕ) :
    parentsAt (BaseRun.twos extra).word = ⟨(Fraction.mk 1 (2 * (extra : ℤ) + 3)).rotate, ⟨1, 1⟩⟩ := by
  have h := rotate_parentsAt (BaseRun.threes extra).word
  rw [threes_frame] at h
  have hone : (Fraction.mk 0 1).rotate = ⟨1, 1⟩ := rfl
  simpa only [BaseRun.word, List.map_replicate, Digit.swapTwoThree, Parents.rotate, hone] using h.symm

theorem threes_registers_cover (extra : ℕ) :
    (BaseRun.threes extra).registers.llCenter.Covers (parentsAt (BaseRun.threes extra).word) := by
  obtain ⟨odd, hodd, hso, hao⟩ := evaluateNative_threes_odd_covers extra
  obtain ⟨even, heven, hse, hae⟩ := evaluateNative_threes_even_covers extra
  have hOdd := Except.ok.inj (hodd.symm.trans (evaluateNative_base (BaseRun.threes extra)))
  have hEven := Except.ok.inj (heven.symm.trans (evaluateNative_base (BaseRun.threes extra)))
  subst odd even
  refine ⟨hso, hse, hao, hae, ?_, ?_, ?_, ?_⟩
  all_goals rw [threes_frame]
  · apply EndpointAtom.attach_covers .zero
  · apply covers_place
    exact stairEven_cover (by simp [BaseMask.Valid])
  · apply EndpointAtom.attach_covers .zero
  · apply covers_place
    exact stairEvenAlt_cover (by simp [BaseMask.Valid])

theorem twos_registers_cover (extra : ℕ) :
    (BaseRun.twos extra).registers.llCenter.Covers (parentsAt (BaseRun.twos extra).word) := by
  obtain ⟨odd, hodd, hso, hao⟩ := evaluateNative_twos_odd_covers extra
  obtain ⟨even, heven, hse, hae⟩ := evaluateNative_twos_even_covers extra
  have hOdd := Except.ok.inj (hodd.symm.trans (evaluateNative_base (BaseRun.twos extra)))
  have hEven := Except.ok.inj (heven.symm.trans (evaluateNative_base (BaseRun.twos extra)))
  subst odd even
  refine ⟨hso, hse, hao, hae, ?_, ?_, ?_, ?_⟩
  all_goals rw [twos_frame]
  · apply covers_place
    exact stairOdd_cover (by simp [BaseMask.Valid])
  · apply EndpointAtom.attach_covers .one
  · apply covers_place
    exact stairOddAlt_cover (by simp [BaseMask.Valid])
  · apply EndpointAtom.attach_covers .one

/-- Every literal initializer covers all eight registers in their own period spans. -/
theorem evaluateNative_base_covers (run : BaseRun) :
    ∃ registers, evaluateNative run.word = .ok registers ∧ registers.Covers (parentsAt run.word) := by
  refine ⟨run.registers.llCenter, evaluateNative_base run, ?_⟩
  cases run with
  | empty => exact empty_registers_cover
  | twos extra => exact twos_registers_cover extra
  | threes extra => exact threes_registers_cover extra

end FLatticePaper.Construction
