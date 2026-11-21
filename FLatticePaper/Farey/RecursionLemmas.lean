import FLatticePaper.Farey.Birth
import FLatticePaper.Farey.Rotation

namespace FLatticePaper.Farey

/-- The child operator `C(p,q)` of `eq:child_operator` on an odd-even pair. -/
def childPair (pair : Parents) : Parents := ⟨pair.current .odd, pair.current .even⟩

/-- `lemma:recursion-unique`: every quadruple is reduced with the stated parities, and distinct words give
distinct quadruples. -/
theorem recursion_unique (word : Word) :
    ((parentsAt word).current .odd).Reduced ∧ ((parentsAt word).current .even).Reduced ∧
    (parentsAt word).odd.Reduced ∧ (parentsAt word).even.Reduced ∧
    ((parentsAt word).current .odd).Odd ∧ (parentsAt word).odd.Odd ∧
    ((parentsAt word).current .even).Even ∧ (parentsAt word).even.Even ∧
    ((parentsAt word).current .odd).InUnitInterval ∧ ((parentsAt word).current .even).InUnitInterval := by
  have hv := parentsAt_valid word
  exact ⟨hv.current_reduced .odd, hv.current_reduced .even, hv.odd_reduced, hv.even_reduced,
    hv.current_odd_parity, hv.odd_parity, hv.current_even_parity, hv.even_parity,
    (hv.current_interior .odd).inUnitInterval, (hv.current_interior .even).inUnitInterval⟩

theorem parentsAt_injective : Function.Injective parentsAt := by
  intro word other heq
  have hodd : Birth.fraction (word, .odd) = Birth.fraction (other, .odd) := by
    change (parentsAt word).current .odd = (parentsAt other).current .odd
    rw [heq]
  exact congrArg Prod.fst (Birth.fraction_injective hodd)

/-- `lemma:rot_child_commute`. -/
theorem rot_child_commute {pair : Parents} (h : pair.ValidFrame) :
    (childPair pair).rotate = childPair pair.rotate :=
  congrArg₂ Parents.mk h.rotate_current_even h.rotate_current_odd

/-- Reversing a word by exchanging the two digits twice returns the word. -/
theorem swapMap_swapMap (word : Word) :
    (word.map Digit.swapTwoThree).map Digit.swapTwoThree = word := by
  induction word with
  | nil => rfl
  | cons digit tail ih => simp only [List.map_cons, Digit.swapTwoThree_swapTwoThree, ih]

/-- `lemma:rot_invariance`. -/
theorem rot_invariance (word : Word) :
    (parentsAt (word ++ [.one])).rotate = (parentsAt word).rotate.step .one ∧
    (parentsAt (word ++ [.two])).rotate = (parentsAt word).rotate.step .three ∧
    (parentsAt (word ++ [.three])).rotate = (parentsAt word).rotate.step .two ∧
    ∀ n : ℕ, (fun w => (parentsAt w).rotate) '' {w : Word | w.length = n} =
      parentsAt '' {w : Word | w.length = n} := by
  have hv := parentsAt_valid word
  refine ⟨?_, ?_, ?_, fun n => ?_⟩
  · rw [parentsAt_append_singleton]
    exact hv.rotate_step .one
  · rw [parentsAt_append_singleton]
    exact hv.rotate_step .two
  · rw [parentsAt_append_singleton]
    exact hv.rotate_step .three
  · ext P
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.map Digit.swapTwoThree, by simp [hw], (rotate_parentsAt w).symm⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.map Digit.swapTwoThree, by simp [hw], by rw [rotate_parentsAt, swapMap_swapMap]⟩

end FLatticePaper.Farey
