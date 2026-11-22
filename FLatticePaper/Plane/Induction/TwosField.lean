import FLatticePaper.Construction.BaseCases
import FLatticePaper.Plane.Induction.StandardField

/-! Task 28: the standard field of the twos family `2^(k+1)`.

* The conjugate of `2^(k+1)` is the threes word `3^k`: `oddBirthPrefix (2^(k+1)) = 2^k` and the swap exchanges 2 and 3.
  So the standard field of `2^(k+1)` is the sewn sheet minimum of the quarter turn of the reciprocal field `reciprocalField k`
  (the closed form in terms of the reciprocal base, `standardField_twos_succ`).
* The even child of `2^(k+1)` is `rotate <1, 2k+4>` (`baseChildren_twos`), the period fraction of the near-one even doubled
  staircase `NearOneBaseCases.near_doubled_staircase_base` with `d = 2k + 4`. Numerically (scripts/twos_even_fit.py) the
  standard field of `2^k` agrees, on its tile, with that staircase for `d = 2k+2`, `k = 1..6`, under `z <-> z + (0, 1)`; the
  Lean identification of the tile values for every `k` is not done here. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- The odd birth prefix of `2^(k+1)` is `2^k`: the trailing threes are none, and one letter is dropped. -/
theorem oddBirthPrefix_replicate_two (k : ℕ) :
    oddBirthPrefix (List.replicate (k + 1) Digit.two) = List.replicate k Digit.two := by
  simp [oddBirthPrefix, List.reverse_replicate, List.replicate_succ']

/-- The conjugate word of `2^(k+1)` is the threes word `3^k`. -/
theorem conjWord_replicate_two (k : ℕ) :
    (oddBirthPrefix (List.replicate (k + 1) Digit.two)).map Digit.swapTwoThree =
      List.replicate k Digit.three := by
  rw [oddBirthPrefix_replicate_two, List.map_replicate]
  rfl

/-- The closed form in terms of the reciprocal base: the standard field of `2^(k+1)` is the sewn sheet minimum of the
quarter turn of the reciprocal field `reciprocalField k`, with the coherent constants of the frame of `2^(k+1)`. -/
theorem standardField_twos_succ (k : ℕ) :
    standardField (List.replicate (k + 1) Digit.two) =
      (frameAt (List.replicate (k + 1) Digit.two)).sewnField
        ((frameAt (List.replicate (k + 1) Digit.two)).sheetMin (quarterTurnField (reciprocalField k)))
        (frameAt (List.replicate (k + 1) Digit.two)).coherentConstantU
        (frameAt (List.replicate (k + 1) Digit.two)).coherentConstantV := by
  have hnot : ¬ ∀ x ∈ List.replicate (k + 1) Digit.two, x = Digit.three := by
    intro h
    exact absurd (h Digit.two (List.mem_replicate.mpr ⟨by omega, rfl⟩)) (by decide)
  rw [standardField, dif_neg hnot, conjWord_replicate_two, standardField_threes]

/-- The even child of `2^(k+1)` is the period fraction `rotate <1, 2k+4>` of the near-one even doubled staircase
with `d = 2k + 4`. -/
theorem child_replicate_two_succ (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).child =
      Fraction.rotate ⟨1, 2 * (k : ℤ) + 4⟩ := by
  have h := (baseChildren_twos (k + 1)).2
  have hd : 2 * ((k + 1 : ℕ) : ℤ) + 2 = 2 * (k : ℤ) + 4 := by push_cast; ring
  rw [hd] at h
  exact h

end FLatticePaper.Induction
