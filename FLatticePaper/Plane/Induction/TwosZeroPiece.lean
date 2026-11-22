import FLatticePaper.Plane.Induction.TwosStrips
import FLatticePaper.Construction.NearOneBaseCases

/-! Task 31, step 1: the zero/zero piece of min(A, C) = V for the twos words.

On the zero/zero points of the closed polygon of `2^(k+1)` (where both reciprocal arguments lie in the transverse zone) the
sheets are the harmonic expressions `hA = h0(z - (1,1))` and `hC = h0(z - (0,2)) + z_1 - z_2`, and `V` is the near-one value
at `z + (0,1)`. The zero/zero points of `E` are exactly the four strips below (checked numerically for k <= 7, and the
identity checked for k <= 10). Each strip is linear in `(k, z_2)` for fixed `z_1`. The proof splits `z_2` by parity, so the
square `z_2^2` becomes an exact multiple of an atom, and then every floor is decided by `omega`. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- The zero/zero piece: `min(h0(z-(1,1)), h0(z-(0,2)) + z_1 - z_2) = paperNearLadderValue (2k+4) (z + (0,1))`. -/
theorem zero_zero_min_eq (k : ℤ) (hk : 0 ≤ k) (z1 z2 : ℤ)
    (hstrip : (z1 = -1 ∧ 2 * k + 4 ≤ z2 ∧ z2 ≤ 4 * k + 8) ∨ (z1 = 0 ∧ 1 ≤ z2 ∧ z2 ≤ 4 * k + 7) ∨
      (z1 = 1 ∧ 0 ≤ z2 ∧ z2 ≤ 2 * k + 4) ∨ (z1 = 2 ∧ 0 ≤ z2 ∧ z2 ≤ 1)) :
    min (harmonicGrid (z1 - 1, z2 - 1)) (harmonicGrid (z1, z2 - 2) + (z1 - z2)) =
      paperNearLadderValue (2 * k + 4) (z1, z2 + 1) := by
  unfold paperNearLadderValue
  rcases hstrip with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
  all_goals
    unfold harmonicGrid
    simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA,
      paperNearLadderB, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, true_and]
    rcases Int.even_or_odd' z2 with ⟨m, rfl | rfl⟩
    all_goals
      ring_nf
      split_ifs <;> omega

end FLatticePaper.Induction
