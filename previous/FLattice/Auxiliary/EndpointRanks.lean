import FLattice.Auxiliary.ElementaryProfiles

/-!
# Actual incoming pairs, deficits and ranks for the two endpoints

The selected slots are literal neighbors of the native F-lattice.
At deficit zero one slot decreases rank; at deficit one both do.
The ranks are unbounded, which is allowed by the proper-gap principle.
-/

set_option autoImplicit false
open scoped BigOperators

namespace FLattice.Auxiliary.EndpointRanks

open ElementaryProfiles

/-- The two incoming slots, in negative and positive coordinate order. -/
def incoming (z : ℤ × ℤ) (i : Fin 2) : ℤ × ℤ :=
  if parity z.1 z.2 = 0 then
    if i = 0 then (z.1 - 1, z.2) else (z.1 + 1, z.2)
  else if i = 0 then (z.1, z.2 - 1) else (z.1, z.2 + 1)

/-- The two endpoint integer functions, indexed by zero and one. -/
def profile (i : Fin 2) : ℤ × ℤ → ℤ := if i = 0 then zeroProfile else oneProfile

/-- The exact nonnegative deficit of each endpoint. -/
def deficit (i : Fin 2) (z : ℤ × ℤ) : ℕ :=
  if parity z.1 z.2 = 0 then (if i = 0 then 0 else 1) else (if i = 0 then 1 else 0)

/-- The directed endpoint ranks used by the finite minimum argument. -/
def rank (i : Fin 2) (z : ℤ × ℤ) : ℤ :=
  if i = 0 then 2 * z.1 + parity z.1 z.2 else 2 * z.2 - parity z.1 z.2

/-- The indexed sum is the literal native incoming sum. -/
theorem incoming_sum (g : ℤ × ℤ → ℤ) (x y : ℤ) :
    (∑ j : Fin 2, g (incoming (x, y) j)) =
      if (x + y) % 2 = 0 then g (x - 1, y) + g (x + 1, y)
        else g (x, y - 1) + g (x, y + 1) := by
  simp only [Fin.sum_univ_two, incoming, parity, Fin.isValue, if_true,
    show (1 : Fin 2) ≠ 0 by decide, if_false]
  split_ifs <;> rfl

/-- Each stated deficit is the actual incoming Laplacian deficit. -/
theorem profile_incoming_sum (i : Fin 2) (x y : ℤ) :
    (∑ j : Fin 2, profile i (incoming (x, y) j)) =
      2 * profile i (x, y) - (deficit i (x, y) : ℤ) := by
  rw [incoming_sum]
  have he := parity_cases x y
  fin_cases i <;> rcases he with he | he
  · have h := zeroProfile_horizontal x y
    have hParity : (x + y) % 2 = 0 := he
    norm_num [profile, deficit, he, hParity]
    omega
  · have h := zeroProfile_vertical x y
    have hParity : (x + y) % 2 ≠ 0 := by change parity x y ≠ 0; omega
    norm_num [profile, deficit, he, hParity]
    omega
  · have h := oneProfile_horizontal x y
    have hParity : (x + y) % 2 = 0 := he
    norm_num [profile, deficit, he, hParity]
    omega
  · have h := oneProfile_vertical x y
    have hParity : (x + y) % 2 ≠ 0 := by change parity x y ≠ 0; omega
    norm_num [profile, deficit, he, hParity]
    omega

/-- More slots than the deficit strictly decrease the displayed rank. -/
theorem selected_incoming (i : Fin 2) (z : ℤ × ℤ) :
    ∃ S : Finset (Fin 2), deficit i z < S.card ∧
      ∀ j ∈ S, rank i (incoming z j) < rank i z := by
  rcases z with ⟨x, y⟩
  obtain ⟨hxm, hxp, hym, hyp⟩ := neighbor_parities x y
  have he := parity_cases x y
  fin_cases i <;> rcases he with he | he
  · refine ⟨{0}, ?_, ?_⟩
    · norm_num [deficit, he]
    · intro j hj
      have hj' : j = 0 := Finset.mem_singleton.mp hj
      subst j
      norm_num [incoming, rank, he]
      omega
  · refine ⟨Finset.univ, ?_, ?_⟩
    · norm_num [deficit, he]
    · intro j _
      fin_cases j <;> norm_num [incoming, rank, he] <;> omega
  · refine ⟨Finset.univ, ?_, ?_⟩
    · norm_num [deficit, he]
    · intro j _
      fin_cases j <;> norm_num [incoming, rank, he] <;> omega
  · refine ⟨{0}, ?_, ?_⟩
    · norm_num [deficit, he]
    · intro j hj
      have hj' : j = 0 := Finset.mem_singleton.mp hj
      subst j
      norm_num [incoming, rank, he]
      omega

end FLattice.Auxiliary.EndpointRanks
