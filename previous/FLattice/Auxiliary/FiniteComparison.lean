import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Finite integer comparison with two predecessors

Conditional internal infrastructure over an arbitrary vertex type. These
lemmas use no project-specific lattice, growth, or recurrence definitions.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary

variable {V α : Type*} [LinearOrder α]

/-- A finite set cannot give each of its vertices a vertex of strictly lower rank. -/
theorem not_nonempty_of_finite_rank_descent
    (s : Set V) (rank : V → α) (hFinite : s.Finite)
    (hDescend : ∀ z ∈ s, ∃ w ∈ s, rank w < rank z) :
    ¬s.Nonempty := by
  intro hNonempty
  obtain ⟨z, hz, hMin⟩ := Set.exists_min_image s rank hFinite hNonempty
  obtain ⟨w, hw, hLess⟩ := hDescend z hz
  exact (not_lt_of_ge (hMin w hw)) hLess

/-- A finite minimum level of an integer gap is empty when every zero-hole
vertex has a lower-rank predecessor and every one-hole vertex has two. -/
theorem not_exists_minimum_of_finite_rank
    (left right : V → V) (h u : V → ℤ) (rank : V → α) (m : ℤ)
    (hFinite : {z | h z - u z = m}.Finite)
    (hLower : ∀ z, m ≤ h z - u z)
    (hSuperharmonic : ∀ z, h (left z) + h (right z) ≤ 2 * h z)
    (hHoles : ∀ z, h z - u z = m →
      2 * u z - u (left z) - u (right z) = 0 ∨
      2 * u z - u (left z) - u (right z) = 1)
    (hZeroRank : ∀ z, h z - u z = m →
      2 * u z - u (left z) - u (right z) = 0 →
      rank (left z) < rank z ∨ rank (right z) < rank z)
    (hOneRank : ∀ z, h z - u z = m →
      2 * u z - u (left z) - u (right z) = 1 →
      rank (left z) < rank z ∧ rank (right z) < rank z) :
    ¬∃ z, h z - u z = m := by
  apply not_nonempty_of_finite_rank_descent {z | h z - u z = m} rank hFinite
  intro z hz
  change h z - u z = m at hz
  have hLeft := hLower (left z)
  have hRight := hLower (right z)
  have hStar := hSuperharmonic z
  rcases hHoles z hz with hZero | hOne
  · have hLeftEq : h (left z) - u (left z) = m := by omega
    have hRightEq : h (right z) - u (right z) = m := by omega
    rcases hZeroRank z hz hZero with hLess | hLess
    · exact ⟨left z, hLeftEq, hLess⟩
    · exact ⟨right z, hRightEq, hLess⟩
  · have hContact : h (left z) - u (left z) = m ∨
        h (right z) - u (right z) = m := by omega
    obtain ⟨hLeftLess, hRightLess⟩ := hOneRank z hz hOne
    rcases hContact with hLeftEq | hRightEq
    · exact ⟨left z, hLeftEq, hLeftLess⟩
    · exact ⟨right z, hRightEq, hRightLess⟩

/-- A superharmonic integer function lies above a prescribed lower profile
if its gap attains a finite minimum level, its prescribed values are above
the profile, and the remaining binary holes have the stated rank descent. -/
theorem le_of_finite_minimum_rank
    (left right : V → V) (h u : V → ℤ) (rank : V → α)
    (prescribed : Set V) (m : ℤ)
    (hFinite : {z | h z - u z = m}.Finite)
    (hLower : ∀ z, m ≤ h z - u z)
    (hAttained : ∃ z, h z - u z = m)
    (hSuperharmonic : ∀ z, h (left z) + h (right z) ≤ 2 * h z)
    (hPrescribed : ∀ z ∈ prescribed, u z ≤ h z)
    (hHoles : ∀ z, z ∉ prescribed →
      2 * u z - u (left z) - u (right z) = 0 ∨
      2 * u z - u (left z) - u (right z) = 1)
    (hZeroRank : ∀ z, z ∉ prescribed →
      2 * u z - u (left z) - u (right z) = 0 →
      rank (left z) < rank z ∨ rank (right z) < rank z)
    (hOneRank : ∀ z, z ∉ prescribed →
      2 * u z - u (left z) - u (right z) = 1 →
      rank (left z) < rank z ∧ rank (right z) < rank z) :
    ∀ z, u z ≤ h z := by
  have hMinimumNonneg : 0 ≤ m := by
    by_contra hNegative
    have hAvoid : ∀ z, h z - u z = m → z ∉ prescribed := by
      intro z hz hMember
      have hBound := hPrescribed z hMember
      omega
    have hNoMinimum := not_exists_minimum_of_finite_rank left right h u rank m
      hFinite hLower hSuperharmonic
      (fun z hz => hHoles z (hAvoid z hz))
      (fun z hz => hZeroRank z (hAvoid z hz))
      (fun z hz => hOneRank z (hAvoid z hz))
    exact hNoMinimum hAttained
  intro z
  have hBound := hLower z
  omega

end FLattice.Auxiliary
