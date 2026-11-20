import FLattice.Auxiliary.PlusEvenDeficitTable
import FLattice.Auxiliary.PlusEvenDeficitTranslations
import Mathlib.Tactic.FinCases

/-!
# The even-plus deficit on the whole physical lattice

Complete representative coverage and all signed period translations extend
the physical deficit table to every lattice point. The exceptional class is
identified with the explicit source coset `D-C(a,b)`, not assumed to agree
with a condition on decoded coordinates.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

private theorem incomingDeficit_cell_cases (m : Parameter) (r s : ℤ) (e v : Fin 2)
    (hr0 : 0 ≤ r) (hrm : r ≤ m.val + 1)
    (hs0 : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1)) :
    (r = 0 ∧ s = 0 ∧ e = 1 ∧ v = 0 ∧
      incomingDeficit m (2 * m.val * r + 2 * s + (v.val : ℤ)) (e.val : ℤ) = 4) ∨
    incomingDeficit m (2 * m.val * r + 2 * s + (v.val : ℤ)) (e.val : ℤ) = 0 ∨
    incomingDeficit m (2 * m.val * r + 2 * s + (v.val : ℤ)) (e.val : ℤ) = 1 := by
  fin_cases e <;> fin_cases v
  · norm_num
    rw [incomingDeficit_00_at_cell m r s hr0 hrm hs0 hsm hMissing]
    split_ifs <;> simp_all
  · norm_num
    rw [incomingDeficit_01_at_cell m r s hr0 hrm hs0 hsm hMissing]
    split_ifs <;> simp_all
  · norm_num
    rw [incomingDeficit_10_at_cell m r s hr0 hrm hs0 hsm hMissing]
    split_ifs <;> simp_all
  · norm_num
    rw [incomingDeficit_11_at_cell m r s hr0 hrm hs0 hsm hMissing]
    split_ifs <;> simp_all

/-- At every physical point the deficit is zero or one, except on the explicit
prescribed coset, where the remaining alternative has deficit four. -/
theorem incomingDeficit_cases (m : Parameter) (x y : ℤ) :
    ((∃ a b : ℤ,
      x = -2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b ∧
      y = -1 - 2 * m.val * a - 2 * b) ∧ incomingDeficit m x y = 4) ∨
    incomingDeficit m x y = 0 ∨ incomingDeficit m x y = 1 := by
  obtain ⟨r, s, k, q, e, v, hr0, hrm, hs0, hsm, hMissing, hx, hy⟩ :=
    exists_valid_lifted_cell m x y
  have hMove : incomingDeficit m x y =
      incomingDeficit m (2 * m.val * r + 2 * s + (v.val : ℤ)) (e.val : ℤ) := by
    rw [hx, hy, show 2 * k + (e.val : ℤ) = (e.val : ℤ) + 2 * k by omega]
    exact incomingDeficit_add_periods m _ _ k q
  have hCases := incomingDeficit_cell_cases m r s e v hr0 hrm hs0 hsm hMissing
  rw [← hMove] at hCases
  rcases hCases with ⟨hr, hs, he, hv, hFour⟩ | hZero | hOne
  · subst r s e v
    left
    refine ⟨?_, hFour⟩
    refine ⟨-q, m.val * q - k - 1, ?_, ?_⟩
    · rw [hx]
      norm_num
      unfold halfPeriod
      ring
    · rw [hy]
      norm_num
      ring
  · exact Or.inr (Or.inl hZero)
  · exact Or.inr (Or.inr hOne)

/-- Every signed index of the prescribed coset has deficit exactly four. -/
theorem incomingDeficit_prescribed (m : Parameter) (a b : ℤ) :
    incomingDeficit m
      (-2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b)
      (-1 - 2 * m.val * a - 2 * b) = 4 := by
  have hm := m.property
  have hMove := incomingDeficit_add_periods m 0 1 (-1 - m.val * a - b) (-a)
  have hBase := incomingDeficit_10_row_zero m 0 (by omega) (by omega)
  norm_num at hMove hBase
  rw [hBase] at hMove
  unfold halfPeriod at hMove
  ring_nf at hMove ⊢
  exact hMove

/-- Deficit four characterizes precisely the source's prescribed coset. -/
theorem incomingDeficit_eq_four_iff (m : Parameter) (x y : ℤ) :
    incomingDeficit m x y = 4 ↔ ∃ a b : ℤ,
      x = -2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b ∧
      y = -1 - 2 * m.val * a - 2 * b := by
  constructor
  · intro hFour
    rcases incomingDeficit_cases m x y with ⟨hCoset, _⟩ | hZero | hOne
    · exact hCoset
    · omega
    · omega
  · rintro ⟨a, b, rfl, rfl⟩
    exact incomingDeficit_prescribed m a b

/-- Outside the explicit prescribed coset the deficit is exactly zero or one. -/
theorem incomingDeficit_zero_or_one (m : Parameter) (x y : ℤ)
    (hOutside : ¬∃ a b : ℤ,
      x = -2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b ∧
      y = -1 - 2 * m.val * a - 2 * b) :
    incomingDeficit m x y = 0 ∨ incomingDeficit m x y = 1 := by
  rcases incomingDeficit_cases m x y with ⟨hCoset, _⟩ | hZero | hOne
  · exact False.elim (hOutside hCoset)
  · exact Or.inl hZero
  · exact Or.inr hOne

/-- The physical deficit is nonnegative on the entire lattice. -/
theorem incomingDeficit_nonneg (m : Parameter) (x y : ℤ) :
    0 ≤ incomingDeficit m x y := by
  rcases incomingDeficit_cases m x y with ⟨_, hFour⟩ | hZero | hOne <;> omega

/-- The literal global even-plus profile satisfies the native superharmonic
inequality at every point, including the prescribed class. -/
theorem profile_incoming_sum_le (m : Parameter) (x y : ℤ) :
    (if (x + y) % 2 = 0 then profile m (x - 1) y + profile m (x + 1) y
      else profile m x (y - 1) + profile m x (y + 1)) ≤ 2 * profile m x y := by
  have h := incomingDeficit_nonneg m x y
  unfold incomingDeficit at h
  split_ifs at h ⊢ <;> omega

end FLattice.Auxiliary.PlusEvenProfile
