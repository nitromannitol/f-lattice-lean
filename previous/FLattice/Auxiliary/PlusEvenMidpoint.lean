import FLattice.Auxiliary.PlusEvenDeficitGlobal
import FLattice.Auxiliary.Ceiling

/-!
# Exact ceiling-midpoint identities for the even-plus profile

At every point outside the explicit prescribed coset the native deficit is
zero or one, so the center is exactly the ceiling of the incoming midpoint.
Odd first coordinates are proved to avoid that coset. These are identities
of the existing global profile, not a new construction or recurrence theorem.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- Outside the explicit prescribed coset, the profile equals its native
integer ceiling average. -/
theorem profile_eq_ceilHalf_incoming (m : Parameter) (x y : ℤ)
    (hOutside : ¬∃ a b : ℤ,
      x = -2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b ∧
      y = -1 - 2 * m.val * a - 2 * b) :
    profile m x y = ceilHalf
      (if (x + y) % 2 = 0 then profile m (x - 1) y + profile m (x + 1) y
        else profile m x (y - 1) + profile m x (y + 1)) := by
  have hDeficit := incomingDeficit_zero_or_one m x y hOutside
  unfold incomingDeficit at hDeficit
  symm
  apply ceilHalf_eq_iff.mpr
  split_ifs at hDeficit ⊢ <;> rcases hDeficit with hZero | hOne <;>
    constructor <;> omega

/-- The explicit prescribed coset has even first coordinate, so every odd
first coordinate lies outside it, irrespective of the second coordinate. -/
theorem odd_first_coordinate_outside_prescribed (m : Parameter) (i y : ℤ) :
    ¬∃ a b : ℤ,
      2 * i + 1 = -2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b ∧
      y = -1 - 2 * m.val * a - 2 * b := by
  rintro ⟨a, b, hx, _⟩
  ring_nf at hx
  omega

/-- The odd-odd phase is the ceiling horizontal midpoint of the adjacent
even-first-coordinate phase. -/
theorem profile_odd_odd_horizontal_midpoint (m : Parameter) (i j : ℤ) :
    profile m (2 * i + 1) (2 * j + 1) =
      ceilHalf (profile m (2 * i) (2 * j + 1) +
        profile m (2 * i + 2) (2 * j + 1)) := by
  have h := profile_eq_ceilHalf_incoming m (2 * i + 1) (2 * j + 1)
    (odd_first_coordinate_outside_prescribed m i (2 * j + 1))
  rw [if_pos (by omega : (2 * i + 1 + (2 * j + 1)) % 2 = 0),
    show 2 * i + 1 - 1 = 2 * i by omega,
    show 2 * i + 1 + 1 = 2 * i + 2 by omega] at h
  exact h

/-- The odd-even phase is the ceiling vertical midpoint of the adjacent
odd-odd phase, with no prescribed-coset assumption. -/
theorem profile_odd_even_vertical_midpoint (m : Parameter) (i j : ℤ) :
    profile m (2 * i + 1) (2 * j) =
      ceilHalf (profile m (2 * i + 1) (2 * j - 1) +
        profile m (2 * i + 1) (2 * j + 1)) := by
  have h := profile_eq_ceilHalf_incoming m (2 * i + 1) (2 * j)
    (odd_first_coordinate_outside_prescribed m i (2 * j))
  rw [if_neg (by omega : (2 * i + 1 + 2 * j) % 2 ≠ 0)] at h
  exact h

/-- The even-odd phase is the ceiling vertical midpoint outside the literal
prescribed coset; the coset condition is retained explicitly. -/
theorem profile_even_odd_vertical_midpoint (m : Parameter) (i j : ℤ)
    (hOutside : ¬∃ a b : ℤ,
      2 * i = -2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b ∧
      2 * j + 1 = -1 - 2 * m.val * a - 2 * b) :
    profile m (2 * i) (2 * j + 1) =
      ceilHalf (profile m (2 * i) (2 * j) + profile m (2 * i) (2 * j + 2)) := by
  have h := profile_eq_ceilHalf_incoming m (2 * i) (2 * j + 1) hOutside
  rw [if_neg (by omega : (2 * i + (2 * j + 1)) % 2 ≠ 0),
    show 2 * j + 1 - 1 = 2 * j by omega,
    show 2 * j + 1 + 1 = 2 * j + 2 by omega] at h
  exact h

end FLattice.Auxiliary.PlusEvenProfile
