import Mathlib.Data.Int.Order.Basic
import Mathlib.Order.Monotone.Defs
import Lean.Elab.Tactic.Omega

/-!
# Integer ceiling averages

Arithmetic infrastructure for finite lower-bound deductions. These lemmas
refer only to integers and do not depend on a lattice or graph interface.
-/

namespace FLattice.Auxiliary

/-- The ceiling of half an integer, using Euclidean integer division. -/
def ceilHalf (t : ℤ) : ℤ := (t + 1) / 2

@[simp] theorem ceilHalf_zero : ceilHalf 0 = 0 := by
  rfl

theorem ceilHalf_le_iff {t c : ℤ} : ceilHalf t ≤ c ↔ t ≤ 2 * c := by
  unfold ceilHalf
  constructor <;> intro h <;> omega

theorem le_ceilHalf_iff {c t : ℤ} : c ≤ ceilHalf t ↔ 2 * c - 1 ≤ t := by
  unfold ceilHalf
  constructor <;> intro h <;> omega

theorem ceilHalf_eq_iff {t c : ℤ} :
    ceilHalf t = c ↔ 2 * c - 1 ≤ t ∧ t ≤ 2 * c := by
  unfold ceilHalf
  constructor
  · intro h
    constructor <;> omega
  · rintro ⟨hlo, hhi⟩
    omega

theorem ceilHalf_mono : Monotone ceilHalf := by
  intro a b hab
  unfold ceilHalf
  omega

/-- Adding an even integer to the input shifts its ceiling half exactly. -/
theorem ceilHalf_add_two_mul (t k : ℤ) :
    ceilHalf (t + 2 * k) = ceilHalf t + k := by
  unfold ceilHalf
  omega

/-- Shifting both averaged inputs by an integer shifts the average by it. -/
theorem ceilHalf_add_add (a b k : ℤ) :
    ceilHalf ((a + k) + (b + k)) = ceilHalf (a + b) + k := by
  unfold ceilHalf
  omega

theorem le_two_mul_ceilHalf (t : ℤ) : t ≤ 2 * ceilHalf t :=
  ceilHalf_le_iff.mp le_rfl

theorem two_mul_ceilHalf_le (t : ℤ) : 2 * ceilHalf t ≤ t + 1 := by
  have h := le_ceilHalf_iff.mp (le_refl (ceilHalf t))
  omega

@[simp] theorem ceilHalf_two_mul (k : ℤ) : ceilHalf (2 * k) = k := by
  unfold ceilHalf
  omega

@[simp] theorem ceilHalf_two_mul_sub_one (k : ℤ) :
    ceilHalf (2 * k - 1) = k := by
  unfold ceilHalf
  omega

theorem ceilHalf_add_le {a b c : ℤ} (h : a + b ≤ 2 * c) :
    ceilHalf (a + b) ≤ c :=
  ceilHalf_le_iff.mpr h

/-- Lower bounds on two inputs propagate through an integer average bound. -/
theorem ceilHalf_add_le_of_le {a b p q c : ℤ}
    (ha : a ≤ p) (hb : b ≤ q) (havg : p + q ≤ 2 * c) :
    ceilHalf (a + b) ≤ c := by
  apply ceilHalf_le_iff.mpr
  omega

/-- A predecessor sum of at least `2 * l - 1` forces ceiling level `l`. -/
theorem le_of_add_le_two_mul {a b c l : ℤ}
    (havg : a + b ≤ 2 * c) (hlevel : 2 * l - 1 ≤ a + b) : l ≤ c := by
  omega

/-- The residual level rule, with the reference hole supplied explicitly. -/
theorem residual_level_le {p q c u v w a b l η : ℤ}
    (havg : p + q ≤ 2 * c) (hhole : η = 2 * w - u - v)
    (ha : a ≤ p - u) (hb : b ≤ q - v)
    (hlevel : 2 * l + η - 1 ≤ a + b) : l ≤ c - w := by
  omega

/-- The same rule when the two residuals and their hole are already isolated. -/
theorem level_le_of_residual_bounds {p q c a b l η : ℤ}
    (havg : p + q ≤ 2 * c + η) (ha : a ≤ p) (hb : b ≤ q)
    (hlevel : 2 * l + η - 1 ≤ a + b) : l ≤ c := by
  omega

/-- At a zero-hole reference star, either positive predecessor gap forces one. -/
theorem one_le_of_residual_zero {p q c : ℤ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (havg : p + q ≤ 2 * c)
    (hmark : 1 ≤ p ∨ 1 ≤ q) : 1 ≤ c := by
  omega

/-- At a one-hole reference star, two positive predecessor gaps force one. -/
theorem one_le_of_residual_one {p q c : ℤ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (havg : p + q ≤ 2 * c + 1) : 1 ≤ c := by
  omega

end FLattice.Auxiliary
