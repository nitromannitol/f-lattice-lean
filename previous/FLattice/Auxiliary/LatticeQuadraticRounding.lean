import FLattice.Auxiliary.PositiveQuadratic
import FLattice.Auxiliary.QuadraticSublevels
import Mathlib.Algebra.Order.Floor.Ring

/-!
# A uniform bound for rounding a real quadratic minimizer

After completing the square, a positive quadratic has its real minimum at
an arbitrary real center. Rounding each coordinate down changes its value
by a constant depending only on the matrix. No rationality, periodicity or
integer-valuedness of the objective is required.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.LatticeQuadraticRounding

/-- Half of the actual two-dimensional matrix quadratic form. -/
noncomputable def quadratic (A : Matrix (Fin 2) (Fin 2) ℝ) (x y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (x * A 0 0 * x + x * A 0 1 * y + y * A 1 0 * x + y * A 1 1 * y)

/-- A matrix-dependent bound for the error caused by coordinatewise rounding. -/
noncomputable def entryBound (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (1 / 2 : ℝ) * (|A 0 0| + |A 0 1| + |A 1 0| + |A 1 1|)

private theorem term_bound (a x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |x * a * y| ≤ |a| := by
  have hProduct : |x| * |y| ≤ 1 := by
    calc
      |x| * |y| ≤ 1 * 1 := mul_le_mul hx hy (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  calc
    |x * a * y| = |a| * (|x| * |y|) := by simp only [abs_mul]; ring
    _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left hProduct (abs_nonneg _)
    _ = |a| := mul_one _

/-- Every point in the closed unit coordinate box has bounded quadratic value. -/
theorem abs_quadratic_le_entryBound
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |quadratic A x y| ≤ entryBound A := by
  have h00 := term_bound (A 0 0) x x hx hx
  have h01 := term_bound (A 0 1) x y hx hy
  have h10 := term_bound (A 1 0) y x hy hx
  have h11 := term_bound (A 1 1) y y hy hy
  have hSum : |x * A 0 0 * x + x * A 0 1 * y + y * A 1 0 * x + y * A 1 1 * y| ≤
      |A 0 0| + |A 0 1| + |A 1 0| + |A 1 1| := by
    calc
      _ ≤ |x * A 0 0 * x + x * A 0 1 * y + y * A 1 0 * x| + |y * A 1 1 * y| :=
        abs_add_le _ _
      _ ≤ (|x * A 0 0 * x + x * A 0 1 * y| + |y * A 1 0 * x|) + |y * A 1 1 * y| :=
        add_le_add (abs_add_le _ _) (le_refl _)
      _ ≤ ((|x * A 0 0 * x| + |x * A 0 1 * y|) + |y * A 1 0 * x|) + |y * A 1 1 * y| :=
        add_le_add (add_le_add (abs_add_le _ _) (le_refl _)) (le_refl _)
      _ ≤ _ := add_le_add (add_le_add (add_le_add h00 h01) h10) h11
  unfold quadratic entryBound
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact mul_le_mul_of_nonneg_left hSum (by norm_num)

/-- The literal positive-semidefinite matrix condition gives a nonnegative quadratic. -/
theorem quadratic_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.PosSemidef) (x y : ℝ) :
    0 ≤ quadratic A x y := by
  have h := hA.dotProduct_mulVec_nonneg (![x, y] : Fin 2 → ℝ)
  rw [quadratic_two_expansion] at h
  exact mul_nonneg (by norm_num) h

/-- Coordinatewise floor gives a uniformly bounded quadratic error at every real center. -/
theorem rounded_quadratic_bound (A : Matrix (Fin 2) (Fin 2) ℝ) (x y : ℝ) :
    |quadratic A ((⌊x⌋ : ℝ) - x) ((⌊y⌋ : ℝ) - y)| ≤ entryBound A := by
  apply abs_quadratic_le_entryBound
  · have hLo := Int.floor_le x
    have hHi := Int.lt_floor_add_one x
    apply abs_le.mpr
    constructor <;> linarith
  · have hLo := Int.floor_le y
    have hHi := Int.lt_floor_add_one y
    apply abs_le.mpr
    constructor <;> linarith

/-- An attained lattice minimum of a completed square differs from its
real minimum by a bounded amount depending only on the actual Hessian. -/
theorem minimum_sub_base_bounds
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.PosDef)
    (F : ℤ × ℤ → ℝ) (T base x y : ℝ)
    (hSquare : ∀ p : ℤ × ℤ,
      F p = base + quadratic A ((p.1 : ℝ) - x) ((p.2 : ℝ) - y))
    (hMinimum : ∃ p : ℤ × ℤ, T = F p ∧ ∀ q : ℤ × ℤ, T ≤ F q) :
    0 ≤ T - base ∧ T - base ≤ entryBound A := by
  obtain ⟨p, hAt, hLower⟩ := hMinimum
  have hNonnegative := quadratic_nonneg A hA.posSemidef ((p.1 : ℝ) - x) ((p.2 : ℝ) - y)
  have hRounded := (abs_le.mp (rounded_quadratic_bound A x y)).2
  have hUpper := hLower (⌊x⌋, ⌊y⌋)
  rw [hSquare] at hAt hUpper
  constructor <;> linarith

end FLattice.Auxiliary.LatticeQuadraticRounding
