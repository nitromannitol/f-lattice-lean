import FLattice.Auxiliary.PlusEvenCells
import FLattice.Auxiliary.PlusEvenPhysicalCells
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp

/-!
# The explicit quadratic background of the even-plus profile

The real polynomial is the manuscript's literal q_D, including its constant
and linear terms. Its affine increments cancel those of the global integer
profile. The residual therefore takes values in a finite representative
rectangle and is globally bounded. No asymptotic convention or unknown
comparison function is introduced here.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- The explicit real polynomial q_D from the comparison-profile source. -/
noncomputable def quadraticBackground (m : Parameter) (x y : ℤ) : ℝ :=
  -(((x : ℝ) - (m.val : ℝ) * (y : ℝ)) ^ 2 - (m.val : ℝ) ^ 2) /
      (4 * (halfPeriod m : ℝ)) -
    ((y : ℝ) + 1) ^ 2 / 4 + 1

/-- The quadratic background has the full signed affine period formula. -/
theorem quadraticBackground_at_lift (m : Parameter) (x y k q : ℤ) :
    quadraticBackground m (x + 2 * m.val * k + 2 * halfPeriod m * q) (2 * k + y) =
      quadraticBackground m x y - (q : ℝ) * (x : ℝ) +
        (q : ℝ) * (m.val : ℝ) * (y : ℝ) - (halfPeriod m : ℝ) * (q : ℝ) ^ 2 -
        (k : ℝ) * (y : ℝ) - (k : ℝ) ^ 2 - (k : ℝ) := by
  have hJ : (halfPeriod m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (halfPeriod_pos m)
  unfold quadraticBackground
  push_cast
  field_simp
  ring

/-- The profile-minus-quadratic residual is unchanged by every signed cell lift. -/
theorem profile_sub_quadraticBackground_lifted_cell (m : Parameter) (c : Cell m)
    (k q : ℤ) :
    (profile m (c.x + 2 * m.val * k + 2 * halfPeriod m * q) (2 * k + c.y) : ℝ) -
        quadraticBackground m (c.x + 2 * m.val * k + 2 * halfPeriod m * q)
          (2 * k + c.y) =
      (profile m c.x c.y : ℝ) - quadraticBackground m c.x c.y := by
  have hProfile := profile_at_lifted_cell m c.r c.s k q c.e c.v
    c.hr0 c.hrm c.hs0 c.hsm c.hMissing
  have hBase := profile_at_cell m c.r c.s c.e c.v
    c.hr0 c.hrm c.hs0 c.hsm c.hMissing
  change profile m (c.x + 2 * m.val * k + 2 * halfPeriod m * q) (2 * k + c.y) =
    representativeHeight c.e c.v c.r c.s - q * c.x + q * m.val * c.y -
      halfPeriod m * q ^ 2 - k * c.y - k ^ 2 - k at hProfile
  change profile m c.x c.y = representativeHeight c.e c.v c.r c.s at hBase
  rw [hProfile, hBase, quadraticBackground_at_lift]
  push_cast
  ring

/-- Every residual equals its value at the literal canonical representative. -/
theorem profile_sub_quadraticBackground_eq_cell (m : Parameter) (x y : ℤ) :
    (profile m x y : ℝ) - quadraticBackground m x y =
      (profile m (cellOf m x y).x (cellOf m x y).y : ℝ) -
        quadraticBackground m (cellOf m x y).x (cellOf m x y).y := by
  obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
  have h := profile_sub_quadraticBackground_lifted_cell m (cellOf m x y) k q
  rw [← hx, ← hy] at h
  exact h

/-- A nonnegative real constant bounds the residual on the whole integer plane. -/
theorem exists_bound_profile_sub_quadraticBackground (m : Parameter) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : ℤ,
      |(profile m x y : ℝ) - quadraticBackground m x y| ≤ B := by
  classical
  let rectangle : Finset (ℤ × ℤ) :=
    (Finset.Ico 0 (2 * halfPeriod m)).product (Finset.Icc 0 1)
  let error : ℤ × ℤ → ℝ := fun z =>
    |(profile m z.1 z.2 : ℝ) - quadraticBackground m z.1 z.2|
  refine ⟨rectangle.sum error, Finset.sum_nonneg (fun z _ => abs_nonneg _), ?_⟩
  intro x y
  rw [profile_sub_quadraticBackground_eq_cell]
  let c := cellOf m x y
  have hx := cell_coordinate_bounds m c.r c.s c.v c.hr0 c.hrm c.hs0 c.hsm c.hMissing
  have hy : 0 ≤ c.y ∧ c.y ≤ 1 := by
    have he := c.e.isLt
    unfold Cell.y
    omega
  have hmem : (c.x, c.y) ∈ rectangle := by
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Ico.mpr hx, Finset.mem_Icc.mpr hy⟩
  change error (c.x, c.y) ≤ rectangle.sum error
  exact Finset.single_le_sum (fun z _ => abs_nonneg _) hmem

end FLattice.Auxiliary.PlusEvenProfile
