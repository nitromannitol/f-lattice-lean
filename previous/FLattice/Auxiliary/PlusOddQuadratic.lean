import FLattice.Auxiliary.PlusOddCoordinates
import FLattice.Auxiliary.PlusEvenCells
import FLattice.Auxiliary.PlusEvenMatrix
import FLattice.Auxiliary.QuadraticGap

/-!
# Quadratic background and proper gaps for the odd-plus profile

The literal source polynomial has the same affine extension as the odd
profile, including the `(m - 1)q` correction. Their difference is bounded
on the full signed lattice. The inverse-matrix identity retains its exact
affine part, so strict matrix domination supplies finite gap sublevels.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- The source polynomial q_* with its full affine normalization. -/
noncomputable def quadraticBackground (m : Parameter) (x y : ℤ) : ℝ :=
  -((x : ℝ) + 1 - (m.val : ℝ) * (y : ℝ)) ^ 2 / (4 * (halfPeriod m : ℝ)) -
    (y : ℝ) ^ 2 / 4 +
    (m.val : ℝ) * ((x : ℝ) + 1 - (m.val : ℝ) * (y : ℝ)) /
      (2 * (halfPeriod m : ℝ)) + 1

/-- All signed period translations have the exact odd affine increment. -/
theorem quadraticBackground_at_lift (m : Parameter) (x y k q : ℤ) :
    quadraticBackground m (x + 2 * m.val * k + 2 * halfPeriod m * q) (2 * k + y) =
      quadraticBackground m x y - (q : ℝ) * (x : ℝ) +
        (q : ℝ) * (m.val : ℝ) * (y : ℝ) - (halfPeriod m : ℝ) * (q : ℝ) ^ 2 +
        ((m.val : ℝ) - 1) * (q : ℝ) - (k : ℝ) * (y : ℝ) - (k : ℝ) ^ 2 := by
  have hJ : (halfPeriod m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (halfPeriod_pos m)
  unfold quadraticBackground
  push_cast
  field_simp
  ring

/-- The profile-minus-polynomial residual is unchanged at every signed lift. -/
theorem profile_sub_quadraticBackground_lifted_cell (m : Parameter) (c : Cell m)
    (k q : ℤ) :
    (profile m (c.x + 2 * m.val * k + 2 * halfPeriod m * q) (2 * k + c.y) : ℝ) -
        quadraticBackground m (c.x + 2 * m.val * k + 2 * halfPeriod m * q)
          (2 * k + c.y) =
      (profile m c.x c.y : ℝ) - quadraticBackground m c.x c.y := by
  have hProfile := profile_at_lifted_cell m c.r c.s k q c.e c.v
    c.hr0 c.hrm c.hs0 c.hsm c.hMissing
  have hBase : profile m c.x c.y = representativeHeight m c.e c.v c.r c.s := by
    simpa only [Cell.x, Cell.y, mul_zero, add_zero, zero_add, zero_mul, sub_zero,
      zero_pow (by decide : 2 ≠ 0)]
      using profile_at_lifted_cell m c.r c.s 0 0 c.e c.v
        c.hr0 c.hrm c.hs0 c.hsm c.hMissing
  change profile m (c.x + 2 * m.val * k + 2 * halfPeriod m * q) (2 * k + c.y) =
    representativeHeight m c.e c.v c.r c.s - q * c.x + q * m.val * c.y -
      halfPeriod m * q ^ 2 + (m.val - 1) * q - k * c.y - k ^ 2 at hProfile
  rw [hProfile, hBase, quadraticBackground_at_lift]
  push_cast
  ring

/-- Every residual equals its value at the common canonical representative. -/
theorem profile_sub_quadraticBackground_eq_cell (m : Parameter) (x y : ℤ) :
    (profile m x y : ℝ) - quadraticBackground m x y =
      (profile m (cellOf m x y).x (cellOf m x y).y : ℝ) -
        quadraticBackground m (cellOf m x y).x (cellOf m x y).y := by
  obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
  have h := profile_sub_quadraticBackground_lifted_cell m (cellOf m x y) k q
  rw [← hx, ← hy] at h
  exact h

/-- A nonnegative constant bounds the residual on the entire integer plane. -/
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

/-- The quadratic part is minus the actual inverse matrix, with its affine
coefficients explicitly accounted for. -/
theorem quadraticBackground_eq_inverse (m : Parameter) (x y : ℤ) :
    quadraticBackground m x y = -(1 / 2 : ℝ) *
      ((x : ℝ) * ((periodMatrix m)⁻¹ 0 0) * (x : ℝ) +
        (x : ℝ) * ((periodMatrix m)⁻¹ 0 1) * (y : ℝ) +
        (y : ℝ) * ((periodMatrix m)⁻¹ 1 0) * (x : ℝ) +
        (y : ℝ) * ((periodMatrix m)⁻¹ 1 1) * (y : ℝ)) +
      (((m.val : ℝ) - 1) / (2 * (halfPeriod m : ℝ))) * (x : ℝ) +
      (-(m.val : ℝ) * ((m.val : ℝ) - 1) / (2 * (halfPeriod m : ℝ))) * (y : ℝ) +
      (1 + (2 * (m.val : ℝ) - 1) / (4 * (halfPeriod m : ℝ))) := by
  have hJ : (halfPeriod m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (halfPeriod_pos m)
  rw [periodMatrix_inv]
  norm_num [quadraticBackground]
  field_simp
  unfold halfPeriod
  push_cast
  ring

/-- The original uniform quadratic growth and actual matrix domination
make every odd-profile gap sublevel finite. -/
theorem finite_gap_sublevels_of_quadratic_growth
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          ε * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef) :
    ∀ b : ℤ, {z : ℤ × ℤ | h z - profile m z.1 z.2 ≤ b}.Finite := by
  obtain ⟨B, _, hBound⟩ := exists_bound_profile_sub_quadraticBackground m
  intro b
  have hFinite := QuadraticGap.finite_sublevels
    (fun z : ℤ × ℤ => (h z : ℝ))
    (fun z : ℤ × ℤ => (profile m z.1 z.2 : ℝ))
    M ((periodMatrix m)⁻¹)
    (((m.val : ℝ) - 1) / (2 * (halfPeriod m : ℝ)))
    (-(m.val : ℝ) * ((m.val : ℝ) - 1) / (2 * (halfPeriod m : ℝ)))
    (1 + (2 * (m.val : ℝ) - 1) / (4 * (halfPeriod m : ℝ))) B
    hGrowth (fun x y => by
      simpa only [quadraticBackground_eq_inverse] using hBound x y) hPositive (b : ℝ)
  apply hFinite.subset
  intro z hz
  change (h z : ℝ) - (profile m z.1 z.2 : ℝ) ≤ (b : ℝ)
  exact_mod_cast hz

end FLattice.Auxiliary.PlusOddProfile
