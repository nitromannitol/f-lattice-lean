import FLattice.Auxiliary.MinusCoordinates
import FLattice.Auxiliary.PlusEvenMatrix
import FLattice.Auxiliary.QuadraticGap

/-!
# Quadratic backgrounds and finite translated gaps for the minus profiles

The literal background has the same affine periods as the chosen minus
profile. Their residual is bounded by reducing to the exact finite Cell
rectangle. Strict domination uses the actual shared period matrix inverse,
and the growth premise always concerns the original unknown function.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile

/-- The minus background with its exact parity-dependent affine normalization. -/
noncomputable def quadraticBackground (m : Parameter) (ε : Fin 2) (x y : ℤ) : ℝ :=
  -((x : ℝ) - (m.val : ℝ) * (y : ℝ)) ^ 2 / (4 * (halfPeriod m : ℝ)) -
    (y : ℝ) ^ 2 / 4 +
    (periodConstant m ε : ℝ) * ((x : ℝ) - (m.val : ℝ) * (y : ℝ)) /
      (2 * (halfPeriod m : ℝ)) - (ε.val : ℝ) * (y : ℝ) / 2

/-- Every signed lift has the same affine correction as the actual profile. -/
theorem quadraticBackground_at_lift (m : Parameter) (ε : Fin 2) (x y t q : ℤ) :
    quadraticBackground m ε (x + 2 * m.val * t + 2 * halfPeriod m * q) (2 * t + y) =
      quadraticBackground m ε x y - (q : ℝ) * (x : ℝ) +
        (q : ℝ) * (m.val : ℝ) * (y : ℝ) - (halfPeriod m : ℝ) * (q : ℝ) ^ 2 +
        (periodConstant m ε : ℝ) * (q : ℝ) - (t : ℝ) * (y : ℝ) -
        (t : ℝ) ^ 2 - (ε.val : ℝ) * (t : ℝ) := by
  have hJ : (halfPeriod m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (halfPeriod_pos m)
  unfold quadraticBackground
  push_cast
  field_simp
  ring

/-- An arbitrary signed shift leaves quadratic matrix minus C inverse;
all affine coefficients, including the constant, are explicit. -/
theorem quadraticBackground_shift_eq_inverse (m : Parameter) (ε : Fin 2) (x y a b : ℤ) :
    quadraticBackground m ε (x + a) (y + b) = -(1 / 2 : ℝ) *
      ((x : ℝ) * ((periodMatrix m)⁻¹ 0 0) * (x : ℝ) +
        (x : ℝ) * ((periodMatrix m)⁻¹ 0 1) * (y : ℝ) +
        (y : ℝ) * ((periodMatrix m)⁻¹ 1 0) * (x : ℝ) +
        (y : ℝ) * ((periodMatrix m)⁻¹ 1 1) * (y : ℝ)) +
      (((periodConstant m ε : ℝ) - (a : ℝ) + (m.val : ℝ) * (b : ℝ)) /
        (2 * (halfPeriod m : ℝ))) * (x : ℝ) +
      (-(m.val : ℝ) * ((periodConstant m ε : ℝ) - (a : ℝ) +
          (m.val : ℝ) * (b : ℝ)) / (2 * (halfPeriod m : ℝ)) -
        ((b : ℝ) + (ε.val : ℝ)) / 2) * (y : ℝ) + quadraticBackground m ε a b := by
  have hJ : (halfPeriod m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (halfPeriod_pos m)
  rw [periodMatrix_inv]
  norm_num [quadraticBackground]
  field_simp
  unfold halfPeriod
  push_cast
  ring

/-- At zero shift the source background has quadratic matrix minus C inverse. -/
theorem quadraticBackground_eq_inverse (m : Parameter) (ε : Fin 2) (x y : ℤ) :
    quadraticBackground m ε x y = -(1 / 2 : ℝ) *
      ((x : ℝ) * ((periodMatrix m)⁻¹ 0 0) * (x : ℝ) +
        (x : ℝ) * ((periodMatrix m)⁻¹ 0 1) * (y : ℝ) +
        (y : ℝ) * ((periodMatrix m)⁻¹ 1 0) * (x : ℝ) +
        (y : ℝ) * ((periodMatrix m)⁻¹ 1 1) * (y : ℝ)) +
      ((periodConstant m ε : ℝ) / (2 * (halfPeriod m : ℝ))) * (x : ℝ) +
      (-(m.val : ℝ) * (periodConstant m ε : ℝ) / (2 * (halfPeriod m : ℝ)) -
        (ε.val : ℝ) / 2) * (y : ℝ) := by
  simpa [quadraticBackground] using quadraticBackground_shift_eq_inverse m ε x y 0 0

/-- Profile minus background is unchanged under every signed valid Cell lift. -/
theorem profile_sub_quadraticBackground_at_lift (m : Parameter) (ε : Fin 2) (c : Cell m)
    (t q : ℤ) :
    (profile m ε (c.x + 2 * m.val * t + 2 * halfPeriod m * q) (2 * t + c.y) : ℝ) -
        quadraticBackground m ε (c.x + 2 * m.val * t + 2 * halfPeriod m * q) (2 * t + c.y) =
      (profile m ε c.x c.y : ℝ) - quadraticBackground m ε c.x c.y := by
  rw [profile_at_lifted_cell, profile_at_cell, quadraticBackground_at_lift]
  push_cast
  ring

/-- Every signed physical residual equals its canonical representative residual. -/
theorem profile_sub_quadraticBackground_eq_cell (m : Parameter) (ε : Fin 2) (x y : ℤ) :
    (profile m ε x y : ℝ) - quadraticBackground m ε x y =
      (profile m ε (cellOf m x y).x (cellOf m x y).y : ℝ) -
        quadraticBackground m ε (cellOf m x y).x (cellOf m x y).y := by
  obtain ⟨t, q, hx, hy⟩ := exists_lifted_cell m x y
  have h := profile_sub_quadraticBackground_at_lift m ε (cellOf m x y) t q
  rw [← hx, ← hy] at h
  exact h

/-- A nonnegative constant bounds the residual on the whole integer plane. -/
theorem exists_bound_profile_sub_quadraticBackground (m : Parameter) (ε : Fin 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : ℤ,
      |(profile m ε x y : ℝ) - quadraticBackground m ε x y| ≤ B := by
  classical
  let rectangle : Finset (ℤ × ℤ) :=
    (Finset.Ico 0 (2 * halfPeriod m)).product (Finset.Icc 0 1)
  let error : ℤ × ℤ → ℝ := fun z =>
    |(profile m ε z.1 z.2 : ℝ) - quadraticBackground m ε z.1 z.2|
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

/-- Original uniform growth and the actual strict matrix gap make every
translated profile-gap sublevel finite, with arbitrary signed shifts. -/
theorem finite_shifted_gap_sublevels_of_quadratic_growth
    (m : Parameter) (ε : Fin 2) (a b : ℤ) (h : ℤ × ℤ → ℤ)
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef) :
    ∀ t : ℤ, {z : ℤ × ℤ | h z - profile m ε (z.1 + a) (z.2 + b) ≤ t}.Finite := by
  obtain ⟨B, _, hBound⟩ := exists_bound_profile_sub_quadraticBackground m ε
  intro t
  have hFinite := QuadraticGap.finite_sublevels
    (fun z : ℤ × ℤ => (h z : ℝ))
    (fun z : ℤ × ℤ => (profile m ε (z.1 + a) (z.2 + b) : ℝ))
    M ((periodMatrix m)⁻¹)
    (((periodConstant m ε : ℝ) - (a : ℝ) + (m.val : ℝ) * (b : ℝ)) /
      (2 * (halfPeriod m : ℝ)))
    (-(m.val : ℝ) * ((periodConstant m ε : ℝ) - (a : ℝ) +
        (m.val : ℝ) * (b : ℝ)) / (2 * (halfPeriod m : ℝ)) -
      ((b : ℝ) + (ε.val : ℝ)) / 2)
    (quadraticBackground m ε a b) B
    hGrowth (fun x y => by
      simpa only [quadraticBackground_shift_eq_inverse] using hBound (x + a) (y + b))
    hPositive (t : ℝ)
  apply hFinite.subset
  intro z hz
  change (h z : ℝ) - (profile m ε (z.1 + a) (z.2 + b) : ℝ) ≤ (t : ℝ)
  exact_mod_cast hz

end FLattice.Auxiliary.MinusProfile
