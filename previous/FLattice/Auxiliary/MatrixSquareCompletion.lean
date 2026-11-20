import FLattice.Auxiliary.MatrixInverseOrder
import Mathlib.Tactic.Ring

/-!
# Exact square completion for the quadratic transport objective

All matrices and vectors are real and finite dimensional. The Hessian,
center and constant are computed with actual matrix inverses. The identities
require no integer minimization assumption and no asymptotic conclusion.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MatrixSquareCompletion

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One half of the literal matrix quadratic form. -/
noncomputable def quadratic (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (x ⬝ᵥ (A *ᵥ x))

/-- The actual index Hessian of the transport objective. -/
noncomputable def hessian (C N : Matrix n n ℝ) : Matrix n n ℝ :=
  C * (N + C⁻¹) * C

/-- The linear vector whose inverse-Hessian image is the real center. -/
noncomputable def gradient (C N B : Matrix n n ℝ) (ell w : n → ℝ) : n → ℝ :=
  (C * N * B) *ᵥ w - ell

/-- The exact real center of the quadratic in the index vector. -/
noncomputable def center (C N B : Matrix n n ℝ) (ell w : n → ℝ) : n → ℝ :=
  (hessian C N)⁻¹ *ᵥ gradient C N B ell w

omit [DecidableEq n] in
private theorem quadratic_sub (A : Matrix n n ℝ) (hA : A.IsSymm) (x y : n → ℝ) :
    quadratic A (x - y) = quadratic A x + quadratic A y - x ⬝ᵥ (A *ᵥ y) := by
  have hCross : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ y) := by
    simpa only [hA.eq] using dotProduct_transpose_mulVec A y x
  simp only [quadratic, mulVec_sub, sub_dotProduct, dotProduct_sub, hCross]
  ring

omit [DecidableEq n] in
private theorem quadratic_add_matrix (A B : Matrix n n ℝ) (x : n → ℝ) :
    quadratic (A + B) x = quadratic A x + quadratic B x := by
  simp only [quadratic, add_mulVec, dotProduct_add]
  ring

omit [DecidableEq n] in
private theorem quadratic_congruence (A B : Matrix n n ℝ) (x : n → ℝ) :
    quadratic A (B *ᵥ x) = quadratic (B.transpose * A * B) x := by
  unfold quadratic
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec]
  rw [dotProduct_comm]

/-- Congruence derives positivity of the actual index Hessian. -/
theorem hessian_posDef (C N : Matrix n n ℝ) (hC : C.IsSymm)
    (hUnit : IsUnit C) (hDomain : (N + C⁻¹).PosDef) : (hessian C N).PosDef := by
  have h := hDomain.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hUnit)
  simpa only [conjTranspose_eq_transpose_of_trivial, hC.eq, hessian] using h

/-- The index Hessian has the exact inverse obtained by the two inverse congruences. -/
theorem hessian_inv (C N : Matrix n n ℝ) (hUnit : IsUnit C)
    (hDomain : (N + C⁻¹).PosDef) :
    (hessian C N)⁻¹ = C⁻¹ * (N + C⁻¹)⁻¹ * C⁻¹ := by
  letI := hUnit.invertible
  letI := hDomain.isUnit.invertible
  apply Matrix.inv_eq_right_inv
  unfold hessian
  simp only [Matrix.mul_assoc, mul_inv_cancel_left_of_invertible,
    mul_inv_of_invertible]

private theorem input_isSymm (C N : Matrix n n ℝ) (hC : C.IsSymm)
    (hDomain : (N + C⁻¹).PosDef) : N.IsSymm := by
  have h := hDomain.isHermitian.sub (Matrix.isHermitian_iff_isSymm.mpr hC.inv)
  simpa only [add_sub_cancel_right, Matrix.isHermitian_iff_isSymm] using h

private theorem completed_quadratic (A : Matrix n n ℝ) (hA : A.PosDef)
    (p b : n → ℝ) :
    quadratic A p - b ⬝ᵥ p =
      quadratic A (p - A⁻¹ *ᵥ b) - quadratic A⁻¹ b := by
  letI := hA.isUnit.invertible
  have hAc : A *ᵥ (A⁻¹ *ᵥ b) = b := by
    rw [mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
  rw [quadratic_sub A (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian), hAc]
  have hAtCenter : quadratic A (A⁻¹ *ᵥ b) = quadratic A⁻¹ b := by
    simp only [quadratic, hAc]
    rw [dotProduct_comm]
  rw [hAtCenter, dotProduct_comm b p]
  ring

/-- The exact constant left after completing the index square. -/
noncomputable def base (C N B : Matrix n n ℝ) (ell w : n → ℝ) : ℝ :=
  quadratic N (B *ᵥ w) - quadratic (hessian C N)⁻¹ (gradient C N B ell w)

private theorem objective_eq_quadratic_linear
    (C N B : Matrix n n ℝ) (hC : C.IsSymm) (hUnit : IsUnit C)
    (hDomain : (N + C⁻¹).PosDef) (ell w p : n → ℝ) :
    quadratic N (B *ᵥ w - C *ᵥ p) + quadratic C p + ell ⬝ᵥ p =
      quadratic (hessian C N) p - gradient C N B ell w ⬝ᵥ p + quadratic N (B *ᵥ w) := by
  letI := hUnit.invertible
  have hN := input_isSymm C N hC hDomain
  have hH : hessian C N = C * N * C + C := by
    unfold hessian
    noncomm_ring [Matrix.inv_mul_of_invertible]
  have hQ : quadratic (hessian C N) p = quadratic N (C *ᵥ p) + quadratic C p := by
    have hCongr := quadratic_congruence N C p
    rw [hC.eq] at hCongr
    rw [hH, quadratic_add_matrix, ← hCongr]
  have hCross : (B *ᵥ w) ⬝ᵥ (N *ᵥ (C *ᵥ p)) =
      (C *ᵥ (N *ᵥ (B *ᵥ w))) ⬝ᵥ p := by
    rw [dotProduct_mulVec, dotProduct_mulVec,
      ← mulVec_transpose N, hN.eq, ← mulVec_transpose C, hC.eq]
  rw [quadratic_sub N hN, hCross, hQ]
  simp only [gradient, ← mulVec_mulVec, sub_dotProduct]
  ring

/-- Full square completion at the computed actual-inverse center. -/
theorem objective_eq_completed_square
    (C N B : Matrix n n ℝ) (hC : C.IsSymm) (hUnit : IsUnit C)
    (hDomain : (N + C⁻¹).PosDef) (ell w p : n → ℝ) :
    quadratic N (B *ᵥ w - C *ᵥ p) + quadratic C p + ell ⬝ᵥ p =
      quadratic (hessian C N) (p - center C N B ell w) + base C N B ell w := by
  rw [objective_eq_quadratic_linear C N B hC hUnit hDomain,
    completed_quadratic (hessian C N) (hessian_posDef C N hC hUnit hDomain)]
  unfold center base
  ring

omit [DecidableEq n] in
private theorem quadratic_sub_matrix (A B : Matrix n n ℝ) (x : n → ℝ) :
    quadratic (A - B) x = quadratic A x - quadratic B x := by
  simp only [quadratic, sub_mulVec, dotProduct_sub]
  ring

private theorem complement_inverse_identity (A R : Matrix n n ℝ) (hA : IsUnit A) :
    (A - R) - (A - R) * A⁻¹ * (A - R) = R - R * A⁻¹ * R := by
  letI := hA.invertible
  noncomm_ring [Matrix.mul_inv_of_invertible, Matrix.inv_mul_of_invertible,
    Matrix.inv_mul_cancel_left_of_invertible]

/-- The two displayed source formulas for the leading background agree. -/
theorem background_matrix_identity (N R : Matrix n n ℝ) (hDomain : (N + R).PosDef) :
    N - N * (N + R)⁻¹ * N = R - R * (N + R)⁻¹ * R := by
  simpa only [add_sub_cancel_right] using
    complement_inverse_identity (N + R) R hDomain.isUnit

private theorem hessian_inverse_sandwich (C N : Matrix n n ℝ) (hUnit : IsUnit C)
    (hDomain : (N + C⁻¹).PosDef) :
    C * (hessian C N)⁻¹ * C = (N + C⁻¹)⁻¹ := by
  letI := hUnit.invertible
  rw [hessian_inv C N hUnit hDomain]
  simp only [Matrix.mul_assoc, inv_mul_of_invertible, mul_inv_cancel_left_of_invertible,
    mul_one]

private theorem leading_matrix_identity (C N B : Matrix n n ℝ)
    (hC : C.IsSymm) (hUnit : IsUnit C) (hDomain : (N + C⁻¹).PosDef) :
    B.transpose * N * B - (C * N * B).transpose * (hessian C N)⁻¹ * (C * N * B) =
      MatrixInverseOrder.transportMatrix C⁻¹ B N := by
  have hN := input_isSymm C N hC hDomain
  calc
    _ = B.transpose * (N - N * (C * (hessian C N)⁻¹ * C) * N) * B := by
      rw [transpose_mul, transpose_mul, hC.eq, hN.eq]
      noncomm_ring
    _ = B.transpose * (N - N * (N + C⁻¹)⁻¹ * N) * B := by
      rw [hessian_inverse_sandwich C N hUnit hDomain]
    _ = _ := by
      rw [background_matrix_identity N C⁻¹ hDomain]
      rfl

/-- The exact base is the transported quadratic plus an explicit linear
term and a constant. No bound on the minimization error is assumed. -/
theorem base_eq_transport_quadratic_add_affine
    (C N B : Matrix n n ℝ) (hC : C.IsSymm) (hUnit : IsUnit C)
    (hDomain : (N + C⁻¹).PosDef) (ell w : n → ℝ) :
    base C N B ell w =
      quadratic (MatrixInverseOrder.transportMatrix C⁻¹ B N) w +
        ell ⬝ᵥ ((hessian C N)⁻¹ *ᵥ ((C * N * B) *ᵥ w)) -
        quadratic (hessian C N)⁻¹ ell := by
  have hH := hessian_posDef C N hC hUnit hDomain
  have hInvSymm := Matrix.isHermitian_iff_isSymm.mp hH.inv.isHermitian
  have hMain : quadratic N (B *ᵥ w) - quadratic (hessian C N)⁻¹ ((C * N * B) *ᵥ w) =
      quadratic (MatrixInverseOrder.transportMatrix C⁻¹ B N) w := by
    rw [quadratic_congruence N B, quadratic_congruence (hessian C N)⁻¹ (C * N * B),
      ← quadratic_sub_matrix, leading_matrix_identity C N B hC hUnit hDomain]
  have hCross : ((C * N * B) *ᵥ w) ⬝ᵥ ((hessian C N)⁻¹ *ᵥ ell) =
      ell ⬝ᵥ ((hessian C N)⁻¹ *ᵥ ((C * N * B) *ᵥ w)) := by
    simpa only [hInvSymm.eq] using
      dotProduct_transpose_mulVec (hessian C N)⁻¹ ((C * N * B) *ᵥ w) ell
  unfold base gradient
  rw [quadratic_sub (hessian C N)⁻¹ hInvSymm, hCross]
  linarith only [hMain]

end FLattice.Auxiliary.MatrixSquareCompletion
