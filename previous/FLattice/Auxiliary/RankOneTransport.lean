import FLattice.Auxiliary.MatrixInverseOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Rank-one reference matrices under the exact transport map

The positivity domain and transformed rank-one matrix are derived from
positive scalar denominators and one explicit quadratic energy identity.
No inverse formula or transformed identity is assumed.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.RankOneTransport

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem outer_sandwich (C : Matrix n n ℝ) (a : n → ℝ) :
    vecMulVec a a * C * vecMulVec a a =
      (a ⬝ᵥ (C *ᵥ a)) • vecMulVec a a := by
  rw [vecMulVec_mul, vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, vecMulVec_smul]

private theorem inverse_product (C : Matrix n n ℝ) (hC : IsUnit C)
    (P : Matrix n n ℝ) (tc tp : ℝ) (hc : tc ≠ 0) (hp : tp ≠ 0)
    (hEnergy : P * C * P = (tc - tp) • P) :
    (C⁻¹ - tc⁻¹ • P) * (C + tp⁻¹ • (C * P * C)) = 1 := by
  letI := hC.invertible
  have hPCPC : P * (C * P * C) = (tc - tp) • (P * C) := by
    calc
      _ = (P * C * P) * C := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hEnergy, Matrix.smul_mul]
  simp only [Matrix.mul_assoc] at hPCPC
  simp only [sub_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul,
    inv_mul_of_invertible, Matrix.mul_assoc, inv_mul_cancel_left_of_invertible,
    hPCPC, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- A positive rank-one denominator makes the actual inverse-domain
matrix positive definite; its inverse is computed explicitly. -/
theorem domain_posDef_and_inverse
    (C : Matrix n n ℝ) (hC : C.PosDef) (a : n → ℝ)
    (tc tp : ℝ) (hc : 0 < tc) (hp : 0 < tp)
    (hEnergy : a ⬝ᵥ (C *ᵥ a) = tc - tp) :
    (C⁻¹ - tc⁻¹ • vecMulVec a a).PosDef ∧
      (C⁻¹ - tc⁻¹ • vecMulVec a a)⁻¹ =
        C + tp⁻¹ • (C * vecMulVec a a * C) := by
  have hSym := Matrix.isHermitian_iff_isSymm.mp hC.isHermitian
  have hOuter : (vecMulVec a a).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star a
  have hSand : (C * vecMulVec a a * C).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hSym.eq] using
      hOuter.conjTranspose_mul_mul_same C
  have hQ := hC.add_posSemidef (hSand.smul (le_of_lt (inv_pos.mpr hp)))
  have hProduct := inverse_product C hC.isUnit (vecMulVec a a) tc tp
    (ne_of_gt hc) (ne_of_gt hp) (by rw [outer_sandwich, hEnergy])
  constructor
  · have hInv : (C + tp⁻¹ • (C * vecMulVec a a * C))⁻¹ =
        C⁻¹ - tc⁻¹ • vecMulVec a a := Matrix.inv_eq_left_inv hProduct
    rw [← hInv]
    exact hQ.inv
  · exact Matrix.inv_eq_right_inv hProduct

/-- Exact rank-one transport, including its derived positivity domain. -/
theorem domain_and_transport
    (C B : Matrix n n ℝ) (hC : C.PosDef) (a : n → ℝ)
    (tc tp : ℝ) (hc : 0 < tc) (hp : 0 < tp)
    (hEnergy : a ⬝ᵥ (C *ᵥ a) = tc - tp) :
    (-(tc⁻¹ • vecMulVec a a) + C⁻¹).PosDef ∧
      MatrixInverseOrder.transportMatrix C⁻¹ B (-(tc⁻¹ • vecMulVec a a)) =
        -(tp⁻¹ • vecMulVec (B.transpose *ᵥ a) (B.transpose *ᵥ a)) := by
  obtain ⟨hDomain, hInv⟩ := domain_posDef_and_inverse C hC a tc tp hc hp hEnergy
  have hArrange : -(tc⁻¹ • vecMulVec a a) + C⁻¹ =
      C⁻¹ - tc⁻¹ • vecMulVec a a := by abel
  refine ⟨hArrange ▸ hDomain, ?_⟩
  letI := hC.isUnit.invertible
  have hInner : C⁻¹ - C⁻¹ *
      (C⁻¹ - tc⁻¹ • vecMulVec a a)⁻¹ * C⁻¹ = -(tp⁻¹ • vecMulVec a a) := by
    rw [hInv]
    simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
      mul_inv_of_invertible,
      inv_mul_cancel_left_of_invertible, mul_one]
    abel
  unfold MatrixInverseOrder.transportMatrix
  rw [hArrange, hInner]
  simp only [mul_neg, neg_mul, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul,
    ← mulVec_transpose]

end FLattice.Auxiliary.RankOneTransport
