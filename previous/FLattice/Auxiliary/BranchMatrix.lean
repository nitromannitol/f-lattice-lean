import FLattice.Auxiliary.RankOneTransport
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

/-!
# Literal branch matrices in rational backward descent

The formulas are proved over real parameters, under the source's numerical
ranges. Thus integer parity and primitivity are not needed for this algebra.
No admissibility, recurrence, or termination conclusion is asserted here.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.BranchMatrix

open Matrix

/-- The source's positive denominator T(n,d). -/
def denominator (n d : ℝ) : ℝ := d ^ 2 + 2 * d * n - n ^ 2

/-- The exact rational rank-one reference matrix B(n,d). -/
noncomputable def rankOneMatrix (n d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  -((denominator n d)⁻¹ • vecMulVec ![n, -d] ![n, -d])

/-- The outer-product definition has exactly the source's four entries. -/
theorem rankOneMatrix_entries (n d : ℝ) :
    rankOneMatrix n d =
      !![-n ^ 2 / denominator n d, n * d / denominator n d;
         n * d / denominator n d, -d ^ 2 / denominator n d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneMatrix, vecMulVec, div_eq_mul_inv] <;> ring

/-- Every reference matrix is literally real symmetric. -/
theorem rankOneMatrix_isSymm (n d : ℝ) : (rankOneMatrix n d).IsSymm := by
  rw [rankOneMatrix_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The zero-slope reference is the first endpoint matrix. -/
theorem rankOneMatrix_zero_one : rankOneMatrix 0 1 = !![0, 0; 0, -1] := by
  rw [rankOneMatrix_entries]
  norm_num [denominator]

/-- The unit-slope reference is the second endpoint matrix. -/
theorem rankOneMatrix_one_one : rankOneMatrix 1 1 = !![-(1/2:ℝ), 1/2; 1/2, -(1/2)] := by
  rw [rankOneMatrix_entries]
  norm_num [denominator]

/-- Actual plus-branch index matrix. -/
def plusC (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![k ^ 2 + 2 * k - 2, k; k, 2]

/-- Actual minus-branch index matrix. -/
def minusC (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![k ^ 2 - 2 * k - 2, k - 2; k - 2, 2]

/-- Source plus physical map. -/
def plusG (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; -1, k]

/-- Source minus physical map. -/
def minusG (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, k]

/-- Literal inverse of the plus physical map. -/
def plusB (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-k, -1; -1, 0]

/-- Literal inverse of the minus physical map. -/
def minusB (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![k, -1; 1, 0]

private theorem posDef_two (a b : ℝ) (h : 0 < 2 * a - b ^ 2) :
    (!![a, b; b, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro x hx
    have hExpand : star x ⬝ᵥ (!![a, b; b, 2] *ᵥ x) =
        2 * (x 1 + b * x 0 / 2) ^ 2 + (2 * a - b ^ 2) * (x 0) ^ 2 / 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    rw [hExpand]
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        apply hx
        ext i
        fin_cases i <;> simp [h0, h1]
      have hSq := sq_pos_of_ne_zero h1
      simp only [h0, mul_zero, zero_div, add_zero, zero_pow (by decide : 2 ≠ 0)]
      linarith
    · have hSq := sq_pos_of_ne_zero h0
      have hProduct := mul_pos h hSq
      have hOther := sq_nonneg (x 1 + b * x 0 / 2)
      linarith

/-- The parent denominator is positive, including both endpoint ratios. -/
theorem denominator_pos (n d : ℝ) (hd : 0 < d) (hn : 0 ≤ n) (hnd : n ≤ d) :
    0 < denominator n d := by
  have hDiff := mul_nonneg hn (sub_nonneg.mpr hnd)
  have hDn := mul_nonneg (le_of_lt hd) hn
  have hDsq := sq_pos_of_pos hd
  unfold denominator
  nlinarith only [hDiff, hDn, hDsq]

/-- Positivity is derived for the literal plus matrix. -/
theorem plusC_posDef (k : ℝ) (hk : 2 ≤ k) : (plusC k).PosDef := by
  apply posDef_two
  nlinarith [sq_nonneg (k - 2)]

/-- Positivity is derived for the literal minus matrix. -/
theorem minusC_posDef (k : ℝ) (hk : 4 ≤ k) : (minusC k).PosDef := by
  apply posDef_two
  nlinarith [sq_nonneg (k - 4)]

/-- The displayed plus inverse is the actual matrix inverse. -/
theorem plusG_inv (k : ℝ) : (plusG k)⁻¹ = plusB k := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusG, plusB, Matrix.mul_apply, Fin.sum_univ_two]

/-- The displayed minus inverse is the actual matrix inverse. -/
theorem minusG_inv (k : ℝ) : (minusG k)⁻¹ = minusB k := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minusG, minusB, Matrix.mul_apply, Fin.sum_univ_two]

/-- The plus child-parent energy identity. -/
theorem plus_energy (k n e : ℝ) :
    (![e, -(k * e + n)] : Fin 2 → ℝ) ⬝ᵥ
        (plusC k *ᵥ ![e, -(k * e + n)]) =
      denominator e (k * e + n) - denominator n e := by
  simp [plusC, denominator, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The minus child-parent energy identity. -/
theorem minus_energy (k n e : ℝ) :
    (![e, -(k * e - n)] : Fin 2 → ℝ) ⬝ᵥ
        (minusC k *ᵥ ![e, -(k * e - n)]) =
      denominator e (k * e - n) - denominator n e := by
  simp [minusC, denominator, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The plus transformed row vector is exactly the parent vector. -/
theorem plus_vector (k n e : ℝ) :
    (plusB k).transpose *ᵥ ![e, -(k * e + n)] = ![n, -e] := by
  ext i
  fin_cases i <;> simp [plusB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The minus transformed row vector is exactly the parent vector. -/
theorem minus_vector (k n e : ℝ) :
    (minusB k).transpose *ᵥ ![e, -(k * e - n)] = ![n, -e] := by
  ext i
  fin_cases i <;> simp [minusB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Full plus branch identity, with its coercivity domain proved internally. -/
theorem plus_domain_and_map (k n e : ℝ) (hk : 2 ≤ k) (he : 0 < e)
    (hn : 0 ≤ n) (hne : n ≤ e) :
    (rankOneMatrix e (k * e + n) + (plusC k)⁻¹).PosDef ∧
      MatrixInverseOrder.transportMatrix (plusC k)⁻¹ (plusG k)⁻¹
        (rankOneMatrix e (k * e + n)) = rankOneMatrix n e := by
  have hParent := denominator_pos n e he hn hne
  have hChildBase : e ≤ k * e + n := by nlinarith
  have hChild := denominator_pos e (k * e + n) (lt_of_lt_of_le he hChildBase)
    (le_of_lt he) hChildBase
  have h := RankOneTransport.domain_and_transport (plusC k) (plusB k)
    (plusC_posDef k hk) ![e, -(k * e + n)]
    (denominator e (k * e + n)) (denominator n e) hChild hParent (plus_energy k n e)
  simpa only [plusG_inv, plus_vector, rankOneMatrix] using h

/-- Full minus branch identity, under exactly the interior parent range. -/
theorem minus_domain_and_map (k n e : ℝ) (hk : 4 ≤ k) (he : 0 < e)
    (hn : 0 < n) (hne : n < e) :
    (rankOneMatrix e (k * e - n) + (minusC k)⁻¹).PosDef ∧
      MatrixInverseOrder.transportMatrix (minusC k)⁻¹ (minusG k)⁻¹
        (rankOneMatrix e (k * e - n)) = rankOneMatrix n e := by
  have hParent := denominator_pos n e he (le_of_lt hn) (le_of_lt hne)
  have hChildBase : e ≤ k * e - n := by nlinarith
  have hChild := denominator_pos e (k * e - n) (lt_of_lt_of_le he hChildBase)
    (le_of_lt he) hChildBase
  have h := RankOneTransport.domain_and_transport (minusC k) (minusB k)
    (minusC_posDef k hk) ![e, -(k * e - n)]
    (denominator e (k * e - n)) (denominator n e) hChild hParent (minus_energy k n e)
  simpa only [minusG_inv, minus_vector, rankOneMatrix] using h

/-- The plus physical map has determinant minus one. -/
theorem plusG_det (k : ℝ) : (plusG k).det = -1 := by
  simp [plusG, Matrix.det_fin_two_of]

/-- The minus physical map has determinant one. -/
theorem minusG_det (k : ℝ) : (minusG k).det = 1 := by
  simp [minusG, Matrix.det_fin_two_of]

private theorem plus_inverse_isUnit (k : ℝ) : IsUnit (plusG k)⁻¹ := by
  rw [plusG_inv]
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simp [plusB, Matrix.det_fin_two_of]

private theorem minus_inverse_isUnit (k : ℝ) : IsUnit (minusG k)⁻¹ := by
  rw [minusG_inv]
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simp [minusB, Matrix.det_fin_two_of]

/-- A strict plus-child dominator has the required domain and maps strictly
above the parent. No admissibility conclusion is bundled into this algebra. -/
theorem plus_strict_dominator (k n e : ℝ) (hk : 2 ≤ k) (he : 0 < e)
    (hn : 0 ≤ n) (hne : n ≤ e) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hAbove : (M - rankOneMatrix e (k * e + n)).PosDef) :
    (M + (plusC k)⁻¹).PosDef ∧
      (MatrixInverseOrder.transportMatrix (plusC k)⁻¹ (plusG k)⁻¹ M -
        rankOneMatrix n e).PosDef := by
  obtain ⟨hDomain, hMap⟩ := plus_domain_and_map k n e hk he hn hne
  have hLarger : (M + (plusC k)⁻¹).PosDef := by
    convert hAbove.add hDomain using 1
    abel
  have hC := plusC_posDef k hk
  have hStrict := MatrixInverseOrder.transportMatrix_sub_posDef (plusC k)⁻¹
    (plusG k)⁻¹ M (rankOneMatrix e (k * e + n))
    (Matrix.isHermitian_iff_isSymm.mp hC.inv.isHermitian) hC.inv.isUnit
    (plus_inverse_isUnit k) hDomain hAbove
  rw [hMap] at hStrict
  exact ⟨hLarger, hStrict⟩

/-- The corresponding strict-domination implication for the minus branch. -/
theorem minus_strict_dominator (k n e : ℝ) (hk : 4 ≤ k) (he : 0 < e)
    (hn : 0 < n) (hne : n < e) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hAbove : (M - rankOneMatrix e (k * e - n)).PosDef) :
    (M + (minusC k)⁻¹).PosDef ∧
      (MatrixInverseOrder.transportMatrix (minusC k)⁻¹ (minusG k)⁻¹ M -
        rankOneMatrix n e).PosDef := by
  obtain ⟨hDomain, hMap⟩ := minus_domain_and_map k n e hk he hn hne
  have hLarger : (M + (minusC k)⁻¹).PosDef := by
    convert hAbove.add hDomain using 1
    abel
  have hC := minusC_posDef k hk
  have hStrict := MatrixInverseOrder.transportMatrix_sub_posDef (minusC k)⁻¹
    (minusG k)⁻¹ M (rankOneMatrix e (k * e - n))
    (Matrix.isHermitian_iff_isSymm.mp hC.inv.isHermitian) hC.inv.isUnit
    (minus_inverse_isUnit k) hDomain hAbove
  rw [hMap] at hStrict
  exact ⟨hLarger, hStrict⟩

end FLattice.Auxiliary.BranchMatrix
