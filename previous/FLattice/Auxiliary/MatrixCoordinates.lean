import FLattice.Auxiliary.PositiveQuadratic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Scalar coordinates for real symmetric two-by-two matrices

These elementary bounds express the positive matrix cones in terms of
the trace coordinate and the Euclidean length of the other two coordinates.
The proofs use a two-variable quadratic inequality, without spectral input.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MatrixCoordinates

/-- The trace and two traceless coordinates of a symmetric matrix. -/
noncomputable def matrix (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(c + a) / 2, b / 2; b / 2, (c - a) / 2]

/-- Euclidean length in the two traceless coordinates. -/
noncomputable def radius (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)

theorem matrix_isSymm (a b c : ℝ) : (matrix a b c).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem matrix_sub (a b c a' b' c' : ℝ) :
    matrix a b c - matrix a' b' c' = matrix (a - a') (b - b') (c - c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [matrix, Matrix.sub_apply] <;> ring

theorem matrix_neg (a b c : ℝ) : -matrix a b c = matrix (-a) (-b) (-c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [matrix, Matrix.neg_apply] <;> ring

theorem matrix_reconstruct (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsSymm) :
    matrix (M 0 0 - M 1 1) (2 * M 0 1) (M 0 0 + M 1 1) = M := by
  have hCross : M 0 1 = M 1 0 := (hM.apply 0 1).symm
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [matrix]
  exact hCross

theorem radius_nonneg (a b : ℝ) : 0 ≤ radius a b := Real.sqrt_nonneg _

theorem radius_sq (a b : ℝ) : radius a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem radius_smul (t a b : ℝ) : radius (t * a) (t * b) = |t| * radius a b := by
  apply (sq_eq_sq₀ (radius_nonneg _ _) (mul_nonneg (abs_nonneg _) (radius_nonneg _ _))).mp
  simp only [radius_sq, mul_pow, sq_abs]
  ring

/-- Two-dimensional Cauchy--Schwarz in the exact polynomial form needed below. -/
theorem traceless_form_lower_bound (a b x y : ℝ) :
    -radius a b * (x ^ 2 + y ^ 2) ≤ a * (x ^ 2 - y ^ 2) + 2 * b * x * y := by
  let u := x ^ 2 - y ^ 2
  let v := 2 * x * y
  let N := x ^ 2 + y ^ 2
  have hIdentity : u ^ 2 + v ^ 2 = N ^ 2 := by dsimp [u, v, N]; ring
  have hCS : (a * u + b * v) ^ 2 ≤ (a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) := by
    nlinarith only [sq_nonneg (a * v - b * u)]
  rw [hIdentity, ← radius_sq a b] at hCS
  have hCS' : (a * u + b * v) ^ 2 ≤ (radius a b * N) ^ 2 := by
    nlinarith only [hCS]
  have hRightNonneg : 0 ≤ radius a b * N :=
    mul_nonneg (radius_nonneg a b) (by dsimp [N]; positivity)
  have hLower : -(radius a b * N) ≤ a * u + b * v := by
    nlinarith only [hCS', hRightNonneg, sq_nonneg (a * u + b * v + radius a b * N)]
  dsimp [u, v, N] at hLower
  nlinarith only [hLower]

/-- The literal quadratic form is bounded below by its smaller scalar cone value. -/
theorem quadratic_form_lower_bound (a b c x y : ℝ) :
    ((c - radius a b) / 2) * (x ^ 2 + y ^ 2) ≤
      x * matrix a b c 0 0 * x + x * matrix a b c 0 1 * y +
        y * matrix a b c 1 0 * x + y * matrix a b c 1 1 * y := by
  have h := traceless_form_lower_bound a b x y
  norm_num [matrix]
  nlinarith only [h]

/-- Being above the scalar cone implies actual matrix positive semidefiniteness. -/
theorem posSemidef_of_radius_le (a b c : ℝ) (h : radius a b ≤ c) :
    (matrix a b c).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (matrix_isSymm a b c))
  intro v
  have hv : v = (![v 0, v 1] : Fin 2 → ℝ) := by ext i; fin_cases i <;> rfl
  rw [hv, quadratic_two_expansion]
  have hBound := quadratic_form_lower_bound a b c (v 0) (v 1)
  have hNonneg : 0 ≤ ((c - radius a b) / 2) * (v 0 ^ 2 + v 1 ^ 2) := by positivity
  exact hNonneg.trans hBound

/-- Strictly above the scalar cone implies actual matrix positive definiteness. -/
theorem posDef_of_radius_lt (a b c : ℝ) (h : radius a b < c) :
    (matrix a b c).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr (matrix_isSymm a b c))
  intro v hv
  have hNorm : 0 < v 0 ^ 2 + v 1 ^ 2 := by
    by_contra hn
    have hZero : v 0 = 0 ∧ v 1 = 0 := by
      constructor <;> nlinarith only [sq_nonneg (v 0), sq_nonneg (v 1), le_of_not_gt hn]
    apply hv
    ext i
    fin_cases i <;> simp [hZero.1, hZero.2]
  have hVector : v = (![v 0, v 1] : Fin 2 → ℝ) := by ext i; fin_cases i <;> rfl
  rw [hVector, quadratic_two_expansion]
  have hBound := quadratic_form_lower_bound a b c (v 0) (v 1)
  have hPositive : 0 < ((c - radius a b) / 2) * (v 0 ^ 2 + v 1 ^ 2) := by positivity
  exact hPositive.trans_le hBound

end FLattice.Auxiliary.MatrixCoordinates
