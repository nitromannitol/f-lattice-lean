import FLattice.Auxiliary.MatrixInverseOrder
import FLattice.Auxiliary.PositiveQuadratic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Continuity and the open domain of the transport matrix formula

The formula uses the actual matrix inverse. Its continuity requires only
invertibility of M+R. On the two-dimensional positive-definite domain,
both signs of a sufficiently small scalar perturbation remain admissible.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.TransportMatrixContinuity

/-- Continuity of the actual transport matrix formula at every admissible inverse. -/
theorem continuousAt_transportMatrix
    {n : Type*} [Fintype n] [DecidableEq n]
    (R B M : Matrix n n ℝ) (hUnit : IsUnit (M + R)) :
    ContinuousAt (MatrixInverseOrder.transportMatrix R B) M := by
  have hDet : (M + R).det ≠ 0 := ((M + R).isUnit_iff_isUnit_det.mp hUnit).ne_zero
  have hInv : ContinuousAt (Inv.inv : Matrix n n ℝ → Matrix n n ℝ) (M + R) :=
    continuousAt_matrix_inv (M + R) (by
      simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hDet))
  have hAdd : ContinuousAt (fun N : Matrix n n ℝ => N + R) M :=
    continuousAt_id.add continuousAt_const
  have hInner : ContinuousAt (fun N : Matrix n n ℝ => (N + R)⁻¹) M :=
    ContinuousAt.comp (f := fun N : Matrix n n ℝ => N + R) hInv hAdd
  exact continuousAt_const.mul
    (continuousAt_const.sub ((continuousAt_const.mul hInner).mul continuousAt_const)) |>.mul
      continuousAt_const

/-- Both signs of a sufficiently small scalar perturbation preserve
literal positive definiteness of a real two-by-two matrix. -/
theorem exists_pos_scalar_radius
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.PosDef) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, |t| < η → (A + t • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := by
  obtain ⟨c, hc, hQuadratic⟩ := exists_pos_quadratic_lower_bound A hA
  refine ⟨c / 2, by positivity, ?_⟩
  intro t ht
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (hA.isHermitian.add (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])))
  intro v hv
  have hNorm : 0 < v 0 ^ 2 + v 1 ^ 2 := by
    by_contra hNonpositive
    have hZero : v 0 = 0 ∧ v 1 = 0 := by
      constructor <;> nlinarith only [sq_nonneg (v 0), sq_nonneg (v 1), le_of_not_gt hNonpositive]
    apply hv
    ext i
    fin_cases i <;> simp [hZero.1, hZero.2]
  have hct : 0 < c + t := by
    have hLower := (abs_lt.mp ht).1
    linarith
  have hBound := hQuadratic (v 0) (v 1)
  have hVector : v = (![v 0, v 1] : Fin 2 → ℝ) := by ext i; fin_cases i <;> rfl
  rw [hVector, quadratic_two_expansion]
  norm_num [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  nlinarith only [hBound, mul_pos hct hNorm]

/-- A small scalar perturbation stays admissible and changes every entry
of the actual transformed matrix by an arbitrarily small amount. -/
theorem exists_scalar_radius_for_entry_bounds
    (R B M : Matrix (Fin 2) (Fin 2) ℝ) (hDomain : (M + R).PosDef)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, |t| < η →
      (M + t • (1 : Matrix (Fin 2) (Fin 2) ℝ) + R).PosDef ∧
      ∀ i j : Fin 2,
        |MatrixInverseOrder.transportMatrix R B (M + t • 1) i j -
          MatrixInverseOrder.transportMatrix R B M i j| ≤ δ := by
  have hPath : ContinuousAt
      (fun t : ℝ => M + t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  have hAt : ContinuousAt (MatrixInverseOrder.transportMatrix R B)
      (M + (0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
    simpa only [zero_smul, add_zero] using
      continuousAt_transportMatrix R B M hDomain.isUnit
  have hComposition : ContinuousAt
      (fun t : ℝ => MatrixInverseOrder.transportMatrix R B (M + t • 1)) 0 :=
    ContinuousAt.comp (g := MatrixInverseOrder.transportMatrix R B)
      (f := fun t : ℝ => M + t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) hAt hPath
  have hEntryContinuous : ∀ i j : Fin 2, ContinuousAt
      (fun t : ℝ => MatrixInverseOrder.transportMatrix R B (M + t • 1) i j) 0 := by
    intro i j
    exact (continuous_apply_apply i j).continuousAt.comp hComposition
  have hEntryRadii : ∀ i j : Fin 2, ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, |t| < η →
      |MatrixInverseOrder.transportMatrix R B (M + t • 1) i j -
        MatrixInverseOrder.transportMatrix R B M i j| < δ := by
    intro i j
    obtain ⟨η, hη, hClose⟩ := Metric.continuousAt_iff.mp (hEntryContinuous i j) δ hδ
    refine ⟨η, hη, ?_⟩
    intro t ht
    simpa only [Real.dist_eq, sub_zero, zero_smul, add_zero] using
      hClose (by simpa only [Real.dist_eq, sub_zero] using ht)
  choose ρ hρ hClose using hEntryRadii
  let η₁ := min (min (ρ 0 0) (ρ 0 1)) (min (ρ 1 0) (ρ 1 1))
  have hη₁ : 0 < η₁ := lt_min (lt_min (hρ 0 0) (hρ 0 1)) (lt_min (hρ 1 0) (hρ 1 1))
  have hRadius : ∀ i j : Fin 2, η₁ ≤ ρ i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨η₂, hη₂, hPos⟩ := exists_pos_scalar_radius (M + R) hDomain
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
  intro t ht
  constructor
  · have h := hPos t (lt_of_lt_of_le ht (min_le_right _ _))
    convert h using 1; abel
  · intro i j
    exact le_of_lt (hClose i j t (lt_of_lt_of_le ht
      (le_trans (min_le_left _ _) (hRadius i j))))

end FLattice.Auxiliary.TransportMatrixContinuity
