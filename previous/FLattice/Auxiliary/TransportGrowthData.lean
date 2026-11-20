import FLattice.Auxiliary.MinusTransportData
import FLattice.Auxiliary.MatrixSquareCompletion

/-!
# Literal real sampling and cost identities for the two integer transports

The formulas here hold for every integer m. Symmetry is unconditional;
invertibility of the shared period matrix is proved for m>=1. No growth,
minimization or superharmonicity assertion is assumed in these algebraic
identities, and no changing growth implementation is imported.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.TransportGrowthData

open Matrix

/-- The plus source matrix, in target-to-source coordinates. -/
noncomputable def plusMatrix (m : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-2 * (m : ℝ), -1; -1, 0]

/-- The minus source matrix, in target-to-source coordinates. -/
noncomputable def minusMatrix (m : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * (m : ℝ) + 2, -1; 1, 0]

/-- The plus cost's linear index term. -/
noncomputable def plusLinear (m : ℤ) : Fin 2 → ℝ := ![(m : ℝ), 0]

/-- The minus cost's linear index term. -/
noncomputable def minusLinear (m : ℤ) : Fin 2 → ℝ := ![-((m : ℝ) + 1), -1]

/-- The shared literal C is symmetric for every integer coefficient. -/
theorem periodMatrix_isSymm (m : ℤ) : (PlusTransport.periodMatrix m).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The shared determinant is the explicit polynomial 4J. -/
theorem periodMatrix_det (m : ℤ) :
    (PlusTransport.periodMatrix m).det = 4 * ((m : ℝ)^2 + 2 * (m : ℝ) - 1) := by
  rw [PlusTransport.periodMatrix, Matrix.det_fin_two_of]
  ring

/-- The actual shared matrix is a unit for every allowed coefficient, including m=1. -/
theorem periodMatrix_isUnit (m : ℤ) (hm : 1 ≤ m) : IsUnit (PlusTransport.periodMatrix m) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [periodMatrix_det]
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith [sq_nonneg (m : ℝ)]

/-- The actual integer plus sampling point has exactly the real affine form Bw-Cp. -/
theorem plus_samplePoint_real (m : ℤ) (w p : ℤ × ℤ) :
    (![((PlusTransport.samplePoint m w p).1 : ℝ),
       ((PlusTransport.samplePoint m w p).2 : ℝ)] : Fin 2 → ℝ) =
      plusMatrix m *ᵥ ![(w.1 : ℝ), (w.2 : ℝ)] -
        PlusTransport.periodMatrix m *ᵥ ![(p.1 : ℝ), (p.2 : ℝ)] := by
  ext i
  fin_cases i <;>
    norm_num [plusMatrix, PlusTransport.periodMatrix, PlusTransport.samplePoint,
      PlusTransport.backwardPoint, PlusTransport.squareCoefficient,
      TransportStarNormalization.samplePoint, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The actual integer minus sampling point has exactly the real affine form Bw-Cp. -/
theorem minus_samplePoint_real (m : ℤ) (w p : ℤ × ℤ) :
    (![((MinusTransport.samplePoint m w p).1 : ℝ),
       ((MinusTransport.samplePoint m w p).2 : ℝ)] : Fin 2 → ℝ) =
      minusMatrix m *ᵥ ![(w.1 : ℝ), (w.2 : ℝ)] -
        PlusTransport.periodMatrix m *ᵥ ![(p.1 : ℝ), (p.2 : ℝ)] := by
  ext i
  fin_cases i <;>
    norm_num [minusMatrix, PlusTransport.periodMatrix, MinusTransport.samplePoint,
      MinusTransport.backwardPoint, PlusTransport.squareCoefficient,
      TransportStarNormalization.samplePoint, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The actual integer plus cost is one half of the C quadratic form plus its linear term. -/
theorem plus_cost_real (m : ℤ) (p : ℤ × ℤ) :
    (PlusTransport.cost m p : ℝ) =
      MatrixSquareCompletion.quadratic (PlusTransport.periodMatrix m) ![(p.1 : ℝ), (p.2 : ℝ)] +
        plusLinear m ⬝ᵥ ![(p.1 : ℝ), (p.2 : ℝ)] := by
  rw [PlusTransport.cost_eq]
  norm_num [MatrixSquareCompletion.quadratic, PlusTransport.periodMatrix,
    plusLinear, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The actual integer minus cost has its exact negative linear phase. -/
theorem minus_cost_real (m : ℤ) (p : ℤ × ℤ) :
    (MinusTransport.cost m p : ℝ) =
      MatrixSquareCompletion.quadratic (PlusTransport.periodMatrix m) ![(p.1 : ℝ), (p.2 : ℝ)] +
        minusLinear m ⬝ᵥ ![(p.1 : ℝ), (p.2 : ℝ)] := by
  rw [MinusTransport.cost_eq]
  norm_num [MatrixSquareCompletion.quadratic, PlusTransport.periodMatrix,
    minusLinear, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

end FLattice.Auxiliary.TransportGrowthData
