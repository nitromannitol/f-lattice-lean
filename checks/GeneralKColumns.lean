import FLatticePaper.GeneralK.ColumnLift
import FLatticePaper.GeneralK.Connectivity
import FLatticePaper.GeneralK.Trace
import FLatticePaper.GeneralK.Envelope
import FLatticePaper.GeneralK.GrowthClosed
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Sqrt

namespace FLatticePaper.GeneralK.Checks

private def sampleColumns : Field := fun site => 7 * site.2 + site.1

theorem three_retained_star_at_origin :
    laplacian 3 (liftColumns 3 sampleColumns) (0, 0) = 1 := by
  change laplacian 3 (liftColumns 3 sampleColumns) (columnSite 3 0 0 0) = 1
  rw [laplacian_liftColumns_columnSite (by decide : (2 : ℤ) ≤ 3)]
  decide

theorem three_chain_slope_drop_in_negative_column :
    laplacian 3 (liftColumns 3 sampleColumns) (-1, -1) = -1 := by
  change laplacian 3 (liftColumns 3 sampleColumns) (columnSite 3 (-1) (-1) 1) = -1
  rw [laplacian_liftColumns_openChain (by decide : (2 : ℤ) ≤ 3) _ _ _ _ (by decide) (by decide)]
  decide

theorem three_cross_phase_path : InputReaches 3 (-1, -1) (4, 0) :=
  inputReaches_all (by decide) _ _

theorem three_grid_harmonic_matrix_is_admitted :
    symmetricMatrix (-(2 / 3)) (1 / 3) (1 / 3) ∈ growthSet 3 := by
  have h := harmonicMatrix_mem_growthSet (by decide : (2 : ℤ) ≤ 3) 1 0
  norm_num [harmonicMatrix] at h
  exact h

theorem three_harmonic_retained_rows_are_superharmonic (column row : ℤ) :
    columnRow 3 (fun ij => harmonicField 3 1 0 (columnSite 3 ij.1 ij.2 0)) column row ≤ 0 := by
  have hk : (2 : ℤ) ≤ 3 := by decide
  exact columnRow_restriction_nonpos hk (fun site => (laplacian_harmonicField hk 1 0 site).le) column row

theorem three_no_growth_above_harmonic_grid (a : ℝ) (ha : -(2 / 3) < a) :
    symmetricMatrix a (1 / 3) (1 / 3) ∉ growthSet 3 := by
  intro h
  have htrace := trace_le_zero_of_mem_growthSet (by decide : (2 : ℤ) ≤ 3) h
  norm_num at htrace
  linarith

theorem three_harmonic_slice_iff (a : ℝ) :
    symmetricMatrix a (1 / 3) (1 / 3) ∈ growthSet 3 ↔ a ≤ -(2 / 3) := by
  constructor
  · intro h
    exact le_of_not_gt fun ha => three_no_growth_above_harmonic_grid a ha h
  · intro ha
    let decrement : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![-(2 / 3) - a, 0]
    have hpos : decrement.PosSemidef := Matrix.PosSemidef.diagonal (by
      intro i
      fin_cases i
      · exact sub_nonneg.mpr ha
      · exact le_rfl)
    have heq : symmetricMatrix (-(2 / 3)) (1 / 3) (1 / 3) - decrement = symmetricMatrix a (1 / 3) (1 / 3) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [symmetricMatrix, decrement]
    rw [← heq]
    exact sub_mem_growthSet_of_posSemidef (by decide) three_grid_harmonic_matrix_is_admitted hpos

/-- An irrational singular negative semidefinite matrix is admitted on every physical graph. -/
theorem irrational_rank_one_is_admitted {k : ℤ} (hk : 2 ≤ k) :
    symmetricMatrix (-2) (-Real.sqrt 2) (-1) ∈ growthSet k := by
  apply mem_growthSet_of_affine_lower_bound hk (field := 0) (fun _ => by simp [laplacian]) 0 0 0
  rintro ⟨x, y⟩
  simp only [zero_mul, add_zero, Pi.zero_apply, Int.cast_zero, matrixQuadratic_symmetricMatrix]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := sq_nonneg (Real.sqrt 2 * (x : ℝ) + (y : ℝ))
  have heq : (Real.sqrt 2 * (x : ℝ) + (y : ℝ)) ^ 2 =
      2 * (x : ℝ) ^ 2 + 2 * Real.sqrt 2 * (x : ℝ) * (y : ℝ) + (y : ℝ) ^ 2 := by
    linear_combination (x : ℝ) ^ 2 * hs
  nlinarith only [hn, heq]

#print axioms laplacian_two
#print axioms interpolate_first
#print axioms interpolate_last
#print axioms laplacian_liftColumns_columnSite
#print axioms laplacian_liftColumns_openChain
#print axioms superharmonic_liftColumns_iff
#print axioms three_retained_star_at_origin
#print axioms three_chain_slope_drop_in_negative_column
#print axioms symmetricMatrix_mem_growthSet_iff
#print axioms mem_growthSet_two_iff
#print axioms add_mem_growthSet
#print axioms phasePrimitive_secondDifference
#print axioms laplacian_harmonicField
#print axioms quadraticGrowth_harmonicField
#print axioms add_harmonicMatrix_mem_growthSet_iff
#print axioms three_grid_harmonic_matrix_is_admitted
#print axioms interpolate_le_of_concave
#print axioms interpolate_monotone_first
#print axioms interpolate_monotone_last
#print axioms liftColumns_restriction_le
#print axioms columnRow_restriction_nonpos
#print axioms three_harmonic_retained_rows_are_superharmonic
#print axioms trace_le_zero_of_mem_growthSet
#print axioms three_no_growth_above_harmonic_grid
#print axioms mem_growthSet_of_affine_lower_bound
#print axioms sub_mem_growthSet_of_posSemidef
#print axioms three_harmonic_slice_iff
#print axioms irrational_rank_one_is_admitted
#print axioms inputReaches_all
#print axioms InputReaches.exists_uniform_upper_bound
#print axioms three_cross_phase_path
#print axioms isClosed_growthSet
#print axioms isClosed_growthSet_two

end FLatticePaper.GeneralK.Checks
