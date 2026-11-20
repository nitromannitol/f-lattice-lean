import FLatticePaper.GeneralK.ColumnLift
import FLatticePaper.GeneralK.Trace

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

end FLatticePaper.GeneralK.Checks
