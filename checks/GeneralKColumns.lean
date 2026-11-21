import FLatticePaper.GeneralK.ColumnLift
import FLatticePaper.GeneralK.ColumnCycleAdmission
import FLatticePaper.GeneralK.ColumnCharge
import FLatticePaper.GeneralK.Connectivity
import FLatticePaper.GeneralK.Trace
import FLatticePaper.GeneralK.Envelope
import FLatticePaper.GeneralK.GrowthClosed
import FLatticePaper.GeneralK.Parabolic
import FLatticePaper.GeneralK.Obstacle
import FLatticePaper.GeneralK.PeriodicEnvelope
import FLatticePaper.GeneralK.ColumnWidth
import FLatticePaper.GeneralK.RationalReference
import FLatticePaper.GeneralK.ColumnCycleBound
import FLatticePaper.GeneralK.ColumnResidual
import FLatticePaper.GeneralK.ColumnUpperObstacle
import FLatticePaper.GeneralK.Classification
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

theorem irrational_rank_one_parabolic_bound {k : ℤ} (hk : 2 ≤ k) (endpoint : ℚ → ℚ → ℝ)
    (hslice : ∀ (u v : ℚ) (a : ℝ), symmetricMatrix a u v ∈ growthSet k ↔ a ≤ endpoint u v) :
    -2 ≤ sInf (parabolicValues endpoint (-Real.sqrt 2) (-1)) :=
  (mem_growthSet_iff_le_sInf_parabolicValues hk hslice _ _ _).mp (irrational_rank_one_is_admitted hk)

private def zeroSlice : ColumnSlice := ⟨3, by decide, 0, 0⟩

theorem three_zero_slice_has_one_row_phase : zeroSlice.length = 1 := by
  apply le_antisymm _ zeroSlice.length_pos
  exact columnLength_min 3 0 0 Nat.one_pos ⟨0, by norm_num⟩ ⟨0, by norm_num⟩

theorem three_zero_slice_reference_origin : zeroSlice.reference 0 (0, 0) = 0 := by
  norm_num [ColumnSlice.reference, ColumnSlice.referencePolynomial]

theorem three_zero_slice_cyclePeak_has_witness : ∃ (sector : zeroSlice.Sector)
    (cycle : zeroSlice.SimpleCycle sector.val),
    zeroSlice.cyclePeak = (zeroSlice.a₀ : ℚ) + zeroSlice.cycleMean sector.val cycle :=
  zeroSlice.cyclePeak_attained

theorem three_zero_slice_cyclePeak_is_admitted : symmetricMatrix (zeroSlice.cyclePeak : ℝ) 0 0 ∈ growthSet 3 := by
  simpa only [zeroSlice, Rat.cast_zero] using zeroSlice.cyclePeak_mem_growthSet

theorem three_harmonic_linearColumnRow (column row : ℤ) :
    linearColumnRow 3 (fun point => harmonicField 3 1 0 (columnSite 3 point.1 point.2 0)) column row = 0 := by
  have hcharge (site : Site) : 0 ≤ -laplacian 3 (harmonicField 3 1 0) site ∧
      -laplacian 3 (harmonicField 3 1 0) site ≤ 0 := by
    simp [laplacian_harmonicField (by decide : (2 : ℤ) ≤ 3)]
  have h := linearColumnRow_restriction_bounds (by decide) hcharge column row
  omega

theorem three_zero_ceiling_majorant : IsLeastMajorant 3 (ceilingObstacle 0 0 0 0 0) 0 := by
  have hzero (site : Site) : ceilingObstacle 0 0 0 0 0 site = 0 := by
    obtain ⟨x, y⟩ := site
    simp [ceilingObstacle, matrixQuadratic_symmetricMatrix]
  exact ⟨fun site => by simp [laplacian], fun site => by simp [hzero site], fun field _ h site => by
    simpa only [hzero site, Pi.zero_apply] using h site⟩

theorem three_zero_correction_has_a_width_certified_shape (column : ℤ) :
    ∃ shape : zeroSlice.Shape 0, ∀ row, ColumnSlice.shapeAt shape row = 0 := by
  have hperiod (i : ℤ) : Function.Periodic (fun row : ℤ => (0 : Field) (i, row))
      (zeroSlice.length : ℤ) := fun _ => rfl
  have hwidth := zeroSlice.abs_sub_zero_le_shapeBound 0 hperiod (field := 0)
    ⟨0, fun _ _ => by simp⟩ (fun _ _ => by
      simpa [linearColumnRow] using zeroSlice.residualBound_nonneg 0) column
  simpa using zeroSlice.exists_shape_of_periodicColumn 0 (fun row => (0 : Field) (column, row))
    (hperiod column) hwidth

private def zeroSector : zeroSlice.Sector := ⟨0, zeroSlice.sectorCount_pos⟩

theorem three_repeated_zero_shape_path_weight_is_bounded :
    ∃ bound : ℚ, ∀ length : ℕ,
      ∑ i ∈ Finset.range length, (ColumnSlice.cycleWeightAt (zeroSlice.zeroCycle zeroSector.val) (i : ℤ) : ℚ) ≤
        length * (zeroSlice.cyclePeak - zeroSlice.a₀) + bound := by
  let cycle := zeroSlice.zeroCycle zeroSector.val
  let path (i : ℕ) := cycle.2.val (ColumnSlice.cycleIndex cycle (i : ℤ))
  obtain ⟨bound, hbound⟩ := zeroSlice.exists_pathWeight_bound zeroSector
  refine ⟨bound, fun length => ?_⟩
  have h := hbound length path (fun i _ => by
    simpa only [path, Int.natCast_add, Int.natCast_one, ColumnSlice.cycleIndex_add_one] using
      cycle.2.property.2.2 (ColumnSlice.cycleIndex cycle (i : ℤ)))
  simpa only [path, Int.natCast_add, Int.natCast_one, cycle, ColumnSlice.cycleWeightAt] using h

theorem three_zero_slice_cyclePeak_eq_zero : (zeroSlice.cyclePeak : ℝ) = 0 := by
  have htrace := trace_le_zero_of_mem_growthSet (by decide : (2 : ℤ) ≤ 3) three_zero_slice_cyclePeak_is_admitted
  norm_num at htrace
  apply le_antisymm (show (zeroSlice.cyclePeak : ℝ) ≤ 0 by exact_mod_cast htrace)
  have hstart := trace_le_zero_of_mem_growthSet (by decide : (2 : ℤ) ≤ 3)
    (startingColumnEntry_mem_growthSet (by decide : (2 : ℤ) ≤ 3) 0 0)
  norm_num at hstart
  have hstart' : (zeroSlice.a₀ : ℝ) ≤ 0 := by exact_mod_cast (show zeroSlice.a₀ ≤ 0 from hstart)
  apply zeroSlice.le_cyclePeak_of_transverse_representative (a := 0) (tiltX := 0) (tiltY := 0) (bound := 0)
    (height := 0) hstart' (fun _ => by simp [laplacian]) 0
  · norm_num [zeroSlice]
  · rintro ⟨x, y⟩
    norm_num [zeroSlice, matrixQuadratic_symmetricMatrix]

#print axioms ColumnSlice.le_cyclePeak_of_bounded_column_restriction
#print axioms ColumnSlice.le_cyclePeak_of_transverse_representative
#print axioms three_zero_slice_cyclePeak_eq_zero
#print axioms rationalSlice_iff_le_cycleEndpoint
#print axioms mem_growthSet_iff_le_cycleParabolic
#print axioms growthSet_eq_closure_cycleCones
#print axioms ColumnSlice.abs_linearColumnRow_sub_reference_le
#print axioms ColumnSlice.exists_pathWeight_bound
#print axioms three_repeated_zero_shape_path_weight_is_bounded
#print axioms three_zero_correction_has_a_width_certified_shape
#print axioms ColumnSlice.abs_sub_zero_le_shapeBound
#print axioms exists_rationalFloorReference
#print axioms exists_periodicEnvelope_of_mem_growthSet
#print axioms ceilEnvelope_input_periodic
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
#print axioms mem_growthSet_iff_le_sInf_parabolicValues
#print axioms growthSet_eq_closure_rationalConeUnion
#print axioms irrational_rank_one_parabolic_bound
#print axioms startingColumnEntry_mem_growthSet
#print axioms ColumnSlice.reference_add_phasePeriod
#print axioms ColumnSlice.reference_add_length
#print axioms ColumnSlice.columnRow_edgeColumns_add_phasePeriod
#print axioms ColumnSlice.cyclePeak_attained
#print axioms three_zero_slice_has_one_row_phase
#print axioms three_zero_slice_cyclePeak_has_witness
#print axioms periodicPrimitive_secondDifference
#print axioms ColumnSlice.columnRow_cycleRetained_nonpos
#print axioms ColumnSlice.cyclePeak_mem_growthSet
#print axioms closure_cycleCone_subset_growthSet
#print axioms three_zero_slice_cyclePeak_is_admitted
#print axioms exists_affine_lower_bound_of_mem_growthSet
#print axioms exists_roundedEnvelope
#print axioms ceilEnvelope_input_sum_le
#print axioms IsLeastMajorant.chargeBound
#print axioms IsLeastMajorant.add_period
#print axioms chain_sub_linearChainValue_bounds
#print axioms linearColumnRow_restriction_bounds
#print axioms three_harmonic_linearColumnRow
#print axioms three_zero_ceiling_majorant

end FLatticePaper.GeneralK.Checks
