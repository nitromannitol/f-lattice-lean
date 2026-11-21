import FLatticePaper.GeneralK.ColumnCycleRepeat
import FLatticePaper.GeneralK.ColumnGrowth
import FLatticePaper.GeneralK.PeriodicPrimitive

namespace FLatticePaper.GeneralK

private theorem columnRow_add_column {k : ℤ} (hk : k ≠ 0) (field : Field) (adjustment : ℤ → ℤ)
    (column row : ℤ) :
    columnRow k (fun site => field site + adjustment site.1) column row =
      columnRow k field column row + (adjustment (column - 1) + adjustment (column + 1) - 2 * adjustment column) := by
  simp only [columnRow]
  have hpos : (k - 1) * (field (column + 1, row) + adjustment (column + 1)) +
      (field (column + 1, row + 1) + adjustment (column + 1)) =
    ((k - 1) * field (column + 1, row) + field (column + 1, row + 1)) + k * adjustment (column + 1) := by ring
  have hneg : (k - 1) * (field (column - 1, row) + adjustment (column - 1)) +
      (field (column - 1, row - 1) + adjustment (column - 1)) =
    ((k - 1) * field (column - 1, row) + field (column - 1, row - 1)) + k * adjustment (column - 1) := by ring
  rw [hpos, hneg, ceilDiv_add_mul hk, ceilDiv_add_mul hk]
  ring

namespace ColumnSlice

private def cycleWeights {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector)
    (index : Fin cycle.1.val) : ℤ :=
  slice.edgeWeight sector (cycle.2.val index) (cycle.2.val (cyclicSucc index))

def cycleAdjustment {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) : ℤ → ℤ :=
  periodicPrimitive (cycleWeights cycle) (firstPhase cycle).val

theorem cycleAdjustment_secondDifference {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) (column : ℤ) :
    cycleAdjustment cycle (column - 1) + cycleAdjustment cycle (column + 1) - 2 * cycleAdjustment cycle column =
      cycleWeightAt cycle column := by
  rw [cycleAdjustment, periodicPrimitive_secondDifference (cycleWeights cycle) _ column
    (cycleIndex cycle column) (cast_cycleIndex cycle column)]
  rw [cycleWeightAt, cycleIndex_add_one]
  rfl

/-- The retained height of a repeated cycle, corrected by the integer
second-difference primitive of its edge weights. -/
def cycleRetained {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) : Field :=
  fun site => cycleColumns cycle site + cycleAdjustment cycle site.1

theorem columnRow_cycleRetained_nonpos {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector)
    (column row : ℤ) : columnRow slice.k (cycleRetained cycle) column row ≤ 0 := by
  unfold cycleRetained
  rw [columnRow_add_column (by have := slice.hk; omega), cycleAdjustment_secondDifference]
  have h := columnRow_cycleColumns_le cycle column row
  omega

private theorem reference_abs_error (slice : ColumnSlice) (sector column row : ℤ) :
    |(slice.reference sector (column, row) : ℝ) - (slice.referencePolynomial sector column row : ℝ)| ≤ 1 := by
  let q := slice.referencePolynomial sector column row
  have hlo : (⌊q⌋ : ℝ) ≤ (q : ℝ) := by exact_mod_cast Int.floor_le q
  have hhi : (q : ℝ) < (⌊q⌋ : ℝ) + 1 := by exact_mod_cast Int.lt_floor_add_one q
  change |(⌊q⌋ : ℝ) - (q : ℝ)| ≤ 1
  exact abs_le.mpr ⟨by linarith only [hhi], by linarith only [hlo]⟩

/-- Repeating any listed cycle gives an admitted physical height with first
entry exactly the reference entry plus the cycle mean. -/
theorem cycleMean_mem_growthSet {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) :
    symmetricMatrix ((slice.a₀ : ℝ) + (slice.cycleMean sector cycle : ℝ)) (slice.mixed : ℝ) (slice.vertical : ℝ) ∈
      growthSet slice.k := by
  have hk : 0 < slice.k := by have := slice.hk; omega
  have hk' : (slice.k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  let mean : ℝ := (slice.cycleMean sector cycle : ℝ)
  let matrix := symmetricMatrix ((slice.a₀ : ℝ) + mean) (slice.mixed : ℝ) (slice.vertical : ℝ)
  let rowTilt : ℝ := (((sector : ℚ) - slice.w * (slice.length : ℚ) ^ 2 / 2) / (slice.length : ℚ) : ℚ)
  obtain ⟨tilt, bound, hbound, hprimitive⟩ := periodicPrimitive_quadratic_bound cycle.2.property.1
    (cycleWeights cycle) (firstPhase cycle).val
  have hmean : (∑ i : Fin cycle.1.val, (cycleWeights cycle i : ℝ)) / (cycle.1.val : ℝ) = mean := by
    simp only [mean, cycleMean, cycleWeights, Rat.cast_div, Rat.cast_sum, Rat.cast_intCast, Rat.cast_natCast]
  rw [hmean] at hprimitive
  refine ⟨isSymm_symmetricMatrix .., liftColumns slice.k (cycleRetained cycle), ?_, ?_⟩
  · exact (superharmonic_liftColumns_iff slice.hk _).mpr (columnRow_cycleRetained_nonpos cycle)
  apply quadraticGrowth_liftColumns_of_retained_bound hk (tilt + rowTilt / (slice.k : ℝ)) (rowTilt / (slice.k : ℝ))
    (1 + (slice.shapeBound sector : ℝ) + bound) (by
      have hshape : (0 : ℝ) ≤ slice.shapeBound sector := by exact_mod_cast slice.shapeBound_nonneg sector
      positivity)
  intro column row
  let shape := (cycle.2.val (cycleIndex cycle column)).2.2
  have hshape : |(shapeAt shape row : ℝ)| ≤ (slice.shapeBound sector : ℝ) := by
    exact_mod_cast slice.abs_entryValue_le (shape.val (slice.rowPhase row))
  have hq : (slice.referencePolynomial sector column row : ℝ) + mean * (column : ℝ) ^ 2 / 2 + tilt * (column : ℝ) =
      matrixQuadratic matrix (columnSite slice.k column row 0) +
        ((tilt + rowTilt / (slice.k : ℝ)) * (column : ℝ) +
          rowTilt / (slice.k : ℝ) * ((slice.k * row - column : ℤ) : ℝ)) := by
    simp only [referencePolynomial, matrix, rowTilt, u, v, w, columnSite, add_zero, matrixQuadratic_symmetricMatrix,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_intCast, Rat.cast_natCast,
      Rat.cast_ofNat, Int.cast_sub, Int.cast_mul]
    field_simp
    ring
  change |(cycleRetained cycle (column, row) : ℝ) - matrixQuadratic matrix (columnSite slice.k column row 0) -
    ((tilt + rowTilt / (slice.k : ℝ)) * (column : ℝ) +
      rowTilt / (slice.k : ℝ) * ((slice.k * row - column : ℤ) : ℝ))| ≤ _
  rw [← sub_add_eq_sub_sub, ← hq]
  have heq : (cycleRetained cycle (column, row) : ℝ) -
      ((slice.referencePolynomial sector column row : ℝ) + mean * (column : ℝ) ^ 2 / 2 + tilt * (column : ℝ)) =
      ((slice.reference sector (column, row) : ℝ) - (slice.referencePolynomial sector column row : ℝ) +
        (shapeAt shape row : ℝ)) +
      ((cycleAdjustment cycle column : ℝ) - mean * (column : ℝ) ^ 2 / 2 - tilt * (column : ℝ)) := by
    simp only [cycleRetained, cycleColumns, Int.cast_add, shape]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
    (reference_abs_error slice sector column row) hshape)) (hprimitive column))

theorem cyclePeak_mem_growthSet (slice : ColumnSlice) :
    symmetricMatrix (slice.cyclePeak : ℝ) (slice.mixed : ℝ) (slice.vertical : ℝ) ∈ growthSet slice.k := by
  obtain ⟨sector, cycle, h⟩ := slice.cyclePeak_attained
  rw [h, Rat.cast_add, Rat.cast_intCast]
  exact cycleMean_mem_growthSet cycle

theorem mem_growthSet_of_le_cyclePeak (slice : ColumnSlice) {a : ℝ} (ha : a ≤ (slice.cyclePeak : ℝ)) :
    symmetricMatrix a (slice.mixed : ℝ) (slice.vertical : ℝ) ∈ growthSet slice.k := by
  have h := sub_mem_growthSet_of_posSemidef slice.hk slice.cyclePeak_mem_growthSet
    (posSemidef_topEntry (sub_nonneg.mpr ha))
  have heq : symmetricMatrix (slice.cyclePeak : ℝ) (slice.mixed : ℝ) (slice.vertical : ℝ) -
      symmetricMatrix ((slice.cyclePeak : ℝ) - a) 0 0 = symmetricMatrix a (slice.mixed : ℝ) (slice.vertical : ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symmetricMatrix]
  rwa [heq] at h

end ColumnSlice

/-- Every real matrix in the closure of the explicit rational cycle cones
is admitted on the physical `F^(k)` graph. -/
theorem closure_cycleCone_subset_growthSet {k : ℤ} (hk : 2 ≤ k) :
    closure (rationalConeUnion (fun b c => ((⟨k, hk, b, c⟩ : ColumnSlice).cyclePeak : ℝ))) ⊆ growthSet k :=
  closure_rationalCone_subset_growthSet hk (fun b c => (⟨k, hk, b, c⟩ : ColumnSlice).cyclePeak_mem_growthSet)

end FLatticePaper.GeneralK
