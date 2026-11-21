import FLatticePaper.GeneralK.ColumnCycleAdmission
import FLatticePaper.GeneralK.ColumnCycleBound
import FLatticePaper.GeneralK.ColumnResidual

namespace FLatticePaper.GeneralK.ColumnSlice

private theorem cast_emod_toNat (value : ℤ) {period : ℕ} (hpos : 0 < period) :
    (((value % (period : ℤ)).toNat : ℕ) : ℤ) = value % (period : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hpos.ne'))

set_option maxHeartbeats 800000 in
/-- An actual column restriction whose correction lies within the exact shape
alphabet has first-entry growth at most the largest cycle endpoint. -/
theorem le_cyclePeak_of_bounded_column_restriction (slice : ColumnSlice) (sector : slice.Sector)
    {field : Field} (hrow : ∀ column row, columnRow slice.k field column row ≤ 0)
    (hperiod : ∀ column, Function.Periodic (fun row => field (column, row) - slice.reference sector.val (column, row))
      (slice.length : ℤ))
    (hosc : ∃ bound : ℤ, ∀ column row,
      |(field (column, row) - slice.reference sector.val (column, row)) -
        (field (column, 0) - slice.reference sector.val (column, 0))| ≤ bound)
    (hlinear : ∀ column row, |linearColumnRow slice.k (field - slice.reference sector.val) column row| ≤
      slice.residualBound sector.val)
    (a slope bound : ℝ)
    (hzero : ∀ column : ℤ,
      |((field (column, 0) - slice.reference sector.val (column, 0) : ℤ) : ℝ) -
        ((a - slice.a₀) * (column : ℝ) ^ 2 / 2 + slope * (column : ℝ))| ≤ bound) :
    a ≤ (slice.cyclePeak : ℝ) := by
  let correction : Field := field - slice.reference sector.val
  let t (column : ℤ) := correction (column, 0)
  have hshape (column : ℤ) : ∃ shape : slice.Shape sector.val, ∀ row,
      shapeAt shape row = correction (column, row) - t column := by
    exact slice.exists_shape_of_periodicColumn sector.val (fun row => correction (column, row)) (hperiod column)
      (slice.abs_sub_zero_le_shapeBound sector.val (field := correction) hperiod hosc hlinear column)
  choose shape hshape using hshape
  let phase (column : ℤ) : Fin slice.phasePeriod :=
    ⟨(column % (slice.phasePeriod : ℤ)).toNat, by
      have h := Int.emod_lt_of_pos column (show 0 < (slice.phasePeriod : ℤ) by exact_mod_cast slice.phasePeriod_pos)
      exact_mod_cast (show (((column % (slice.phasePeriod : ℤ)).toNat : ℕ) : ℤ) < slice.phasePeriod by
        rw [cast_emod_toNat _ slice.phasePeriod_pos]; exact h)⟩
  have hphase (column : ℤ) : ((phase column).val : ℤ) = column % (slice.phasePeriod : ℤ) :=
    cast_emod_toNat _ slice.phasePeriod_pos
  have hphaseNext (column : ℤ) : phase (column + 1) = cyclicSucc (phase column) := by
    apply Fin.ext
    apply Int.ofNat_inj.mp
    simp only [cyclicSucc, Int.natCast_mod, Int.natCast_add, Int.natCast_one, hphase, Int.emod_add_emod]
  let vertex (column : ℤ) : slice.Vertex sector.val := (phase column, shape (column - 1), shape column)
  have hedge (column : ℤ) : IsEdge (vertex column) (vertex (column + 1)) := by
    refine ⟨hphaseNext column, ?_⟩
    change shape (column + 1 - 1) = shape column
    rw [add_sub_cancel_right]
  have hweight (column : ℤ) : t (column - 1) + t (column + 1) - 2 * t column ≤
      slice.edgeWeight sector.val (vertex column) (vertex (column + 1)) := by
    let edge (center : ℤ) := slice.edgeColumns sector.val center (shape (column - 1)) (shape column) (shape (column + 1))
    let d := t (column - 1) + t (column + 1) - 2 * t column
    have hread (row : ℤ) : columnRow slice.k field column row = columnRow slice.k (edge column) column row + d := by
      rw [← columnRow_add_column (by have := slice.hk; omega) _ t]
      simp only [columnRow, edge, edgeColumns, ite_true,
        if_neg (show column + 1 ≠ column - 1 by omega), if_neg (show column + 1 ≠ column by omega),
        if_neg (show column ≠ column - 1 by omega), hshape]
      have hval (i j : ℤ) : slice.reference sector.val (i, j) + (correction (i, j) - t i) + t i = field (i, j) := by
        change _ + ((field (i, j) - slice.reference sector.val (i, j)) - t i) + t i = _
        ring
      simp only [hval]
    have hrowBound (row : ℤ) : columnRow slice.k (edge (phase column).val) (phase column).val row ≤ -d := by
      have hp : Function.Periodic (fun center => columnRow slice.k (edge center) center row) (slice.phasePeriod : ℤ) :=
        fun center => slice.columnRow_edgeColumns_add_phasePeriod sector.val center row _ _ _
      have heq := periodic_eq_emod hp column
      change columnRow slice.k (edge column) column row =
        columnRow slice.k (edge (column % (slice.phasePeriod : ℤ))) (column % (slice.phasePeriod : ℤ)) row at heq
      rw [hphase, ← heq]
      have h := hrow column row
      rw [hread] at h
      omega
    change d ≤ slice.edgeWeight sector.val (vertex column) (vertex (column + 1))
    unfold edgeWeight
    apply le_neg.mpr
    apply Finset.max'_le
    intro value hv
    obtain ⟨row, -, rfl⟩ := Finset.mem_image.mp hv
    exact hrowBound row
  obtain ⟨offset, hoffset⟩ := slice.exists_pathWeight_bound sector
  let path (i : ℕ) := vertex ((i : ℤ) + 1)
  let difference (i : ℕ) : ℝ := (t ((i : ℤ) + 1) : ℝ) - (t (i : ℤ) : ℝ)
  have htel (n : ℕ) : ∑ i ∈ Finset.range n, (difference (i + 1) - difference i) = difference n - difference 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have hsum (n : ℕ) : ((t ((n : ℤ) + 1) : ℤ) : ℝ) - (t (n : ℤ) : ℝ) - ((t 1 : ℝ) - (t 0 : ℝ)) ≤
      (n : ℝ) * ((slice.cyclePeak : ℝ) - slice.a₀) + (offset : ℝ) := by
    have hw := hoffset n path (fun i _ => by simpa only [path, Int.natCast_add, Int.natCast_one] using hedge ((i : ℤ) + 1))
    have hw' : (∑ i ∈ Finset.range n, (slice.edgeWeight sector.val (path i) (path (i + 1)) : ℝ)) ≤
        (n : ℝ) * ((slice.cyclePeak : ℝ) - slice.a₀) + (offset : ℝ) := by exact_mod_cast hw
    apply le_trans _ hw'
    change difference n - difference 0 ≤ _
    rw [← htel n]
    apply Finset.sum_le_sum
    intro i _
    have h := hweight ((i : ℤ) + 1)
    rw [add_sub_cancel_right] at h
    have hc : (t (i : ℤ) : ℝ) + (t ((i : ℤ) + 1 + 1) : ℝ) - 2 * (t ((i : ℤ) + 1) : ℝ) ≤
        (slice.edgeWeight sector.val (path i) (path (i + 1)) : ℝ) := by
      push_cast [path]
      exact_mod_cast h
    simpa only [difference, Int.natCast_add, Int.natCast_one] using (show _ ≤ _ by linarith only [hc])
  by_contra! hgt
  have hd : 0 < a - (slice.cyclePeak : ℝ) := sub_pos.mpr hgt
  let c := (offset : ℝ) + ((t 1 : ℝ) - (t 0 : ℝ)) + 2 * bound - ((a - slice.a₀) / 2 + slope)
  obtain ⟨n, hn⟩ := exists_nat_gt (c / (a - (slice.cyclePeak : ℝ)))
  have hlarge := (div_lt_iff₀ hd).mp hn
  have hlo := (abs_le.mp (hzero ((n : ℤ) + 1))).1
  have hhi := (abs_le.mp (hzero (n : ℤ))).2
  change -bound ≤ (t ((n : ℤ) + 1) : ℝ) - _ at hlo
  change (t (n : ℤ) : ℝ) - _ ≤ bound at hhi
  push_cast at hlo hhi
  have h := hsum n
  dsimp only [c] at hlarge
  linarith only [hlarge, hlo, hhi, h]

end FLatticePaper.GeneralK.ColumnSlice
