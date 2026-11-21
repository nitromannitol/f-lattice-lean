import FLatticePaper.GeneralK.ColumnCycles
import Mathlib.Algebra.Ring.Periodic

namespace FLatticePaper.GeneralK.ColumnSlice

/-- The horizontal phase chosen to start the listed cycle. -/
def firstPhase {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) : Fin slice.phasePeriod :=
  (cycle.2.val ⟨0, cycle.2.property.1⟩).1

private theorem phase_eq_add_mod {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector)
    (index : Fin cycle.1.val) :
    (cycle.2.val index).1.val = ((firstPhase cycle).val + index.val) % slice.phasePeriod := by
  obtain ⟨i, hi⟩ := index
  induction i with
  | zero =>
    exact (Nat.mod_eq_of_lt (firstPhase cycle).isLt).symm
  | succ i ih =>
    have hprev : i < cycle.1.val := by omega
    have hstep := (cycle.2.property.2.2 ⟨i, hprev⟩).1
    have heq : cyclicSucc (⟨i, hprev⟩ : Fin cycle.1.val) = ⟨i + 1, hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
    rw [heq] at hstep
    have hphase := congrArg Fin.val hstep
    change (cycle.2.val ⟨i + 1, hi⟩).1.val =
      ((cycle.2.val ⟨i, hprev⟩).1.val + 1) % slice.phasePeriod at hphase
    rw [hphase, ih hprev, Nat.mod_add_mod, Nat.add_assoc]

/-- Every directed cycle advances through a whole number of phase periods. -/
theorem phasePeriod_dvd_cycleLength {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) :
    slice.phasePeriod ∣ cycle.1.val := by
  have hn := cycle.2.property.1
  let last : Fin cycle.1.val := ⟨cycle.1.val - 1, by omega⟩
  have hs : cyclicSucc last = ⟨0, hn⟩ := by
    apply Fin.ext
    change (cycle.1.val - 1 + 1) % cycle.1.val = 0
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  have h := congrArg Fin.val (cycle.2.property.2.2 last).1
  rw [hs] at h
  change (firstPhase cycle).val = ((cycle.2.val last).1.val + 1) % slice.phasePeriod at h
  rw [phase_eq_add_mod cycle last, Nat.mod_add_mod, Nat.add_assoc] at h
  have hi : last.val + 1 = cycle.1.val := by dsimp [last]; omega
  rw [hi] at h
  have hnat := h.symm.trans (Nat.mod_eq_of_lt (firstPhase cycle).isLt).symm
  have hint : (((firstPhase cycle).val : ℤ) + (cycle.1.val : ℤ)) % (slice.phasePeriod : ℤ) =
      ((firstPhase cycle).val : ℤ) % (slice.phasePeriod : ℤ) := by exact_mod_cast hnat
  have hd := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hint
  rw [add_sub_cancel_left] at hd
  exact Int.natCast_dvd_natCast.mp (Int.dvd_iff_emod_eq_zero.mpr hd)

/-- The cycle slot at a physical column, aligned to the phase of its first
vertex. The remainder convention applies to all positive and negative columns. -/
def cycleIndex {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) (column : ℤ) : Fin cycle.1.val :=
  ⟨((column - (firstPhase cycle).val) % (cycle.1.val : ℤ)).toNat, by
    have hpos : (0 : ℤ) < (cycle.1.val : ℤ) := by exact_mod_cast cycle.2.property.1
    have hlo := Int.emod_nonneg (column - (firstPhase cycle).val) (ne_of_gt hpos)
    have hhi := Int.emod_lt_of_pos (column - (firstPhase cycle).val) hpos
    omega⟩

theorem cast_cycleIndex {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) (column : ℤ) :
    ((cycleIndex cycle column).val : ℤ) = (column - (firstPhase cycle).val) % (cycle.1.val : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast (ne_of_gt cycle.2.property.1))

theorem cycleIndex_add_one {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) (column : ℤ) :
    cycleIndex cycle (column + 1) = cyclicSucc (cycleIndex cycle column) := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  simp only [cyclicSucc, Int.natCast_mod, Int.natCast_add, Int.natCast_one, cast_cycleIndex, Int.emod_add_emod]
  congr 1
  ring

theorem phase_cycleIndex {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) (column : ℤ) :
    ((cycle.2.val (cycleIndex cycle column)).1.val : ℤ) = column % (slice.phasePeriod : ℤ) := by
  rw [phase_eq_add_mod cycle]
  simp only [Int.natCast_mod, Int.natCast_add, cast_cycleIndex]
  have hd : (slice.phasePeriod : ℤ) ∣ (cycle.1.val : ℤ) := by exact_mod_cast phasePeriod_dvd_cycleLength cycle
  rw [Int.add_emod, Int.emod_emod_of_dvd _ hd, ← Int.add_emod]
  congr 1
  ring

/-- The reference height with the cycle's current shape in each column. -/
def cycleColumns {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) : Field := fun site =>
  slice.reference sector site + shapeAt (cycle.2.val (cycleIndex cycle site.1)).2.2 site.2

def cycleWeightAt {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) (column : ℤ) : ℤ :=
  slice.edgeWeight sector (cycle.2.val (cycleIndex cycle column)) (cycle.2.val (cycleIndex cycle (column + 1)))

/-- Repeating the cycle on all integer columns bounds every actual reduced
row by the negative edge weight, using the true row and phase period laws. -/
theorem columnRow_cycleColumns_le {slice : ColumnSlice} {sector : ℤ} (cycle : slice.SimpleCycle sector) (column row : ℤ) :
    columnRow slice.k (cycleColumns cycle) column row ≤ -cycleWeightAt cycle column := by
  let source := cycle.2.val (cycleIndex cycle column)
  let target := cycle.2.val (cycleIndex cycle (column + 1))
  let prev := cycle.2.val (cycleIndex cycle (column - 1))
  have hshape : source.2.1 = prev.2.2 := by
    have h := (cycle.2.property.2.2 (cycleIndex cycle (column - 1))).2
    rw [← cycleIndex_add_one, sub_add_cancel] at h
    exact h
  have hrow : columnRow slice.k (cycleColumns cycle) column row =
      columnRow slice.k (slice.edgeColumns sector column source.2.1 source.2.2 target.2.2) column row := by
    simp only [columnRow, cycleColumns, edgeColumns, ite_true,
      if_neg (show column + 1 ≠ column - 1 by omega), if_neg (show column + 1 ≠ column by omega),
      if_neg (show column ≠ column - 1 by omega)]
    rw [hshape]
  rw [hrow]
  let horizontal (i : ℤ) := columnRow slice.k (slice.edgeColumns sector i source.2.1 source.2.2 target.2.2) i row
  have hperiod : Function.Periodic horizontal (slice.phasePeriod : ℤ) := fun i =>
    slice.columnRow_edgeColumns_add_phasePeriod sector i row source.2.1 source.2.2 target.2.2
  have hsource : (source.1.val : ℤ) = column % (slice.phasePeriod : ℤ) := phase_cycleIndex cycle column
  have hshift := (hperiod.zsmul (column / (slice.phasePeriod : ℤ))) (column % (slice.phasePeriod : ℤ))
  have hcol : horizontal column = horizontal source.1.val := by
    rw [hsource]
    simpa only [zsmul_eq_mul, Int.cast_id, mul_comm (column / (slice.phasePeriod : ℤ)), Int.emod_add_mul_ediv] using hshift
  change horizontal column ≤ _
  rw [hcol]
  let vertical (r : ℤ) := columnRow slice.k (slice.edgeColumns sector source.1.val source.2.1 source.2.2 target.2.2)
    source.1.val r
  have hvperiod : Function.Periodic vertical (slice.length : ℤ) := fun r =>
    slice.columnRow_edgeColumns_add_length sector source.1.val r source.2.1 source.2.2 target.2.2
  have hvshift := (hvperiod.zsmul (row / (slice.length : ℤ))) (row % (slice.length : ℤ))
  have hrowPhase : ((slice.rowPhase row).val : ℤ) = row % (slice.length : ℤ) := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast ne_of_gt slice.length_pos))
  have hvrow : vertical row = vertical (slice.rowPhase row).val := by
    rw [hrowPhase]
    simpa only [zsmul_eq_mul, Int.cast_id, mul_comm (row / (slice.length : ℤ)), Int.emod_add_mul_ediv] using hvshift
  change vertical row ≤ -slice.edgeWeight sector source target
  rw [hvrow]
  exact slice.columnRow_le_neg_edgeWeight sector source target (slice.rowPhase row)

end FLatticePaper.GeneralK.ColumnSlice
