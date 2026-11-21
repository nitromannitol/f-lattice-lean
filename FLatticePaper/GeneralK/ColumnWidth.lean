import FLatticePaper.GeneralK.ColumnCharge
import FLatticePaper.GeneralK.ColumnFourier

namespace FLatticePaper.GeneralK.ColumnSlice

private theorem rowPeriodic_eq_mod {length : ℕ} {field : ℤ → ℤ}
    (hper : Function.Periodic field (length : ℤ)) (row : ℤ) : field row = field (row % (length : ℤ)) := by
  have h := (hper.zsmul (row / (length : ℤ))) (row % (length : ℤ))
  simpa only [zsmul_eq_mul, Int.cast_id, mul_comm (row / (length : ℤ)), Int.emod_add_mul_ediv] using h

private theorem norm_intCast_complex (value : ℤ) : ‖(value : ℂ)‖ = (|value| : ℝ) := by
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]

/-- A bounded periodic row correction lands inside the exact shape interval
when its linear row deficit is at most `K`. -/
theorem abs_sub_zero_le_shapeBound (slice : ColumnSlice) (sector : ℤ) {field : Field}
    (hperiod : ∀ column, Function.Periodic (fun row => field (column, row)) (slice.length : ℤ))
    (hoscillation : ∃ initial : ℤ, ∀ column row, |field (column, row) - field (column, 0)| ≤ initial)
    (hlinear : ∀ column row, |linearColumnRow slice.k field column row| ≤ slice.residualBound sector)
    (column row : ℤ) : |field (column, row) - field (column, 0)| ≤ slice.shapeBound sector := by
  letI : NeZero slice.length := ⟨slice.length_pos.ne'⟩
  let cyclic (column : ℤ) (row : ZMod slice.length) : ℂ := field (column, (row.val : ℤ))
  have hread (i j : ℤ) : cyclic i (j : ZMod slice.length) = (field (i, j) : ℂ) := by
    simp only [cyclic, ZMod.val_intCast]
    rw [rowPeriodic_eq_mod (hperiod i) j]
  have hosc : ∃ initial : ℝ, ∀ i r, ‖cyclic i r - cyclic i 0‖ ≤ initial := by
    obtain ⟨initial, hi⟩ := hoscillation
    refine ⟨initial, fun i r => ?_⟩
    have hcast : ((r.val : ℤ) : ZMod slice.length) = r := by simp
    have hzero (i : ℤ) : cyclic i 0 = (field (i, 0) : ℂ) := by simpa using hread i 0
    rw [← hcast, hread, hzero, ← Int.cast_sub, norm_intCast_complex]
    exact_mod_cast hi i r.val
  have hrow (i : ℤ) (r : ZMod slice.length) :
      ‖complexColumnRow (slice.k : ℝ) cyclic i r‖ ≤ (slice.residualBound sector : ℝ) := by
    have hpos : r + 1 = (((r.val : ℤ) + 1 : ℤ) : ZMod slice.length) := by simp
    have hneg : r - 1 = (((r.val : ℤ) - 1 : ℤ) : ZMod slice.length) := by simp
    rw [complexColumnRow, hpos, hneg, hread, hread]
    change ‖(((slice.k : ℝ) - 1 : ℝ) : ℂ) * (field (i + 1, (r.val : ℤ)) : ℂ) +
      (field (i + 1, (r.val : ℤ) + 1) : ℂ) + (((slice.k : ℝ) - 1 : ℝ) : ℂ) *
      (field (i - 1, (r.val : ℤ)) : ℂ) + (field (i - 1, (r.val : ℤ) - 1) : ℂ) -
      2 * ((slice.k : ℝ) : ℂ) * (field (i, (r.val : ℤ)) : ℂ)‖ ≤ _
    have heq : (((slice.k : ℝ) - 1 : ℝ) : ℂ) * (field (i + 1, (r.val : ℤ)) : ℂ) +
      (field (i + 1, (r.val : ℤ) + 1) : ℂ) + (((slice.k : ℝ) - 1 : ℝ) : ℂ) *
      (field (i - 1, (r.val : ℤ)) : ℂ) + (field (i - 1, (r.val : ℤ) - 1) : ℂ) -
      2 * ((slice.k : ℝ) : ℂ) * (field (i, (r.val : ℤ)) : ℂ) =
        (linearColumnRow slice.k field i r.val : ℂ) := by
      simp [linearColumnRow]
    rw [heq, norm_intCast_complex]
    exact_mod_cast hlinear i r.val
  have hk : (2 : ℝ) ≤ slice.k := by exact_mod_cast slice.hk
  have hwidth := norm_sub_zero_le_column_width hk cyclic hosc hrow column (row : ZMod slice.length)
  have hzero : cyclic column 0 = (field (column, 0) : ℂ) := by simpa using hread column 0
  rw [hread, hzero, ← Int.cast_sub, norm_intCast_complex] at hwidth
  have hshape : ((slice.length : ℝ) - 1) * (slice.residualBound sector : ℝ) * (slice.k : ℝ) * (slice.length : ℝ) ^ 2 /
      (8 * ((slice.k : ℝ) - 1)) ≤ (slice.shapeBound sector : ℝ) := by
    have hcast (a b : ℚ) (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := Rat.cast_le.mpr h
    have h := hcast _ _ (Int.le_ceil (((slice.length : ℚ) - 1) * (slice.residualBound sector : ℚ) *
      (slice.k : ℚ) * (slice.length : ℚ) ^ (2 : ℕ) / (8 * ((slice.k : ℚ) - 1))))
    simpa only [shapeBound, Rat.cast_intCast, Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast,
      Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow] using h
  exact_mod_cast hwidth.trans hshape

/-- The actual normalized columns satisfying the width bound are shapes in
the finite alphabet, with equality at every integer row. -/
theorem exists_shape_of_periodicColumn (slice : ColumnSlice) (sector : ℤ) (field : ℤ → ℤ)
    (hperiod : Function.Periodic field (slice.length : ℤ))
    (hbound : ∀ row, |field row - field 0| ≤ slice.shapeBound sector) :
    ∃ shape : slice.Shape sector, ∀ row, shapeAt shape row = field row - field 0 := by
  have hvalue (row : Fin slice.length) : ∃ entry : slice.ShapeEntry sector,
      entryValue entry = field row.val - field 0 := exists_entryValue (hbound row.val)
  choose entries hentries using hvalue
  have hzero : entries (slice.rowPhase 0) = slice.zeroEntry sector := by
    have h := hentries (slice.rowPhase 0)
    rw [rowPhase_zero] at h ⊢
    change entryValue (entries ⟨0, slice.length_pos⟩) = field 0 - field 0 at h
    apply Fin.ext
    have hbound := slice.shapeBound_nonneg sector
    change ((entries ⟨0, slice.length_pos⟩).val : ℤ) - slice.shapeBound sector = _ at h
    change (entries ⟨0, slice.length_pos⟩).val = (slice.shapeBound sector).toNat
    omega
  refine ⟨⟨entries, hzero⟩, fun row => ?_⟩
  change entryValue (entries (slice.rowPhase row)) = _
  rw [hentries]
  have hcast : ((slice.rowPhase row).val : ℤ) = row % (slice.length : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast slice.length_pos.ne'))
  rw [hcast, ← rowPeriodic_eq_mod hperiod row]

end FLatticePaper.GeneralK.ColumnSlice
