import FLatticePaper.GeneralK.ColumnWidth

namespace FLatticePaper.GeneralK

theorem linearColumnRow_add_affine (k : ℤ) (field : Field) (horizontal vertical constant column row : ℤ) :
    linearColumnRow k (fun site => field site + (horizontal * site.1 + vertical * site.2 + constant)) column row =
      linearColumnRow k field column row := by
  simp only [linearColumnRow]
  ring

theorem linearColumnRow_sub (k : ℤ) (first second : Field) (column row : ℤ) :
    linearColumnRow k (first - second) column row =
      linearColumnRow k first column row - linearColumnRow k second column row := by
  simp only [linearColumnRow, Pi.sub_apply]
  ring

namespace ColumnSlice

theorem linearColumnRow_reference_add_phasePeriod (slice : ColumnSlice) (sector column row : ℤ) :
    linearColumnRow slice.k (slice.reference sector) (column + slice.phasePeriod) row =
      linearColumnRow slice.k (slice.reference sector) column row := by
  obtain ⟨slope, vertical, constant, hperiod⟩ := slice.reference_add_phasePeriod sector
  rw [← linearColumnRow_add_affine _ _ slope (slice.k * vertical) constant column row]
  simp only [linearColumnRow, add_right_comm column (slice.phasePeriod : ℤ) 1,
    show column + (slice.phasePeriod : ℤ) - 1 = column - 1 + slice.phasePeriod by ring, hperiod]

theorem linearColumnRow_reference_add_length (slice : ColumnSlice) (sector column row : ℤ) :
    linearColumnRow slice.k (slice.reference sector) column (row + slice.length) =
      linearColumnRow slice.k (slice.reference sector) column row := by
  obtain ⟨mixed, vertical, -, -, hperiod⟩ := slice.reference_add_length sector
  rw [← linearColumnRow_add_affine _ _ mixed (slice.k * vertical) sector column row]
  simp only [linearColumnRow, add_right_comm row (slice.length : ℤ) 1,
    show row + (slice.length : ℤ) - 1 = row - 1 + slice.length by ring, hperiod]

theorem periodic_eq_emod {α : Type*} {field : ℤ → α} {period : ℤ}
    (hperiod : Function.Periodic field period) (index : ℤ) : field index = field (index % period) := by
  have h := (hperiod.zsmul (index / period)) (index % period)
  simpa only [zsmul_eq_mul, Int.cast_id, mul_comm (index / period), Int.emod_add_mul_ediv] using h

/-- The finite reference norm bounds the linear row on the entire plane. -/
theorem abs_linearColumnRow_reference_le (slice : ColumnSlice) (sector column row : ℤ) :
    |linearColumnRow slice.k (slice.reference sector) column row| ≤
      slice.residualBound sector - slice.k ^ 2 * slice.chargeBound := by
  let lin := linearColumnRow slice.k (slice.reference sector)
  let p := column % (slice.phasePeriod : ℤ)
  let r := row % (slice.length : ℤ)
  have hp : 0 < (slice.phasePeriod : ℤ) := by exact_mod_cast slice.phasePeriod_pos
  have hr : 0 < (slice.length : ℤ) := by exact_mod_cast slice.length_pos
  have hpCast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (Int.emod_nonneg _ hp.ne')
  have hrCast : (r.toNat : ℤ) = r := Int.toNat_of_nonneg (Int.emod_nonneg _ hr.ne')
  have hpMem : p.toNat ∈ Finset.range slice.phasePeriod := Finset.mem_range.mpr (by
    exact_mod_cast (show (p.toNat : ℤ) < slice.phasePeriod by rw [hpCast]; exact Int.emod_lt_of_pos _ hp))
  have hrMem : r.toNat ∈ Finset.range slice.length := Finset.mem_range.mpr (by
    exact_mod_cast (show (r.toNat : ℤ) < slice.length by rw [hrCast]; exact Int.emod_lt_of_pos _ hr))
  have hmem : (p.toNat, r.toNat) ∈ (Finset.range slice.phasePeriod).product (Finset.range slice.length) :=
    Finset.mem_product.mpr ⟨hpMem, hrMem⟩
  have hmax := Finset.le_sup (f := fun point : ℕ × ℕ => (lin point.1 point.2).natAbs) hmem
  have hleft : Function.Periodic (fun i => lin i row) (slice.phasePeriod : ℤ) :=
    fun i => slice.linearColumnRow_reference_add_phasePeriod sector i row
  have hright : Function.Periodic (lin p) (slice.length : ℤ) :=
    slice.linearColumnRow_reference_add_length sector p
  change |lin column row| ≤ _
  rw [show lin column row = lin p r from (periodic_eq_emod hleft column).trans (periodic_eq_emod hright row)]
  simpa only [residualBound, add_sub_cancel_left, hpCast, hrCast, Int.natCast_natAbs, lin] using
    (Int.ofNat_le.mpr hmax)

/-- The least majorant's retained restriction, after subtracting the sector
reference, has linear row norm at most the graph's exact `K`. -/
theorem abs_linearColumnRow_sub_reference_le (slice : ColumnSlice) (sector : ℤ) {height : Field}
    (hcharge : ∀ site, 0 ≤ -laplacian slice.k height site ∧ -laplacian slice.k height site ≤ slice.chargeBound)
    (column row : ℤ) :
    let restricted : Field := fun ij => height (columnSite slice.k ij.1 ij.2 0)
    |linearColumnRow slice.k (restricted - slice.reference sector) column row| ≤ slice.residualBound sector := by
  dsimp only
  rw [linearColumnRow_sub]
  obtain ⟨hlo, hhi⟩ := linearColumnRow_restriction_bounds slice.hk hcharge column row
  have h := slice.abs_linearColumnRow_reference_le sector column row
  have hr := abs_sub (linearColumnRow slice.k (fun ij => height (columnSite slice.k ij.1 ij.2 0)) column row)
    (linearColumnRow slice.k (slice.reference sector) column row)
  rw [abs_of_nonpos (neg_nonneg.mp hlo)] at hr
  omega

end ColumnSlice
end FLatticePaper.GeneralK
