import FLatticePaper.GeneralK.ColumnReference
import Mathlib.Data.Fintype.Sigma

namespace FLatticePaper.GeneralK

/-- The retained row before taking ceilings, multiplied by `k`. -/
def linearColumnRow (k : ℤ) (field : Field) (column row : ℤ) : ℤ :=
  (k - 1) * field (column + 1, row) + field (column + 1, row + 1) +
    (k - 1) * field (column - 1, row) + field (column - 1, row - 1) - 2 * k * field (column, row)

namespace ColumnSlice

/-- The charge bound `D` for the least periodic obstacle majorant. -/
def chargeBound (slice : ColumnSlice) : ℤ := max 1 ⌈2 - min (slice.a₀ : ℚ) slice.vertical⌉

/-- The bound `K` on the linear retained row of the shape correction. -/
def residualBound (slice : ColumnSlice) (sector : ℤ) : ℤ :=
  let maxRow : ℕ := ((Finset.range slice.phasePeriod).product (Finset.range slice.length)).sup fun point =>
    (linearColumnRow slice.k (slice.reference sector) point.1 point.2).natAbs
  slice.k ^ 2 * slice.chargeBound + (maxRow : ℤ)

/-- The bound `E` on each entry of a normalized column shape. -/
def shapeBound (slice : ColumnSlice) (sector : ℤ) : ℤ :=
  ⌈((slice.length : ℚ) - 1) * (slice.residualBound sector : ℚ) * (slice.k : ℚ) * (slice.length : ℚ) ^ 2 /
    (8 * ((slice.k : ℚ) - 1))⌉

theorem chargeBound_pos (slice : ColumnSlice) : 0 < slice.chargeBound :=
  zero_lt_one.trans_le (le_max_left ..)

theorem residualBound_nonneg (slice : ColumnSlice) (sector : ℤ) : 0 ≤ slice.residualBound sector := by
  have hd := slice.chargeBound_pos
  unfold residualBound
  positivity

theorem shapeBound_nonneg (slice : ColumnSlice) (sector : ℤ) : 0 ≤ slice.shapeBound sector := by
  have hk : (2 : ℚ) ≤ slice.k := by exact_mod_cast slice.hk
  have hl : (1 : ℚ) ≤ (slice.length : ℚ) := by exact_mod_cast slice.length_pos
  have hres : (0 : ℚ) ≤ slice.residualBound sector := by exact_mod_cast slice.residualBound_nonneg sector
  unfold shapeBound
  apply Int.ceil_nonneg
  exact div_nonneg (by positivity [sub_nonneg.mpr hl, hk]) (by positivity [show (1 : ℚ) ≤ slice.k by linarith])

/-- The row phase of any retained row, including negative rows. -/
def rowPhase (slice : ColumnSlice) (row : ℤ) : Fin slice.length :=
  ⟨(row % (slice.length : ℤ)).toNat, by
    have hpos : 0 < (slice.length : ℤ) := by exact_mod_cast slice.length_pos
    have hlo := Int.emod_nonneg row (ne_of_gt hpos)
    have hhi := Int.emod_lt_of_pos row hpos
    omega⟩

@[simp] theorem rowPhase_zero (slice : ColumnSlice) : slice.rowPhase 0 = ⟨0, slice.length_pos⟩ := by
  apply Fin.ext
  simp [rowPhase]

theorem rowPhase_add_length (slice : ColumnSlice) (row : ℤ) :
    slice.rowPhase (row + (slice.length : ℤ)) = slice.rowPhase row := by
  apply Fin.ext
  simp [rowPhase]

/-- The interval of shape entries `[-E,E]` is encoded by `Fin (2E+1)`. -/
abbrev ShapeEntry (slice : ColumnSlice) (sector : ℤ) := Fin (2 * (slice.shapeBound sector).toNat + 1)

def entryValue {slice : ColumnSlice} {sector : ℤ} (entry : slice.ShapeEntry sector) : ℤ :=
  (entry.val : ℤ) - slice.shapeBound sector

def zeroEntry (slice : ColumnSlice) (sector : ℤ) : slice.ShapeEntry sector :=
  ⟨(slice.shapeBound sector).toNat, by omega⟩

@[simp] theorem entryValue_zeroEntry (slice : ColumnSlice) (sector : ℤ) :
    entryValue (slice.zeroEntry sector) = 0 := by
  change ((slice.shapeBound sector).toNat : ℤ) - slice.shapeBound sector = 0
  have h := slice.shapeBound_nonneg sector
  omega

theorem abs_entryValue_le {slice : ColumnSlice} {sector : ℤ} (entry : slice.ShapeEntry sector) :
    |entryValue entry| ≤ slice.shapeBound sector := by
  have hbound := slice.shapeBound_nonneg sector
  have hentry := entry.isLt
  apply abs_le.mpr
  unfold entryValue
  constructor <;> omega

theorem exists_entryValue {slice : ColumnSlice} {sector value : ℤ} (hvalue : |value| ≤ slice.shapeBound sector) :
    ∃ entry : slice.ShapeEntry sector, entryValue entry = value := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hvalue
  have hbound := slice.shapeBound_nonneg sector
  refine ⟨⟨(value + slice.shapeBound sector).toNat, by omega⟩, ?_⟩
  change ((value + slice.shapeBound sector).toNat : ℤ) - slice.shapeBound sector = value
  omega

/-- A normalized column shape, with zeroth row fixed at zero. -/
abbrev Shape (slice : ColumnSlice) (sector : ℤ) :=
  {shape : Fin slice.length → slice.ShapeEntry sector // shape (slice.rowPhase 0) = slice.zeroEntry sector}

def zeroShape (slice : ColumnSlice) (sector : ℤ) : slice.Shape sector :=
  ⟨fun _ => slice.zeroEntry sector, rfl⟩

def shapeAt {slice : ColumnSlice} {sector : ℤ} (shape : slice.Shape sector) (row : ℤ) : ℤ :=
  entryValue (shape.val (slice.rowPhase row))

@[simp] theorem shapeAt_zero {slice : ColumnSlice} {sector : ℤ} (shape : slice.Shape sector) : shapeAt shape 0 = 0 := by
  rw [shapeAt, shape.property, entryValue_zeroEntry]

theorem shapeAt_add_length {slice : ColumnSlice} {sector : ℤ} (shape : slice.Shape sector) (row : ℤ) :
    shapeAt shape (row + (slice.length : ℤ)) = shapeAt shape row := by
  simp only [shapeAt, rowPhase_add_length]

/-- The vertex remembers the phase, previous shape, and current shape. -/
abbrev Vertex (slice : ColumnSlice) (sector : ℤ) := Fin slice.phasePeriod × slice.Shape sector × slice.Shape sector

def cyclicSucc {length : ℕ} (index : Fin length) : Fin length :=
  ⟨(index.val + 1) % length, Nat.mod_lt _ (Nat.zero_le index.val |>.trans_lt index.isLt)⟩

def IsEdge {slice : ColumnSlice} {sector : ℤ} (source target : slice.Vertex sector) : Prop :=
  target.1 = cyclicSucc source.1 ∧ target.2.1 = source.2.2

instance {slice : ColumnSlice} {sector : ℤ} (source target : slice.Vertex sector) : Decidable (IsEdge source target) :=
  inferInstanceAs (Decidable (_ = _ ∧ _ = _))

/-- The three shapes used by an edge, with an arbitrary integer lift of the
source column. Only those columns are read by the displayed row operator. -/
def edgeColumns (slice : ColumnSlice) (sector column : ℤ)
    (previous current next : slice.Shape sector) : Field := fun site =>
  slice.reference sector site + shapeAt (if site.1 = column - 1 then previous else if site.1 = column then current else next) site.2

theorem edgeColumns_add_length (slice : ColumnSlice) (sector column : ℤ)
    (previous current next : slice.Shape sector) :
    ∃ mixed vertical : ℤ, ∀ site,
      slice.edgeColumns sector column previous current next (site.1, site.2 + (slice.length : ℤ)) =
        slice.edgeColumns sector column previous current next site +
          (mixed * site.1 + slice.k * vertical * site.2 + sector) := by
  obtain ⟨mixed, vertical, _, _, h⟩ := slice.reference_add_length sector
  refine ⟨mixed, vertical, fun site => ?_⟩
  simp only [edgeColumns, shapeAt_add_length]
  rw [h]
  ac_rfl

theorem edgeColumns_add_phasePeriod (slice : ColumnSlice) (sector column : ℤ)
    (previous current next : slice.Shape sector) :
    ∃ slope rowSlope constant : ℤ, ∀ site,
      slice.edgeColumns sector (column + (slice.phasePeriod : ℤ)) previous current next
        (site.1 + (slice.phasePeriod : ℤ), site.2) =
      slice.edgeColumns sector column previous current next site +
        (slope * site.1 + slice.k * rowSlope * site.2 + constant) := by
  obtain ⟨slope, rowSlope, constant, h⟩ := slice.reference_add_phasePeriod sector
  refine ⟨slope, rowSlope, constant, fun site => ?_⟩
  simp only [edgeColumns]
  rw [h]
  simp only [show site.1 + (slice.phasePeriod : ℤ) = column + (slice.phasePeriod : ℤ) - 1 ↔
    site.1 = column - 1 by omega, add_left_inj]
  ac_rfl

private theorem columnRow_translate (k : ℤ) (field : Field) (horizontal vertical column row : ℤ) :
    columnRow k (fun site => field (site.1 + horizontal, site.2 + vertical)) column row =
      columnRow k field (column + horizontal) (row + vertical) := by
  simp only [columnRow]
  rw [show column + 1 + horizontal = column + horizontal + 1 by omega,
    show column - 1 + horizontal = column + horizontal - 1 by omega,
    show row + 1 + vertical = row + vertical + 1 by omega,
    show row - 1 + vertical = row + vertical - 1 by omega]

theorem columnRow_edgeColumns_add_length (slice : ColumnSlice) (sector column row : ℤ)
    (previous current next : slice.Shape sector) :
    columnRow slice.k (slice.edgeColumns sector column previous current next) column (row + (slice.length : ℤ)) =
      columnRow slice.k (slice.edgeColumns sector column previous current next) column row := by
  obtain ⟨mixed, vertical, h⟩ := slice.edgeColumns_add_length sector column previous current next
  have heq := funext h
  have hshift := columnRow_translate slice.k (slice.edgeColumns sector column previous current next)
    0 (slice.length : ℤ) column row
  simp only [add_zero] at hshift
  rw [← hshift, heq]
  exact columnRow_add_affine (by have := slice.hk; omega) _ _ _ _ _ _

theorem columnRow_edgeColumns_add_phasePeriod (slice : ColumnSlice) (sector column row : ℤ)
    (previous current next : slice.Shape sector) :
    columnRow slice.k (slice.edgeColumns sector (column + (slice.phasePeriod : ℤ)) previous current next)
        (column + (slice.phasePeriod : ℤ)) row =
      columnRow slice.k (slice.edgeColumns sector column previous current next) column row := by
  obtain ⟨slope, rowSlope, constant, h⟩ := slice.edgeColumns_add_phasePeriod sector column previous current next
  have heq := funext h
  have hshift := columnRow_translate slice.k (slice.edgeColumns sector (column + (slice.phasePeriod : ℤ)) previous current next)
    (slice.phasePeriod : ℤ) 0 column row
  simp only [add_zero] at hshift
  rw [← hshift, heq]
  exact columnRow_add_affine (by have := slice.hk; omega) _ _ _ _ _ _

/-- The weight of an edge is the negative of its largest actual retained row. -/
def edgeWeight (slice : ColumnSlice) (sector : ℤ) (source target : slice.Vertex sector) : ℤ :=
  let column : ℤ := source.1.val
  let rowValues := (Finset.range slice.length).image (fun row : ℕ =>
    columnRow slice.k (slice.edgeColumns sector column source.2.1 source.2.2 target.2.2) column row)
  have hrows : (Finset.range slice.length).Nonempty := ⟨0, Finset.mem_range.mpr slice.length_pos⟩
  Neg.neg (rowValues.max' (hrows.image _))

theorem columnRow_le_neg_edgeWeight (slice : ColumnSlice) (sector : ℤ) (source target : slice.Vertex sector)
    (row : Fin slice.length) :
    columnRow slice.k (slice.edgeColumns sector source.1.val source.2.1 source.2.2 target.2.2) source.1.val row.val ≤
      -slice.edgeWeight sector source target := by
  unfold edgeWeight
  simp only [neg_neg]
  let value (r : ℕ) := columnRow slice.k (slice.edgeColumns sector source.1.val source.2.1 source.2.2 target.2.2)
    source.1.val r
  exact Finset.le_max' ((Finset.range slice.length).image value) (value row.val)
    (Finset.mem_image_of_mem value (Finset.mem_range.mpr row.isLt))

end ColumnSlice

end FLatticePaper.GeneralK
