import FLatticePaper.GeneralK.Parabolic
import Mathlib.Data.Rat.Floor

namespace FLatticePaper.GeneralK

/-- The $k$ harmonic parameters immediately above the requested rational slice. -/
def startingColumnIndices (k : ℤ) (c : ℚ) : Finset ℤ :=
  (Finset.range k.toNat).image (fun index : ℕ => ⌊(k : ℚ) * c⌋ + (index : ℤ) + 1)

theorem mem_startingColumnIndices {k index : ℤ} {c : ℚ} (hk : 0 ≤ k) :
    index ∈ startingColumnIndices k c ↔ ⌊(k : ℚ) * c⌋ + 1 ≤ index ∧ index ≤ ⌊(k : ℚ) * c⌋ + k := by
  rw [startingColumnIndices, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨(index - ⌊(k : ℚ) * c⌋ - 1).toNat, Finset.mem_range.mpr ?_, ?_⟩ <;> omega

theorem startingColumnIndices_nonempty {k : ℤ} (hk : 2 ≤ k) (c : ℚ) :
    (startingColumnIndices k c).Nonempty := by
  refine ⟨_, (mem_startingColumnIndices (by omega)).mpr ⟨le_rfl, ?_⟩⟩
  omega

private def startingColumnCandidate (k : ℤ) (b c : ℚ) (index : ℤ) : ℤ :=
  let s := (index : ℚ) / (k : ℚ)
  let t : ℤ := ⌊b - s + 1 / 2⌋
  ⌊-((k : ℚ) - 1) * s - (b - s - t) ^ 2 / (s - c)⌋

/-- The explicit integer starting entry $a_0$ of the rational column graph. -/
def startingColumnEntry (k : ℤ) (b c : ℚ) (hk : 2 ≤ k) : ℤ :=
  ((startingColumnIndices k c).image (startingColumnCandidate k b c)).max'
    ((startingColumnIndices_nonempty hk c).image _)

theorem startingColumnEntry_mem_growthSet {k : ℤ} (hk : 2 ≤ k) (b c : ℚ) :
    symmetricMatrix (startingColumnEntry k b c hk) b c ∈ growthSet k := by
  let a₀ := startingColumnEntry k b c hk
  have ha := Finset.max'_mem ((startingColumnIndices k c).image (startingColumnCandidate k b c))
    ((startingColumnIndices_nonempty hk c).image (startingColumnCandidate k b c))
  change a₀ ∈ (startingColumnIndices k c).image (startingColumnCandidate k b c) at ha
  obtain ⟨index, hindex, hmax⟩ := Finset.mem_image.mp ha
  let s := (index : ℚ) / (k : ℚ)
  let t : ℤ := ⌊b - s + 1 / 2⌋
  have hk' : 0 < (k : ℚ) := by exact_mod_cast (show 0 < k by omega)
  have hcs : c < s := by
    apply (lt_div_iff₀ hk').mpr
    rw [mul_comm]
    have hlo := ((mem_startingColumnIndices (by omega)).mp hindex).1
    have hcast : ((⌊(k : ℚ) * c⌋ : ℤ) : ℚ) + 1 ≤ index := by exact_mod_cast hlo
    exact (Int.lt_floor_add_one _).trans_le hcast
  let r := -((k : ℚ) - 1) * s - (b - s - t) ^ 2 / (s - c)
  have hf : (a₀ : ℚ) ≤ r := by rw [← hmax]; exact Int.floor_le r
  have hf' : (a₀ : ℝ) ≤ -((k : ℝ) - 1) * (s : ℝ) - ((b : ℝ) - s - (t : ℝ)) ^ 2 / ((s : ℝ) - c) := by
    have hcast : (a₀ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hf
    simpa [r] using hcast
  have hs : (s : ℝ) = (index : ℝ) / (k : ℝ) := by simp [s]
  have hcs' : 0 < (s : ℝ) - (c : ℝ) := sub_pos.mpr (by exact_mod_cast hcs)
  have hdecrement : (symmetricMatrix (-((k : ℝ) - 1) * (s : ℝ)) ((s : ℝ) + t) (s : ℝ) -
      symmetricMatrix (a₀ : ℝ) (b : ℝ) (c : ℝ)).PosSemidef := by
    let mixed := (s : ℝ) + t - (b : ℝ)
    let vertical := (s : ℝ) - (c : ℝ)
    have htop : 0 ≤ -((k : ℝ) - 1) * (s : ℝ) - a₀ - mixed ^ 2 / vertical := by
      have heq : ((b : ℝ) - s - t) ^ 2 = mixed ^ 2 := by dsimp [mixed]; ring
      rw [heq] at hf'
      linarith only [hf']
    have hmain := posSemidef_parabolic mixed vertical hcs'
    have hdiag : (symmetricMatrix (-((k : ℝ) - 1) * (s : ℝ) - a₀ - mixed ^ 2 / vertical) 0 0).PosSemidef := by
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (Matrix.isHermitian_iff_isSymm.mpr (isSymm_symmetricMatrix ..))
      intro x
      simp [star_trivial, symmetricMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have h := mul_nonneg htop (sq_nonneg (x 0))
      nlinarith only [h]
    convert hmain.add hdiag using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symmetricMatrix, mixed, vertical]
  have hbase : symmetricMatrix (-((k : ℝ) - 1) * (s : ℝ)) ((s : ℝ) + t) (s : ℝ) ∈ growthSet k := by
    rw [hs]
    exact harmonicMatrix_mem_growthSet hk index t
  have hgrowth := sub_mem_growthSet_of_posSemidef hk hbase hdecrement
  rwa [sub_sub_cancel] at hgrowth

private theorem integral_iff_exists_int (q : ℚ) : q.den = 1 ↔ ∃ integer : ℤ, q = integer := by
  constructor
  · intro h
    exact ⟨q.num, ((Rat.den_eq_one_iff q).mp h).symm⟩
  · rintro ⟨integer, rfl⟩
    exact Rat.den_intCast integer

private theorem den_mul_rat (q : ℚ) : (q.den : ℚ) * q = (q.num : ℚ) := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  calc
    _ = (q.den : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) := congrArg ((q.den : ℚ) * ·) q.num_div_den.symm
    _ = _ := by field_simp

private def ColumnLengthSpec (k : ℤ) (b c : ℚ) (length : ℕ) : Prop :=
  0 < length ∧ ((k : ℚ) * (length : ℚ) * b).den = 1 ∧ ((k : ℚ) * (length : ℚ) * c).den = 1

instance (k : ℤ) (b c : ℚ) (length : ℕ) : Decidable (ColumnLengthSpec k b c length) :=
  inferInstanceAs (Decidable (0 < length ∧ _ ∧ _))

private theorem exists_columnLength (k : ℤ) (b c : ℚ) : ∃ length, ColumnLengthSpec k b c length := by
  refine ⟨b.den * c.den, Nat.mul_pos b.den_pos c.den_pos, ?_, ?_⟩
  · apply (integral_iff_exists_int _).mpr
    refine ⟨k * c.den * b.num, ?_⟩
    push_cast
    linear_combination (k : ℚ) * (c.den : ℚ) * den_mul_rat b
  · apply (integral_iff_exists_int _).mpr
    refine ⟨k * b.den * c.num, ?_⟩
    push_cast
    linear_combination (k : ℚ) * (b.den : ℚ) * den_mul_rat c

/-- The least positive length $L$ clearing both $k b$ and $k c$. -/
def columnLength (k : ℤ) (b c : ℚ) : ℕ := Nat.find (exists_columnLength k b c)

theorem columnLength_pos (k : ℤ) (b c : ℚ) : 0 < columnLength k b c :=
  (Nat.find_spec (exists_columnLength k b c)).1

theorem columnLength_spec (k : ℤ) (b c : ℚ) :
    (∃ v : ℤ, (k : ℚ) * (columnLength k b c : ℚ) * b = v) ∧
    (∃ w : ℤ, (k : ℚ) * (columnLength k b c : ℚ) * c = w) := by
  have hp := (Nat.find_spec (exists_columnLength k b c)).2
  exact ⟨(integral_iff_exists_int _).mp hp.1, (integral_iff_exists_int _).mp hp.2⟩

theorem columnLength_min (k : ℤ) (b c : ℚ) {length : ℕ} (hpos : 0 < length)
    (hb : ∃ v : ℤ, (k : ℚ) * (length : ℚ) * b = v) (hc : ∃ w : ℤ, (k : ℚ) * (length : ℚ) * c = w) :
    columnLength k b c ≤ length :=
  Nat.find_min' _ ⟨hpos, (integral_iff_exists_int _).mpr hb, (integral_iff_exists_int _).mpr hc⟩

private def ColumnPhaseSpec (k : ℤ) (u v : ℚ) (period : ℕ) : Prop :=
  0 < period ∧ ((period : ℚ) * u).den = 1 ∧ ((period : ℚ) * v / (k : ℚ)).den = 1 ∧
    ((period : ℚ) ^ 2 * u / 2).den = 1

instance (k : ℤ) (u v : ℚ) (period : ℕ) : Decidable (ColumnPhaseSpec k u v period) :=
  inferInstanceAs (Decidable (0 < period ∧ _ ∧ _ ∧ _))

private theorem exists_columnPhasePeriod (k : ℤ) (u v : ℚ) : ∃ period, ColumnPhaseSpec k u v period := by
  let w := v / (k : ℚ)
  let half := u / 2
  let period := u.den * w.den * half.den
  refine ⟨period, Nat.mul_pos (Nat.mul_pos u.den_pos w.den_pos) half.den_pos, ?_, ?_, ?_⟩
  · apply (integral_iff_exists_int _).mpr
    refine ⟨(w.den : ℤ) * (half.den : ℤ) * u.num, ?_⟩
    dsimp only [period]
    push_cast
    linear_combination (w.den : ℚ) * (half.den : ℚ) * den_mul_rat u
  · apply (integral_iff_exists_int _).mpr
    refine ⟨(u.den : ℤ) * (half.den : ℤ) * w.num, ?_⟩
    rw [mul_div_assoc]
    change (period : ℚ) * w = _
    dsimp only [period]
    push_cast
    linear_combination (u.den : ℚ) * (half.den : ℚ) * den_mul_rat w
  · apply (integral_iff_exists_int _).mpr
    refine ⟨(period : ℤ) * (u.den : ℤ) * (w.den : ℤ) * half.num, ?_⟩
    rw [mul_div_assoc]
    change (period : ℚ) ^ 2 * half = _
    push_cast
    have hperiod : (period : ℚ) = (u.den : ℚ) * (w.den : ℚ) * (half.den : ℚ) := by simp [period]
    nth_rw 1 [pow_two, hperiod]
    linear_combination (period : ℚ) * (u.den : ℚ) * (w.den : ℚ) * den_mul_rat half

/-- The least positive horizontal phase period $S$ of the reference row data. -/
def columnPhasePeriod (k : ℤ) (u v : ℚ) : ℕ := Nat.find (exists_columnPhasePeriod k u v)

theorem columnPhasePeriod_pos (k : ℤ) (u v : ℚ) : 0 < columnPhasePeriod k u v :=
  (Nat.find_spec (exists_columnPhasePeriod k u v)).1

theorem columnPhasePeriod_spec (k : ℤ) (u v : ℚ) :
    (∃ slope : ℤ, (columnPhasePeriod k u v : ℚ) * u = slope) ∧
    (∃ slope : ℤ, (columnPhasePeriod k u v : ℚ) * v / (k : ℚ) = slope) ∧
    (∃ constant : ℤ, (columnPhasePeriod k u v : ℚ) ^ 2 * u / 2 = constant) := by
  have hp := (Nat.find_spec (exists_columnPhasePeriod k u v)).2
  exact ⟨(integral_iff_exists_int _).mp hp.1, (integral_iff_exists_int _).mp hp.2.1,
    (integral_iff_exists_int _).mp hp.2.2⟩

theorem columnPhasePeriod_min (k : ℤ) (u v : ℚ) {period : ℕ} (hpos : 0 < period)
    (hu : ∃ slope : ℤ, (period : ℚ) * u = slope) (hv : ∃ slope : ℤ, (period : ℚ) * v / (k : ℚ) = slope)
    (hc : ∃ constant : ℤ, (period : ℚ) ^ 2 * u / 2 = constant) : columnPhasePeriod k u v ≤ period :=
  Nat.find_min' _ ⟨hpos, (integral_iff_exists_int _).mpr hu, (integral_iff_exists_int _).mpr hv,
    (integral_iff_exists_int _).mpr hc⟩

/-- The two rational physical entries fixed while constructing a column graph. -/
structure ColumnSlice where
  k : ℤ
  hk : 2 ≤ k
  mixed : ℚ
  vertical : ℚ

namespace ColumnSlice

def a₀ (slice : ColumnSlice) : ℤ := startingColumnEntry slice.k slice.mixed slice.vertical slice.hk

def u (slice : ColumnSlice) : ℚ := (slice.a₀ : ℚ) - 2 * slice.mixed + slice.vertical

def v (slice : ColumnSlice) : ℚ := (slice.k : ℚ) * (slice.mixed - slice.vertical)

def w (slice : ColumnSlice) : ℚ := (slice.k : ℚ) ^ 2 * slice.vertical

def length (slice : ColumnSlice) : ℕ := columnLength slice.k slice.mixed slice.vertical

def phasePeriod (slice : ColumnSlice) : ℕ := columnPhasePeriod slice.k slice.u slice.v

theorem length_pos (slice : ColumnSlice) : 0 < slice.length := columnLength_pos ..

theorem phasePeriod_pos (slice : ColumnSlice) : 0 < slice.phasePeriod := columnPhasePeriod_pos ..

/-- The rational polynomial whose floor is the sector reference height. -/
def referencePolynomial (slice : ColumnSlice) (sector column row : ℤ) : ℚ :=
  slice.u * (column : ℚ) ^ 2 / 2 + slice.v * (column : ℚ) * (row : ℚ) +
    slice.w * (row : ℚ) ^ 2 / 2 +
    ((sector : ℚ) - slice.w * (slice.length : ℚ) ^ 2 / 2) / (slice.length : ℚ) * (row : ℚ)

def reference (slice : ColumnSlice) (sector : ℤ) : Field :=
  fun point => ⌊slice.referencePolynomial sector point.1 point.2⌋

/-- Translation by the least phase period adds an integer affine height in
the physical coordinates. In retained coordinates its row slope is a multiple of `k`. -/
theorem reference_add_phasePeriod (slice : ColumnSlice) (sector : ℤ) :
    ∃ slope rowSlope constant : ℤ, ∀ column row,
      slice.reference sector (column + (slice.phasePeriod : ℤ), row) =
        slice.reference sector (column, row) + (slope * column + slice.k * rowSlope * row + constant) := by
  obtain ⟨⟨slope, hs⟩, ⟨rowSlope, hr⟩, ⟨constant, hc⟩⟩ := columnPhasePeriod_spec slice.k slice.u slice.v
  have hk : (slice.k : ℚ) ≠ 0 := by exact_mod_cast (show slice.k ≠ 0 from ne_of_gt (by have := slice.hk; omega))
  have hr' : (slice.phasePeriod : ℚ) * slice.v = (slice.k : ℚ) * (rowSlope : ℚ) := by
    exact ((div_eq_iff hk).mp hr).trans (mul_comm _ _)
  change (slice.phasePeriod : ℚ) * slice.u = (slope : ℚ) at hs
  change (slice.phasePeriod : ℚ) ^ 2 * slice.u / 2 = (constant : ℚ) at hc
  refine ⟨slope, rowSlope, constant, fun column row => ?_⟩
  have heq : slice.referencePolynomial sector (column + (slice.phasePeriod : ℤ)) row =
      slice.referencePolynomial sector column row + ((slope * column + slice.k * rowSlope * row + constant : ℤ) : ℚ) := by
    simp only [referencePolynomial, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    linear_combination (column : ℚ) * hs + (row : ℚ) * hr' + hc
  simp only [reference, heq, Int.floor_add_intCast]

/-- Translation by the least row period adds exactly `v L i + w L r + d`. -/
theorem reference_add_length (slice : ColumnSlice) (sector : ℤ) :
    ∃ mixed vertical : ℤ, slice.v * (slice.length : ℚ) = mixed ∧
      slice.w * (slice.length : ℚ) = (slice.k : ℚ) * vertical ∧
      ∀ column row, slice.reference sector (column, row + (slice.length : ℤ)) =
        slice.reference sector (column, row) + (mixed * column + slice.k * vertical * row + sector) := by
  obtain ⟨⟨bL, hb⟩, ⟨cL, hc⟩⟩ := columnLength_spec slice.k slice.mixed slice.vertical
  change (slice.k : ℚ) * (slice.length : ℚ) * slice.mixed = bL at hb
  change (slice.k : ℚ) * (slice.length : ℚ) * slice.vertical = cL at hc
  have hv : slice.v * (slice.length : ℚ) = ((bL - cL : ℤ) : ℚ) := by
    simp only [v, Int.cast_sub]
    linear_combination hb - hc
  have hw : slice.w * (slice.length : ℚ) = (slice.k : ℚ) * (cL : ℚ) := by
    simp only [w]
    linear_combination (slice.k : ℚ) * hc
  have hl : (slice.length : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt slice.length_pos
  have hconstant := div_mul_cancel₀ ((sector : ℚ) - slice.w * (slice.length : ℚ) ^ 2 / 2) hl
  refine ⟨bL - cL, cL, hv, hw, fun column row => ?_⟩
  have heq : slice.referencePolynomial sector column (row + (slice.length : ℤ)) =
      slice.referencePolynomial sector column row + (((bL - cL) * column + slice.k * cL * row + sector : ℤ) : ℚ) := by
    simp only [referencePolynomial, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    simp only [Int.cast_sub] at hv
    linear_combination (column : ℚ) * hv + (row : ℚ) * hw + hconstant
  simp only [reference, heq, Int.floor_add_intCast]

end ColumnSlice

private theorem ceilDiv_add_mul {k : ℤ} (hk : k ≠ 0) (value constant : ℤ) :
    ceilDiv (value + k * constant) k = ceilDiv value k + constant := by
  unfold ceilDiv
  rw [show -(value + k * constant) = -value + (-constant) * k by ring, Int.add_mul_ediv_right _ _ hk]
  ring

/-- Adding an integer affine height in the physical coordinates leaves the
literal two-ceiling row unchanged. -/
theorem columnRow_add_affine {k : ℤ} (hk : k ≠ 0) (field : Field) (slope rowSlope constant column row : ℤ) :
    columnRow k (fun site => field site + (slope * site.1 + k * rowSlope * site.2 + constant)) column row =
      columnRow k field column row := by
  unfold columnRow
  dsimp only
  have hpos : (k - 1) * (field (column + 1, row) + (slope * (column + 1) + k * rowSlope * row + constant)) +
      (field (column + 1, row + 1) + (slope * (column + 1) + k * rowSlope * (row + 1) + constant)) =
    ((k - 1) * field (column + 1, row) + field (column + 1, row + 1)) +
      k * (slope * (column + 1) + k * rowSlope * row + constant + rowSlope) := by ring
  have hneg : (k - 1) * (field (column - 1, row) + (slope * (column - 1) + k * rowSlope * row + constant)) +
      (field (column - 1, row - 1) + (slope * (column - 1) + k * rowSlope * (row - 1) + constant)) =
    ((k - 1) * field (column - 1, row) + field (column - 1, row - 1)) +
      k * (slope * (column - 1) + k * rowSlope * row + constant - rowSlope) := by ring
  rw [hpos, hneg, ceilDiv_add_mul hk, ceilDiv_add_mul hk]
  ring

end FLatticePaper.GeneralK
