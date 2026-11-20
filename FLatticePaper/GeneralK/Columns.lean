import FLatticePaper.Graph
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace FLatticePaper.GeneralK

/-- The sites with horizontal inputs on the physical `F^(k)` graph. -/
def Retained (k : ℤ) (site : Site) : Prop := (site.1 + site.2) % k = 0

instance (k : ℤ) (site : Site) : Decidable (Retained k site) :=
  inferInstanceAs (Decidable ((site.1 + site.2) % k = 0))

def incomingNeg (k : ℤ) (site : Site) : Site :=
  if Retained k site then (site.1 - 1, site.2) else (site.1, site.2 - 1)

def incomingPos (k : ℤ) (site : Site) : Site :=
  if Retained k site then (site.1 + 1, site.2) else (site.1, site.2 + 1)

def laplacian (k : ℤ) (field : Field) (site : Site) : ℤ :=
  (field (incomingNeg k site) - field site) + (field (incomingPos k site) - field site)

def Superharmonic (k : ℤ) (field : Field) : Prop := ∀ site, laplacian k field site ≤ 0

theorem laplacian_two (field : Field) (site : Site) : laplacian 2 field site = FLatticePaper.laplacian field site :=
  rfl

/-- A site at height `offset` above the retained site `(i, kr-i)`. -/
def columnSite (k column row offset : ℤ) : Site := (column, k * row - column + offset)

theorem columnSite_phase (k column row offset : ℤ) :
    ((columnSite k column row offset).1 + (columnSite k column row offset).2) % k = offset % k := by
  change (column + (k * row - column + offset)) % k = offset % k
  rw [show column + (k * row - column + offset) = offset + row * k by ring,
    Int.add_mul_emod_self_right]

theorem retained_columnSite (k column row : ℤ) : Retained k (columnSite k column row 0) := by
  simp [Retained, columnSite_phase]

theorem columnSite_coordinates (k : ℤ) (site : Site) :
    columnSite k site.1 ((site.1 + site.2) / k) ((site.1 + site.2) % k) = site := by
  refine Prod.ext rfl ?_
  change k * ((site.1 + site.2) / k) - site.1 + (site.1 + site.2) % k = site.2
  have h := Int.emod_add_mul_ediv (site.1 + site.2) k
  omega

theorem incomingPos_columnSite (k column row : ℤ) :
    incomingPos k (columnSite k column row 0) = columnSite k (column + 1) row 1 := by
  rw [incomingPos, if_pos (retained_columnSite k column row)]
  refine Prod.ext rfl ?_
  simp only [columnSite, add_zero]
  ring

theorem incomingNeg_columnSite (k column row : ℤ) :
    incomingNeg k (columnSite k column row 0) = columnSite k (column - 1) (row - 1) (k - 1) := by
  rw [incomingNeg, if_pos (retained_columnSite k column row)]
  refine Prod.ext rfl ?_
  simp only [columnSite, add_zero]
  ring

/-- The integer interpolation with slopes `q+1` followed by `q`, where
`last-first = k*q + r` and the first `r` steps have the larger slope. -/
def interpolate (k first last offset : ℤ) : ℤ :=
  first + offset * ((last - first) / k) + min offset ((last - first) % k)

theorem interpolate_zero {k : ℤ} (hk : 0 < k) (first last : ℤ) :
    interpolate k first last 0 = first := by
  have h := Int.emod_nonneg (last - first) (ne_of_gt hk)
  simp [interpolate, min_eq_left h]

theorem interpolate_top {k : ℤ} (hk : 0 < k) (first last : ℤ) :
    interpolate k first last k = last := by
  have hr := Int.emod_lt_of_pos (last - first) hk
  have hdiv := Int.emod_add_mul_ediv (last - first) k
  simp only [interpolate, min_eq_right hr.le]
  omega

/-- The integer ceiling of a quotient by a positive denominator. -/
def ceilDiv (numerator denominator : ℤ) : ℤ := -((-numerator) / denominator)

private theorem ceilDiv_eq {k n value : ℤ} (hk : 0 < k)
    (hlo : (value - 1) * k < n) (hhi : n ≤ value * k) : ceilDiv n k = value := by
  have hlo' : -value ≤ (-n) / k := (Int.le_ediv_iff_mul_le hk).mpr (by
    rw [neg_mul]
    omega)
  have hhi' : (-n) / k < -value + 1 := (Int.ediv_lt_iff_lt_mul hk).mpr (by
    rw [show (-value + 1) * k = -((value - 1) * k) by ring]
    omega)
  unfold ceilDiv
  omega

theorem interpolate_first {k : ℤ} (hk : 2 ≤ k) (first last : ℤ) :
    interpolate k first last 1 = ceilDiv ((k - 1) * first + last) k := by
  let q := (last - first) / k
  let r := (last - first) % k
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega : k ≠ 0)
  have hrk : r < k := Int.emod_lt_of_pos _ (by omega)
  have hdiv : r + k * q = last - first := Int.emod_add_mul_ediv _ _
  have hn : (k - 1) * first + last = (first + q) * k + r := by
    linear_combination -hdiv
  change first + 1 * q + min 1 r = _
  by_cases hr : r = 0
  · rw [hr, min_eq_right (by decide : (0 : ℤ) ≤ 1), one_mul, add_zero]
    symm
    apply ceilDiv_eq (by omega : 0 < k) <;> rw [hn, hr, add_zero]
    rw [sub_mul, one_mul]
    omega
  · have hmin : 1 ≤ r := by omega
    rw [min_eq_left hmin, one_mul]
    symm
    apply ceilDiv_eq (by omega : 0 < k) <;> rw [hn]
    · rw [add_sub_cancel_right]
      omega
    · simp only [add_mul, one_mul]
      omega

theorem interpolate_last {k : ℤ} (hk : 2 ≤ k) (first last : ℤ) :
    interpolate k first last (k - 1) = ceilDiv (first + (k - 1) * last) k := by
  let q := (last - first) / k
  let r := (last - first) % k
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega : k ≠ 0)
  have hrk : r < k := Int.emod_lt_of_pos _ (by omega)
  have hdiv : r + k * q = last - first := Int.emod_add_mul_ediv _ _
  have hn : first + (k - 1) * last = (last - q) * k - r := by linear_combination hdiv
  change first + (k - 1) * q + min (k - 1) r = _
  rw [min_eq_right (by omega : r ≤ k - 1), show first + (k - 1) * q + r = last - q by
    linear_combination hdiv]
  symm
  apply ceilDiv_eq (by omega : 0 < k) <;> rw [hn]
  · rw [sub_mul, one_mul]
    omega
  · omega

/-- Interpolate consecutive retained sites in every physical column. -/
def liftColumns (k : ℤ) (columns : Field) (site : Site) : ℤ :=
  let sum := site.1 + site.2
  let row := sum / k
  interpolate k (columns (site.1, row)) (columns (site.1, row + 1)) (sum % k)

theorem liftColumns_columnSite {k : ℤ} (hk : 0 < k) (columns : Field) (column row offset : ℤ)
    (hlo : 0 ≤ offset) (hhi : offset < k) :
    liftColumns k columns (columnSite k column row offset) =
      interpolate k (columns (column, row)) (columns (column, row + 1)) offset := by
  have hsum : column + (k * row - column + offset) = offset + row * k := by ring
  have hrow : (column + (k * row - column + offset)) / k = row := by
    rw [hsum, Int.add_mul_ediv_right _ _ (ne_of_gt hk), Int.ediv_eq_zero_of_lt hlo hhi, zero_add]
  change interpolate k (columns (column, (column + (k * row - column + offset)) / k))
    (columns (column, (column + (k * row - column + offset)) / k + 1))
    (((columnSite k column row offset).1 + (columnSite k column row offset).2) % k) = _
  rw [columnSite_phase, Int.emod_eq_of_lt hlo hhi, hrow]

theorem liftColumns_closedChain {k : ℤ} (hk : 0 < k) (columns : Field) (column row offset : ℤ)
    (hlo : 0 ≤ offset) (hhi : offset ≤ k) :
    liftColumns k columns (columnSite k column row offset) =
      interpolate k (columns (column, row)) (columns (column, row + 1)) offset := by
  by_cases heq : offset = k
  · subst offset
    have htop : columnSite k column row k = columnSite k column (row + 1) 0 := by
      refine Prod.ext rfl ?_
      simp only [columnSite]
      ring
    rw [htop, liftColumns_columnSite hk columns column (row + 1) 0 (by omega) hk,
      interpolate_zero hk, interpolate_top hk]
  · exact liftColumns_columnSite hk columns column row offset hlo (by omega)

/-- The reduced operator of `eq:columnrow` in physical column coordinates. -/
def columnRow (k : ℤ) (columns : Field) (column row : ℤ) : ℤ :=
  ceilDiv ((k - 1) * columns (column + 1, row) + columns (column + 1, row + 1)) k +
  ceilDiv ((k - 1) * columns (column - 1, row) + columns (column - 1, row - 1)) k -
  2 * columns (column, row)

/-- At every retained vertex, the physical Laplacian of the literal lift is
exactly the two-ceiling column row. This also covers coincident chain ports at `k=2`. -/
theorem laplacian_liftColumns_columnSite {k : ℤ} (hk : 2 ≤ k) (columns : Field) (column row : ℤ) :
    laplacian k (liftColumns k columns) (columnSite k column row 0) = columnRow k columns column row := by
  have hpos : 0 < k := by omega
  unfold laplacian columnRow
  rw [incomingNeg_columnSite, incomingPos_columnSite,
    liftColumns_columnSite hpos columns (column - 1) (row - 1) (k - 1) (by omega) (by omega),
    liftColumns_columnSite hpos columns (column + 1) row 1 (by omega) (by omega),
    liftColumns_columnSite hpos columns column row 0 (by omega) hpos,
    interpolate_zero hpos, interpolate_first hk, interpolate_last hk, sub_add_cancel]
  simp only [add_comm (columns (column - 1, row - 1))]
  ring

/-- Inside a chain the lift has a slope drop precisely at the nonzero
remainder of the endpoint difference. -/
theorem laplacian_liftColumns_openChain {k : ℤ} (hk : 2 ≤ k) (columns : Field)
    (column row offset : ℤ) (hlo : 0 < offset) (hhi : offset < k) :
    laplacian k (liftColumns k columns) (columnSite k column row offset) =
      if offset = (columns (column, row + 1) - columns (column, row)) % k then -1 else 0 := by
  have hpos : 0 < k := by omega
  have hphase : ¬ Retained k (columnSite k column row offset) := by
    rw [Retained, columnSite_phase, Int.emod_eq_of_lt hlo.le hhi]
    omega
  have hneg : incomingNeg k (columnSite k column row offset) = columnSite k column row (offset - 1) := by
    rw [incomingNeg, if_neg hphase]
    exact Prod.ext rfl (by simp only [columnSite]; ring)
  have hplus : incomingPos k (columnSite k column row offset) = columnSite k column row (offset + 1) := by
    rw [incomingPos, if_neg hphase]
    exact Prod.ext rfl (by simp only [columnSite]; ring)
  unfold laplacian
  rw [hneg, hplus,
    liftColumns_closedChain hpos columns column row (offset - 1) (by omega) (by omega),
    liftColumns_closedChain hpos columns column row (offset + 1) (by omega) (by omega),
    liftColumns_closedChain hpos columns column row offset hlo.le hhi.le]
  let first := columns (column, row)
  let quotient := (columns (column, row + 1) - first) / k
  let remainder := (columns (column, row + 1) - first) % k
  change (first + (offset - 1) * quotient + min (offset - 1) remainder -
      (first + offset * quotient + min offset remainder)) +
    (first + (offset + 1) * quotient + min (offset + 1) remainder -
      (first + offset * quotient + min offset remainder)) =
      if offset = remainder then -1 else 0
  by_cases heq : offset = remainder
  · rw [if_pos heq, min_eq_left (by omega : offset - 1 ≤ remainder), min_eq_left heq.le,
      min_eq_right (by omega : remainder ≤ offset + 1)]
    linear_combination -heq
  · rw [if_neg heq]
    by_cases hlt : offset < remainder
    · rw [min_eq_left (by omega : offset - 1 ≤ remainder), min_eq_left hlt.le,
        min_eq_left (by omega : offset + 1 ≤ remainder)]
      ring
    · rw [min_eq_right (by omega : remainder ≤ offset - 1), min_eq_right (by omega : remainder ≤ offset),
        min_eq_right (by omega : remainder ≤ offset + 1)]
      ring

/-- Superharmonicity of the column lift is exactly the reduced row condition. -/
theorem superharmonic_liftColumns_iff {k : ℤ} (hk : 2 ≤ k) (columns : Field) :
    Superharmonic k (liftColumns k columns) ↔ ∀ column row, columnRow k columns column row ≤ 0 := by
  constructor
  · intro h column row
    rw [← laplacian_liftColumns_columnSite hk]
    exact h (columnSite k column row 0)
  · intro h site
    let offset := (site.1 + site.2) % k
    have hcoordinates := columnSite_coordinates k site
    change columnSite k site.1 ((site.1 + site.2) / k) offset = site at hcoordinates
    rw [← hcoordinates]
    by_cases heq : offset = 0
    · rw [heq, laplacian_liftColumns_columnSite hk]
      exact h _ _
    · have hlo : 0 < offset := by
        have := Int.emod_nonneg (site.1 + site.2) (by omega : k ≠ 0)
        omega
      have hhi : offset < k := Int.emod_lt_of_pos _ (by omega)
      rw [laplacian_liftColumns_openChain hk _ _ _ _ hlo hhi]
      split <;> decide

end FLatticePaper.GeneralK
