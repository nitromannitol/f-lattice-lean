import FLattice.Auxiliary.PlusEvenCells

/-!
# Actual odd-native predecessors of the shared representative cells

The edge is first taken in physical coordinates using the odd native
parity rule, and only then decoded by the literal canonical-cell map.
Every seam is proved by recovering a valid signed lift. These statements
are geometry only: they do not assert a height, deficit or rank property.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- The actual odd-native incoming point, horizontal exactly when `x+y+1` is even.
Index zero is the negative direction and index one the positive direction. -/
def incomingPoint (x y : ℤ) (i : Fin 2) : ℤ × ℤ :=
  if (x + y + 1) % 2 = 0 then
    (x + (if i = 0 then -1 else 1), y)
  else
    (x, y + (if i = 0 then -1 else 1))

/-- Decode the actual incoming point of a physical representative. -/
def incomingCell {m : Parameter} (c : Cell m) (i : Fin 2) : Cell m :=
  cellOf m (incomingPoint c.x c.y i).1 (incomingPoint c.x c.y i).2

/-- Every even-parity translation commutes with the actual incoming edge. -/
theorem incomingPoint_add_of_even (x y a b : ℤ) (i : Fin 2)
    (hEven : (a + b) % 2 = 0) :
    incomingPoint (x + a) (y + b) i =
      ((incomingPoint x y i).1 + a, (incomingPoint x y i).2 + b) := by
  have hParity : (x + a + (y + b) + 1) % 2 = (x + y + 1) % 2 := by omega
  unfold incomingPoint
  rw [hParity]
  split <;> apply Prod.ext <;> dsimp <;> omega

/-- Incoming-point decoding is invariant under arbitrary signed periods. -/
theorem cellOf_incomingPoint_add_periods (m : Parameter) (x y k q : ℤ) (i : Fin 2) :
    cellOf m (incomingPoint (x + 2 * m.val * k + 2 * halfPeriod m * q)
        (y + 2 * k) i).1
      (incomingPoint (x + 2 * m.val * k + 2 * halfPeriod m * q)
        (y + 2 * k) i).2 =
      cellOf m (incomingPoint x y i).1 (incomingPoint x y i).2 := by
  have hEven : (2 * m.val * k + 2 * halfPeriod m * q + 2 * k) % 2 = 0 := by
    have h : 2 * m.val * k + 2 * halfPeriod m * q + 2 * k =
        2 * (m.val * k + halfPeriod m * q + k) := by ring
    rw [h]
    omega
  have hPoint := incomingPoint_add_of_even x y
    (2 * m.val * k + 2 * halfPeriod m * q) (2 * k) i hEven
  rw [← add_assoc] at hPoint
  rw [hPoint]
  change cellOf m ((incomingPoint x y i).1 +
      (2 * m.val * k + 2 * halfPeriod m * q))
      ((incomingPoint x y i).2 + 2 * k) = _
  rw [← add_assoc]
  exact cellOf_add_periods m (incomingPoint x y i).1 (incomingPoint x y i).2 k q

/-- At every signed lift, the decoded input is the representative's incoming cell. -/
theorem cellOf_incomingPoint_lifted_cell (m : Parameter) (c : Cell m)
    (k q : ℤ) (i : Fin 2) :
    cellOf m (incomingPoint (c.x + 2 * m.val * k + 2 * halfPeriod m * q)
        (2 * k + c.y) i).1
      (incomingPoint (c.x + 2 * m.val * k + 2 * halfPeriod m * q)
        (2 * k + c.y) i).2 = incomingCell c i := by
  rw [add_comm (2 * k) c.y]
  exact cellOf_incomingPoint_add_periods m c.x c.y k q i

private theorem incomingPoint_at_cell {m : Parameter} (c : Cell m) (i : Fin 2) :
    incomingPoint c.x c.y i =
      if ((c.e.val : ℤ) + (c.v.val : ℤ) + 1) % 2 = 0 then
        (c.x + (if i = 0 then -1 else 1), c.y)
      else (c.x, c.y + (if i = 0 then -1 else 1)) := by
  have h : c.x + c.y + 1 =
      2 * (m.val * c.r + c.s) + ((c.e.val : ℤ) + (c.v.val : ℤ) + 1) := by
    unfold Cell.x Cell.y
    ring
  have hParity : (c.x + c.y + 1) % 2 = ((c.e.val : ℤ) + (c.v.val : ℤ) + 1) % 2 := by
    rw [h]
    omega
  simp only [incomingPoint, hParity]

private theorem incomingCell_fields_of_lift {m : Parameter} (c : Cell m) (i : Fin 2)
    (r s : ℤ) (e v : Fin 2) (k q : ℤ)
    (hr0 : 0 ≤ r) (hrm : r ≤ m.val + 1)
    (hs0 : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1))
    (hx : (incomingPoint c.x c.y i).1 =
      2 * m.val * r + 2 * s + (v.val : ℤ) + 2 * m.val * k + 2 * halfPeriod m * q)
    (hy : (incomingPoint c.x c.y i).2 = 2 * k + (e.val : ℤ)) :
    (incomingCell c i).r = r ∧ (incomingCell c i).s = s ∧
      (incomingCell c i).e = e ∧ (incomingCell c i).v = v := by
  let d : Cell m := ⟨r, s, e, v, hr0, hrm, hs0, hsm, hMissing⟩
  have hd : incomingCell c i = d := by
    unfold incomingCell
    rw [hx, hy]
    exact cellOf_lifted_cell m d k q
  rw [hd]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The upward input of every 00 cell. -/
theorem incomingCell_00_up {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) :
    (incomingCell c 1).r = c.r ∧ (incomingCell c 1).s = c.s ∧
      (incomingCell c 1).e = 1 ∧ (incomingCell c 1).v = 0 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 1 (c.r) (c.s) 1 0 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]

/-- The ordinary downward input subtracts the diagonal period. -/
theorem incomingCell_00_down_inner {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hr : c.r ≤ m.val) (hEnd : ¬(c.r = m.val ∧ c.s = m.val - 1)) :
    (incomingCell c 0).r = c.r + 1 ∧ (incomingCell c 0).s = c.s ∧
      (incomingCell c 0).e = 1 ∧ (incomingCell c 0).v = 0 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 0 (c.r + 1) (c.s) 1 0 (-1) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]
    ring
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]

/-- The penultimate 00 endpoint crosses both period seams. -/
theorem incomingCell_00_down_penultimate {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hr : c.r = m.val) (hs : c.s = m.val - 1) :
    (incomingCell c 0).r = 0 ∧ (incomingCell c 0).s = 0 ∧
      (incomingCell c 0).e = 1 ∧ (incomingCell c 0).v = 0 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 0 (0) (0) 1 0 (-1) (1)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs]
    ring
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs]

/-- The top 00 row crosses both period seams. -/
theorem incomingCell_00_down_top {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hr : c.r = m.val + 1) :
    (incomingCell c 0).r = 0 ∧ (incomingCell c 0).s = c.s + 1 ∧
      (incomingCell c 0).e = 1 ∧ (incomingCell c 0).v = 0 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 0 (0) (c.s + 1) 1 0 (-1) (1)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr]
    ring
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr]

/-- The left input of every 01 cell. -/
theorem incomingCell_01_left {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) :
    (incomingCell c 0).r = c.r ∧ (incomingCell c 0).s = c.s ∧
      (incomingCell c 0).e = 0 ∧ (incomingCell c 0).v = 0 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 0 (c.r) (c.s) 0 0 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]

/-- The ordinary right input of a 01 cell. -/
theorem incomingCell_01_right_inner {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hs : c.s ≤ m.val - 2) (hEnd : ¬(c.r = m.val + 1 ∧ c.s = m.val - 2)) :
    (incomingCell c 1).r = c.r ∧ (incomingCell c 1).s = c.s + 1 ∧
      (incomingCell c 1).e = 0 ∧ (incomingCell c 1).v = 0 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 1 (c.r) (c.s + 1) 0 0 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]
    ring
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]

/-- The last-column right input carries into the next row. -/
theorem incomingCell_01_right_last {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hs : c.s = m.val - 1) :
    (incomingCell c 1).r = c.r + 1 ∧ (incomingCell c 1).s = 0 ∧
      (incomingCell c 1).e = 0 ∧ (incomingCell c 1).v = 0 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 1 (c.r + 1) (0) 0 0 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hs]
    ring
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hs]

/-- The right input at the truncated top endpoint wraps horizontally. -/
theorem incomingCell_01_right_top_endpoint {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hr : c.r = m.val + 1) (hs : c.s = m.val - 2) :
    (incomingCell c 1).r = 0 ∧ (incomingCell c 1).s = 0 ∧
      (incomingCell c 1).e = 0 ∧ (incomingCell c 1).v = 0 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 1 (0) (0) 0 0 (0) (1)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs]
    ring
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs]

/-- The right input of every 10 cell. -/
theorem incomingCell_10_right {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) :
    (incomingCell c 1).r = c.r ∧ (incomingCell c 1).s = c.s ∧
      (incomingCell c 1).e = 1 ∧ (incomingCell c 1).v = 1 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 1 (c.r) (c.s) 1 1 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]

/-- The ordinary left input of a 10 cell. -/
theorem incomingCell_10_left_of_pos {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hs : 1 ≤ c.s) :
    (incomingCell c 0).r = c.r ∧ (incomingCell c 0).s = c.s - 1 ∧
      (incomingCell c 0).e = 1 ∧ (incomingCell c 0).v = 1 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 0 (c.r) (c.s - 1) 1 1 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]
    ring
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]

/-- The inner left carry of a 10 cell. -/
theorem incomingCell_10_left_of_zero {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hs : c.s = 0) (hr : 1 ≤ c.r) :
    (incomingCell c 0).r = c.r - 1 ∧ (incomingCell c 0).s = m.val - 1 ∧
      (incomingCell c 0).e = 1 ∧ (incomingCell c 0).v = 1 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 0 (c.r - 1) (m.val - 1) 1 1 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hs]
    ring
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hs]

/-- The left input at 10(0,0) wraps by a negative horizontal period. -/
theorem incomingCell_10_left_origin {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hr : c.r = 0) (hs : c.s = 0) :
    (incomingCell c 0).r = m.val + 1 ∧ (incomingCell c 0).s = m.val - 2 ∧
      (incomingCell c 0).e = 1 ∧ (incomingCell c 0).v = 1 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 0 (m.val + 1) (m.val - 2) 1 1 (0) (-1)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs]
    ring
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs]

/-- The downward input of every 11 cell. -/
theorem incomingCell_11_down {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) :
    (incomingCell c 0).r = c.r ∧ (incomingCell c 0).s = c.s ∧
      (incomingCell c 0).e = 0 ∧ (incomingCell c 0).v = 1 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 0 (c.r) (c.s) 0 1 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]

/-- The ordinary upward input adds the diagonal period. -/
theorem incomingCell_11_up_of_pos {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hr : 1 ≤ c.r) :
    (incomingCell c 1).r = c.r - 1 ∧ (incomingCell c 1).s = c.s ∧
      (incomingCell c 1).e = 0 ∧ (incomingCell c 1).v = 1 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 1 (c.r - 1) (c.s) 0 1 (1) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]
    ring
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod]

/-- The upward input at 11(0,0) crosses both period seams. -/
theorem incomingCell_11_up_origin {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hr : c.r = 0) (hs : c.s = 0) :
    (incomingCell c 1).r = m.val ∧ (incomingCell c 1).s = m.val - 1 ∧
      (incomingCell c 1).e = 0 ∧ (incomingCell c 1).v = 1 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 1 (m.val) (m.val - 1) 0 1 (1) (-1)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs]
    ring
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs]

/-- The rest of the low 11 row crosses both period seams. -/
theorem incomingCell_11_up_row_zero {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hr : c.r = 0) (hs : 1 ≤ c.s) :
    (incomingCell c 1).r = m.val + 1 ∧ (incomingCell c 1).s = c.s - 1 ∧
      (incomingCell c 1).e = 0 ∧ (incomingCell c 1).v = 1 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  refine incomingCell_fields_of_lift c 1 (m.val + 1) (c.s - 1) 0 1 (1) (-1)
    (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr]
    ring
  · rw [incomingPoint_at_cell]
    norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr]

end FLattice.Auxiliary.PlusOddProfile
