import FLattice.Auxiliary.PlusOddCoordinates
import FLattice.Auxiliary.PlusOddPredecessors

/-!
# Actual incoming heights at every odd-plus representative seam

All sixteen values evaluate the global odd profile at the literal physical
incoming point. The target cell and affine correction are derived together
from the signed lift, including every wrap. These are exact height identities;
no global deficit bound, superharmonicity or comparison premise is assumed.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

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

private theorem profile_incoming_of_lift {m : Parameter} (c : Cell m) (i : Fin 2)
    (r s : ℤ) (e v : Fin 2) (k q : ℤ)
    (hr0 : 0 ≤ r) (hrm : r ≤ m.val + 1)
    (hs0 : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1))
    (hx : (incomingPoint c.x c.y i).1 =
      2 * m.val * r + 2 * s + (v.val : ℤ) + 2 * m.val * k + 2 * halfPeriod m * q)
    (hy : (incomingPoint c.x c.y i).2 = 2 * k + (e.val : ℤ)) :
    profile m (incomingPoint c.x c.y i).1 (incomingPoint c.x c.y i).2 =
      representativeHeight m e v r s - q * (2 * m.val * r + 2 * s + (v.val : ℤ))
        + q * m.val * (e.val : ℤ) - halfPeriod m * q ^ 2
        + (m.val - 1) * q - k * (e.val : ℤ) - k ^ 2 := by
  rw [hx, hy]
  exact profile_at_lifted_cell m r s k q e v hr0 hrm hs0 hsm hMissing

/-- The upward input of every 00 cell. Its value includes the exact odd affine correction. -/
theorem profile_incoming_00_up {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) :
    profile m (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 1 0 (c.r) (c.s) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 1 (c.r) (c.s) 1 0 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod])
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod])
  norm_num at h
  exact h

/-- The ordinary downward input subtracts the diagonal period. Its value includes the exact odd affine correction. -/
theorem profile_incoming_00_down_inner {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hr : c.r ≤ m.val) (hEnd : ¬(c.r = m.val ∧ c.s = m.val - 1)) :
    profile m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 1 0 (c.r + 1) (c.s) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 0 (c.r + 1) (c.s) 1 0 (-1) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod])
  norm_num at h
  ring_nf at h ⊢
  exact h

/-- The penultimate 00 endpoint crosses both period seams. Its value includes the exact odd affine correction. -/
theorem profile_incoming_00_down_penultimate {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hr : c.r = m.val) (hs : c.s = m.val - 1) :
    profile m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 1 0 (0) (0) - m.val ^ 2 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 0 (0) (0) 1 0 (-1) (1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs])
  norm_num at h
  simp only [halfPeriod] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The top 00 row crosses both period seams. Its value includes the exact odd affine correction. -/
theorem profile_incoming_00_down_top {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hr : c.r = m.val + 1) :
    profile m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 1 0 (0) (c.s + 1) - m.val ^ 2 - 2 * c.s - 2 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 0 (0) (c.s + 1) 1 0 (-1) (1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr])
  norm_num at h
  simp only [halfPeriod] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The left input of every 01 cell. Its value includes the exact odd affine correction. -/
theorem profile_incoming_01_left {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) :
    profile m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 0 0 (c.r) (c.s) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 0 (c.r) (c.s) 0 0 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod])
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod])
  norm_num at h
  exact h

/-- The ordinary right input of a 01 cell. Its value includes the exact odd affine correction. -/
theorem profile_incoming_01_right_inner {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hs : c.s ≤ m.val - 2) (hEnd : ¬(c.r = m.val + 1 ∧ c.s = m.val - 2)) :
    profile m (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 0 (c.r) (c.s + 1) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 1 (c.r) (c.s + 1) 0 0 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod])
  norm_num at h
  ring_nf at h ⊢
  exact h

/-- The last-column right input carries into the next row. Its value includes the exact odd affine correction. -/
theorem profile_incoming_01_right_last {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hs : c.s = m.val - 1) :
    profile m (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 0 (c.r + 1) (0) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 1 (c.r + 1) (0) 0 0 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hs])
  norm_num at h
  ring_nf at h ⊢
  exact h

/-- The right input at the truncated top endpoint wraps horizontally. Its value includes the exact odd affine correction. -/
theorem profile_incoming_01_right_top_endpoint {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hr : c.r = m.val + 1) (hs : c.s = m.val - 2) :
    profile m (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 0 (0) (0) - halfPeriod m + m.val - 1 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 1 (0) (0) 0 0 (0) (1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs])
  norm_num at h
  simp only [halfPeriod] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The right input of every 10 cell. Its value includes the exact odd affine correction. -/
theorem profile_incoming_10_right {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) :
    profile m (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 1 1 (c.r) (c.s) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 1 (c.r) (c.s) 1 1 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod])
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod])
  norm_num at h
  exact h

/-- The ordinary left input of a 10 cell. Its value includes the exact odd affine correction. -/
theorem profile_incoming_10_left_of_pos {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hs : 1 ≤ c.s) :
    profile m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 1 1 (c.r) (c.s - 1) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 0 (c.r) (c.s - 1) 1 1 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod])
  norm_num at h
  ring_nf at h ⊢
  exact h

/-- The inner left carry of a 10 cell. Its value includes the exact odd affine correction. -/
theorem profile_incoming_10_left_of_zero {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hs : c.s = 0) (hr : 1 ≤ c.r) :
    profile m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 1 1 (c.r - 1) (m.val - 1) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 0 (c.r - 1) (m.val - 1) 1 1 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hs])
  norm_num at h
  ring_nf at h ⊢
  exact h

/-- The left input at 10(0,0) wraps by a negative horizontal period. Its value includes the exact odd affine correction. -/
theorem profile_incoming_10_left_origin {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hr : c.r = 0) (hs : c.s = 0) :
    profile m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 1 1 (m.val + 1) (m.val - 2) + m.val ^ 2 - 1 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 0 (m.val + 1) (m.val - 2) 1 1 (0) (-1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs])
  norm_num at h
  simp only [halfPeriod] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The downward input of every 11 cell. Its value includes the exact odd affine correction. -/
theorem profile_incoming_11_down {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) :
    profile m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 0 1 (c.r) (c.s) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 0 (c.r) (c.s) 0 1 (0) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod])
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod])
  norm_num at h
  exact h

/-- The ordinary upward input adds the diagonal period. Its value includes the exact odd affine correction. -/
theorem profile_incoming_11_up_of_pos {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hr : 1 ≤ c.r) :
    profile m (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 1 (c.r - 1) (c.s) - 1 := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 1 (c.r - 1) (c.s) 0 1 (1) (0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod])
  norm_num at h
  ring_nf at h ⊢
  exact h

/-- The upward input at 11(0,0) crosses both period seams. Its value includes the exact odd affine correction. -/
theorem profile_incoming_11_up_origin {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hr : c.r = 0) (hs : c.s = 0) :
    profile m (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 1 (m.val) (m.val - 1) + m.val ^ 2 - m.val + 2 * c.s := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 1 (m.val) (m.val - 1) 0 1 (1) (-1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr, hs])
  norm_num [hs] at h
  simp only [halfPeriod] at h ⊢
  rw [hs]
  ring_nf at h ⊢
  exact h

/-- The rest of the low 11 row crosses both period seams. Its value includes the exact odd affine correction. -/
theorem profile_incoming_11_up_row_zero {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hr : c.r = 0) (hs : 1 ≤ c.s) :
    profile m (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 1 (m.val + 1) (c.s - 1) + m.val ^ 2 - m.val + 2 * c.s := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have h := profile_incoming_of_lift c 1 (m.val + 1) (c.s - 1) 0 1 (1) (-1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, Cell.y, he, hv, halfPeriod, hr])
  norm_num at h
  simp only [halfPeriod] at h ⊢
  ring_nf at h ⊢
  exact h

end FLattice.Auxiliary.PlusOddProfile
