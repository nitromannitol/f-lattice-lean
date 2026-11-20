import FLattice.Auxiliary.MinusCoordinates
import FLattice.Auxiliary.PlusEvenPredecessors

/-!
# Exact physical incoming heights for the even-minus profile

The shared predecessor module supplies geometry only. Each height below
is derived independently from the minus profile's signed affine extension,
retaining every low-row and horizontal/diagonal period correction.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile

private theorem incomingPoint_at_cell {m : Parameter} (c : Cell m) (i : Fin 2) :
    incomingPoint c.x c.y i =
      if ((c.e.val : ℤ) + (c.v.val : ℤ)) % 2 = 0 then
        (c.x + (if i = 0 then -1 else 1), c.y)
      else (c.x, c.y + (if i = 0 then -1 else 1)) := by
  have h : c.x + c.y =
      2 * (m.val * c.r + c.s) + ((c.e.val : ℤ) + (c.v.val : ℤ)) := by
    unfold Cell.x Cell.y
    ring
  have hp : (c.x + c.y) % 2 = ((c.e.val : ℤ) + (c.v.val : ℤ)) % 2 := by
    rw [h]
    omega
  simp only [incomingPoint, hp]

private theorem even_profile_incoming_lift {m : Parameter} (c : Cell m) (i : Fin 2)
    (k q : ℤ)
    (hx : (incomingPoint c.x c.y i).1 =
      (incomingCell c i).x + 2 * m.val * k + 2 * halfPeriod m * q)
    (hy : (incomingPoint c.x c.y i).2 = 2 * k + (incomingCell c i).y) :
    profile m 0 (incomingPoint c.x c.y i).1 (incomingPoint c.x c.y i).2 =
      representativeHeight m 0 (incomingCell c i) - q * (incomingCell c i).x +
        q * m.val * (incomingCell c i).y - halfPeriod m * q ^ 2 +
        (m.val + 1) * q - k * (incomingCell c i).y - k ^ 2 := by
  rw [hx, hy]
  simpa [periodConstant] using profile_at_lifted_cell m 0 (incomingCell c i) k q

/-- The actual `00_left_of_pos` input, with its minus-family affine correction. -/
theorem even_profile_incoming_00_left_of_pos {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hs : 1 ≤ c.s) :
    profile m 0 (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 0 (incomingCell c 0) + (0) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_00_left_of_pos c he hv hs
  have h := even_profile_incoming_lift c 0 (0) (0)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod, hs] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `00_left_of_zero` input, with its minus-family affine correction. -/
theorem even_profile_incoming_00_left_of_zero {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hs : c.s = 0) (hr : 1 ≤ c.r) :
    profile m 0 (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 0 (incomingCell c 0) + (0) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_00_left_of_zero c he hv hs hr
  have h := even_profile_incoming_lift c 0 (0) (0)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod, hs, hr]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod, hs, hr] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `00_left_origin` input, with its minus-family affine correction. -/
theorem even_profile_incoming_00_left_origin {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hr : c.r = 0) (hs : c.s = 0) :
    profile m 0 (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 0 (incomingCell c 0) + (m.val ^ 2 + m.val - 3) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_00_left_origin c he hv hr hs
  have h := even_profile_incoming_lift c 0 (0) (-1)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod, hr, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod, hr, hs] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `00_right` input, with its minus-family affine correction. -/
theorem even_profile_incoming_00_right {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) :
    profile m 0 (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 (incomingCell c 1) + (0) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_00_right c he hv
  have h := even_profile_incoming_lift c 1 (0) (0)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod])
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `01_up` input, with its minus-family affine correction. -/
theorem even_profile_incoming_01_up {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) :
    profile m 0 (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 (incomingCell c 1) + (0) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_01_up c he hv
  have h := even_profile_incoming_lift c 1 (0) (0)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod])
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `01_down_inner` input, with its minus-family affine correction. -/
theorem even_profile_incoming_01_down_inner {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hr : c.r ≤ m.val)
    (hEnd : ¬(c.r = m.val ∧ c.s = m.val - 1)) :
    profile m 0 (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 0 (incomingCell c 0) + (0) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_01_down_inner c he hv hr hEnd
  have h := even_profile_incoming_lift c 0 (-1) (0)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod, hr]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod, hr] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `01_down_penultimate` input, with its minus-family affine correction. -/
theorem even_profile_incoming_01_down_penultimate {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hr : c.r = m.val) (hs : c.s = m.val - 1) :
    profile m 0 (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 0 (incomingCell c 0) + (1 - m.val ^ 2) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_01_down_penultimate c he hv hr hs
  have h := even_profile_incoming_lift c 0 (-1) (1)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod, hr, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod, hr, hs] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `01_down_top` input, with its minus-family affine correction. -/
theorem even_profile_incoming_01_down_top {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hr : c.r = m.val + 1) :
    profile m 0 (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 0 (incomingCell c 0) + (-m.val ^ 2 - 2 * c.s - 1) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_01_down_top c he hv hr
  have h := even_profile_incoming_lift c 0 (-1) (1)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod, hr]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod, hr] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `10_down` input, with its minus-family affine correction. -/
theorem even_profile_incoming_10_down {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) :
    profile m 0 (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 0 (incomingCell c 0) + (0) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_10_down c he hv
  have h := even_profile_incoming_lift c 0 (0) (0)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod])
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `10_up_of_pos` input, with its minus-family affine correction. -/
theorem even_profile_incoming_10_up_of_pos {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hr : 1 ≤ c.r) :
    profile m 0 (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 (incomingCell c 1) + (-1) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_10_up_of_pos c he hv hr
  have h := even_profile_incoming_lift c 1 (1) (0)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod, hr]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod, hr] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `10_up_origin` input, with its minus-family affine correction. -/
theorem even_profile_incoming_10_up_origin {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hr : c.r = 0) (hs : c.s = 0) :
    profile m 0 (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 (incomingCell c 1) + (m.val ^ 2 - m.val - 3) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_10_up_origin c he hv hr hs
  have h := even_profile_incoming_lift c 1 (1) (-1)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod, hr, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod, hr, hs] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `10_up_row_zero` input, with its minus-family affine correction. -/
theorem even_profile_incoming_10_up_row_zero {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hr : c.r = 0) (hs : 1 ≤ c.s) :
    profile m 0 (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 (incomingCell c 1) + (m.val ^ 2 - m.val + 2 * c.s - 3) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_10_up_row_zero c he hv hr hs
  have h := even_profile_incoming_lift c 1 (1) (-1)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod, hr, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod, hr, hs] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `11_left` input, with its minus-family affine correction. -/
theorem even_profile_incoming_11_left {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) :
    profile m 0 (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 =
      representativeHeight m 0 (incomingCell c 0) + (0) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_11_left c he hv
  have h := even_profile_incoming_lift c 0 (0) (0)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod])
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `11_right_inner` input, with its minus-family affine correction. -/
theorem even_profile_incoming_11_right_inner {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hs : c.s ≤ m.val - 2)
    (hEnd : ¬(c.r = m.val + 1 ∧ c.s = m.val - 2)) :
    profile m 0 (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 (incomingCell c 1) + (0) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_11_right_inner c he hv hs hEnd
  have h := even_profile_incoming_lift c 1 (0) (0)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod, hs] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `11_right_last` input, with its minus-family affine correction. -/
theorem even_profile_incoming_11_right_last {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hs : c.s = m.val - 1) :
    profile m 0 (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 (incomingCell c 1) + (0) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_11_right_last c he hv hs
  have h := even_profile_incoming_lift c 1 (0) (0)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod, hs] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The actual `11_right_top_endpoint` input, with its minus-family affine correction. -/
theorem even_profile_incoming_11_right_top_endpoint {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hr : c.r = m.val + 1) (hs : c.s = m.val - 2) :
    profile m 0 (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 =
      representativeHeight m 0 (incomingCell c 1) + (2 - m.val ^ 2) := by
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_11_right_top_endpoint c he hv hr hs
  have h := even_profile_incoming_lift c 1 (0) (1)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.x, he, hv, hr', hs', he', hv', halfPeriod, hr, hs]
      ring)
    (by
      rw [incomingPoint_at_cell]
      norm_num [Cell.y, he, hv, he'])
  norm_num [Cell.x, Cell.y, hr', hs', he', hv', halfPeriod, hr, hs] at h ⊢
  ring_nf at h ⊢
  exact h

end FLattice.Auxiliary.MinusProfile
