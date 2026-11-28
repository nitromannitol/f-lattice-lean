import FLatticePaper.Tiles.SwapBaseBlock

/-! # The region cases of `SwapBaseInput`

The overlap of the two translates of a base tile is not a fixed block here: it grows with the word (`23, 47, 79, ...` points),
so the compatibility is proved for all points of the overlap at once. The triangular term of the paper value is handled by the
shift identity `tri_shift` (the parity of `t(t+1)`), the `min`/`max` terms and the indicator of the two-point set are split. -/

namespace FLatticePaper.Tiles.SwapRegions

open FLatticePaper.Construction

/-- The triangular term shifts by two: `s(s+1)/2 = t(t+1)/2 + 2t + 3` when `s = t + 2`. -/
theorem tri_shift (s t : ℤ) (h : s = t + 2) : s * (s + 1) / 2 = t * (t + 1) / 2 + 2 * t + 3 := by
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self t
  subst h
  have e : (t + 2) * (t + 2 + 1) = t * (t + 1) + 4 * t + 6 := by ring
  rw [e, hr]
  omega

/-- The paper ladder value as a function of its two coordinates, with the indicator written as linear conditions. -/
theorem ladder_value_formula (d z1 z2 : ℤ) : paperLadderValue d (z1, z2) =
    -(z2 * (z2 + 1) / 2) + (z2 + min (z1 - 1) 0) + min 0 (d + 1 - z1) + max (z1 + z2 - d - 2) 0 +
      (if (z1 = 0 ∧ z2 = 0) ∨ (z1 = d + 2 ∧ z2 = d + 2) ∨ (z1 + z2 = d + 2 ∧ 1 < z2 ∧ z2 < d + 1) then 1 else 0) := by
  unfold paperLadderValue
  simp only [Set.indicator_apply, paperLadderA, paperLadderB, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff, or_assoc]

/-- Membership in the ladder tile as linear conditions. -/
theorem ladder_tile_mem (d z1 z2 : ℤ) : (z1, z2) ∈ paperLadderTile d ↔
    (((z1 = 0 ∧ z2 = 0) ∨ (z1 = d + 2 ∧ z2 = d + 2) ∨ (z1 + z2 = d + 2 ∧ 1 < z2 ∧ z2 < d + 1) ∨
      (-d + 2 ≤ z1 ∧ z1 ≤ 2 * d ∧ 0 ≤ z2 ∧ z2 ≤ d + 2 ∧ 1 ≤ z1 + z2 ∧ z1 + z2 ≤ 2 * d + 3)) ∧
      ¬((d ≤ z1 ∧ z2 = 0) ∨ (z1 ≤ 2 ∧ z2 = d + 2))) := by
  unfold paperLadderTile paperLadderA paperLadderB paperLadderC paperLadderD
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff]
  tauto

/-- The core of the ladder region: for `z = y + (2k+2, 2)` with both points in the linear part of the ladder tile, the value
difference plus `y2` vanishes (the indicators are off, and the `min`/`max` terms are fixed except one pair, which equals `1 - y1`). -/
theorem ladder_core (k : ℤ) (z1 z2 y1 y2 : ℤ) (hz1 : z1 = y1 + (2 * k + 2)) (hz2 : z2 = y2 + 2)
    (hyC : -(2 * k + 2) + 2 ≤ y1 ∧ y1 ≤ 2 * (2 * k + 2) ∧ 0 ≤ y2 ∧ y2 ≤ 2 * k + 2 + 2 ∧ 1 ≤ y1 + y2 ∧
      y1 + y2 ≤ 2 * (2 * k + 2) + 3)
    (hzC : -(2 * k + 2) + 2 ≤ z1 ∧ z1 ≤ 2 * (2 * k + 2) ∧ 0 ≤ z2 ∧ z2 ≤ 2 * k + 2 + 2 ∧ 1 ≤ z1 + z2 ∧
      z1 + z2 ≤ 2 * (2 * k + 2) + 3) :
    paperLadderValue (2 * k + 2) (z1, z2) - paperLadderValue (2 * k + 2) (y1, y2) + y2 = 0 := by
  have ht := tri_shift z2 y2 hz2
  have m1 : min (z1 - 1) 0 = 0 := min_eq_right (by omega)
  have m2 : min 0 (2 * k + 2 + 1 - y1) = 0 := min_eq_left (by omega)
  have m3 : max (z1 + z2 - (2 * k + 2) - 2) 0 = z1 + z2 - (2 * k + 2) - 2 := max_eq_left (by omega)
  have m4 : max (y1 + y2 - (2 * k + 2) - 2) 0 = 0 := max_eq_right (by omega)
  have m5 : min 0 (2 * k + 2 + 1 - z1) - min (y1 - 1) 0 = 1 - y1 := by
    have e : 2 * k + 2 + 1 - z1 = -(y1 - 1) := by omega
    rw [e]
    rcases le_total (y1 - 1) 0 with h | h
    · rw [min_eq_left h, min_eq_left (by omega : (0 : ℤ) ≤ -(y1 - 1))]
      ring
    · rw [min_eq_right h, min_eq_right (by omega : -(y1 - 1) ≤ (0 : ℤ))]
      ring
  rw [ladder_value_formula, ladder_value_formula]
  split_ifs <;> omega

/-- The special point `x = (1, 2k+5)`: `y = (0,0)` (indicator on) and `z = (2k+2, 2)` (indicator on). -/
theorem ladder_P1 (k : ℤ) (hk : 1 ≤ k) (x1 x2 : ℤ) (h1 : x1 = 1) (h2 : x2 = 2 * k + 5) :
    paperLadderValue (2 * k + 2) (x1 + (2 * k + 1), x2 - (2 * k + 3)) -
      paperLadderValue (2 * k + 2) (x1 - 1, x2 - (2 * k + 5)) + ((1 - 1) * x1 + (-(2 * k + 2) - -(2 * k + 3)) * x2) =
      2 * k + 5 := by
  have ht := tri_shift (x2 - (2 * k + 3)) (x2 - (2 * k + 5)) (by ring)
  have m1 : min (x1 + (2 * k + 1) - 1) 0 = 0 := min_eq_right (by omega)
  have m2 : min 0 (2 * k + 2 + 1 - (x1 + (2 * k + 1))) = 0 := min_eq_left (by omega)
  have m3 : max (x1 + (2 * k + 1) + (x2 - (2 * k + 3)) - (2 * k + 2) - 2) 0 = 0 := max_eq_right (by omega)
  have m4 : min (x1 - 1 - 1) 0 = x1 - 1 - 1 := min_eq_left (by omega)
  have m5 : min 0 (2 * k + 2 + 1 - (x1 - 1)) = 0 := min_eq_left (by omega)
  have m6 : max (x1 - 1 + (x2 - (2 * k + 5)) - (2 * k + 2) - 2) 0 = 0 := max_eq_right (by omega)
  rw [ladder_value_formula, ladder_value_formula]
  split_ifs <;> omega

/-- The special point `x = (3, 4k+7)`: `z = (2k+4, 2k+4)` (indicator on) and `y = (2, 2k+2)` (indicator on). -/
theorem ladder_P2 (k : ℤ) (hk : 1 ≤ k) (x1 x2 : ℤ) (h1 : x1 = 3) (h2 : x2 = 4 * k + 7) :
    paperLadderValue (2 * k + 2) (x1 + (2 * k + 1), x2 - (2 * k + 3)) -
      paperLadderValue (2 * k + 2) (x1 - 1, x2 - (2 * k + 5)) + ((1 - 1) * x1 + (-(2 * k + 2) - -(2 * k + 3)) * x2) =
      2 * k + 5 := by
  have ht := tri_shift (x2 - (2 * k + 3)) (x2 - (2 * k + 5)) (by ring)
  have m1 : min (x1 + (2 * k + 1) - 1) 0 = 0 := min_eq_right (by omega)
  have m2 : min 0 (2 * k + 2 + 1 - (x1 + (2 * k + 1))) = 2 * k + 2 + 1 - (x1 + (2 * k + 1)) :=
    min_eq_right (by omega)
  have m3 : max (x1 + (2 * k + 1) + (x2 - (2 * k + 3)) - (2 * k + 2) - 2) 0 =
      x1 + (2 * k + 1) + (x2 - (2 * k + 3)) - (2 * k + 2) - 2 := max_eq_left (by omega)
  have m4 : min (x1 - 1 - 1) 0 = 0 := min_eq_right (by omega)
  have m5 : min 0 (2 * k + 2 + 1 - (x1 - 1)) = 0 := min_eq_left (by omega)
  have m6 : max (x1 - 1 + (x2 - (2 * k + 5)) - (2 * k + 2) - 2) 0 = 0 := max_eq_right (by omega)
  rw [ladder_value_formula, ladder_value_formula]
  split_ifs <;> omega

/-- The ladder region (`u1 = 3^k`, word `3^k 1`, the pair (1,2)): on the overlap of the two translates of the ladder tile
`T_{1/d}`, `d = 2k+2`, at the offsets `(-2k-1, 2k+3)` and `(1, 2k+5)`, the paper value difference plus the affine part is the
constant `2k+5`. The overlap is the linear part (`ladder_core`) and the two special points (`ladder_P1`, `ladder_P2`). -/
theorem ladder_region (k : ℤ) (hk : 1 ≤ k) (x : Site)
    (h0 : x - (-2 * k - 1, 2 * k + 3) ∈ paperLadderTile (2 * k + 2))
    (h1 : x - (1, 2 * k + 5) ∈ paperLadderTile (2 * k + 2)) :
    paperLadderValue (2 * k + 2) (x - (-2 * k - 1, 2 * k + 3)) - paperLadderValue (2 * k + 2) (x - (1, 2 * k + 5))
      + ((1 - 1) * x.1 + (-(2 * k + 2) - -(2 * k + 3)) * x.2) = 2 * k + 5 := by
  obtain ⟨x1, x2⟩ := x
  have e0 : (x1, x2) - (-2 * k - 1, 2 * k + 3) = (x1 + (2 * k + 1), x2 - (2 * k + 3)) := by
    show (x1 - (-2 * k - 1), x2 - (2 * k + 3)) = _
    rw [Prod.mk.injEq]
    exact ⟨by ring, rfl⟩
  have e1 : (x1, x2) - (1, 2 * k + 5) = (x1 - 1, x2 - (2 * k + 5)) := by
    show (x1 - 1, x2 - (2 * k + 5)) = _
    rfl
  rw [e0] at h0
  rw [e1] at h1
  rw [e0, e1]
  rw [ladder_tile_mem] at h0 h1
  obtain ⟨hz, -⟩ := h0
  obtain ⟨hy, -⟩ := h1
  rcases hz with hA0 | hA1 | hB | hC <;> rcases hy with hA0' | hA1' | hB' | hC'
  all_goals first
    | (exfalso; omega)
    | exact ladder_P1 k hk x1 x2 (by omega) (by omega)
    | exact ladder_P2 k hk x1 x2 (by omega) (by omega)
    | (have key := ladder_core k (x1 + (2 * k + 1)) (x2 - (2 * k + 3)) (x1 - 1) (x2 - (2 * k + 5)) (by ring) (by ring)
          hC' hC
       linarith)

end FLatticePaper.Tiles.SwapRegions
