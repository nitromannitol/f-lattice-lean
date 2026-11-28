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
theorem ladder_P1 (k : ℤ) (_hk : 1 ≤ k) (x1 x2 : ℤ) (h1 : x1 = 1) (h2 : x2 = 2 * k + 5) :
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

/-- The near-ladder value as a function of the two coordinates, with the indicator as linear conditions. -/
theorem nl_value_formula (d a b : ℤ) : paperNearLadderValue d (a, b) =
    -((b - a) ^ 2 / 4) + min 0 (d - b) + min 0 (2 * d - b) + max (b - a - d) 0 +
      (if (a = -1 ∧ b = 2 * d + 1) ∨ (a = d + 1 ∧ b = d - 1) ∨ (b - a = d ∧ 0 < a ∧ a < d) then 1 else 0) := by
  unfold paperNearLadderValue
  simp only [Set.indicator_apply, paperNearLadderA, paperNearLadderB, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff, or_assoc]

/-- The shift of a square by an even multiple: `((D - 2m)^2)/4 = D^2/4 - mD + m^2`. -/
theorem sq_shift_half (D m : ℤ) : (D - 2 * m) ^ 2 / 4 = D ^ 2 / 4 - m * D + m ^ 2 := by
  have h : (D - 2 * m) ^ 2 = D ^ 2 + 4 * (m ^ 2 - m * D) := by ring
  rw [h]
  omega

/-- The linear part of the near-ladder region: for `p = (a,b)` and `p' = (a+2, b-d)` (`d = 2k+2`) both in the linear part of the
near-ladder tile, the value difference is `(k+1)a - (k+2)b + (k+2)^2`. -/
theorem nladder_core (k a b : ℤ) (_hk : 1 ≤ k)
    (hpC : -1 ≤ a ∧ a ≤ 2 * k + 2 + 1 ∧ 1 ≤ b ∧ b ≤ 3 * (2 * k + 2) - 1 ∧ -1 ≤ b - a ∧ b - a ≤ 2 * (2 * k + 2) + 1)
    (hqC : -1 ≤ a + 2 ∧ a + 2 ≤ 2 * k + 2 + 1 ∧ 1 ≤ b - (2 * k + 2) ∧ b - (2 * k + 2) ≤ 3 * (2 * k + 2) - 1 ∧
      -1 ≤ b - (2 * k + 2) - (a + 2) ∧ b - (2 * k + 2) - (a + 2) ≤ 2 * (2 * k + 2) + 1) :
    paperNearLadderValue (2 * k + 2) (a, b) - paperNearLadderValue (2 * k + 2) (a + 2, b - (2 * k + 2)) =
      (k + 1) * a - (k + 2) * b + (k + 2) ^ 2 := by
  rw [nl_value_formula, nl_value_formula]
  have hsq : (b - (2 * k + 2) - (a + 2)) ^ 2 / 4 = (b - a) ^ 2 / 4 - (k + 2) * (b - a) + (k + 2) ^ 2 := by
    have e : b - (2 * k + 2) - (a + 2) = (b - a) - 2 * (k + 2) := by ring
    rw [e, sq_shift_half]
  have F1 : min 0 (2 * k + 2 - b) = 2 * k + 2 - b := min_eq_right (by omega)
  have F2 : min 0 (2 * k + 2 - (b - (2 * k + 2))) = min 0 (2 * (2 * k + 2) - b) := by
    congr 1
    ring
  have F3 : min 0 (2 * (2 * k + 2) - (b - (2 * k + 2))) = 0 := min_eq_left (by omega)
  have F4 : max (b - a - (2 * k + 2)) 0 = b - a - (2 * k + 2) := max_eq_left (by omega)
  have F5 : max (b - (2 * k + 2) - (a + 2) - (2 * k + 2)) 0 = 0 := max_eq_right (by omega)
  split_ifs with hA hB <;> first | (exfalso; omega) | linarith

/-- Membership in the near-ladder tile as linear conditions (the exclusion `D` is kept as one conjunct). -/
theorem nl_tile_mem (d a b : ℤ) : (a, b) ∈ paperNearLadderTile d ↔
    (((a = -1 ∧ b = 2 * d + 1) ∨ (a = d + 1 ∧ b = d - 1) ∨ (b - a = d ∧ 0 < a ∧ a < d) ∨
      (-1 ≤ a ∧ a ≤ d + 1 ∧ 1 ≤ b ∧ b ≤ 3 * d - 1 ∧ -1 ≤ b - a ∧ b - a ≤ 2 * d + 1)) ∧
      ¬((a = -1 ∧ b ≤ d + 1) ∨ (a = d + 1 ∧ 2 * d - 1 ≤ b))) := by
  unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff]
  tauto

/-- The near-ladder special point `(a, b) = (2k+1, 4k+3)`: `(a,b)` in `B` and `(a+2, b-d)` the point `(d+1, d-1)` of `A`. -/
theorem nladder_S1 (k a b : ℤ) (hk : 1 ≤ k) (ha : a = 2 * k + 1) (hb : b = 4 * k + 3) :
    paperNearLadderValue (2 * k + 2) (a, b) - paperNearLadderValue (2 * k + 2) (a + 2, b - (2 * k + 2)) =
      (k + 1) * a - (k + 2) * b + (k + 2) ^ 2 := by
  subst ha hb
  rw [nl_value_formula, nl_value_formula]
  have q1 : (4 * k + 3 - (2 * k + 1)) ^ 2 / 4 = (k + 1) ^ 2 := by
    rw [show 4 * k + 3 - (2 * k + 1) = 2 * (k + 1) by ring, show (2 * (k + 1)) ^ 2 = 4 * (k + 1) ^ 2 by ring]
    omega
  have q2 : (4 * k + 3 - (2 * k + 2) - (2 * k + 1 + 2)) ^ 2 / 4 = 1 := by
    rw [show 4 * k + 3 - (2 * k + 2) - (2 * k + 1 + 2) = -2 by ring]
    norm_num
  rw [q1, q2]
  simp only [min_def, max_def]
  split_ifs <;> first | (exfalso; omega) | ring

/-- The near-ladder special point `(a, b) = (-1, 4k+5)`: `(a,b)` in `A` and `(a+2, b-d)` in `B`. -/
theorem nladder_S2 (k a b : ℤ) (hk : 1 ≤ k) (ha : a = -1) (hb : b = 4 * k + 5) :
    paperNearLadderValue (2 * k + 2) (a, b) - paperNearLadderValue (2 * k + 2) (a + 2, b - (2 * k + 2)) =
      (k + 1) * a - (k + 2) * b + (k + 2) ^ 2 := by
  subst ha hb
  rw [nl_value_formula, nl_value_formula]
  have q1 : (4 * k + 5 - -1) ^ 2 / 4 = (2 * k + 3) ^ 2 := by
    rw [show 4 * k + 5 - -1 = 2 * (2 * k + 3) by ring, show (2 * (2 * k + 3)) ^ 2 = 4 * (2 * k + 3) ^ 2 by ring]
    omega
  have q2 : (4 * k + 5 - (2 * k + 2) - (-1 + 2)) ^ 2 / 4 = (k + 1) ^ 2 := by
    rw [show 4 * k + 5 - (2 * k + 2) - (-1 + 2) = 2 * (k + 1) by ring,
      show (2 * (k + 1)) ^ 2 = 4 * (k + 1) ^ 2 by ring]
    omega
  rw [q1, q2]
  simp only [min_def, max_def]
  split_ifs <;> first | (exfalso; (try simp only [true_and] at *); omega) | ring


/-- The near-ladder region (`u2 = 2^k`, word `2^k 1`, the pair (2,5)): on the overlap of the two translates of the near-ladder
tile at the offsets `(2k+4, 2k+2)` and `(2k+2, 4k+4)`, the value difference plus the affine part is the constant `(k+1)(k+2)`.
The overlap is the linear part (`nladder_core`) and the two special points (`nladder_S1`, `nladder_S2`). -/
theorem nladder_region (k : ℤ) (hk : 1 ≤ k) (x1 x2 : ℤ)
    (h0 : (x1 - (2 * k + 4), x2 - (2 * k + 2) + 1) ∈ paperNearLadderTile (2 * k + 2))
    (h1 : (x1 - (2 * k + 2), x2 - (4 * k + 4) + 1) ∈ paperNearLadderTile (2 * k + 2)) :
    paperNearLadderValue (2 * k + 2) (x1 - (2 * k + 4), x2 - (2 * k + 2) + 1) -
      paperNearLadderValue (2 * k + 2) (x1 - (2 * k + 2), x2 - (4 * k + 4) + 1) +
      ((0 - (k + 1)) * x1 + (0 - -(k + 2)) * x2) = (k + 1) * (k + 2) := by
  rw [nl_tile_mem] at h0 h1
  obtain ⟨hz, -⟩ := h0
  obtain ⟨hy, -⟩ := h1
  have e : (x1 - (2 * k + 4) + 2, x2 - (2 * k + 2) + 1 - (2 * k + 2)) = (x1 - (2 * k + 2), x2 - (4 * k + 4) + 1) :=
    Prod.ext (by ring) (by ring)
  rcases hz with hA0 | hA1 | hB | hC <;> rcases hy with hA0' | hA1' | hB' | hC'
  all_goals first
    | (exfalso; omega)
    | (have key := nladder_S1 k (x1 - (2 * k + 4)) (x2 - (2 * k + 2) + 1) hk (by omega) (by omega)
       rw [e] at key
       linear_combination key)
    | (have key := nladder_S2 k (x1 - (2 * k + 4)) (x2 - (2 * k + 2) + 1) hk (by omega) (by omega)
       rw [e] at key
       linear_combination key)
    | (have key := nladder_core k (x1 - (2 * k + 4)) (x2 - (2 * k + 2) + 1) hk
         ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
         ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
       rw [e] at key
       linear_combination key)


end FLatticePaper.Tiles.SwapRegions
