import FLatticePaper.Plane.Induction.TwosPeriods
import FLatticePaper.Plane.Induction.TwosPieces

/-! # The zero and harmonic strip facts of the twos standard fields (task 40)

On the closed polygon of `2^(k+1)` the standard field is the TeX value `paperNearLadderValue d (z.1, z.2+1)`, `d = 2k+4`
(`rotate_eq_on_E`). With `x = (z.1, z.2+1)`:

* the zero zone `1 - (2k+5) ≤ tGrade z` is `(2k+3) x1 - (2k+5) x2 + 4k+9 ≥ 0`;
* the harmonic zone `sGrade z ≤ 2((2k+5)+(2k+3)) - 1` is `(2k+4) x1 + x2 ≤ 2(2k+4)`.

On the tile pieces (`closedPolygon_twos_tile`) the zero zone meets the tile in the columns `u = x2 - x1 ∈ {-2,-1,0,1}`,
where the TeX value is `0`. The harmonic zone meets the tile in the columns `x1 ∈ {-1,0,1}`, where the TeX value is the
harmonic grid. The two boundary points of the polygon are outside the zero zone; `(-1, d)` meets the harmonic zone and
has the harmonic value. The proofs use the tile membership as inequalities, the parity of the harmonic grid on each
column, and `omega`/`nlinarith` for the zones. -/

namespace FLatticePaper.Induction
open Farey Construction

/-! ### Floors of quotients by four -/

theorem ediv4_of (a q r : ℤ) (h : a = 4 * q + r) (h0 : 0 ≤ r) (h4 : r < 4) : a / 4 = q := by
  subst h
  omega

/-! ### The harmonic grid on the columns `x1 = 1, 0, -1` -/

theorem harmonicGrid_col_one (w : ℤ) : harmonicGrid (1, w) = -(w ^ 2 / 4) := by
  unfold harmonicGrid
  dsimp only
  rcases Int.even_or_odd' w with ⟨j, rfl | rfl⟩
  · have hp : (1 + 2 * j) % 2 = 1 := by omega
    rw [hp, show (2 * j) ^ 2 / 4 = j ^ 2 from ediv4_of _ _ 0 (by ring) (by norm_num) (by norm_num)]
    exact ediv4_of _ _ 0 (by ring) (by norm_num) (by norm_num)
  · have hp : (1 + (2 * j + 1)) % 2 = 0 := by omega
    rw [hp, show (2 * j + 1) ^ 2 / 4 = j ^ 2 + j from ediv4_of _ _ 1 (by ring) (by norm_num) (by norm_num)]
    exact ediv4_of _ _ 0 (by ring) (by norm_num) (by norm_num)

theorem harmonicGrid_col_zero (w : ℤ) : harmonicGrid (0, w) = -((w + 1) ^ 2 / 4) := by
  unfold harmonicGrid
  dsimp only
  rcases Int.even_or_odd' w with ⟨j, rfl | rfl⟩
  · have hp : (0 + 2 * j) % 2 = 0 := by omega
    rw [hp, show (2 * j + 1) ^ 2 / 4 = j ^ 2 + j from ediv4_of _ _ 1 (by ring) (by norm_num) (by norm_num)]
    exact ediv4_of _ _ 0 (by ring) (by norm_num) (by norm_num)
  · have hp : (0 + (2 * j + 1)) % 2 = 1 := by omega
    rw [hp, show (2 * j + 1 + 1) ^ 2 / 4 = (j + 1) ^ 2 from ediv4_of _ _ 0 (by ring) (by norm_num) (by norm_num)]
    exact ediv4_of _ _ 0 (by ring) (by norm_num) (by norm_num)

theorem harmonicGrid_col_neg_one (w : ℤ) : harmonicGrid (-1, w) = 1 - ((w + 2) ^ 2 / 4) := by
  unfold harmonicGrid
  dsimp only
  rcases Int.even_or_odd' w with ⟨j, rfl | rfl⟩
  · have hp : (-1 + 2 * j) % 2 = 1 := by omega
    rw [hp, show (2 * j + 2) ^ 2 / 4 = (j + 1) ^ 2 from ediv4_of _ _ 0 (by ring) (by norm_num) (by norm_num)]
    exact ediv4_of _ _ 0 (by ring) (by norm_num) (by norm_num)
  · have hp : (-1 + (2 * j + 1)) % 2 = 0 := by omega
    rw [hp, show (2 * j + 1 + 2) ^ 2 / 4 = j ^ 2 + 3 * j + 2 from ediv4_of _ _ 1 (by ring) (by norm_num)
      (by norm_num)]
    exact ediv4_of _ _ 0 (by ring) (by norm_num) (by norm_num)

/-! ### The tile and the TeX value -/

/-- The cases of a point of the tile `paperNearLadderTile d`, as explicit inequalities. -/
theorem mem_tile_cases (d x1 x2 : ℤ) (h : (x1, x2) ∈ paperNearLadderTile d) :
    ((x1 = -1 ∧ x2 = 2 * d + 1) ∨ (x1 = d + 1 ∧ x2 = d - 1) ∨ (x2 - x1 = d ∧ 0 < x1 ∧ x1 < d) ∨
      (-1 ≤ x1 ∧ x1 ≤ d + 1 ∧ 1 ≤ x2 ∧ x2 ≤ 3 * d - 1 ∧ -1 ≤ x2 - x1 ∧ x2 - x1 ≤ 2 * d + 1)) ∧
    ¬ (x1 = -1 ∧ x2 ≤ d + 1) ∧ ¬ (x1 = d + 1 ∧ 2 * d - 1 ≤ x2) := by
  simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
    Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq,
    not_or] at h
  obtain ⟨hABC, hD1, hD2⟩ := h
  exact ⟨by tauto, hD1, hD2⟩

/-- The TeX value with its indicator of `A ∪ B`. -/
theorem nearValue_formula (d x1 x2 : ℤ) :
    paperNearLadderValue d (x1, x2) = -((x2 - x1) ^ 2 / 4) + min 0 (d - x2) + min 0 (2 * d - x2) +
      max ((x2 - x1) - d) 0 + (paperNearLadderA d ∪ paperNearLadderB d).indicator (fun _ => (1 : ℤ)) (x1, x2) := by
  rfl

/-- A point which is none of the corners and not on the diagonal `B` has no indicator. -/
theorem notMem_AB {d x1 x2 : ℤ} (h : ¬ ((x1 = -1 ∧ x2 = 2 * d + 1) ∨ (x1 = d + 1 ∧ x2 = d - 1) ∨
    (x2 - x1 = d ∧ 0 < x1 ∧ x1 < d))) : (x1, x2) ∉ paperNearLadderA d ∪ paperNearLadderB d := by
  intro hm
  apply h
  simp only [paperNearLadderA, paperNearLadderB, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_setOf_eq, Prod.mk.injEq] at hm
  tauto

/-! ### The zero zone on the tile -/

/-- On the tile, inside the zero zone, the TeX value vanishes. -/
theorem zero_tile_value (k : ℕ) (x1 x2 : ℤ) (hT : (x1, x2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4))
    (hb : (2 * (k : ℤ) + 3) * x1 - (2 * (k : ℤ) + 5) * x2 + 4 * (k : ℤ) + 9 ≥ 0) :
    paperNearLadderValue (2 * (k : ℤ) + 4) (x1, x2) = 0 := by
  obtain ⟨hcases, hD1, hD2⟩ := mem_tile_cases _ x1 x2 hT
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  have key : -2 * x1 - (2 * (k : ℤ) + 5) * (x2 - x1) + 4 * (k : ℤ) + 9 ≥ 0 := by linarith
  rw [nearValue_formula]
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · exfalso
    subst h1
    subst h2
    nlinarith
  · subst h1
    subst h2
    rw [Set.indicator_of_mem (Set.mem_union_left _ (by simp [paperNearLadderA]))]
    rw [show (2 * (k : ℤ) + 4 - 1 - (2 * (k : ℤ) + 4 + 1)) ^ 2 / 4 = 1 from
      ediv4_of _ _ 0 (by ring) (by norm_num) (by norm_num)]
    simp only [min_def, max_def]
    split_ifs <;> omega
  · exfalso
    nlinarith
  · have hu : x2 - x1 ≤ 1 := by
      by_contra hcon
      have hu2 : 2 ≤ x2 - x1 := by omega
      rcases (show x1 = -1 ∨ 0 ≤ x1 by omega) with hx | hx
      · subst hx
        have hx2 : 2 * (k : ℤ) + 6 ≤ x2 := by omega
        nlinarith
      · nlinarith [mul_nonneg hk (show (0 : ℤ) ≤ x2 - x1 - 2 by omega)]
    rw [Set.indicator_of_notMem (notMem_AB (by omega))]
    have hu' : x2 - x1 = -1 ∨ x2 - x1 = 0 ∨ x2 - x1 = 1 := by omega
    rcases hu' with hu' | hu' | hu' <;> rw [hu'] at key ⊢ <;> simp only [min_def, max_def] <;>
      norm_num <;> split_ifs <;> omega

/-! ### The harmonic zone on the tile -/

/-- On the tile, inside the harmonic zone, the TeX value is the harmonic grid. -/
theorem harm_tile_value (k : ℕ) (x1 x2 : ℤ) (hT : (x1, x2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4))
    (hb : (2 * (k : ℤ) + 4) * x1 + x2 ≤ 2 * (2 * (k : ℤ) + 4)) :
    paperNearLadderValue (2 * (k : ℤ) + 4) (x1, x2) = harmonicGrid (x1, x2 - 1) := by
  obtain ⟨hcases, hD1, hD2⟩ := mem_tile_cases _ x1 x2 hT
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  rw [nearValue_formula]
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · -- the corner `(-1, 2d+1)`
    subst h1
    subst h2
    rw [Set.indicator_of_mem (Set.mem_union_left _ (by simp [paperNearLadderA])), harmonicGrid_col_neg_one]
    rw [show (2 * (2 * (k : ℤ) + 4) + 1 - -1 : ℤ) = 2 * (2 * (k : ℤ) + 4) + 1 - 1 + 2 by ring]
    generalize (2 * (2 * (k : ℤ) + 4) + 1 - 1 + 2) ^ 2 / 4 = Q
    simp only [min_def, max_def]
    split_ifs <;> omega
  · -- the corner `(d+1, d-1)` is outside the harmonic zone
    exfalso
    subst h1
    subst h2
    nlinarith
  · -- the diagonal `B` is outside the harmonic zone
    exfalso
    nlinarith
  · have hx1 : x1 ≤ 1 := by
      by_contra hcon
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * (k : ℤ) + 4 by positivity) (show (0 : ℤ) ≤ x1 - 2 by omega)]
    rcases (show x1 = -1 ∨ x1 = 0 ∨ x1 = 1 by omega) with hx | hx | hx
    · -- the column `x1 = -1`, `d+2 ≤ x2 ≤ 2d`
      subst hx
      rw [Set.indicator_of_notMem (notMem_AB (by omega)), harmonicGrid_col_neg_one]
      rw [show (x2 - -1 : ℤ) = x2 - 1 + 2 by ring]
      generalize (x2 - 1 + 2) ^ 2 / 4 = Q
      simp only [min_def, max_def]
      split_ifs <;> omega
    · -- the column `x1 = 0`
      subst hx
      rw [Set.indicator_of_notMem (notMem_AB (by omega)), harmonicGrid_col_zero, sub_add_cancel, sub_zero]
      simp only [sub_zero] at *
      generalize x2 ^ 2 / 4 = Q
      simp only [min_def, max_def]
      split_ifs <;> omega
    · -- the column `x1 = 1`
      subst hx
      rw [Set.indicator_of_notMem (notMem_AB (by omega)), harmonicGrid_col_one]
      generalize (x2 - 1) ^ 2 / 4 = Q
      simp only [min_def, max_def]
      split_ifs <;> omega

/-! ### The strip facts of the standard field on the closed polygon -/

/-- The zero strip of the standard field of `2^(k+1)` on its closed polygon. -/
theorem twos_zero_strip (k : ℕ) {z : Site}
    (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon)
    (ht : 1 - (frameAt (List.replicate (k + 1) Digit.two)).child.den ≤
      (frameAt (List.replicate (k + 1) Digit.two)).tGrade z) :
    standardField (List.replicate (k + 1) Digit.two) z = 0 := by
  have hvalid : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) := ⟨by omega, by omega⟩
  obtain ⟨S, hagree, hperiod, -⟩ := ladderOdd_exists_extension hvalid
  rw [twos_standardField_eq_rotate k hagree hperiod z, rotate_eq_on_E k hagree hperiod hz]
  have hden : (frameAt (List.replicate (k + 1) Digit.two)).child.den = 2 * (k : ℤ) + 5 := by
    rw [twos_child_eq k]
  rw [hden, twos_tGrade] at ht
  rcases closedPolygon_twos_tile k z hz with h | h | h
  · exact zero_tile_value k z.1 (z.2 + 1) h (by linarith)
  · exfalso
    subst h
    dsimp only at ht
    nlinarith
  · exfalso
    subst h
    dsimp only at ht
    nlinarith

/-- The harmonic strip of the standard field of `2^(k+1)` on its closed polygon. -/
theorem twos_harm_strip (k : ℕ) {z : Site}
    (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon)
    (hs : (frameAt (List.replicate (k + 1) Digit.two)).sGrade z ≤
      2 * ((frameAt (List.replicate (k + 1) Digit.two)).child.den +
        (frameAt (List.replicate (k + 1) Digit.two)).child.num) - 1) :
    standardField (List.replicate (k + 1) Digit.two) z = harmonicGrid z := by
  have hvalid : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) := ⟨by omega, by omega⟩
  obtain ⟨S, hagree, hperiod, -⟩ := ladderOdd_exists_extension hvalid
  rw [twos_standardField_eq_rotate k hagree hperiod z, rotate_eq_on_E k hagree hperiod hz]
  have hden : (frameAt (List.replicate (k + 1) Digit.two)).child.den = 2 * (k : ℤ) + 5 := by
    rw [twos_child_eq k]
  have hnum : (frameAt (List.replicate (k + 1) Digit.two)).child.num = 2 * (k : ℤ) + 3 := by
    rw [twos_child_eq k]
  unfold ChildFrame.sGrade at hs
  rw [hden, hnum] at hs
  have h2 : 2 * ((2 * (k : ℤ) + 4) * z.1 + (z.2 + 1)) ≤ 8 * (k : ℤ) + 17 := by linarith [hs]
  have hb : (2 * (k : ℤ) + 4) * z.1 + (z.2 + 1) ≤ 2 * (2 * (k : ℤ) + 4) := by
    generalize (2 * (k : ℤ) + 4) * z.1 = A at h2 ⊢
    omega
  rcases closedPolygon_twos_tile k z hz with h | h | h
  · rw [harm_tile_value k z.1 (z.2 + 1) h hb, add_sub_cancel_right]
  · -- the boundary point `(-1, d)`
    subst h
    dsimp only
    rw [nearValue_formula, harmonicGrid_col_neg_one,
      Set.indicator_of_notMem (notMem_AB (by omega)),
      show (2 * (k : ℤ) + 4 + 1 - -1 : ℤ) = 2 * (k : ℤ) + 4 + 2 by ring]
    generalize (2 * (k : ℤ) + 4 + 2) ^ 2 / 4 = Q
    simp only [min_def, max_def]
    split_ifs <;> omega
  · -- the boundary point `(d+1, 2d-2)` is outside the harmonic zone
    exfalso
    subst h
    dsimp only at hb
    nlinarith

end FLatticePaper.Induction
