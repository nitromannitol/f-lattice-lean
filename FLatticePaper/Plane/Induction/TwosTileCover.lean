import FLatticePaper.Plane.Induction.TwosPieces
import FLatticePaper.Plane.Induction.TwosValues

/-! Task 72 / twos base: the native tile of the twos standard field, and the three-shift cover of the closed polygon.

* `standardField_twos_eq_tile`: the standard field of `2^(k+1)` is the near-one closed form at every site `w` whose point
  `(w₁, w₂+1)` lies in the native tile `paperNearLadderTile d` (`d = 2k+4`), not only on the closed polygon.
* `twos_shift_cover`: for `z` in the closed polygon, one of the three points
  `z − v + (0,1)`, `z − v − V + (0,1)`, `z − v + U + (0,1)` lies in the tile, where `v = (1, −(d−1))` is the parent shift,
  `U = (d+1, d−1)` the kernel and `V = (−2, 2d)` the transverse period. The three points are
  `(z₁−1, z₂+d)`, `(z₁+1, z₂−d)` and `(z₁+d, z₂+2d−1)`. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- **The standard field of `2^(k+1)` on the native tile.** -/
theorem standardField_twos_eq_tile (k : ℕ) {w x : Site} (hx : x = (w.1, w.2 + 1))
    (hxt : x ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    standardField (List.replicate (k + 1) Digit.two) w = paperNearLadderValue (2 * (k : ℤ) + 4) x := by
  have hvalid : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) := ⟨by omega, by omega⟩
  obtain ⟨S, hagree, hperiod, -⟩ := ladderOdd_exists_extension hvalid
  have hd : 4 ≤ 2 * (k : ℤ) + 4 ∧ (2 * (k : ℤ) + 4) % 2 = 0 := ⟨by omega, by omega⟩
  rw [twos_standardField_eq_rotate k hagree hperiod w]
  have h := rotate_tile_identity hd hagree x hxt
  have hw : x - (0, 1) = w := by
    rw [hx]
    ext <;> simp
  rw [hw] at h
  exact h

set_option maxHeartbeats 400000 in
/-- **The shift choice on the closed-polygon arithmetic.** On the output `key` of `twos_E_arith` (with `v = z₂ − z₁`), the point
`(z₁−1, z₂+d)` (shift `0`) is in the tile, unless `(z₁, v) = (−1, d+1)` or `z₁ = 0, v ≤ 1` (then `(z₁+d, z₂+2d−1)`, shift `+U`),
or `v ≥ d+2` or `z₁ ≥ 1, v = d+1` (then `(z₁+1, z₂−d)`, shift `−V`). -/
theorem twos_cover_tree (d z1 z2 : ℤ) (hd : 4 ≤ d)
    (key : (-1 ≤ z1 ∧ z1 ≤ d + 1 ∧ -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * d ∧ 0 ≤ z1 + (z2 - z1) ∧
        z1 + (z2 - z1) ≤ 3 * d - 2 ∧ ¬(z1 = -1 ∧ z1 + (z2 - z1) ≤ d) ∧
        ¬(z1 = d + 1 ∧ 2 * d - 2 ≤ z1 + (z2 - z1))) ∨
      (z1 = -1 ∧ z2 - z1 = 2 * d + 1) ∨ (z1 = d + 1 ∧ z2 - z1 = -3) ∨
      (z1 = -1 ∧ z1 + (z2 - z1) = d) ∨ (z1 = d + 1 ∧ z1 + (z2 - z1) = 2 * d - 2)) :
    (z1 - 1, z2 + d) ∈ paperNearLadderTile d ∨ (z1 + 1, z2 - d) ∈ paperNearLadderTile d ∨
      (z1 + d, z2 + 2 * d - 1) ∈ paperNearLadderTile d := by
  classical
  by_cases hL2 : (z1 = -1 ∧ z2 - z1 = d + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1)
  · right; right
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.mk.injEq, not_or]
    omega
  by_cases hL0 : 0 ≤ z1 ∧ z2 - z1 ≤ d ∧ z2 ≤ 2 * d - 1
  · left
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.mk.injEq, not_or]
    omega
  · right; left
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.mk.injEq, not_or]
    omega

/-- **The three-shift cover.** -/
theorem twos_shift_cover (k : ℕ) {z : Site}
    (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon) :
    (z.1 - 1, z.2 + (2 * (k : ℤ) + 4)) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) ∨
      (z.1 + 1, z.2 - (2 * (k : ℤ) + 4)) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) ∨
      (z.1 + (2 * (k : ℤ) + 4), z.2 + 2 * (2 * (k : ℤ) + 4) - 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
  classical
  obtain ⟨hn, hd⟩ := twos_child_num_den k
  have hT : (frameAt (List.replicate (k + 1) Digit.two)).child.periodDenominator =
      2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) := by
    simp only [Fraction.periodDenominator, hn, hd]
    ring
  obtain ⟨z1, z2⟩ := z
  rw [ChildFrame.mem_closedPolygon_iff] at hz
  simp only [ChildFrame.tGrade, ChildFrame.sGrade, hn, hd, hT, EvenSite] at hz
  have hu0 : 0 ≤ (2 * (k : ℤ) + 4 + 1) * z1 + (z2 - z1) := by
    rcases hz with ⟨_, _, _, h3, _⟩ | ⟨_, _, _, h3, _⟩ <;> linarith
  have huP : (2 * (k : ℤ) + 4 + 1) * z1 + (z2 - z1) ≤
      (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1 + (2 * (k : ℤ) + 4) - 1 := by
    rcases hz with ⟨_, _, _, _, h4⟩ | ⟨_, _, _, _, h4⟩ <;> linarith
  have hev : (z2 - z1) % 2 = 0 → 2 - 2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) ≤
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ∧
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ≤ 2 * (2 * (k : ℤ) + 4) - 2 := by
    intro hv
    rcases hz with ⟨_, h1, h2, _, _⟩ | ⟨ho, _⟩
    · exact ⟨by linarith, by linarith⟩
    · exfalso
      omega
  have hod : (z2 - z1) % 2 = 1 → (2 * (k : ℤ) + 4) - 1 - 2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) ≤
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ∧
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ≤ (2 * (k : ℤ) + 4) + 1 := by
    intro hv
    rcases hz with ⟨he, _, _, _, _⟩ | ⟨_, h1, h2, _, _⟩
    · exfalso
      omega
    · exact ⟨by linarith, by linarith⟩
  have key := twos_E_arith (2 * (k : ℤ) + 4) z1 (z2 - z1) (by omega) hu0 huP hev hod
  exact twos_cover_tree (2 * (k : ℤ) + 4) z1 z2 (by omega) key

end FLatticePaper.Induction
