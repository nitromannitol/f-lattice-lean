import FLatticePaper.Tiles.BaseHmOddClass1

/-! # The per-tile identity of the zero tiles at `(2j-2k-1, 2k+2)`, `k+2 ≤ j ≤ 2k+1`, of the reversed odd `3^k` piece

Here the letter is `p` (tile `zero`), the affine factor is `(1, -(2k+1))` and the constant is `c0Hm k + (1 + 2(j-k-2))`. -/

namespace FLatticePaper.Tiles.BaseHmOddClass3

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.BaseHmOdd FLatticePaper.Construction
open FLatticePaper.Tiles.BaseHmOddValues FLatticePaper.Tiles.BaseHmOddClass1 FLatticePaper.Tiles.BaseTileProps

theorem aHm_tail (k j : ℕ) (hj1 : k + 2 ≤ j) (hj2 : j ≤ 2 * k + 1) :
    aHm k j = ((1 : ℤ), -(2 * (k : ℤ) + 1)) := by
  unfold aHm
  rw [letter_rev_wL k j (by omega), if_neg (show ¬ (j = k + 1 ∨ j = 2 * k + 2) by omega)]
  ext
  · norm_num [alphaH]
  · norm_num [alphaH]
    ring

theorem cHm_tail (k j : ℕ) (hj1 : k + 2 ≤ j) (hj2 : j ≤ 2 * k + 1) :
    cHm k j = c0Hm k + (1 + 2 * ((j : ℤ) - (k : ℤ) - 2)) := by
  unfold cHm dHm
  rw [if_neg (show j ≠ 0 by omega), if_neg (show ¬ j ≤ k by omega)]
  by_cases h : j ≤ k + 2
  · rw [if_pos h]
    have hj' : (j : ℤ) = (k : ℤ) + 2 := by
      have : j = k + 2 := by omega
      rw [this]; push_cast; ring
    rw [hj']
    ring
  · rw [if_neg h, if_pos (show j ≤ 2 * k + 1 by omega)]

theorem val_zero_tail (k j : ℕ) (hj1 : k + 2 ≤ j) (hj2 : j ≤ 2 * k + 1) (u : GInt)
    (hu : u ∈ tileShape ZTile.zero) :
    paperLadderValue (2 * (k : ℤ) + 2) (u + (2 * (j : ℤ) - 2 * (k : ℤ) - 1, 2 * (k : ℤ) + 2)) =
      zTileOdo ZTile.zero u + ptDot (aHm k j) u + cHm k j := by
  rw [aHm_tail k j hj1 hj2, cHm_tail k j hj1 hj2]
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  have hpt : (a, b) + (2 * (j : ℤ) - 2 * (k : ℤ) - 1, 2 * (k : ℤ) + 2)
      = (a + (2 * (j : ℤ) - 2 * (k : ℤ) - 1), 2 * (k : ℤ) + (b + 1 + 1)) := by
    rw [Prod.mk_add_mk]
    congr 1
    ring
  rw [hpt, plV, tri_gen]
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [zTileOdo, zeroOdometer, ptDot, c0Hm, min_def, max_def] <;>
    split_ifs <;> (try (exfalso; omega)) <;> ring

end FLatticePaper.Tiles.BaseHmOddClass3
