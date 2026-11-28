import FLatticePaper.Tiles.BaseHmOddClass2

/-! # The per-tile identity of the one tile at `(2k+3, 2k+3)`, `j = 2k+2`, of the reversed odd `3^k` piece

Here the letter is `q` (tile `one`), the affine factor is `(0, -(2k+1))` and the constant is `c0Hm k` (the `dHm` term vanishes). -/

namespace FLatticePaper.Tiles.BaseHmOddLast

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.BaseHmOdd FLatticePaper.Construction
open FLatticePaper.Tiles.BaseHmOddValues FLatticePaper.Tiles.BaseHmOddClass1 FLatticePaper.Tiles.BaseTileProps

theorem aHm_last (k : ℕ) : aHm k (2 * k + 2) = ((0 : ℤ), -(2 * (k : ℤ) + 1)) := by
  unfold aHm
  rw [letter_rev_wL k (2 * k + 2) (by omega), if_pos (Or.inr rfl)]
  ext
  · norm_num [alphaH]
  · norm_num [alphaH]
    ring

theorem cHm_last (k : ℕ) (hk : 1 ≤ k) : cHm k (2 * k + 2) = c0Hm k := by
  unfold cHm dHm
  rw [if_neg (show 2 * k + 2 ≠ 0 by omega), if_neg (show ¬ (2 * k + 2 ≤ k) by omega),
    if_neg (show ¬ (2 * k + 2 ≤ k + 2) by omega), if_neg (show ¬ (2 * k + 2 ≤ 2 * k + 1) by omega)]
  simp

theorem val_one_last (k : ℕ) (hk : 1 ≤ k) (u : GInt) (hu : u ∈ tileShape ZTile.one) :
    paperLadderValue (2 * (k : ℤ) + 2) (u + (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 3)) =
      zTileOdo ZTile.one u + ptDot (aHm k (2 * k + 2)) u + cHm k (2 * k + 2) := by
  rw [aHm_last k, cHm_last k hk]
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  have hpt : (a, b) + (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 3)
      = (a + (2 * (k : ℤ) + 3), 2 * (k : ℤ) + (b + 2 + 1)) := by
    rw [Prod.mk_add_mk]
    congr 1
    ring
  rw [hpt, plV, tri_gen]
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [zTileOdo, oneOdometer, ptDot, c0Hm, min_def, max_def] <;>
    split_ifs <;> (try (exfalso; omega)) <;> ring

end FLatticePaper.Tiles.BaseHmOddLast
