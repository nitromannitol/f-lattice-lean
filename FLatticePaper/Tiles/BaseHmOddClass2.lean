import FLatticePaper.Tiles.BaseHmOddClass3

/-! # The per-tile identity of the one tile at `(2, 2k+2)`, `j = k+1`, of the reversed odd `3^k` piece

Here the letter is `q` (tile `one`), the affine factor is `(0, -(2k+1))` and the constant is `c0Hm k + 1`. -/

namespace FLatticePaper.Tiles.BaseHmOddClass2

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.BaseHmOdd FLatticePaper.Construction
open FLatticePaper.Tiles.BaseHmOddValues FLatticePaper.Tiles.BaseHmOddClass1 FLatticePaper.Tiles.BaseTileProps

theorem aHm_one (k : ℕ) : aHm k (k + 1) = ((0 : ℤ), -(2 * (k : ℤ) + 1)) := by
  unfold aHm
  rw [letter_rev_wL k (k + 1) (by omega), if_pos (Or.inl rfl)]
  ext
  · norm_num [alphaH]
  · norm_num [alphaH]
    ring

theorem cHm_one (k : ℕ) : cHm k (k + 1) = c0Hm k + 1 := by
  unfold cHm dHm
  rw [if_neg (show k + 1 ≠ 0 by omega), if_neg (show ¬ (k + 1 ≤ k) by omega), if_pos (show k + 1 ≤ k + 2 by omega)]

theorem val_one_mid (k : ℕ) (hk : 1 ≤ k) (u : GInt) (hu : u ∈ tileShape ZTile.one) :
    paperLadderValue (2 * (k : ℤ) + 2) (u + (2, 2 * (k : ℤ) + 2)) =
      zTileOdo ZTile.one u + ptDot (aHm k (k + 1)) u + cHm k (k + 1) := by
  rw [aHm_one k, cHm_one k]
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  have hpt : (a, b) + ((2 : ℤ), 2 * (k : ℤ) + 2) = (a + 2, 2 * (k : ℤ) + (b + 1 + 1)) := by
    rw [Prod.mk_add_mk]
    congr 1
    ring
  rw [hpt, plV, tri_gen]
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [zTileOdo, oneOdometer, ptDot, c0Hm, min_def, max_def] <;>
    split_ifs <;> (try (exfalso; omega)) <;> ring

end FLatticePaper.Tiles.BaseHmOddClass2
