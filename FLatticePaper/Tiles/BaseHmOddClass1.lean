import FLatticePaper.Tiles.BaseHmOddValues

/-! # The per-tile identity of the zero tiles at `(2j-2k, 2k+1)`, `j ≤ k`, of the reversed odd `3^k` piece

For `u` in the zero tile and `j ≤ k`: `paperLadderValue (2k+2) (u + P_j) = zTileOdo zero u + ptDot (aHm k j) u + cHm k j`, where
`P_j = (2j-2k, 2k+1)`, `aHm k j = (1, -(2k+1))` and `cHm k j = c0Hm k + 2j`. -/

namespace FLatticePaper.Tiles.BaseHmOddClass1

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.BaseHmOdd FLatticePaper.Construction
open FLatticePaper.Tiles.BaseHmOddValues FLatticePaper.Tiles.BaseTileProps

/-- The triangular term of `plV` at the second coordinate `2k + (b+1)`, in closed form. -/
theorem tri_gen (k b : ℤ) :
    -((2 * k + (b + 1)) * (2 * k + (b + 1) + 1) / 2) =
      -(k * (2 * k + 2 * (b + 1) + 1) + (b + 1) * (b + 1 + 1) / 2) := by
  have hT : (b + 1) * (b + 1 + 1) = 2 * ((b + 1) * (b + 1 + 1) / 2) := by
    have h2 : (2 : ℤ) ∣ (b + 1) * (b + 1 + 1) := (Int.even_mul_succ_self (b + 1)).two_dvd
    exact (Int.mul_ediv_cancel' h2).symm
  rw [tri_eq k (b + 1) _ hT]

theorem val_zero_mid (k j : ℕ) (hk : 1 ≤ k) (hj : j ≤ k) (u : GInt) (hu : u ∈ tileShape ZTile.zero) :
    paperLadderValue (2 * (k : ℤ) + 2) (u + (2 * (j : ℤ) - 2 * (k : ℤ), 2 * (k : ℤ) + 1)) =
      zTileOdo ZTile.zero u + ptDot (aHm k j) u + cHm k j := by
  rw [aHm_mid k j hk hj, cHm_mid k j hj]
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  have hpt : (a, b) + (2 * (j : ℤ) - 2 * (k : ℤ), 2 * (k : ℤ) + 1)
      = (a + (2 * (j : ℤ) - 2 * (k : ℤ)), 2 * (k : ℤ) + (b + 1)) := by
    rw [Prod.mk_add_mk]
    congr 1
    ring
  rw [hpt, plV, tri_gen]
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [zTileOdo, zeroOdometer, ptDot, c0Hm, min_def, max_def] <;>
    split_ifs <;> (try (exfalso; omega)) <;> ring

end FLatticePaper.Tiles.BaseHmOddClass1
