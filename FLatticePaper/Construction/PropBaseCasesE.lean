import FLatticePaper.Tiles.LadderVerticalRespects
import FLatticePaper.Tiles.AltStairRespects
import FLatticePaper.Tiles.NearStairVerticalRespects
import FLatticePaper.Tiles.NearLadderAltRespects

/-! # `prop:base_cases`, item (e): the alternate tiles are partial pseudo-squares respected by the alternate odometers

The four rows of the alternate table of item (e) are assembled from the row lemmas. The tile `T̂_{1/d}` (or `T̂_{p_1}`,
`T̂_{q_1}`) is indexed by `d` and the word by `k`; the table couples them as `d = 2k+2` for the odd `3^k` row and the even
`2^k` row, and as `d = 2k+3` for the even `3^k` row and the odd `2^k` row. The staircase row is anchored at the exceptional
point `c(T̂_{1/d}) = (0,0)`; the other rows are anchored at the lower-left point of the tile. -/

namespace FLatticePaper.Construction

open FLatticePaper.Tiles

/-- A partial `w_v`-pseudo-square is witnessed by its respect: the anchor and the inside-tile witness are part of it. -/
theorem isPartialV_of_respectsPartialV {T : Set GInt} {wv : BinaryWord} {S : GInt → ℤ}
    (h : RespectsPartialV T wv S) : IsPartialV T wv := by
  obtain ⟨c, hLL, c', hIn, -, -⟩ := h
  exact ⟨c, hLL, c', hIn⟩

/-- A partial `w_h`-pseudo-square is witnessed by its respect: the anchor and the inside-tile witness are part of it. -/
theorem isPartialH_of_respectsPartialH {T : Set GInt} {wh : BinaryWord} {S : GInt → ℤ}
    (h : RespectsPartialH T wh S) : IsPartialH T wh := by
  obtain ⟨c, hLL, c', hIn, -, -⟩ := h
  exact ⟨c, hLL, c', hIn⟩

/-- Item (e) of `prop:base_cases`: the four rows of the alternate table. -/
theorem prop_base_cases_e :
    -- row 1: `3^k` odd, `k ≥ 1`, `T̂_{1/d}` with `d = 2k+2`, `w_v = p^{2k+1} q`
    (∀ k : ℕ, 1 ≤ k →
      IsPartialV (paperLadderAltTile (2 * (k : ℤ) + 2)) (lvWord k) ∧
        RespectsPartialV (paperLadderAltTile (2 * (k : ℤ) + 2)) (lvWord k)
          (paperLadderAltValue (2 * (k : ℤ) + 2))) ∧
    -- row 2: `3^k` even, `k ≥ 0`, `T̂_{1/d}` with `d = 2k+3`, `w_h = q p^{k+1}`, anchored at `(0,0)`
    (∀ k : ℕ,
      IsPartialHAt (paperStairAltTile (2 * (k : ℤ) + 3)) (0, 0) (stairH k) ∧
        RespectsPartialHAt (paperStairAltTile (2 * (k : ℤ) + 3)) (0, 0) (stairH k)
          (paperStairAltValue (2 * (k : ℤ) + 3))) ∧
    -- row 3: `2^k` odd, `k ≥ 0`, `T̂_{p_1}` with `d = 2k+3`, `w_v = p q^{k+1}`
    (∀ k : ℕ,
      IsPartialV (paperNearStairAltTile (2 * (k : ℤ) + 3)) (pqWord k) ∧
        RespectsPartialV (paperNearStairAltTile (2 * (k : ℤ) + 3)) (pqWord k)
          (paperNearStairAltValue (2 * (k : ℤ) + 3))) ∧
    -- row 4: `2^k` even, `k ≥ 1`, `T̂_{q_1}` with `d = 2k+2`, `w_h = q^{2k+1} p`
    (∀ k : ℕ, 1 ≤ k →
      IsPartialH (paperNearLadderAltTile (2 * (k : ℤ) + 2)) (nlaWord k) ∧
        RespectsPartialH (paperNearLadderAltTile (2 * (k : ℤ) + 2)) (nlaWord k)
          (paperNearLadderAltValue (2 * (k : ℤ) + 2))) :=
  ⟨fun k hk => ⟨isPartialV_of_respectsPartialV (lv_respectsPartialV k hk), lv_respectsPartialV k hk⟩,
    fun k => ⟨altStair_isPartialHAt k, altStair_respectsPartialHAt k⟩,
    fun k => ⟨isPartialV_of_respectsPartialV (pq_respectsPartialV k), pq_respectsPartialV k⟩,
    fun k hk => ⟨isPartialH_of_respectsPartialH (nla_respectsPartialH k hk), nla_respectsPartialH k hk⟩⟩

end FLatticePaper.Construction
