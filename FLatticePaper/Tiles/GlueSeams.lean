import FLatticePaper.Tiles.GlueChain
import FLatticePaper.Tiles.PTFamilySlope

/-! # The seams of a child string

At a seam of a child string the last tile of one placed block and the first tile of the next overlap (with offset `1 + i`,
`1`, `-1 + 2i`, `-1 + i` for the bottom, top, left and right strings), so the boundary clause of `PTFamily.SeamClause` is
vacuous, and the slope clause is a relation between the affine factors of the two tiles (`slope_tile`): with the surgical
table, the next factor is the last one plus `0`, `(1, 0)`, `(0, -1)`, `(1, -1)` respectively. -/

namespace FLatticePaper.Tiles.GlueSeams

open FLatticePaper.Tiles

/-- A seam whose two tiles overlap, with the slope clause in the form of `slope_tile`. -/
theorem seam_of (o : Orientation) (rev : Bool) (F G : PTFamily)
    (hslope : (zTileBaseSlope (G.tile 0).1 + (((G.a 0).1 : ℚ), ((G.a 0).2 : ℚ))) -
        (zTileBaseSlope (F.tile (F.n - 1)).1 + (((F.a (F.n - 1)).1 : ℚ), ((F.a (F.n - 1)).2 : ℚ))) =
      surgicalSlopeDiff o rev (zTileLetter (F.tile (F.n - 1)).1) (zTileLetter (G.tile 0).1))
    (hov : ∃ x, x ∈ F.dom (F.n - 1) ∧ x ∈ G.dom 0) : PTFamily.SeamClause o rev F G := by
  unfold PTFamily.SeamClause
  rw [PTFamily.slope_tile, PTFamily.slope_tile]
  exact ⟨hslope, fun h => absurd hov h⟩

theorem mem_dom_of (F : PTFamily) (k : ℕ) (ty : ZTile) (pos : GInt) (ht : F.tile k = (ty, pos)) (y : GInt)
    (hy : y ∈ tileShape ty) : pos + y ∈ F.dom k := by
  unfold PTFamily.dom
  rw [ht]
  exact List.mem_map.2 ⟨y, hy, add_comm _ _⟩

/-- **A bottom seam** `T_{0/1} | T_{1/1}` (offset `1 + i`), with equal affine factors. -/
theorem seam_bot (F G : PTFamily) (P : GInt) (hF : F.tile (F.n - 1) = (ZTile.zero, P))
    (hG : G.tile 0 = (ZTile.one, P + (1, 1))) (ha : G.a 0 = F.a (F.n - 1)) :
    PTFamily.SeamClause .horizontal false F G := by
  apply seam_of
  · rw [hF, hG, ha]
    ext <;> (simp [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]; try ring)
  · refine ⟨P + (1, 1), mem_dom_of F _ _ _ hF (1, 1) (by decide), ?_⟩
    have h := mem_dom_of G 0 _ _ hG (0, 0) (by decide)
    rwa [show ∀ v : GInt, v + ((0 : ℤ), (0 : ℤ)) = v from fun v => by ext <;> simp] at h

/-- **A top seam** `T_{1/1} | T_{0/1}` of a reversed horizontal string (offset `1`), the enlarged tile allowed. -/
theorem seam_top (F G : PTFamily) (P : GInt) (t : ZTile) (htF : t = ZTile.one ∨ t = ZTile.oneD)
    (hF : F.tile (F.n - 1) = (t, P)) (hG : G.tile 0 = (ZTile.zero, P + (1, 0))) (ha : G.a 0 = F.a (F.n - 1) + (1, 0)) :
    PTFamily.SeamClause .horizontal true F G := by
  apply seam_of
  · rw [hF, hG, ha]
    rcases htF with rfl | rfl <;> (ext <;> (simp [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one, zTileBaseSlope_oneD]; try ring))
  · have h1 : ((1 : ℤ), (0 : ℤ)) ∈ tileShape t := by rcases htF with rfl | rfl <;> decide
    refine ⟨P + (1, 0), mem_dom_of F _ _ _ hF (1, 0) h1, ?_⟩
    have h := mem_dom_of G 0 _ _ hG (0, 0) (by decide)
    rwa [show ∀ v : GInt, v + ((0 : ℤ), (0 : ℤ)) = v from fun v => by ext <;> simp] at h

/-- **A left seam** `T_{0/1} | T_{1/1}` of a reversed vertical string (offset `-1 + 2i`). -/
theorem seam_left (F G : PTFamily) (P : GInt) (hF : F.tile (F.n - 1) = (ZTile.zero, P))
    (hG : G.tile 0 = (ZTile.one, P + (-1, 2))) (ha : G.a 0 = F.a (F.n - 1) + (0, -1)) :
    PTFamily.SeamClause .vertical true F G := by
  apply seam_of
  · rw [hF, hG, ha]
    ext <;> (simp [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]; try ring)
  · refine ⟨P + (0, 2), mem_dom_of F _ _ _ hF (0, 2) (by decide), ?_⟩
    have h := mem_dom_of G 0 _ _ hG (1, 0) (by decide)
    have e : P + (-1, 2) + ((1 : ℤ), (0 : ℤ)) = P + (0, 2) := by ext <;> simp
    rwa [e] at h

/-- **A right seam** `T_{1/1} | T_{0/1}` of a forward vertical string (offset `-1 + i`). -/
theorem seam_right (F G : PTFamily) (P : GInt) (hF : F.tile (F.n - 1) = (ZTile.one, P))
    (hG : G.tile 0 = (ZTile.zero, P + (-1, 1))) (ha : G.a 0 = F.a (F.n - 1) + (1, -1)) :
    PTFamily.SeamClause .vertical false F G := by
  apply seam_of
  · rw [hF, hG, ha]
    ext <;> (simp [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]; try ring)
  · refine ⟨P + (0, 1), mem_dom_of F _ _ _ hF (0, 1) (by decide), ?_⟩
    have h := mem_dom_of G 0 _ _ hG (1, 0) (by decide)
    have e : P + (-1, 1) + ((1 : ℤ), (0 : ℤ)) = P + (0, 1) := by ext <;> simp
    rwa [e] at h

/-! ### Placed families -/

theorem placed_tile (F : PTFamily) (off a : GInt) (c : ℤ) (k : ℕ) (hk : k < F.n) :
    (F.placed off a c).tile k = ((F.tile k).1, (F.tile k).2 + off) := by
  unfold PTFamily.placed
  show ((F.translate off).affineAdd a c).ts.getD k _ = _
  show (F.translate off).ts.getD k _ = _
  exact PTFamily.translate_tile F off k hk

theorem placed_a (F : PTFamily) (off a : GInt) (c : ℤ) (k : ℕ) : (F.placed off a c).a k = F.a k + a := rfl

end FLatticePaper.Tiles.GlueSeams
