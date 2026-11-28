import FLatticePaper.Tiles.HorizontalEnlarged
import FLatticePaper.Tiles.TileListBridge

/-! # The forward horizontal clause of `RespectsAnchored` for a base odometer (the `Hp` piece)

The forward horizontal string of a word `w` (`hStringAt w (0,0)`, with the enlarged tiles) is the tile list of the explicit
family `HPE w`, which respects it (`HPE_respects`). That family has affine factor `0` and constant `0`. So a partial
odometer `S` respects the string as soon as it equals the odometer of `HPE w` on each of its tiles. For the base words the
per-tile identity is a closed-form computation with the paper values (to be proved family by family). -/

namespace FLatticePaper.Tiles

/-- The odometer of the forward enlarged family is the zero-one tile odometer of its tile (no affine part). -/
theorem HPE_odo_eq (w : BinaryWord) (k : ℕ) (x : GInt) :
    (HPE w).odo k x = zTileOdo ((HPE w).tile k).1 (x - ((HPE w).tile k).2) := by
  simp [PTFamily.odo, HPE]

/-- The forward horizontal clause: a partial odometer respects `hStringAt w (0,0)` (forward, not reversed) as soon as it
equals `zTileOdo` of each tile of the enlarged forward family on that tile's domain. -/
theorem respectsTiles_hp_of_tiles (w : BinaryWord) (S : GInt → ℤ)
    (h : ∀ k < (HPE w).n, ∀ x ∈ (HPE w).dom k, S x = zTileOdo ((HPE w).tile k).1 (x - ((HPE w).tile k).2)) :
    RespectsTiles .horizontal false (hStringAt w (0, 0)) S := by
  refine ⟨HPE w, ?_, ?_, HPE_respects w⟩
  · exact zoForwardE_eq_hStringAt w
  · intro k hk x hx
    rw [HPE_odo_eq]
    exact h k hk x hx

end FLatticePaper.Tiles
