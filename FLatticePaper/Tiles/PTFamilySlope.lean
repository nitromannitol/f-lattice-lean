import FLatticePaper.Tiles.PTChain
import FLatticePaper.Tiles.SurgicalAffineChain

/-! The slope of a placed family's tile odometer: the base slope of the tile type plus the family's affine factor. Together
with `tileAffine` (the slope on the single placed tile minus the base slope), this gives the affine factors of the corner tiles
of a register family, which the seam identities of `SeamIdentities` use. -/

namespace FLatticePaper.Tiles

theorem PTFamily.slope_tile (F : PTFamily) (k : ℕ) :
    slopeOf (F.odo k) (F.dom k) =
      zTileBaseSlope (F.tile k).1 + (((F.a k).1 : ℚ), ((F.a k).2 : ℚ)) := by
  unfold PTFamily.odo PTFamily.dom zTileBaseSlope
  exact slopeOf_translate_affine (zTileOdo (F.tile k).1) (tileShape (F.tile k).1) (F.tile k).2 (F.a k) (F.b k)
    (tileShape_unitSquares_ne_zt _)

/-- The affine factor of a family's tile is its `a` (`tileAffine` of the odometer on the placed tile). -/
theorem PTFamily.tileAffine_tile (F : PTFamily) (k : ℕ) :
    tileAffine (F.odo k) (F.tile k) = (((F.a k).1 : ℚ), ((F.a k).2 : ℚ)) := by
  unfold tileAffine
  have h := F.slope_tile k
  have hd : placedSites [F.tile k] = F.dom k := by
    unfold PTFamily.dom placedSites
    simp
  rw [hd, h]
  simp

end FLatticePaper.Tiles
