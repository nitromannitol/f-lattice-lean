import FLatticePaper.Tiles.CornerValues
import FLatticePaper.Tiles.StdCornerAnchors

/-! # (a) of `lemma:tile-odometer-existence` for the odometers of the standard tiles

For the odd and the even child of every word, an odometer that respects the boundary words of the child (`RespectsAnchored`,
the respects conjunct of the joint family) and is compatible with its lattice adjacent copies ((c) of the weak lemma) satisfies
the translation identities (a): `CornerValues.tileTranslation_of_respects` with the anchors of the standard tiles
(`StdCornerAnchors`, w2), the end letters of the boundary words, and the parity of `v_{n/d,1}` (the odd fraction gives
`(2d, 2n)`, the even fraction has `n + d` even, `parentsAt_valid`). -/

namespace FLatticePaper.Tiles.TileTranslationStd

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily (TileTranslation LatticeSelfCompatible)
open FLatticePaper.Tiles.SurgicalWeak (RespectsAnchored)
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Construction (texV1Odd texV1Even texV2)

/-- The eight corner values (`eq:std_corner_values`) of an odometer respecting the boundary words of the odd child of `w`,
normalised. -/
theorem stdCorners_odd (w : Word) (o : PartialOdometer)
    (hR : RespectsAnchored o.dom (hWordOf w false) (vWordOf w false) o.val) :
    ∃ (α : GInt) (β : ℤ), JointFamily.FirstTileNormal o α β ∧
      TileTranslation.StdCornerValues o α β (texV1Odd ((parentsAt w).current .odd)) (texV2 ((parentsAt w).current .odd))
        (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) := by
  have hpar : ((texV1Odd ((parentsAt w).current .odd)).1 + (texV1Odd ((parentsAt w).current .odd)).2) % 2 = 0 := by
    simp only [texV1Odd]; omega
  exact CornerValues.std_corner_values o (hWordOf w false) (vWordOf w false) _ _ _ hR
    (hWordOf_head_last w false).1 (hWordOf_head_last w false).2
    (StringCorners.vertWord_head_last w).1 (StringCorners.vertWord_head_last w).2
    (StdCornerAnchors.stdAnchorX_odd w) (StdCornerAnchors.stdAnchorY_odd w) (StdCornerAnchors.stdAnchorC_odd w) hpar

/-- The eight corner values of an odometer respecting the boundary words of the even child of `w`, normalised. -/
theorem stdCorners_even (w : Word) (o : PartialOdometer)
    (hR : RespectsAnchored o.dom (hWordOf w true) (vWordOf w true) o.val) :
    ∃ (α : GInt) (β : ℤ), JointFamily.FirstTileNormal o α β ∧
      TileTranslation.StdCornerValues o α β (texV1Even ((parentsAt w).current .even)) (texV2 ((parentsAt w).current .even))
        (offsetA ((parentsAt w).current .even).num ((parentsAt w).current .even).den true) := by
  have hev := (parentsAt_valid w).current_even_parity
  unfold Fraction.Even at hev
  have hpar : ((texV1Even ((parentsAt w).current .even)).1 + (texV1Even ((parentsAt w).current .even)).2) % 2 = 0 := by
    simp only [texV1Even]; omega
  exact CornerValues.std_corner_values o (hWordOf w true) (vWordOf w true) _ _ _ hR
    (hWordOf_head_last w true).1 (hWordOf_head_last w true).2
    (StringCorners.vWord_even_head_last w).1 (StringCorners.vWord_even_head_last w).2
    (StdCornerAnchors.stdAnchorX_even w) (StdCornerAnchors.stdAnchorY_even w) (StdCornerAnchors.stdAnchorC_even w) hpar

/-- (a) for the odd child of `w`. -/
theorem tileTranslation_odd (w : Word) (o : PartialOdometer)
    (hR : RespectsAnchored o.dom (hWordOf w false) (vWordOf w false) o.val)
    (hcX : LatticeSelfCompatible o (texV1Odd ((parentsAt w).current .odd)) 0)
    (hcY : LatticeSelfCompatible o (texV2 ((parentsAt w).current .odd))
      (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true)) :
    TileTranslation o (texV1Odd ((parentsAt w).current .odd)) (texV2 ((parentsAt w).current .odd))
      (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) := by
  have hpar : ((texV1Odd ((parentsAt w).current .odd)).1 + (texV1Odd ((parentsAt w).current .odd)).2) % 2 = 0 := by
    simp only [texV1Odd]; omega
  exact CornerValues.tileTranslation_of_respects o (hWordOf w false) (vWordOf w false) _ _ _ hR
    (hWordOf_head_last w false).1 (hWordOf_head_last w false).2
    (StringCorners.vertWord_head_last w).1 (StringCorners.vertWord_head_last w).2
    (StdCornerAnchors.stdAnchorX_odd w) (StdCornerAnchors.stdAnchorY_odd w) (StdCornerAnchors.stdAnchorC_odd w)
    hpar hcX hcY

/-- (a) for the even child of `w`. -/
theorem tileTranslation_even (w : Word) (o : PartialOdometer)
    (hR : RespectsAnchored o.dom (hWordOf w true) (vWordOf w true) o.val)
    (hcX : LatticeSelfCompatible o (texV1Even ((parentsAt w).current .even)) 0)
    (hcY : LatticeSelfCompatible o (texV2 ((parentsAt w).current .even))
      (offsetA ((parentsAt w).current .even).num ((parentsAt w).current .even).den true)) :
    TileTranslation o (texV1Even ((parentsAt w).current .even)) (texV2 ((parentsAt w).current .even))
      (offsetA ((parentsAt w).current .even).num ((parentsAt w).current .even).den true) := by
  have hev := (parentsAt_valid w).current_even_parity
  unfold Fraction.Even at hev
  have hpar : ((texV1Even ((parentsAt w).current .even)).1 + (texV1Even ((parentsAt w).current .even)).2) % 2 = 0 := by
    simp only [texV1Even]; omega
  exact CornerValues.tileTranslation_of_respects o (hWordOf w true) (vWordOf w true) _ _ _ hR
    (hWordOf_head_last w true).1 (hWordOf_head_last w true).2
    (StringCorners.vWord_even_head_last w).1 (StringCorners.vWord_even_head_last w).2
    (StdCornerAnchors.stdAnchorX_even w) (StdCornerAnchors.stdAnchorY_even w) (StdCornerAnchors.stdAnchorC_even w)
    hpar hcX hcY

end FLatticePaper.Tiles.TileTranslationStd
