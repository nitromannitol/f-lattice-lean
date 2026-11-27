import FLatticePaper.Plane.SurgicalGlobalOdometers
import FLatticePaper.Tiles.OddGlobalGlue

/-! The glued odd odometer has the two generator periods of its modified deck (`HasGeneratorPeriods`), so the periodicity
algebra of `SurgicalGlobalOdometers` applies to it. This is the standard odd child; the covering H2 is inherited. -/

namespace FLatticePaper

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CommonExtFamily
  FLatticePaper.Tiles.CommonExtStandard FLatticePaper.Tiles.PointNonNeighbour FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.CommonExtWitness FLatticePaper.Tiles.CellDerivation

theorem surgical_odd_generator_periods (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X_v : ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z → z - texV1Odd (fracOdd w) ∈ oddTile w →
      tileCovers (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) z)
    (H2Y_v : ∀ z, BoundaryVertex ({t : GInt | t - texV1Odd (fracOdd w) ∈ cellTileOf (oddTile w)} : Set GInt) z → z ∈ oddTile w →
      tileCovers (vRevStringAt (vWordOf w false).reverse (texV1Odd (fracOdd w))) z)
    (H2X_h : ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z → z - (-texV2 (fracOdd w)) ∈ oddTile w →
      tileCovers (hStringAt (hWordOf w false) 0) z)
    (H2Y_h : ∀ z, BoundaryVertex ({t : GInt | t - (-texV2 (fracOdd w)) ∈ cellTileOf (oddTile w)} : Set GInt) z → z ∈ oddTile w →
      tileCovers (hRevStringAt (hWordOf w false).reverse (1, -2)) z) :
    ∃ f : Field, (∃ c : ℤ, ∀ x ∈ (↑(oddTile w) : Set (ℤ × ℤ)), f x = (oddO w).val x + c) ∧
      ∃ c1 c2 : ℤ, HasGeneratorPeriods (fracOdd w) f c1 c2 := by
  obtain ⟨f, hT, ⟨c1, hK⟩, ⟨c2, hV⟩⟩ := FLatticePaper.Tiles.odd_glue S oddO evenO h w H2X_v H2Y_v H2X_h H2Y_h
  have hkern : (fracOdd w).modifiedDeck.kernel = texV1Odd (fracOdd w) :=
    FLatticePaper.Tiles.DeckCoverage.modifiedDeck_kernel_of_odd (parentsAt_valid w).current_odd_parity
  refine ⟨f, hT, c1, c2, ?_⟩
  unfold HasGeneratorPeriods
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [hkern]
    exact hK x
  · have hg : dotZ ((fracOdd w).num, -(fracOdd w).den) x = -(fracOdd w).transverseGrade x := by
      simp only [dotZ, Fraction.transverseGrade]
      ring
    have h2 := hV x
    rw [hg] at h2
    show f (x + texV2 (fracOdd w)) = f x - (fracOdd w).transverseGrade x + c2
    linarith

end FLatticePaper
