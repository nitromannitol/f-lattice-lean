import FLatticePaper.Plane.SurgicalGlobalOdometers
import FLatticePaper.Tiles.EvenGlobalGlue

/-! The glued even odometer has the two generator periods of its modified deck (`HasGeneratorPeriods`), so the periodicity
algebra of `SurgicalGlobalOdometers` applies to the even child. The covering H2 is inherited. -/

namespace FLatticePaper

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CommonExtFamily
  FLatticePaper.Tiles.CommonExtStandard FLatticePaper.Tiles.PointNonNeighbour FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.CommonExtWitness FLatticePaper.Tiles.CellDerivation

theorem surgical_even_generator_periods (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X_v : ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z →
      tileCovers (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) z)
    (H2Y_v : ∀ z, BoundaryVertex ({t : GInt | t - texV1Even (fracEven w) ∈ cellTileOf (evenTile w)} : Set GInt) z →
      tileCovers (vRevStringAt (vWordOf w true).reverse (texV1Even (fracEven w))) z)
    (H2X_h : ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z →
      tileCovers (hStringAt (hWordOf w true) 0) z)
    (H2Y_h : ∀ z, BoundaryVertex ({t : GInt | t - (-texV2 (fracEven w)) ∈ cellTileOf (evenTile w)} : Set GInt) z →
      tileCovers (hRevStringAt (hWordOf w true).reverse (1, -2)) z) :
    ∃ f : Field, (∃ c : ℤ, ∀ x ∈ (↑(evenTile w) : Set (ℤ × ℤ)), f x = (evenO w).val x + c) ∧
      ∃ c1 c2 : ℤ, HasGeneratorPeriods (fracEven w) f c1 c2 := by
  obtain ⟨f, hT, ⟨c1, hK⟩, ⟨c2, hV⟩⟩ := FLatticePaper.Tiles.even_glue S oddO evenO h w H2X_v H2Y_v H2X_h H2Y_h
  have hkern : (fracEven w).modifiedDeck.kernel = texV1Even (fracEven w) :=
    FLatticePaper.Tiles.DeckCoverage.modifiedDeck_kernel_of_even (parentsAt_valid w).current_even_parity
  refine ⟨f, hT, c1, c2, ?_⟩
  unfold HasGeneratorPeriods
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [hkern]
    exact hK x
  · have hg : dotZ ((fracEven w).num, -(fracEven w).den) x = -(fracEven w).transverseGrade x := by
      simp only [dotZ, Fraction.transverseGrade]
      ring
    have h2 := hV x
    rw [hg] at h2
    show f (x + texV2 (fracEven w)) = f x - (fracEven w).transverseGrade x + c2
    linarith

end FLatticePaper
