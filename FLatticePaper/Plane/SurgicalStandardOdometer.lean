import FLatticePaper.Plane.SurgicalGlueOdd
import FLatticePaper.Plane.SurgicalGlueEven

/-! `lemma:global_odometers`, the standard case, assembled for both children of a fraction: the glued extension of the
tile odometer (`odd_glue`, `even_glue`) has the two generator periods of its modified deck, hence the periodicity
`SatisfiesPeriodicity` and the quadratic growth `HasQuadraticGrowth` (through `satisfiesPeriodicity_of_generatorPeriods`
and `generator_periods_growth`), and the corrected periodicity of `surgical_corrected_periodicity`. The covering hypotheses
H2 of the closed-walk theorems are named and inherited. Superharmonicity and recurrence are not part of this statement. -/

namespace FLatticePaper

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CommonExtFamily
  FLatticePaper.Tiles.CommonExtStandard FLatticePaper.Tiles.PointNonNeighbour FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.CommonExtWitness FLatticePaper.Tiles.CellDerivation
open scoped Matrix

theorem surgical_global_odometer_standard_odd (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
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
    ∃ g : Field, (∃ c : ℤ, ∀ x ∈ (↑(oddTile w) : Set (ℤ × ℤ)), g x = (oddO w).val x + c) ∧
      SatisfiesPeriodicity (fracOdd w) g ∧ HasQuadraticGrowth g (fracOdd w).matrix ∧
      ∃ b : Fin 2 → ℝ, ∀ v ∈ (fracOdd w).modifiedDeck.span, ∀ x : Site,
        (g (x + v) : ℝ) - (1 / 2 : ℝ) * (siteVector (x + v) ⬝ᵥ ((fracOdd w).matrix *ᵥ siteVector (x + v))) -
            (b ⬝ᵥ siteVector (x + v)) =
          (g x : ℝ) - (1 / 2 : ℝ) * (siteVector x ⬝ᵥ ((fracOdd w).matrix *ᵥ siteVector x)) -
            (b ⬝ᵥ siteVector x) := by
  obtain ⟨g, hT, c1, c2, hgp⟩ := surgical_odd_generator_periods S oddO evenO h w H2X_v H2Y_v H2X_h H2Y_h
  obtain ⟨-, -, -, -, -, -, -, -, hint, -⟩ := recursion_unique w
  exact ⟨g, hT, satisfiesPeriodicity_of_generatorPeriods hint hgp, generator_periods_growth hint hgp,
    surgical_corrected_periodicity hint hgp⟩

theorem surgical_global_odometer_standard_even (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X_v : ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z → z - texV1Even (fracEven w) ∈ evenTile w →
      tileCovers (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) z)
    (H2Y_v : ∀ z, BoundaryVertex ({t : GInt | t - texV1Even (fracEven w) ∈ cellTileOf (evenTile w)} : Set GInt) z → z ∈ evenTile w →
      tileCovers (vRevStringAt (vWordOf w true).reverse (texV1Even (fracEven w))) z)
    (H2X_h : ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z → z - (-texV2 (fracEven w)) ∈ evenTile w →
      tileCovers (hStringAt (hWordOf w true) 0) z)
    (H2Y_h : ∀ z, BoundaryVertex ({t : GInt | t - (-texV2 (fracEven w)) ∈ cellTileOf (evenTile w)} : Set GInt) z → z ∈ evenTile w →
      tileCovers (hRevStringAt (hWordOf w true).reverse (1, -2)) z) :
    ∃ g : Field, (∃ c : ℤ, ∀ x ∈ (↑(evenTile w) : Set (ℤ × ℤ)), g x = (evenO w).val x + c) ∧
      SatisfiesPeriodicity (fracEven w) g ∧ HasQuadraticGrowth g (fracEven w).matrix ∧
      ∃ b : Fin 2 → ℝ, ∀ v ∈ (fracEven w).modifiedDeck.span, ∀ x : Site,
        (g (x + v) : ℝ) - (1 / 2 : ℝ) * (siteVector (x + v) ⬝ᵥ ((fracEven w).matrix *ᵥ siteVector (x + v))) -
            (b ⬝ᵥ siteVector (x + v)) =
          (g x : ℝ) - (1 / 2 : ℝ) * (siteVector x ⬝ᵥ ((fracEven w).matrix *ᵥ siteVector x)) -
            (b ⬝ᵥ siteVector x) := by
  obtain ⟨g, hT, c1, c2, hgp⟩ := surgical_even_generator_periods S oddO evenO h w H2X_v H2Y_v H2X_h H2Y_h
  obtain ⟨-, -, -, -, -, -, -, -, -, hint⟩ := recursion_unique w
  exact ⟨g, hT, satisfiesPeriodicity_of_generatorPeriods hint hgp, generator_periods_growth hint hgp,
    surgical_corrected_periodicity hint hgp⟩

end FLatticePaper
