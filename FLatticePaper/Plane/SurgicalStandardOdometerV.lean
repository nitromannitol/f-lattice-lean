import FLatticePaper.Plane.SurgicalStandardOdometer
import FLatticePaper.Tiles.OverlapSides

/-! `lemma:global_odometers`, the standard case, with the horizontal covering hypotheses discharged: `H2X_h` and `H2Y_h` of
`surgical_global_odometer_standard_odd` and `surgical_global_odometer_standard_even` are the theorems
`OverlapSides.horizontal_H2X_odd`, `horizontal_H2Y_odd`, `horizontal_H2X_even`, `horizontal_H2Y_even`. The two vertical covering
hypotheses `H2X_v`, `H2Y_v` remain named inputs. -/

namespace FLatticePaper.Plane.SurgicalStandardOdometerV

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CommonExtFamily
  FLatticePaper.Tiles.CommonExtStandard FLatticePaper.Tiles.PointNonNeighbour FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.CommonExtWitness FLatticePaper.Tiles.CellDerivation
open scoped Matrix

/-- **The standard global odometer of the odd child**, with only the vertical covering hypotheses. -/
theorem surgical_global_odometer_standard_odd_v (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X_v : ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z → z - texV1Odd (fracOdd w) ∈ oddTile w →
      tileCovers (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) z)
    (H2Y_v : ∀ z, BoundaryVertex ({t : GInt | t - texV1Odd (fracOdd w) ∈ cellTileOf (oddTile w)} : Set GInt) z → z ∈ oddTile w →
      tileCovers (vRevStringAt (vWordOf w false).reverse (texV1Odd (fracOdd w))) z) :
    ∃ g : Field, (∃ c : ℤ, ∀ x ∈ (↑(oddTile w) : Set (ℤ × ℤ)), g x = (oddO w).val x + c) ∧
      SatisfiesPeriodicity (fracOdd w) g ∧ HasQuadraticGrowth g (fracOdd w).matrix ∧
      ∃ b : Fin 2 → ℝ, ∀ v ∈ (fracOdd w).modifiedDeck.span, ∀ x : Site,
        (g (x + v) : ℝ) - (1 / 2 : ℝ) * (siteVector (x + v) ⬝ᵥ ((fracOdd w).matrix *ᵥ siteVector (x + v))) -
            (b ⬝ᵥ siteVector (x + v)) =
          (g x : ℝ) - (1 / 2 : ℝ) * (siteVector x ⬝ᵥ ((fracOdd w).matrix *ᵥ siteVector x)) -
            (b ⬝ᵥ siteVector x) :=
  surgical_global_odometer_standard_odd S oddO evenO h w H2X_v H2Y_v
    (FLatticePaper.Tiles.OverlapSides.horizontal_H2X_odd w) (FLatticePaper.Tiles.OverlapSides.horizontal_H2Y_odd w)

/-- **The standard global odometer of the even child**, with only the vertical covering hypotheses. -/
theorem surgical_global_odometer_standard_even_v (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X_v : ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z → z - texV1Even (fracEven w) ∈ evenTile w →
      tileCovers (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) z)
    (H2Y_v : ∀ z, BoundaryVertex ({t : GInt | t - texV1Even (fracEven w) ∈ cellTileOf (evenTile w)} : Set GInt) z → z ∈ evenTile w →
      tileCovers (vRevStringAt (vWordOf w true).reverse (texV1Even (fracEven w))) z) :
    ∃ g : Field, (∃ c : ℤ, ∀ x ∈ (↑(evenTile w) : Set (ℤ × ℤ)), g x = (evenO w).val x + c) ∧
      SatisfiesPeriodicity (fracEven w) g ∧ HasQuadraticGrowth g (fracEven w).matrix ∧
      ∃ b : Fin 2 → ℝ, ∀ v ∈ (fracEven w).modifiedDeck.span, ∀ x : Site,
        (g (x + v) : ℝ) - (1 / 2 : ℝ) * (siteVector (x + v) ⬝ᵥ ((fracEven w).matrix *ᵥ siteVector (x + v))) -
            (b ⬝ᵥ siteVector (x + v)) =
          (g x : ℝ) - (1 / 2 : ℝ) * (siteVector x ⬝ᵥ ((fracEven w).matrix *ᵥ siteVector x)) -
            (b ⬝ᵥ siteVector x) :=
  surgical_global_odometer_standard_even S oddO evenO h w H2X_v H2Y_v
    (FLatticePaper.Tiles.OverlapSides.horizontal_H2X_even w) (FLatticePaper.Tiles.OverlapSides.horizontal_H2Y_even w)

end FLatticePaper.Plane.SurgicalStandardOdometerV
