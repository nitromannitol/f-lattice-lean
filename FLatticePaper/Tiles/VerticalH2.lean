import FLatticePaper.Tiles.OverlapSides
import FLatticePaper.Tiles.VerticalReflect
import FLatticePaper.Tiles.VerticalCover
import FLatticePaper.Plane.SurgicalStandardOdometerV

/-! The vertical covering hypotheses `H2X_v` and `H2Y_v` of the standard tiles, discharged, and the standard global odometers
with no covering hypothesis.

* `vertical_H2X_*`: a boundary vertex `z` of the cell region of `P` with `z - v_1 ∈ P` lies on the right walk of `P`
  (`OverlapSides.odd_right_of_overlap`), which the forward vertical string covers (`VerticalCover.S3_odd`, `S3_even`).
* `vertical_H2Y_*`: a boundary vertex of the cell region of `P + v_1` that lies in `P` is `t + v_1` for a point `t` of the
  left side (`OverlapSides.odd_left_of_overlap`), and the translated left side is covered by the reversed vertical string
  (`VerticalReflect.S4_odd`, `S4_even`, with S3 supplied by `VerticalCover`).
* `standard_vertical_surrounding_*`: the two vertical covering statements together (the vertical part of item (c) of
  `lemma:standard_tile_properties`, in the overlap form).
* `surgical_global_odometer_standard_*_all`: the standard global odometers of both children with no covering hypothesis. -/

namespace FLatticePaper.Tiles.VerticalH2

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
  FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.CommonExtFamily FLatticePaper.Tiles.CommonExtStandard FLatticePaper.Tiles.PointNonNeighbour
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.CommonExtWitness FLatticePaper.Tiles.CellDerivation
  FLatticePaper.Tiles.OverlapSides FLatticePaper.Tiles.VerticalReflect FLatticePaper.Tiles.VerticalCover
open scoped Matrix

/-- S4 for the odd child with S3 supplied by `VerticalCover.S3_odd`. -/
theorem S4_odd_all (w : Word) :
    ∀ t ∈ (F2Word.walk 0 (oddRight w)).map (fun y => F2Word.sum (oddRight w) - y),
      tileCovers (vRevStringAt (vWordOf w false).reverse (texV1Odd (fracOdd w))) (t + texV1Odd (fracOdd w)) :=
  S4_odd w (VerticalCover.S3_odd w)

/-- S4 for the even child with S3 supplied by `VerticalCover.S3_even`. -/
theorem S4_even_all (w : Word) :
    ∀ t ∈ (F2Word.walk 0 (evenRight w)).map (fun y => F2Word.sum (evenRight w) - y),
      tileCovers (vRevStringAt (vWordOf w true).reverse (texV1Even (fracEven w))) (t + texV1Even (fracEven w)) :=
  S4_even w (VerticalCover.S3_even w)

/-- `H2X_v`, odd child. -/
theorem vertical_H2X_odd (w : Word) :
    ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z → z - texV1Odd (fracOdd w) ∈ oddTile w →
      tileCovers (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) z :=
  fun z hz hzv => VerticalCover.S3_odd w z (odd_right_of_overlap w z (mem_of_boundaryVertex hz) hzv)

/-- `H2Y_v`, odd child. -/
theorem vertical_H2Y_odd (w : Word) :
    ∀ z, BoundaryVertex ({t : GInt | t - texV1Odd (fracOdd w) ∈ cellTileOf (oddTile w)} : Set GInt) z →
      z ∈ oddTile w → tileCovers (vRevStringAt (vWordOf w false).reverse (texV1Odd (fracOdd w))) z := by
  intro z hz hzP
  have hz' : z - texV1Odd (fracOdd w) ∈ oddTile w := mem_sub_of_boundaryVertex hz
  have hu := odd_left_of_overlap w (z - texV1Odd (fracOdd w)) hz' (by rwa [sub_add_cancel])
  have hmem : z - texV1Odd (fracOdd w) ∈
      (F2Word.walk 0 (oddRight w)).map (fun y => F2Word.sum (oddRight w) - y) := by
    refine List.mem_map.2 ⟨F2Word.sum (oddRight w) - (z - texV1Odd (fracOdd w)), hu, ?_⟩
    show F2Word.sum (oddRight w) - (F2Word.sum (oddRight w) - (z - texV1Odd (fracOdd w))) =
      z - texV1Odd (fracOdd w)
    abel
  have hc := S4_odd_all w _ hmem
  rwa [sub_add_cancel] at hc

/-- `H2X_v`, even child. -/
theorem vertical_H2X_even (w : Word) :
    ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z → z - texV1Even (fracEven w) ∈ evenTile w →
      tileCovers (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) z :=
  fun z hz hzv => VerticalCover.S3_even w z (even_right_of_overlap w z (mem_of_boundaryVertex hz) hzv)

/-- `H2Y_v`, even child. -/
theorem vertical_H2Y_even (w : Word) :
    ∀ z, BoundaryVertex ({t : GInt | t - texV1Even (fracEven w) ∈ cellTileOf (evenTile w)} : Set GInt) z →
      z ∈ evenTile w → tileCovers (vRevStringAt (vWordOf w true).reverse (texV1Even (fracEven w))) z := by
  intro z hz hzP
  have hz' : z - texV1Even (fracEven w) ∈ evenTile w := mem_sub_of_boundaryVertex hz
  have hu := even_left_of_overlap w (z - texV1Even (fracEven w)) hz' (by rwa [sub_add_cancel])
  have hmem : z - texV1Even (fracEven w) ∈
      (F2Word.walk 0 (evenRight w)).map (fun y => F2Word.sum (evenRight w) - y) := by
    refine List.mem_map.2 ⟨F2Word.sum (evenRight w) - (z - texV1Even (fracEven w)), hu, ?_⟩
    show F2Word.sum (evenRight w) - (F2Word.sum (evenRight w) - (z - texV1Even (fracEven w))) =
      z - texV1Even (fracEven w)
    abel
  have hc := S4_even_all w _ hmem
  rwa [sub_add_cancel] at hc

/-- The vertical part of item (c) of `lemma:standard_tile_properties`, odd child: the overlap is covered by the vertical strings. -/
theorem standard_vertical_surrounding_odd (w : Word) :
    (∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z → z - texV1Odd (fracOdd w) ∈ oddTile w →
      tileCovers (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) z) ∧
    (∀ z, BoundaryVertex ({t : GInt | t - texV1Odd (fracOdd w) ∈ cellTileOf (oddTile w)} : Set GInt) z →
      z ∈ oddTile w → tileCovers (vRevStringAt (vWordOf w false).reverse (texV1Odd (fracOdd w))) z) :=
  ⟨vertical_H2X_odd w, vertical_H2Y_odd w⟩

/-- The vertical part of item (c), even child. -/
theorem standard_vertical_surrounding_even (w : Word) :
    (∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z → z - texV1Even (fracEven w) ∈ evenTile w →
      tileCovers (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) z) ∧
    (∀ z, BoundaryVertex ({t : GInt | t - texV1Even (fracEven w) ∈ cellTileOf (evenTile w)} : Set GInt) z →
      z ∈ evenTile w → tileCovers (vRevStringAt (vWordOf w true).reverse (texV1Even (fracEven w))) z) :=
  ⟨vertical_H2X_even w, vertical_H2Y_even w⟩

/-- **The standard global odometer of the odd child, with no covering hypothesis.** -/
theorem surgical_global_odometer_standard_odd_all (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    :
    ∃ g : Field, (∃ c : ℤ, ∀ x ∈ (↑(oddTile w) : Set (ℤ × ℤ)), g x = (oddO w).val x + c) ∧
      SatisfiesPeriodicity (fracOdd w) g ∧ HasQuadraticGrowth g (fracOdd w).matrix ∧
      ∃ b : Fin 2 → ℝ, ∀ v ∈ (fracOdd w).modifiedDeck.span, ∀ x : Site,
        (g (x + v) : ℝ) - (1 / 2 : ℝ) * (siteVector (x + v) ⬝ᵥ ((fracOdd w).matrix *ᵥ siteVector (x + v))) -
            (b ⬝ᵥ siteVector (x + v)) =
          (g x : ℝ) - (1 / 2 : ℝ) * (siteVector x ⬝ᵥ ((fracOdd w).matrix *ᵥ siteVector x)) -
            (b ⬝ᵥ siteVector x)
:=
  FLatticePaper.Plane.SurgicalStandardOdometerV.surgical_global_odometer_standard_odd_v S oddO evenO h w
    (vertical_H2X_odd w) (vertical_H2Y_odd w)

/-- **The standard global odometer of the even child, with no covering hypothesis.** -/
theorem surgical_global_odometer_standard_even_all (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    :
    ∃ g : Field, (∃ c : ℤ, ∀ x ∈ (↑(evenTile w) : Set (ℤ × ℤ)), g x = (evenO w).val x + c) ∧
      SatisfiesPeriodicity (fracEven w) g ∧ HasQuadraticGrowth g (fracEven w).matrix ∧
      ∃ b : Fin 2 → ℝ, ∀ v ∈ (fracEven w).modifiedDeck.span, ∀ x : Site,
        (g (x + v) : ℝ) - (1 / 2 : ℝ) * (siteVector (x + v) ⬝ᵥ ((fracEven w).matrix *ᵥ siteVector (x + v))) -
            (b ⬝ᵥ siteVector (x + v)) =
          (g x : ℝ) - (1 / 2 : ℝ) * (siteVector x ⬝ᵥ ((fracEven w).matrix *ᵥ siteVector x)) -
            (b ⬝ᵥ siteVector x)
:=
  FLatticePaper.Plane.SurgicalStandardOdometerV.surgical_global_odometer_standard_even_v S oddO evenO h w
    (vertical_H2X_even w) (vertical_H2Y_even w)

end FLatticePaper.Tiles.VerticalH2
