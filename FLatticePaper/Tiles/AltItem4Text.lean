import FLatticePaper.Tiles.AltItem4Rot
import FLatticePaper.Tiles.VerticalH2

/-! # Item (4) of `lemma:alternate_tile_properties` in the form of the text

For every non-base word, both alternate children `T̂` and every neighbour `v = i v₁ + j v₂` (`|i|, |j| ≤ 1`, `v ≠ 0`), every
point `x` of `T̂ ∩ (T̂ + v)` lies in a stacked zero-one string of the surrounding (`OnStackedString`: on both strands of the
horizontal or the vertical stacked string of a translate of a standard tile), or the two translates overlap completely on a
subtile containing `x` (a copy `J` of the decomposition of `T̂` with `J ⊆ T̂ ∩ (T̂ + v)`).

The string case is the enclosure form `StackedAt` of `AltItem4Defs` through item (c) of the standard tiles: for `z ∈ T` with
`z + v₂ ∈ T`, `z` lies on the forward horizontal string of `T` and on its reversed horizontal string at `(1, -2)`
(`OverlapSides`, `HorizontalTop`); for `z ∈ T` with `z - v₁ ∈ T`, on the forward vertical string of `T` and on its reversed
vertical string at `v₁` (`VerticalCover`, `VerticalH2`). -/

namespace FLatticePaper.Tiles.AltItem4

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)

/-- `x` lies on both strands of the horizontal or of the vertical stacked zero-one string of the translate by `a` of the
standard tile of `(u, par)`: the forward string of the tile and the reversed string of its translate by `-v₂` (horizontal)
or by `v₁` (vertical), placed as in item (c) of the standard tiles. -/
def OnStackedString (x : Site) : Prop :=
  ∃ (u : Word) (par : Bool) (a : Site),
    (tileCovers (hStringAt (hWordOf u par) 0) (x - a) ∧
        tileCovers (hRevStringAt (hWordOf u par).reverse (1, -2)) (x - a)) ∨
      (tileCovers (vStringAt (vWordOf u par) (lastPosOf (hStringAt (hWordOf u par) 0))) (x - a) ∧
        tileCovers (vRevStringAt (vWordOf u par).reverse (latV1 u par)) (x - a))

/-- Item (c) of the standard tiles, horizontal: a point of `T ∩ (T - v₂)` lies on both horizontal strands. -/
theorem stacked_h (u : Word) (par : Bool) (z : Site) (h1 : z ∈ SiteStrings.tileOf u par)
    (h2 : z + texV2 (fracOf u par) ∈ SiteStrings.tileOf u par) :
    tileCovers (hStringAt (hWordOf u par) 0) z ∧ tileCovers (hRevStringAt (hWordOf u par).reverse (1, -2)) z := by
  cases par
  · simp only [SiteStrings.tileOf, fracOf, Bool.false_eq_true, if_false] at h1 h2
    have h2' : z - (-texV2 (StandardClause.fracOdd u)) ∈ oddTile u := by rw [sub_neg_eq_add]; exact h2
    refine ⟨HorizontalSides.bottom_covered_odd u z (OverlapSides.odd_bottom_of_overlap u z h1 h2'), ?_⟩
    have hb := OverlapSides.odd_top_of_overlap u (z - (-texV2 (StandardClause.fracOdd u))) h2' (by rwa [sub_add_cancel])
    have hc := HorizontalTop.top_covered_odd u _ hb
    have e : F2Word.sum (StandardBoundary.oddBottom u) + F2Word.sum (StandardBoundary.oddRight u) -
        (F2Word.sum (StandardBoundary.oddBottom u) + F2Word.sum (StandardBoundary.oddRight u) -
          (z - (-texV2 (StandardClause.fracOdd u)))) + (-texV2 (StandardClause.fracOdd u)) = z := by abel
    rwa [e] at hc
  · simp only [SiteStrings.tileOf, fracOf, if_true] at h1 h2
    have h2' : z - (-texV2 (StandardClause.fracEven u)) ∈ evenTile u := by rw [sub_neg_eq_add]; exact h2
    refine ⟨HorizontalSides.bottom_covered_even u z (OverlapSides.even_bottom_of_overlap u z h1 h2'), ?_⟩
    have hb := OverlapSides.even_top_of_overlap u (z - (-texV2 (StandardClause.fracEven u))) h2' (by rwa [sub_add_cancel])
    have hc := HorizontalTop.top_covered_even u _ hb
    have e : F2Word.sum (StandardBoundary.evenBottom u) + F2Word.sum (StandardBoundary.evenRight u) -
        (F2Word.sum (StandardBoundary.evenBottom u) + F2Word.sum (StandardBoundary.evenRight u) -
          (z - (-texV2 (StandardClause.fracEven u)))) + (-texV2 (StandardClause.fracEven u)) = z := by abel
    rwa [e] at hc

/-- Item (c) of the standard tiles, vertical: a point of `T ∩ (T + v₁)` lies on both vertical strands. -/
theorem stacked_v (u : Word) (par : Bool) (z : Site) (h1 : z ∈ SiteStrings.tileOf u par)
    (h2 : z - latV1 u par ∈ SiteStrings.tileOf u par) :
    tileCovers (vStringAt (vWordOf u par) (lastPosOf (hStringAt (hWordOf u par) 0))) z ∧
      tileCovers (vRevStringAt (vWordOf u par).reverse (latV1 u par)) z := by
  cases par
  · simp only [SiteStrings.tileOf, latV1, fracOf, Bool.false_eq_true, if_false] at h1 h2 ⊢
    refine ⟨VerticalCover.S3_odd u z (OverlapSides.odd_right_of_overlap u z h1 h2), ?_⟩
    have hu := OverlapSides.odd_left_of_overlap u (z - texV1Odd (StandardClause.fracOdd u)) h2 (by rwa [sub_add_cancel])
    have hmem : z - texV1Odd (StandardClause.fracOdd u) ∈
        (F2Word.walk 0 (StandardBoundary.oddRight u)).map (fun y => F2Word.sum (StandardBoundary.oddRight u) - y) := by
      refine List.mem_map.2 ⟨F2Word.sum (StandardBoundary.oddRight u) - (z - texV1Odd (StandardClause.fracOdd u)), hu, ?_⟩
      abel
    have hc := VerticalH2.S4_odd_all u _ hmem
    rwa [sub_add_cancel] at hc
  · simp only [SiteStrings.tileOf, latV1, fracOf, if_true] at h1 h2 ⊢
    refine ⟨VerticalCover.S3_even u z (OverlapSides.even_right_of_overlap u z h1 h2), ?_⟩
    have hu := OverlapSides.even_left_of_overlap u (z - texV1Even (StandardClause.fracEven u)) h2 (by rwa [sub_add_cancel])
    have hmem : z - texV1Even (StandardClause.fracEven u) ∈
        (F2Word.walk 0 (StandardBoundary.evenRight u)).map (fun y => F2Word.sum (StandardBoundary.evenRight u) - y) := by
      refine List.mem_map.2 ⟨F2Word.sum (StandardBoundary.evenRight u) - (z - texV1Even (StandardClause.fracEven u)), hu, ?_⟩
      abel
    have hc := VerticalH2.S4_even_all u _ hmem
    rwa [sub_add_cancel] at hc

/-- **The enclosure form gives the stacked string.** -/
theorem onStackedString_of_stackedAt (x : Site) (h : StackedAt x) : OnStackedString x := by
  obtain ⟨u, par, a, i, j, hn, h1, h2⟩ := h
  rw [mem_shift] at h1 h2
  have ev : ∀ i j : ℤ, latV u par i j = (i * (latV1 u par).1 + j * (texV2 (fracOf u par)).1,
      i * (latV1 u par).2 + j * (texV2 (fracOf u par)).2) := fun _ _ => rfl
  rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `x ∈ T + a`, `x ∈ T + a + v₁`
    refine ⟨u, par, a, Or.inr (stacked_v u par _ h1 ?_)⟩
    convert h2 using 1; rw [ev]; ext <;> simp <;> ring
  · refine ⟨u, par, a - latV1 u par, Or.inr (stacked_v u par _ ?_ ?_)⟩
    · convert h2 using 1; rw [ev]; ext <;> simp <;> ring
    · convert h1 using 1; ext <;> simp <;> ring
  · refine ⟨u, par, a + texV2 (fracOf u par), Or.inl (stacked_h u par _ ?_ ?_)⟩
    · convert h2 using 1; rw [ev]; ext <;> simp
    · convert h1 using 1; ext <;> simp <;> ring
  · refine ⟨u, par, a, Or.inl (stacked_h u par _ h1 ?_)⟩
    convert h2 using 1; rw [ev]; ext <;> simp <;> ring

/-! ### The copies are subtiles -/

theorem oddCopies_sub {w : Word} (hw : ¬ IsBase w) (J : Tile) (hJ : J ∈ oddCopies w) (y : Site) (hy : y ∈ J) :
    y ∈ altOddTile AltRotStep.B w := by
  obtain ⟨y', -, he⟩ := altOddTile_eq AltRotStep.B hw
  rw [he, Finset.mem_union, mem_oddStd_iff]
  left
  simp only [oddCopies, List.mem_append, List.mem_map] at hJ
  rcases hJ with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl ⟨a, ha, hy⟩
  · exact Or.inr ⟨a, ha, hy⟩

theorem evenCopies_sub {w : Word} (hw : ¬ IsBase w) (J : Tile) (hJ : J ∈ evenCopies w) (y : Site) (hy : y ∈ J) :
    y ∈ altEvenTile AltRotStep.B w := by
  obtain ⟨y', -, he⟩ := altEvenTile_eq AltRotStep.B hw
  rw [he, Finset.mem_union, mem_evenStd_iff]
  left
  simp only [evenCopies, List.mem_append, List.mem_map] at hJ
  rcases hJ with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl ⟨a, ha, hy⟩
  · exact Or.inr ⟨a, ha, hy⟩

/-- The conclusion in the form of the text, from the conclusion with copies. -/
theorem text_of_concl (T : Tile) (C : List Tile) (hC : ∀ J ∈ C, ∀ y ∈ J, y ∈ T) (v x : Site) (h : Concl C v x) :
    OnStackedString x ∨ ∃ J ∈ C, x ∈ J ∧ ∀ y ∈ J, y ∈ T ∧ y ∈ shift T v := by
  rcases h with ⟨J, hJ, hx, hJv⟩ | h
  · refine Or.inr ⟨J, hJ, hx, fun y hy => ⟨hC J hJ y hy, ?_⟩⟩
    rw [mem_shift]
    exact hC _ hJv _ (by rw [mem_shift, sub_neg_eq_add]; simpa using hy)
  · exact Or.inl (onStackedString_of_stackedAt x h)

/-- **Item (4), odd alternate child**: for every neighbour `v = i v₁ + j v₂` of the lattice of `T̂(p₀)`, every point of
`T̂(p₀) ∩ (T̂(p₀) + v)` lies in a stacked zero-one string, or in a copy `J` of the decomposition of `T̂(p₀)` with
`J ⊆ T̂(p₀) ∩ (T̂(p₀) + v)`. -/
theorem alt_item4_odd {w : Word} (hw : ¬ IsBase w) (i j : ℤ) (hi : i = -1 ∨ i = 0 ∨ i = 1)
    (hj : j = -1 ∨ j = 0 ∨ j = 1) (hij : ¬ (i = 0 ∧ j = 0)) (x : Site) (h1 : x ∈ altOddTile AltRotStep.B w)
    (h2 : x ∈ shift (altOddTile AltRotStep.B w) (latV w false i j)) :
    OnStackedString x ∨ ∃ J ∈ oddCopies w, x ∈ J ∧
      ∀ y ∈ J, y ∈ altOddTile AltRotStep.B w ∧ y ∈ shift (altOddTile AltRotStep.B w) (latV w false i j) :=
  text_of_concl _ _ (oddCopies_sub hw) _ _ (item4_odd hw i j hi hj hij x h1 (mem_shift.1 h2))

/-- **Item (4), even alternate child.** -/
theorem alt_item4_even {w : Word} (hw : ¬ IsBase w) (i j : ℤ) (hi : i = -1 ∨ i = 0 ∨ i = 1)
    (hj : j = -1 ∨ j = 0 ∨ j = 1) (hij : ¬ (i = 0 ∧ j = 0)) (x : Site) (h1 : x ∈ altEvenTile AltRotStep.B w)
    (h2 : x ∈ shift (altEvenTile AltRotStep.B w) (latV w true i j)) :
    OnStackedString x ∨ ∃ J ∈ evenCopies w, x ∈ J ∧
      ∀ y ∈ J, y ∈ altEvenTile AltRotStep.B w ∧ y ∈ shift (altEvenTile AltRotStep.B w) (latV w true i j) :=
  text_of_concl _ _ (evenCopies_sub hw) _ _ (item4_even hw i j hi hj hij x h1 (mem_shift.1 h2))

end FLatticePaper.Tiles.AltItem4
