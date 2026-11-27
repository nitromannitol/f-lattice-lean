import FLatticePaper.Tiles.CellDerivation
import FLatticePaper.Tiles.StandardAll
import FLatticePaper.Tiles.StandardCornerCells
import FLatticePaper.Tiles.PointNonNeighbour

/-! (e) of the common extension: a common point of a standard tile `T` and its translate `T + v₁` lies in the zero-one
strings of both (`CellDerivation.common_point_in_strings`). The hypotheses H1 (every point is a corner of a cell of its
tile) come from `HasCornerCell` (`oddTile_hcc`), H3 (no cell of both tiles) from the cell uniqueness of the almost tiling
(`clauseA_standard_odd_all`), and H2 (boundary vertices lie in the strings) is an explicit hypothesis, the input of w3. -/

namespace FLatticePaper.Tiles.OverlapStrings

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
  FLatticePaper.Tiles.CellDerivation FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary
  FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardAll

/-- `HasCorner c z` is the membership `z ∈ cellCorners c`. -/
theorem hasCorner_iff_mem (c z : GInt) : HasCorner c z ↔ z ∈ cellCorners c := by
  rw [FLatticePaper.Tiles.Standard.mem_cellCorners_iff]
  simp [HasCorner, gOne, gI]

/-- Translation invariance of the corner relation. -/
theorem hasCorner_add_iff_aux (s z v : GInt) : HasCorner (s + v) (z + v) ↔ HasCorner s z := by
  simp only [HasCorner, add_right_comm s v, add_left_inj]

/-- Translating a corner relation: `HasCorner (s + v) z` iff `HasCorner s (z - v)`. -/
theorem hasCorner_add_sub_iff (s z v : GInt) : HasCorner (s + v) z ↔ HasCorner s (z - v) := by
  have h := hasCorner_add_iff_aux s (z - v) v
  rw [sub_add_cancel] at h
  exact h

/-- The general translate lemma: if the cells of `P` never coincide with a translate by `v`, then a common point of `P` and
`P + v` lies in the strings `SX` of `P` and in `SY` (the translate of the strings, by hypothesis H2 for each tile). -/
theorem common_in_strings_of_translate {P : Finset GInt} (hP : HasCornerCell P) (v : GInt)
    (hdisj : ∀ s, s ∈ cellTileOf P → s - v ∈ cellTileOf P → False) (SX SY : Set GInt)
    (H2X : ∀ z, BoundaryVertex (↑(cellTileOf P) : Set GInt) z → z ∈ SX)
    (H2Y : ∀ z, BoundaryVertex ({t : GInt | t - v ∈ cellTileOf P} : Set GInt) z → z ∈ SY) :
    ∀ z ∈ P, z - v ∈ P → z ∈ SX ∧ z ∈ SY := by
  intro z hz hzv
  have H1X : ∀ z ∈ (↑P : Set GInt), ∃ s ∈ (↑(cellTileOf P) : Set GInt), HasCorner s z := by
    intro z hz
    obtain ⟨c, hzc, hall⟩ := hP z (Finset.mem_coe.1 hz)
    exact ⟨c, Finset.mem_coe.2 (FLatticePaper.Tiles.PointNonNeighbour.mem_cellTileOf_of_cell hall),
      (hasCorner_iff_mem c z).2 hzc⟩
  have H1Y : ∀ z ∈ ({z : GInt | z - v ∈ P} : Set GInt),
      ∃ s ∈ ({t : GInt | t - v ∈ cellTileOf P} : Set GInt), HasCorner s z := by
    intro z hz
    have hz' : z - v ∈ P := hz
    obtain ⟨c, hzc, hall⟩ := hP (z - v) hz'
    refine ⟨c + v, ?_, ?_⟩
    · show (c + v) - v ∈ cellTileOf P
      rw [add_sub_cancel_right]
      exact FLatticePaper.Tiles.PointNonNeighbour.mem_cellTileOf_of_cell hall
    · exact (hasCorner_add_sub_iff c z v).2 ((hasCorner_iff_mem c (z - v)).2 hzc)
  have H3 : ∀ s, s ∈ (↑(cellTileOf P) : Set GInt) → s ∈ ({t : GInt | t - v ∈ cellTileOf P} : Set GInt) → False := by
    intro s hs hs'
    exact hdisj s (Finset.mem_coe.1 hs) hs'
  exact FLatticePaper.Tiles.CellDerivation.common_point_in_strings (↑(cellTileOf P) : Set GInt)
    ({t : GInt | t - v ∈ cellTileOf P} : Set GInt) (↑P : Set GInt) ({z : GInt | z - v ∈ P} : Set GInt) SX SY
    H1X H1Y H2X H2Y H3 z (Finset.mem_coe.2 hz) hzv

theorem v1_mem_latticeOf (v1 v2 : GInt) : v1 ∈ latticeOf v1 v2 := ⟨1, 0, by ext <;> simp⟩

/-- The vector `v₁ = almostV₁ (oddBottom w)` is nonzero: its second coordinate is `cntI + 1 ≥ 1`. -/
theorem texV1_odd_ne_zero (w : Word) : texV1Odd (fracOdd w) ≠ 0 := by
  intro h
  have h1 : ∀ x ∈ oddBottom w, x = .one ∨ x = .i := (admissible_oddStandard w).1.1
  have hn1 : ∀ x ∈ oddBottom w, x ≠ .negI := fun x hx => by
    rcases h1 x hx with rfl | rfl <;> decide
  have hv := congrArg Prod.snd h
  rw [← sum_oddBottom w, FLatticePaper.Tiles.almostV₁_eq (oddBottom w) hn1] at hv
  have hv' : cntI (oddBottom w) + 1 = 0 := hv
  have := FLatticePaper.Tiles.cntI_nonneg (oddBottom w)
  omega

/-- The cells of the odd standard tile and of its translate by `v₁` are disjoint (uniqueness of the almost tiling). -/
theorem odd_hdisj (w : Word) :
    ∀ s, s ∈ cellTileOf (oddTile w) → s - texV1Odd (fracOdd w) ∈ cellTileOf (oddTile w) → False := by
  intro s hs hsv
  obtain ⟨huniq, -⟩ := clauseA_standard_odd_all w
  have h := huniq s 0 (FLatticePaper.Tiles.zero_mem_lattice _ _) (texV1Odd (fracOdd w))
    (v1_mem_latticeOf _ _) (by rw [sub_zero]; exact hs) hsv
  exact texV1_odd_ne_zero w h.symm

/-- **(e) for the odd standard tile.** A common point of `T` and `T + v₁` lies in the strings `SX` of `T` and `SY` of `T + v₁`,
given H2 for both tiles (the boundary vertices of their cell regions lie in their strings; the input of w3). -/
theorem oddTile_common_in_strings (w : Word) (SX SY : Set GInt)
    (H2X : ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z → z ∈ SX)
    (H2Y : ∀ z, BoundaryVertex ({t : GInt | t - texV1Odd (fracOdd w) ∈ cellTileOf (oddTile w)} : Set GInt) z → z ∈ SY) :
    ∀ z ∈ oddTile w, z - texV1Odd (fracOdd w) ∈ oddTile w → z ∈ SX ∧ z ∈ SY :=
  common_in_strings_of_translate (oddTile_hcc w) (texV1Odd (fracOdd w)) (odd_hdisj w) SX SY H2X H2Y

/-- The vector `v₁ = almostV₁ (evenBottom w)` is nonzero: its second coordinate is `cntI + 1 ≥ 1`. -/
theorem texV1_even_ne_zero (w : Word) : texV1Even (fracEven w) ≠ 0 := by
  intro h
  have h1 : ∀ x ∈ evenBottom w, x = .one ∨ x = .i := (admissible_evenStandard w).1.1
  have hn1 : ∀ x ∈ evenBottom w, x ≠ .negI := fun x hx => by
    rcases h1 x hx with rfl | rfl <;> decide
  have hv := congrArg Prod.snd h
  rw [← sum_evenBottom w, FLatticePaper.Tiles.almostV₁_eq (evenBottom w) hn1] at hv
  have hv' : cntI (evenBottom w) + 1 = 0 := hv
  have := FLatticePaper.Tiles.cntI_nonneg (evenBottom w)
  omega

/-- The cells of the even standard tile and of its translate by `v₁` are disjoint. -/
theorem even_hdisj (w : Word) :
    ∀ s, s ∈ cellTileOf (evenTile w) → s - texV1Even (fracEven w) ∈ cellTileOf (evenTile w) → False := by
  intro s hs hsv
  obtain ⟨huniq, -⟩ := clauseA_standard_even_all w
  have h := huniq s 0 (FLatticePaper.Tiles.zero_mem_lattice _ _) (texV1Even (fracEven w))
    (v1_mem_latticeOf _ _) (by rw [sub_zero]; exact hs) hsv
  exact texV1_even_ne_zero w h.symm

/-- **(e) for the even standard tile**, with H2 for both tiles as hypotheses. -/
theorem evenTile_common_in_strings (w : Word) (SX SY : Set GInt)
    (H2X : ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z → z ∈ SX)
    (H2Y : ∀ z, BoundaryVertex ({t : GInt | t - texV1Even (fracEven w) ∈ cellTileOf (evenTile w)} : Set GInt) z → z ∈ SY) :
    ∀ z ∈ evenTile w, z - texV1Even (fracEven w) ∈ evenTile w → z ∈ SX ∧ z ∈ SY :=
  common_in_strings_of_translate (evenTile_hcc w) (texV1Even (fracEven w)) (even_hdisj w) SX SY H2X H2Y

end FLatticePaper.Tiles.OverlapStrings
