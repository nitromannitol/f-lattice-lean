import FLatticePaper.Tiles.StandardAll
import FLatticePaper.Tiles.StandardCornerCells

/-! Point-level exclusion of non-neighbour translates for the standard tiles.

Let `P` be the point set of a standard tile, with H1 (`HasCornerCell P`), and let `u = k v₁ + k' v₂` be a lattice vector with
`2 ≤ |k|` or `2 ≤ |k'|` (a non-surround vector). If `z ∈ P` and `z - u ∈ P`, then `z` is a corner of a cell `x` of the cell tile
of `P` and `z - u` a corner of a cell `y` of it. With the unit shift `δ = y - x + u` (both coordinates in `[-1, 1]`) one has
`x - (u - δ) = y`, so the cell tile overlaps its translate by `u - δ`. `gap_not_overlap` excludes that overlap. -/

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardDischarge
open FLatticePaper.Tiles.StandardAll

namespace FLatticePaper.Tiles.PointNonNeighbour

/-- The corners of a unit cell: a point of the cell with lower-left corner `c` lies in its box. -/
theorem cellCorners_bounds {c z : GInt} (h : z ∈ cellCorners c) :
    c.1 ≤ z.1 ∧ z.1 ≤ c.1 + 1 ∧ c.2 ≤ z.2 ∧ z.2 ≤ c.2 + 1 := by
  rw [FLatticePaper.Tiles.Standard.mem_cellCorners_iff] at h
  rcases h with rfl | rfl | rfl | rfl <;> (try simp only [gOne, gI, Prod.fst_add, Prod.snd_add]) <;> omega

/-- A cell whose four corners lie in `P` belongs to the cell tile of `P`. -/
theorem mem_cellTileOf_of_cell {P : Finset GInt} {x : GInt} (hx : ∀ y ∈ cellCorners x, y ∈ P) :
    x ∈ cellTileOf P := by
  unfold cellTileOf
  rw [Finset.mem_filter]
  exact ⟨hx x ((FLatticePaper.Tiles.Standard.mem_cellCorners_iff x x).2 (Or.inl rfl)), fun y hy => hx y hy⟩

/-- If no unit-shifted translate `u - δ` of the cell tile of `P` overlaps it, then `P` and `P + u` share no point. -/
theorem no_point_contact_of_gap {P : Finset GInt} (hP : HasCornerCell P) (u : GInt)
    (hgap : ∀ δ : GInt, -1 ≤ δ.1 ∧ δ.1 ≤ 1 ∧ -1 ≤ δ.2 ∧ δ.2 ≤ 1 → ¬ Overlap (cellTileOf P) (u - δ)) :
    ∀ z ∈ P, z - u ∉ P := by
  intro z hz hzu
  obtain ⟨x, hxz, hxP⟩ := hP z hz
  obtain ⟨y, hyz, hyP⟩ := hP (z - u) hzu
  have hx : x ∈ cellTileOf P := mem_cellTileOf_of_cell hxP
  have hy : y ∈ cellTileOf P := mem_cellTileOf_of_cell hyP
  obtain ⟨hx1, hx2, hx3, hx4⟩ := cellCorners_bounds hxz
  have hy' : y.1 ≤ z.1 - u.1 ∧ z.1 - u.1 ≤ y.1 + 1 ∧ y.2 ≤ z.2 - u.2 ∧ z.2 - u.2 ≤ y.2 + 1 :=
    cellCorners_bounds hyz
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy'
  have hb : -1 ≤ (y - x + u).1 ∧ (y - x + u).1 ≤ 1 ∧ -1 ≤ (y - x + u).2 ∧ (y - x + u).2 ≤ 1 := by
    show -1 ≤ y.1 - x.1 + u.1 ∧ y.1 - x.1 + u.1 ≤ 1 ∧ -1 ≤ y.2 - x.2 + u.2 ∧ y.2 - x.2 + u.2 ≤ 1
    omega
  have hxy : x - (u - (y - x + u)) = y :=
    Prod.ext (by show x.1 - (u.1 - (y.1 - x.1 + u.1)) = y.1; ring)
      (by show x.2 - (u.2 - (y.2 - x.2 + u.2)) = y.2; ring)
  have hov : Overlap (cellTileOf P) (u - (y - x + u)) := ⟨x, hx, by rw [hxy]; exact hy⟩
  exact hgap (y - x + u) hb hov

/-- The odd standard tile: a non-surround lattice translate misses it (core form, with the packing vectors). -/
theorem oddTile_nonneighbour_core (w : Farey.Word) (i j : ℤ) (hns : 2 ≤ |i| ∨ 2 ≤ |j|) :
    ∀ z ∈ oddTile w, z - (i * (almostV₁ (oddBottom w)).1 + j * (almostV₂ (oddRight w)).1,
      i * (almostV₁ (oddBottom w)).2 + j * (almostV₂ (oddRight w)).2) ∉ oddTile w := by
  have hA := admissible_oddStandard w
  have hT := (standardBoundaryWord_all w).1
  have h1 : ∀ x ∈ oddBottom w, x = .one ∨ x = .i := hA.1.1
  have h2 := FLatticePaper.Tiles.StandardDischarge.letters_of_mulNegI_admissible hA.2
  have hn1 : ∀ x ∈ oddBottom w, x ≠ .negI := fun x hx => by
    rcases h1 x hx with rfl | rfl <;> decide
  have hn2 : ∀ x ∈ oddRight w, x ≠ .negI := fun x hx => by
    rcases h2 x hx with rfl | rfl <;> decide
  apply no_point_contact_of_gap (oddTile_hcc w)
  intro δ hδ hov
  rw [FLatticePaper.Tiles.almostV₁_eq (oddBottom w) hn1,
    FLatticePaper.Tiles.almostV₂_eq (oddRight w) hn2] at hov
  exact (FLatticePaper.Tiles.gap_not_overlap hT h1 h2 hA.1 hA.2 i j hns δ.1 δ.2 ⟨hδ.1, hδ.2.1⟩ ⟨hδ.2.2.1, hδ.2.2.2⟩) hov

/-- The even standard tile: the same, with the even packing vectors. -/
theorem evenTile_nonneighbour_core (w : Farey.Word) (i j : ℤ) (hns : 2 ≤ |i| ∨ 2 ≤ |j|) :
    ∀ z ∈ evenTile w, z - (i * (almostV₁ (evenBottom w)).1 + j * (almostV₂ (evenRight w)).1,
      i * (almostV₁ (evenBottom w)).2 + j * (almostV₂ (evenRight w)).2) ∉ evenTile w := by
  have hA := admissible_evenStandard w
  have hT := (standardBoundaryWord_all w).2
  have h1 : ∀ x ∈ evenBottom w, x = .one ∨ x = .i := hA.1.1
  have h2 := FLatticePaper.Tiles.StandardDischarge.letters_of_mulNegI_admissible hA.2
  have hn1 : ∀ x ∈ evenBottom w, x ≠ .negI := fun x hx => by
    rcases h1 x hx with rfl | rfl <;> decide
  have hn2 : ∀ x ∈ evenRight w, x ≠ .negI := fun x hx => by
    rcases h2 x hx with rfl | rfl <;> decide
  apply no_point_contact_of_gap (evenTile_hcc w)
  intro δ hδ hov
  rw [FLatticePaper.Tiles.almostV₁_eq (evenBottom w) hn1,
    FLatticePaper.Tiles.almostV₂_eq (evenRight w) hn2] at hov
  exact (FLatticePaper.Tiles.gap_not_overlap hT h1 h2 hA.1 hA.2 i j hns δ.1 δ.2 ⟨hδ.1, hδ.2.1⟩ ⟨hδ.2.2.1, hδ.2.2.2⟩) hov

/-- **Point-level non-neighbour exclusion, odd standard tiles.** For `u = k v₁ + k' v₂` with `2 ≤ |k|` or `2 ≤ |k'|`,
where `v₁ = texV1Odd (fracOdd w)`, `v₂ = texV2 (fracOdd w)` are the lattice vectors of clause (a): no point `z` of the tile
has `z - u` in the tile. -/
theorem oddTile_nonneighbour (w : Farey.Word) (k k' : ℤ) (hns : 2 ≤ |k| ∨ 2 ≤ |k'|) (z : GInt)
    (hz : z ∈ oddTile w) :
    z - (k * (texV1Odd (fracOdd w)).1 + k' * (texV2 (fracOdd w)).1,
      k * (texV1Odd (fracOdd w)).2 + k' * (texV2 (fracOdd w)).2) ∉ oddTile w := by
  rw [← FLatticePaper.Tiles.StandardBoundary.sum_oddBottom w, ← FLatticePaper.Tiles.StandardBoundary.sum_oddRight w]
  exact oddTile_nonneighbour_core w k k' hns z hz

/-- **Point-level non-neighbour exclusion, even standard tiles** (lattice `texV1Even`, `texV2`). -/
theorem evenTile_nonneighbour (w : Farey.Word) (k k' : ℤ) (hns : 2 ≤ |k| ∨ 2 ≤ |k'|) (z : GInt)
    (hz : z ∈ evenTile w) :
    z - (k * (texV1Even (fracEven w)).1 + k' * (texV2 (fracEven w)).1,
      k * (texV1Even (fracEven w)).2 + k' * (texV2 (fracEven w)).2) ∉ evenTile w := by
  rw [← FLatticePaper.Tiles.StandardBoundary.sum_evenBottom w, ← FLatticePaper.Tiles.StandardBoundary.sum_evenRight w]
  exact evenTile_nonneighbour_core w k k' hns z hz

/-! ### The diagonal translates

The cells of the tile lie in the box `[c.1 + X₂, c.1 + P) × [c.2, c.2 + H)` (`cell_bounds`), so the points of the tile lie in the
box `[c.1 + X₂, c.1 + P] × [c.2, c.2 + H]`. The translate by `g₁ + g₂` has row offset `H + 1`, and the translate by `g₁ − g₂` has
column offset `P − X₂ + 1`: each lies one unit outside the box, so the two point sets are disjoint. -/

/-- Row form: the point set misses its translate by any vector of row offset `cntI w1 + cntI w2 + 1`. -/
theorem diag_row_disjoint {P : Finset GInt} (hP : HasCornerCell P) {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt (cellTileOf P) c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (v : GInt) (hv : v.2 = cntI w1 + cntI w2 + 1) :
    ∀ z ∈ P, z - v ∉ P := by
  intro z hz hzv
  obtain ⟨x, hxz, hxP⟩ := hP z hz
  obtain ⟨y, hyz, hyP⟩ := hP (z - v) hzv
  obtain ⟨hx1, hx2, hx3, hx4⟩ := FLatticePaper.Tiles.cell_bounds hT h1 h2 x (mem_cellTileOf_of_cell hxP)
  obtain ⟨hy1, hy2, hy3, hy4⟩ := FLatticePaper.Tiles.cell_bounds hT h1 h2 y (mem_cellTileOf_of_cell hyP)
  obtain ⟨hz1, hz2, hz3, hz4⟩ := cellCorners_bounds hxz
  obtain ⟨hw1, hw2, hw3, hw4⟩ := cellCorners_bounds hyz
  have e : (z - v).2 = z.2 - v.2 := rfl
  omega

/-- Column form: the point set misses its translate by any vector of column offset `P - (X₂ - 1)`. -/
theorem diag_col_disjoint {P : Finset GInt} (hP : HasCornerCell P) {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt (cellTileOf P) c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (v : GInt) (hv : v.1 = (F2Word.sum w1).1 - ((F2Word.sum w2).1 - 1)) :
    ∀ z ∈ P, z - v ∉ P := by
  intro z hz hzv
  obtain ⟨x, hxz, hxP⟩ := hP z hz
  obtain ⟨y, hyz, hyP⟩ := hP (z - v) hzv
  obtain ⟨hx1, hx2, hx3, hx4⟩ := FLatticePaper.Tiles.cell_bounds hT h1 h2 x (mem_cellTileOf_of_cell hxP)
  obtain ⟨hy1, hy2, hy3, hy4⟩ := FLatticePaper.Tiles.cell_bounds hT h1 h2 y (mem_cellTileOf_of_cell hyP)
  obtain ⟨hz1, hz2, hz3, hz4⟩ := cellCorners_bounds hxz
  obtain ⟨hw1, hw2, hw3, hw4⟩ := cellCorners_bounds hyz
  have e : (z - v).1 = z.1 - v.1 := rfl
  omega

/-- The translate by `-v` misses the set whenever the translate by `v` does. -/
theorem point_add_disjoint_of_sub {P : Finset GInt} {v : GInt} (h : ∀ z ∈ P, z - v ∉ P) :
    ∀ z ∈ P, z + v ∉ P := by
  intro z hz hzv
  apply h (z + v) hzv
  rw [add_sub_cancel_right]
  exact hz

/-- **The diagonal translates of the odd standard tile miss it.** The four translates `±(v₁ + v₂)`, `±(v₁ - v₂)` of the packing
vectors `v₁ = almostV₁ (oddBottom w)`, `v₂ = almostV₂ (oddRight w)` (equal to `texV1Odd`, `texV2` by `sum_oddBottom`,
`sum_oddRight`). -/
theorem oddTile_diagonal_disjoint (w : Farey.Word) :
    (∀ z ∈ oddTile w, z - (texV1Odd (fracOdd w) + texV2 (fracOdd w)) ∉ oddTile w) ∧
    (∀ z ∈ oddTile w, z + (texV1Odd (fracOdd w) + texV2 (fracOdd w)) ∉ oddTile w) ∧
    (∀ z ∈ oddTile w, z - (texV1Odd (fracOdd w) - texV2 (fracOdd w)) ∉ oddTile w) ∧
    (∀ z ∈ oddTile w, z + (texV1Odd (fracOdd w) - texV2 (fracOdd w)) ∉ oddTile w) := by
  have hA := admissible_oddStandard w
  have hT := (standardBoundaryWord_all w).1
  have h1 : ∀ x ∈ oddBottom w, x = .one ∨ x = .i := hA.1.1
  have h2 := FLatticePaper.Tiles.StandardDischarge.letters_of_mulNegI_admissible hA.2
  have hn1 : ∀ x ∈ oddBottom w, x ≠ .negI := fun x hx => by
    rcases h1 x hx with rfl | rfl <;> decide
  have hn2 : ∀ x ∈ oddRight w, x ≠ .negI := fun x hx => by
    rcases h2 x hx with rfl | rfl <;> decide
  rw [← FLatticePaper.Tiles.StandardBoundary.sum_oddBottom w, ← FLatticePaper.Tiles.StandardBoundary.sum_oddRight w]
  have hrow : (almostV₁ (oddBottom w) + almostV₂ (oddRight w)).2 =
      cntI (oddBottom w) + cntI (oddRight w) + 1 := by
    rw [Prod.snd_add, FLatticePaper.Tiles.almostV₁_eq _ hn1, FLatticePaper.Tiles.almostV₂_eq _ hn2]
    show cntI (oddBottom w) + 1 + cntI (oddRight w) = cntI (oddBottom w) + cntI (oddRight w) + 1
    ring
  have hcol : (almostV₁ (oddBottom w) - almostV₂ (oddRight w)).1 =
      (F2Word.sum (oddBottom w)).1 - ((F2Word.sum (oddRight w)).1 - 1) := by
    rw [Prod.fst_sub, FLatticePaper.Tiles.almostV₁_eq _ hn1, FLatticePaper.Tiles.almostV₂_eq _ hn2]
  have hplus := diag_row_disjoint (oddTile_hcc w) hT h1 h2 _ hrow
  have hminus := diag_col_disjoint (oddTile_hcc w) hT h1 h2 _ hcol
  exact ⟨hplus, point_add_disjoint_of_sub hplus, hminus, point_add_disjoint_of_sub hminus⟩

/-- **The diagonal translates of the even standard tile miss it** (the even packing vectors). -/
theorem evenTile_diagonal_disjoint (w : Farey.Word) :
    (∀ z ∈ evenTile w, z - (texV1Even (fracEven w) + texV2 (fracEven w)) ∉ evenTile w) ∧
    (∀ z ∈ evenTile w, z + (texV1Even (fracEven w) + texV2 (fracEven w)) ∉ evenTile w) ∧
    (∀ z ∈ evenTile w, z - (texV1Even (fracEven w) - texV2 (fracEven w)) ∉ evenTile w) ∧
    (∀ z ∈ evenTile w, z + (texV1Even (fracEven w) - texV2 (fracEven w)) ∉ evenTile w) := by
  have hA := admissible_evenStandard w
  have hT := (standardBoundaryWord_all w).2
  have h1 : ∀ x ∈ evenBottom w, x = .one ∨ x = .i := hA.1.1
  have h2 := FLatticePaper.Tiles.StandardDischarge.letters_of_mulNegI_admissible hA.2
  have hn1 : ∀ x ∈ evenBottom w, x ≠ .negI := fun x hx => by
    rcases h1 x hx with rfl | rfl <;> decide
  have hn2 : ∀ x ∈ evenRight w, x ≠ .negI := fun x hx => by
    rcases h2 x hx with rfl | rfl <;> decide
  rw [← FLatticePaper.Tiles.StandardBoundary.sum_evenBottom w, ← FLatticePaper.Tiles.StandardBoundary.sum_evenRight w]
  have hrow : (almostV₁ (evenBottom w) + almostV₂ (evenRight w)).2 =
      cntI (evenBottom w) + cntI (evenRight w) + 1 := by
    rw [Prod.snd_add, FLatticePaper.Tiles.almostV₁_eq _ hn1, FLatticePaper.Tiles.almostV₂_eq _ hn2]
    show cntI (evenBottom w) + 1 + cntI (evenRight w) = cntI (evenBottom w) + cntI (evenRight w) + 1
    ring
  have hcol : (almostV₁ (evenBottom w) - almostV₂ (evenRight w)).1 =
      (F2Word.sum (evenBottom w)).1 - ((F2Word.sum (evenRight w)).1 - 1) := by
    rw [Prod.fst_sub, FLatticePaper.Tiles.almostV₁_eq _ hn1, FLatticePaper.Tiles.almostV₂_eq _ hn2]
  have hplus := diag_row_disjoint (evenTile_hcc w) hT h1 h2 _ hrow
  have hminus := diag_col_disjoint (evenTile_hcc w) hT h1 h2 _ hcol
  exact ⟨hplus, point_add_disjoint_of_sub hplus, hminus, point_add_disjoint_of_sub hminus⟩

end FLatticePaper.Tiles.PointNonNeighbour
