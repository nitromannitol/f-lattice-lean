import FLatticePaper.Tiles.StackedWalkPattern
import FLatticePaper.Tiles.StackedBottomLink
import FLatticePaper.Tiles.CheckerFree
import FLatticePaper.Tiles.CellExtremes
import FLatticePaper.Tiles.CommonExtensionWitness
import FLatticePaper.Tiles.AlmostTilingAssembly
import FLatticePaper.Tiles.RowInterval

/-! The bottom walk of the odd tile as boundary edges of the tile. A consecutive pair of the bottom walk is a consecutive pair of
the boundary walk (the bottom side is the first part of `boundaryWordOf`), hence a directed boundary edge of the cell tile
(`IsBoundaryWordAt`). For a horizontal step `(t, h) → (t + 1, h)` the boundary edge gives the cell `(t, h)` of the tile
(`CheckerFree.boundary_out`). The highest point of the bottom walk over a column `t` is followed by such a step as soon as the walk
reaches column `t + 1`, so the cell at its height lies in the tile: the lowest cell of the tile over `t` is at or below the top
of the bottom walk over `t`. Every point of the bottom walk is a site of the tile. -/

namespace FLatticePaper.Tiles.StackedTopCell

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StackedWalkPattern FLatticePaper.Tiles.CellExtremes
  FLatticePaper.Tiles.OverlapSides FLatticePaper.Tiles.BaseCellIdentities

/-- A pair in the middle of a list is a consecutive pair of the list. -/
theorem zip_mem_pair (A B : List GInt) (p q : GInt) :
    (p, q) ∈ List.zip (A ++ p :: q :: B) ((A ++ p :: q :: B).tail) := by
  induction A with
  | nil => simp
  | cons a A ih =>
    have hne : A ++ p :: q :: B ≠ [] := by simp
    obtain ⟨m, M', hM⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.cons_append, List.tail_cons, hM] at ih ⊢
    rw [List.zip_cons_cons]
    exact List.mem_cons_of_mem _ ih

theorem zip_mem_of_mid (L : List GInt) (p q : GInt) (h : ∃ A B : List GInt, L = A ++ p :: q :: B) :
    (p, q) ∈ List.zip L L.tail := by
  obtain ⟨A, B, rfl⟩ := h
  exact zip_mem_pair A B p q

/-- **A horizontal step of the bottom walk is a boundary edge of the odd tile.** -/
theorem bnd_pair (w : Word) (p q : GInt) (l1 l2 : List GInt)
    (h : F2Word.walk (0, 0) (oddBottom w) = l1 ++ [p, q] ++ l2) :
    (p, q) ∈ (cellTileOf (oddTile w)).boundaryEdges := by
  have hB := OverlapSides.boundary_odd w
  unfold IsBoundaryWordAt at hB
  obtain ⟨-, -, -, hfin⟩ := hB
  rw [← hfin, List.mem_toFinset]
  have hw : boundaryWordOf (oddBottom w) (oddRight w) =
      oddBottom w ++ (oddRight w ++ ((F2Word.rev (oddBottom w)).hat ++ (F2Word.rev (oddRight w)).hat)) := by
    simp [boundaryWordOf, List.append_assoc]
  rw [hw, WalkDecomp.walk_append, h]
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
  apply zip_mem_of_mid
  exact ⟨_, _, rfl⟩

/-- **Every point of the bottom walk is a site of the odd tile.** -/
theorem walk_site (w : Word) : ∀ p ∈ F2Word.walk (0, 0) (oddBottom w), p ∈ oddTile w := by
  intro p hp
  by_cases hpc : p = ((0, 0) : GInt)
  · subst hpc
    exact CommonExtWitness.zero_mem_oddTile w
  · have hu : ∀ x ∈ oddBottom w, x = Unit4.one ∨ x = Unit4.i := (admissible_oddStandard w).1.1
    obtain ⟨q, l1, l2, hl⟩ := pattern_pred (oddBottom w) hu (0, 0) p hp hpc
    have he := bnd_pair w q p l1 l2 hl
    obtain ⟨s, hs, hq, hpcorner⟩ := corners_of_boundaryEdge (cellTileOf (oddTile w)) (q, p) he
    exact ((mem_cellTileOf _ _).1 hs).2 hpcorner

/-- Existence of a point of a list over a column, at maximal height among the points of that column. -/
theorem exists_top_col (L : List GInt) (t : ℤ) (h : ∃ q ∈ L, q.1 = t) :
    ∃ b ∈ L, b.1 = t ∧ ∀ q ∈ L, q.1 = t → q.2 ≤ b.2 := by
  classical
  obtain ⟨q0, hq0, hq01⟩ := h
  have hne : (L.toFinset.filter (fun q => q.1 = t)).Nonempty :=
    ⟨q0, Finset.mem_filter.2 ⟨List.mem_toFinset.2 hq0, hq01⟩⟩
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image _ (fun q : GInt => q.2) hne
  obtain ⟨hbL, hb1⟩ := Finset.mem_filter.1 hb
  refine ⟨b, List.mem_toFinset.1 hbL, hb1, ?_⟩
  intro q hqL hq1
  exact hmax q (Finset.mem_filter.2 ⟨List.mem_toFinset.2 hqL, hq1⟩)

/-- The bottom walk meets every column between its start and its end. -/
theorem col_exists (w : Word) (r : ℤ) (hr0 : 0 ≤ r) (hr1 : r ≤ (F2Word.sum (oddBottom w)).1) :
    ∃ h : ℤ, ((r, h) : GInt) ∈ F2Word.walk (0, 0) (oddBottom w) := by
  have hu : ∀ x ∈ oddBottom w, x = Unit4.one ∨ x = Unit4.i := (admissible_oddStandard w).1.1
  have hn : ∀ x ∈ oddBottom w, x ≠ Unit4.negI := fun x hx => by
    rcases hu x hx with h | h <;> rw [h] <;> decide
  have hcol : colN (oddBottom w) (0, 0) (cntI (oddBottom w)) = (F2Word.sum (oddBottom w)).1 :=
    OverlapSides.colN_top (oddBottom w) hn (cntI (oddBottom w)) le_rfl
  obtain ⟨h, -, -, hw⟩ := FLatticePaper.Tiles.StackedBottomLink.walk_reach (oddBottom w) hu r
    (cntI (oddBottom w)) hr0 (cntI_nonneg _) le_rfl (by rw [hcol]; exact hr1)
  exact ⟨h, hw⟩

/-- **The top cell of the bottom walk over a column.** For a column `t` with `0 ≤ t` and `t + 1 ≤ sum (oddBottom w).1`, the highest
point `(t, B)` of the bottom walk over `t` is a point of the walk, and the cell `(t, B)` lies in the odd tile. -/
theorem top_cell (w : Word) (t : ℤ) (ht0 : 0 ≤ t) (ht1 : t + 1 ≤ (F2Word.sum (oddBottom w)).1) :
    ∃ B : ℤ, ((t, B) : GInt) ∈ F2Word.walk (0, 0) (oddBottom w) ∧
      (∀ q ∈ F2Word.walk (0, 0) (oddBottom w), q.1 = t → q.2 ≤ B) ∧
      ((t, B) : GInt) ∈ cellTileOf (oddTile w) := by
  have hu : ∀ x ∈ oddBottom w, x = Unit4.one ∨ x = Unit4.i := (admissible_oddStandard w).1.1
  obtain ⟨_, hh0⟩ := col_exists w t ht0 (by omega)
  obtain ⟨b, hbW, hb1, hbmax⟩ := exists_top_col (F2Word.walk (0, 0) (oddBottom w)) t ⟨_, hh0, rfl⟩
  have hbeq : b = ((t, b.2) : GInt) := by
    ext
    · exact hb1
    · rfl
  rw [hbeq] at hbW hbmax
  have hnext : ∃ q ∈ F2Word.walk (0, 0) (oddBottom w), q.1 = t + 1 := by
    obtain ⟨_, hh1⟩ := col_exists w (t + 1) (by omega) ht1
    exact ⟨_, hh1, rfl⟩
  obtain ⟨l1, l2, hl⟩ := pattern_step (oddBottom w) hu (0, 0) t b.2 hbW hbmax hnext
  have he := bnd_pair w ((t, b.2) : GInt) ((t + 1, b.2) : GInt) l1 l2 hl
  refine ⟨b.2, hbW, hbmax, ?_⟩
  rcases boundary_out (cellTileOf (oddTile w)) ((t, b.2) : GInt)
      ((t + 1, b.2) : GInt) he with ⟨-, hv, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
  · exact hv
  · have := congrArg Prod.fst hb
    simp [gI] at this <;> omega
  · have := congrArg Prod.fst hb
    simp [gOne] at this <;> omega
  · have := congrArg Prod.fst hb
    simp [gI] at this <;> omega

end FLatticePaper.Tiles.StackedTopCell
