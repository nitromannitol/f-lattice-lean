import FLatticePaper.Tiles.RegionRuns
import FLatticePaper.Tiles.FourWalks

/-! Task 55 (R2): the boundary of a cell tile whose rows are the arc intervals of a four-arc loop is that loop.

This file collects the general lemmas: the walk of `boundaryWordOf w1 w2` is the walk `w1 ++ w2` followed by its half-turn
image; the four directed boundary edges of a cell tile, in terms of the cells. -/

namespace FLatticePaper.Tiles.RegionBoundary

open FLatticePaper FLatticePaper.Tiles RegionRuns FLatticePaper.Tiles.FourWalks

theorem halfE_halfE (z : GInt) (e : GInt × GInt) : halfE z (halfE z e) = e := by
  simp [halfE]

theorem walk_split (w1 w2 : F2Word) :
    edgesFrom (0, 0) (boundaryWordOf w1 w2) =
      edgesFrom (0, 0) (w1 ++ w2) ++ (edgesFrom (0, 0) (w1 ++ w2)).map (halfE (F2Word.sum (w1 ++ w2))) := by
  show edgesFrom 0 (boundaryWordOf w1 w2) =
    edgesFrom 0 (w1 ++ w2) ++ (edgesFrom 0 (w1 ++ w2)).map (halfE (F2Word.sum (w1 ++ w2)))
  rw [edgesFrom_boundaryWordOf, edgesFrom_append]
  simp only [zero_add, List.map_append, List.append_assoc, arc_sum_append]

theorem mem_walk_iff (w1 w2 : F2Word) (e : GInt × GInt) :
    e ∈ edgesFrom (0, 0) (boundaryWordOf w1 w2) ↔
      e ∈ edgesFrom (0, 0) (w1 ++ w2) ∨ halfE (F2Word.sum (w1 ++ w2)) e ∈ edgesFrom (0, 0) (w1 ++ w2) := by
  rw [walk_split, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨f, hf, rfl⟩)
    · exact Or.inl h
    · right
      rw [halfE_halfE]
      exact hf
  · rintro (h | h)
    · exact Or.inl h
    · right
      exact ⟨halfE _ e, h, halfE_halfE _ _⟩

/-- The edges of a walk have the shape `e.2 = e.1 + x.vec` for a letter `x` of the word. -/
theorem edge_shape (c : GInt) (u : F2Word) (e : GInt × GInt) (he : e ∈ edgesFrom c u) :
    ∃ x ∈ u, e.2 = e.1 + x.vec := by
  induction u generalizing c with
  | nil => simp [edgesFrom] at he
  | cons x u ih =>
    simp only [edgesFrom, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨x, List.mem_cons_self, rfl⟩
    · obtain ⟨y, hy, hy'⟩ := ih _ he
      exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

/-- A boundary edge of a cell tile is a unit step. -/
theorem boundary_edge_shape (T : CellTile) (e : GInt × GInt) (he : e ∈ T.boundaryEdges) :
    ∃ c ∈ T, ∃ f ∈ cellEdgesWithOther c, f.2.2 ∉ T ∧ (f.1, f.2.1) = e :=
  (mem_boundaryEdges_iff T e).mp he

/-- The bottom edge `(q, k) → (q+1, k)` is a boundary edge iff the cell `(q, k)` is in the tile and `(q, k-1)` is not. -/
theorem bdry_E_iff (T : CellTile) (q k : ℤ) :
    ((q, k), (q + 1, k)) ∈ T.boundaryEdges ↔ ((q, k) : GInt) ∈ T ∧ ((q, k - 1) : GInt) ∉ T := by
  rw [mem_boundaryEdges_iff]
  constructor
  · rintro ⟨c, hc, f, hf, hnot, hfe⟩
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · simp only [gOne, gI, Prod.ext_iff] at hfe hnot
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      have hc' : c = (q, k) := by
        ext
        · simp at h1 ⊢; omega
        · simp at h2 ⊢; omega
      subst hc'
      refine ⟨hc, ?_⟩
      simpa [gI] using hnot
    · exfalso
      simp only [gOne, gI, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      simp at h1 h2 h3 h4
      omega
    · exfalso
      simp only [gOne, gI, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      simp at h1 h2 h3 h4
      omega
    · exfalso
      simp only [gI, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      simp at h1 h2 h3 h4
      omega
  · rintro ⟨hq, hnot⟩
    refine ⟨(q, k), hq, (((q, k) : GInt), ((q, k) : GInt) + gOne, ((q, k) : GInt) - gI),
      ?_, ?_, ?_⟩
    · simp [cellEdgesWithOther]
    · simpa [gI] using hnot
    · simp [gOne]

/-- The top edge `(q+1, k) → (q, k)` is a boundary edge iff `(q, k-1)` is in the tile and `(q, k)` is not. -/
theorem bdry_W_iff (T : CellTile) (q k : ℤ) :
    ((q + 1, k), (q, k)) ∈ T.boundaryEdges ↔ ((q, k - 1) : GInt) ∈ T ∧ ((q, k) : GInt) ∉ T := by
  rw [mem_boundaryEdges_iff]
  constructor
  · rintro ⟨c, hc, f, hf, hnot, hfe⟩
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exfalso
      simp only [gOne, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      simp at h1 h2 h3 h4
      omega
    · exfalso
      simp only [gOne, gI, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      simp at h1 h2 h3 h4
      omega
    · simp only [gOne, gI, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      have hc' : c = (q, k - 1) := by
        ext
        · simp at h1 ⊢; omega
        · simp at h2 ⊢; omega
      subst hc'
      refine ⟨hc, ?_⟩
      simpa [gI] using hnot
    · exfalso
      simp only [gI, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      simp at h1 h2 h3 h4
      omega
  · rintro ⟨hq, hnot⟩
    refine ⟨(q, k - 1), hq, (((q, k - 1) : GInt) + gOne + gI, ((q, k - 1) : GInt) + gI, ((q, k - 1) : GInt) + gI),
      ?_, ?_, ?_⟩
    · simp [cellEdgesWithOther]
    · simpa [gI] using hnot
    · simp [gOne, gI]

/-- The right edge `(x, k) → (x, k+1)` is a boundary edge iff `(x-1, k)` is in the tile and `(x, k)` is not. -/
theorem bdry_N_iff (T : CellTile) (x k : ℤ) :
    ((x, k), (x, k + 1)) ∈ T.boundaryEdges ↔ ((x - 1, k) : GInt) ∈ T ∧ ((x, k) : GInt) ∉ T := by
  rw [mem_boundaryEdges_iff]
  constructor
  · rintro ⟨c, hc, f, hf, hnot, hfe⟩
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exfalso
      simp only [gOne, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      simp at h1 h2 h3 h4
      omega
    · simp only [gOne, gI, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      have hc' : c = (x - 1, k) := by
        ext
        · simp at h1 ⊢; omega
        · simp at h2 ⊢; omega
      subst hc'
      refine ⟨hc, ?_⟩
      simpa [gOne] using hnot
    · exfalso
      simp only [gOne, gI, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      simp at h1 h2 h3 h4
      omega
    · exfalso
      simp only [gI, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      simp at h1 h2 h3 h4
      omega
  · rintro ⟨hq, hnot⟩
    refine ⟨(x - 1, k), hq, (((x - 1, k) : GInt) + gOne, ((x - 1, k) : GInt) + gOne + gI,
      ((x - 1, k) : GInt) + gOne), ?_, ?_, ?_⟩
    · simp [cellEdgesWithOther]
    · simpa [gOne] using hnot
    · simp [gOne, gI]

/-- The left edge `(x, k+1) → (x, k)` is a boundary edge iff `(x, k)` is in the tile and `(x-1, k)` is not. -/
theorem bdry_S_iff (T : CellTile) (x k : ℤ) :
    ((x, k + 1), (x, k)) ∈ T.boundaryEdges ↔ ((x, k) : GInt) ∈ T ∧ ((x - 1, k) : GInt) ∉ T := by
  rw [mem_boundaryEdges_iff]
  constructor
  · rintro ⟨c, hc, f, hf, hnot, hfe⟩
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exfalso
      simp only [gOne, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      simp at h1 h2 h3 h4
      omega
    · exfalso
      simp only [gOne, gI, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      simp at h1 h2 h3 h4
      omega
    · exfalso
      simp only [gOne, gI, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      simp at h1 h2 h3 h4
      omega
    · simp only [gI, Prod.ext_iff] at hfe
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfe
      have hc' : c = (x, k) := by
        ext
        · simp at h1 ⊢; omega
        · simp at h2 ⊢; omega
      subst hc'
      refine ⟨hc, ?_⟩
      simpa [gOne] using hnot
  · rintro ⟨hq, hnot⟩
    refine ⟨(x, k), hq, (((x, k) : GInt) + gI, ((x, k) : GInt), ((x, k) : GInt) - gOne), ?_, ?_, ?_⟩
    · simp [cellEdgesWithOther]
    · simpa [gOne] using hnot
    · simp [gI]

end FLatticePaper.Tiles.RegionBoundary
