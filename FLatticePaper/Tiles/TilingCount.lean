import FLatticePaper.Tiles.TilingGreen
import FLatticePaper.Tiles.TilingLattice

/-! Task 32, part 3: counting the cells and boundary edges of a tile by the cosets of a lattice `N`.

For a cell tile `T` and a subgroup `N` of the Gaussian integers, `cellCount N T Q` is the number of cells of `T` in the coset
`Q`, and `edgeCount N T Q D` is the number of directed boundary edges of `T` whose tail lies in the coset `Q` and whose
direction is `D`. The boundary edge balance `edgeCount N T Q D = edgeCount N T (Q + [D]) (-D)` (the cancellation of the boundary
edges of the translates) is a hypothesis here; it is proved from the boundary word in `TilingCriteria`. Under it the cell
counts are constant on the cosets. -/

namespace FLatticePaper.Tiles
open Classical

/-- The coset map `GInt → GInt ⧸ N`. -/
noncomputable def qmk (N : AddSubgroup GInt) : GInt →+ GInt ⧸ N := QuotientAddGroup.mk' N

/-- The number of cells of `T` in the coset `Q` of `N`. -/
noncomputable def cellCount (N : AddSubgroup GInt) (T : CellTile) (Q : GInt ⧸ N) : ℕ :=
  (T.filter fun t => qmk N t = Q).card

/-- The number of directed boundary edges of `T` with tail in the coset `Q` and direction `D`. -/
noncomputable def edgeCount (N : AddSubgroup GInt) (T : CellTile) (Q : GInt ⧸ N) (D : GInt) : ℕ :=
  (T.boundaryEdges.filter fun a => qmk N a.1 = Q ∧ a.2 - a.1 = D).card

/-- The tail offset of the `j`-th edge of a cell: `cellEdge c j = (c + off1 j, c + off1 j + dirJ j)`. -/
def off1 : Fin 4 → GInt
  | 0 => 0
  | 1 => gOne
  | 2 => gOne + gI
  | 3 => gI

/-- The direction of the `j`-th edge of a cell. -/
def dirJ : Fin 4 → GInt
  | 0 => gOne
  | 1 => gI
  | 2 => -gOne
  | 3 => -gI

theorem cellEdge_eq (c : GInt) (j : Fin 4) :
    cellEdge c j = (c + off1 j, c + off1 j + dirJ j) := by
  fin_cases j
  · simp [cellEdge, off1, dirJ]
  · simp [cellEdge, off1, dirJ]
  · refine Prod.ext ?_ ?_ <;> simp [cellEdge, off1, dirJ] <;> abel
  · simp [cellEdge, off1, dirJ]

theorem dirJ_injective {j j' : Fin 4} (h : dirJ j = dirJ j') : j = j' := by
  fin_cases j <;> fin_cases j' <;> simp [dirJ, gOne, gI, Prod.ext_iff] at h ⊢

/-- The cells of `T` in the coset `Q` whose `j`-th neighbour lies outside `T`: each gives one boundary edge of `T`, the
`j`-th edge of the cell, whose tail lies in the coset `Q + [off1 j]` and whose direction is `dirJ j`. -/
theorem cellCount_outside (N : AddSubgroup GInt) (T : CellTile) (Q : GInt ⧸ N) (j : Fin 4) :
    (T.filter fun t => qmk N t = Q ∧ cellOther t j ∉ T).card =
      edgeCount N T (Q + qmk N (off1 j)) (dirJ j) := by
  unfold edgeCount
  apply Finset.card_nbij (fun t => cellEdge t j)
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter] at ht ⊢
    refine ⟨(mem_cellBoundary_iff _ _).2 ⟨t, ht.1, j, rfl, ht.2.2⟩, ?_, ?_⟩
    · rw [cellEdge_eq, map_add, ht.2.1]
    · rw [cellEdge_eq]
      simp
  · intro t ht t' ht' h
    have h1 : t + off1 j = t' + off1 j := by
      have := congrArg Prod.fst h
      simpa [cellEdge_eq] using this
    exact add_right_cancel h1
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha
    obtain ⟨hab, hcls, hdir⟩ := ha
    obtain ⟨c, hc, j', hcj, hn⟩ := (mem_cellBoundary_iff _ _).1 hab
    have hdir' : dirJ j' = dirJ j := by
      rw [← hcj, cellEdge_eq] at hdir
      simpa using hdir
    have hjj : j' = j := dirJ_injective hdir'
    subst hjj
    have hq : qmk N c = Q := by
      rw [← hcj, cellEdge_eq, map_add] at hcls
      exact add_right_cancel hcls
    refine ⟨c, ?_, hcj⟩
    simp only [Finset.mem_coe, Finset.mem_filter]
    exact ⟨hc, hq, hn⟩

end FLatticePaper.Tiles
