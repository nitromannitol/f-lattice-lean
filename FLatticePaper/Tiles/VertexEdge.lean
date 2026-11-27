import FLatticePaper.Tiles.AlmostTiling
import FLatticePaper.Tiles.CellDerivation
import FLatticePaper.Tiles.RowScan

/-! The vertex-edge lemma of the cell derivation. A boundary vertex of a cell region is an endpoint of a directed boundary edge of
the region (`CellTile.boundaryEdges`), so it is a vertex of every boundary word of the region (`IsBoundaryWordAt`).

The four unit squares at a corner `z` are cyclically adjacent. A corner that is not interior has a cell and a non-cell among them,
and an adjacent pair of a cell and a non-cell gives one of the four directed edges of the cell (`edge_below`, `edge_left`,
`edge_right`, `edge_top`), each with `z` as an endpoint. -/

namespace FLatticePaper.Tiles.VertexEdge

open FLatticePaper.Tiles FLatticePaper.Tiles.CellDerivation

theorem edge_below (T : CellTile) (x : GInt) (hx : x ∈ T) (hn : x - gI ∉ T) :
    (x, x + gOne) ∈ T.boundaryEdges := by
  rw [mem_boundaryEdges_iff]
  exact ⟨x, hx, (x, x + gOne, x - gI), by simp [cellEdgesWithOther], hn, rfl⟩

theorem edge_left (T : CellTile) (x : GInt) (hx : x ∈ T) (hn : x - gOne ∉ T) :
    (x + gI, x) ∈ T.boundaryEdges := by
  rw [mem_boundaryEdges_iff]
  exact ⟨x, hx, (x + gI, x, x - gOne), by simp [cellEdgesWithOther], hn, rfl⟩

theorem edge_right (T : CellTile) (x : GInt) (hx : x ∈ T) (hn : x + gOne ∉ T) :
    (x + gOne, x + gOne + gI) ∈ T.boundaryEdges := by
  rw [mem_boundaryEdges_iff]
  exact ⟨x, hx, (x + gOne, x + gOne + gI, x + gOne), by simp [cellEdgesWithOther], hn, rfl⟩

theorem edge_top (T : CellTile) (x : GInt) (hx : x ∈ T) (hn : x + gI ∉ T) :
    (x + gOne + gI, x + gI) ∈ T.boundaryEdges := by
  rw [mem_boundaryEdges_iff]
  exact ⟨x, hx, (x + gOne + gI, x + gI, x + gI), by simp [cellEdgesWithOther], hn, rfl⟩

/-! The eight adjacent cell/non-cell pairs around `z`. Going round `z`: the square `z` (NE), `z - gOne` (NW), `z - gOne - gI`
(SW), `z - gI` (SE). -/

theorem in_out_1 (T : CellTile) (z : GInt) (h1 : z ∈ T) (h2 : z - gOne ∉ T) :
    ∃ e ∈ T.boundaryEdges, z = e.1 ∨ z = e.2 :=
  ⟨_, edge_left T z h1 h2, Or.inr rfl⟩

theorem in_out_2 (T : CellTile) (z : GInt) (h1 : z - gOne ∈ T) (h2 : z ∉ T) :
    ∃ e ∈ T.boundaryEdges, z = e.1 ∨ z = e.2 := by
  have h2' : z - gOne + gOne ∉ T := by rw [sub_add_cancel]; exact h2
  exact ⟨_, edge_right T (z - gOne) h1 h2', Or.inl (sub_add_cancel z gOne).symm⟩

theorem in_out_3 (T : CellTile) (z : GInt) (h1 : z - gOne ∈ T) (h2 : z - gOne - gI ∉ T) :
    ∃ e ∈ T.boundaryEdges, z = e.1 ∨ z = e.2 :=
  ⟨_, edge_below T (z - gOne) h1 h2, Or.inr (sub_add_cancel z gOne).symm⟩

theorem in_out_4 (T : CellTile) (z : GInt) (h1 : z - gOne - gI ∈ T) (h2 : z - gOne ∉ T) :
    ∃ e ∈ T.boundaryEdges, z = e.1 ∨ z = e.2 := by
  have h2' : z - gOne - gI + gI ∉ T := by rw [sub_add_cancel]; exact h2
  have e : z - gOne - gI + gOne + gI = z := by abel
  exact ⟨_, edge_top T (z - gOne - gI) h1 h2', Or.inl e.symm⟩

theorem in_out_5 (T : CellTile) (z : GInt) (h1 : z - gOne - gI ∈ T) (h2 : z - gI ∉ T) :
    ∃ e ∈ T.boundaryEdges, z = e.1 ∨ z = e.2 := by
  have e1 : z - gOne - gI + gOne = z - gI := by abel
  have h2' : z - gOne - gI + gOne ∉ T := by rw [e1]; exact h2
  have e2 : z - gOne - gI + gOne + gI = z := by abel
  exact ⟨_, edge_right T (z - gOne - gI) h1 h2', Or.inr e2.symm⟩

theorem in_out_6 (T : CellTile) (z : GInt) (h1 : z - gI ∈ T) (h2 : z - gOne - gI ∉ T) :
    ∃ e ∈ T.boundaryEdges, z = e.1 ∨ z = e.2 := by
  have e1 : z - gI - gOne = z - gOne - gI := by abel
  have h2' : z - gI - gOne ∉ T := by rw [e1]; exact h2
  have e2 : z - gI + gI = z := by abel
  exact ⟨_, edge_left T (z - gI) h1 h2', Or.inl e2.symm⟩

theorem in_out_7 (T : CellTile) (z : GInt) (h1 : z - gI ∈ T) (h2 : z ∉ T) :
    ∃ e ∈ T.boundaryEdges, z = e.1 ∨ z = e.2 := by
  have h2' : z - gI + gI ∉ T := by rw [sub_add_cancel]; exact h2
  exact ⟨_, edge_top T (z - gI) h1 h2', Or.inr (sub_add_cancel z gI).symm⟩

theorem in_out_8 (T : CellTile) (z : GInt) (h1 : z ∈ T) (h2 : z - gI ∉ T) :
    ∃ e ∈ T.boundaryEdges, z = e.1 ∨ z = e.2 :=
  ⟨_, edge_below T z h1 h2, Or.inl rfl⟩

/-- **The vertex-edge lemma.** A boundary vertex of the cell region of a cell tile is an endpoint of a directed boundary edge. -/
theorem vertex_edge (T : CellTile) (z : GInt) (hz : BoundaryVertex (↑T : Set GInt) z) :
    ∃ e ∈ T.boundaryEdges, z = e.1 ∨ z = e.2 := by
  obtain ⟨⟨s, hs, hsz⟩, hnot⟩ := hz
  have hs' : s ∈ T := Finset.mem_coe.1 hs
  have k1 : z + ((-1 : ℤ), (0 : ℤ)) = z - gOne := by
    ext <;> simp [gOne]
    ring
  have k2 : z + ((0 : ℤ), (-1 : ℤ)) = z - gI := by
    ext <;> simp [gI]
    ring
  have k3 : z + ((-1 : ℤ), (-1 : ℤ)) = z - gOne - gI := by ext <;> simp [gOne, gI] <;> ring
  unfold Interior at hnot
  simp only [Finset.mem_coe, k1, k2, k3] at hnot
  have hany : z ∈ T ∨ z - gOne ∈ T ∨ z - gI ∈ T ∨ z - gOne - gI ∈ T := by
    rcases squares_at hsz with h | h | h | h
    · rw [h] at hs'; exact Or.inl hs'
    · rw [h, k1] at hs'; exact Or.inr (Or.inl hs')
    · rw [h, k2] at hs'; exact Or.inr (Or.inr (Or.inl hs'))
    · rw [h, k3] at hs'; exact Or.inr (Or.inr (Or.inr hs'))
  by_cases hA : z ∈ T <;> by_cases hB : z - gOne ∈ T <;> by_cases hD : z - gI ∈ T <;>
    by_cases hC : z - gOne - gI ∈ T
  all_goals first
    | exact (hnot ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
    | (rcases hany with h | h | h | h <;> contradiction)
    | exact in_out_1 T z (by assumption) (by assumption)
    | exact in_out_2 T z (by assumption) (by assumption)
    | exact in_out_3 T z (by assumption) (by assumption)
    | exact in_out_4 T z (by assumption) (by assumption)
    | exact in_out_5 T z (by assumption) (by assumption)
    | exact in_out_6 T z (by assumption) (by assumption)

/-- **A boundary vertex lies on every boundary walk of its cell region.** -/
theorem mem_walk_of_boundaryVertex (T : CellTile) (c : GInt) (w : F2Word) (hw : IsBoundaryWordAt T c w)
    (z : GInt) (hz : BoundaryVertex (↑T : Set GInt) z) : z ∈ F2Word.walk c w := by
  obtain ⟨⟨a, b⟩, he, hzab⟩ := vertex_edge T z hz
  unfold IsBoundaryWordAt at hw
  obtain ⟨-, -, -, hset⟩ := hw
  rw [← hset, List.mem_toFinset] at he
  obtain ⟨h1, h2⟩ := List.of_mem_zip he
  rcases hzab with h | h
  · rw [h]; exact h1
  · rw [h]; exact List.mem_of_mem_tail h2

end FLatticePaper.Tiles.VertexEdge
