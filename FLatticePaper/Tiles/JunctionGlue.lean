import FLatticePaper.Tiles.RowChain

/-! Task 53, step 2: junctions of the pieces of a standard child, as pure combinatorics (no geometry).

The six copies of the registers in an odd or even child are edge-connected pieces. Numerically (`scripts/junctions.py`,
`scripts/junction_core.py`), for every non-base word, the pieces are joined in a six-cycle, and each junction is
witnessed by a cell `x` of the child adjacent to a cell of each of the two pieces (either a bridging cell, or a cell of
one piece adjacent to the other). This file proves the two gluing lemmas that such a junction feeds into. -/

namespace FLatticePaper.Tiles

/-- A set in which every cell reaches a fixed cell `a` is edge-connected. -/
theorem edgeConnectedIn_of_reach {S : CellTile} {a : GInt}
    (hreach : ∀ y ∈ S, Relation.ReflTransGen (CellRel S) y a) : EdgeConnectedIn S := by
  intro x hx y hy
  exact (hreach x hx).trans (cellRel_rtg_symm (cellRel_symm S) (hreach y hy))

/-- Two edge-connected pieces joined through one witness cell `x`, adjacent to a cell `a` of the first piece and a cell
`b` of the second, form an edge-connected set (the pieces together with `x`). -/
theorem edgeConnectedIn_junction {A B : CellTile} (hA : EdgeConnectedIn A) (hB : EdgeConnectedIn B) {a b x : GInt}
    (ha : a ∈ A) (hb : b ∈ B) (hax : CellAdj a x) (hbx : CellAdj b x) :
    EdgeConnectedIn (insert x (A ∪ B)) := by
  have hxS : x ∈ insert x (A ∪ B) := Finset.mem_insert_self x (A ∪ B)
  have haS : a ∈ insert x (A ∪ B) := Finset.mem_insert_of_mem (Finset.mem_union_left B ha)
  have hbS : b ∈ insert x (A ∪ B) := Finset.mem_insert_of_mem (Finset.mem_union_right A hb)
  refine edgeConnectedIn_of_reach (a := a) (fun y hy => ?_)
  rcases Finset.mem_insert.mp hy with rfl | hyAB
  · exact Relation.ReflTransGen.single ⟨hxS, haS, cellAdj_symm hax⟩
  rcases Finset.mem_union.mp hyAB with hyA | hyB
  · have hsub : A ⊆ insert x (A ∪ B) := by
      intro z hz
      exact Finset.mem_insert_of_mem (Finset.mem_union_left B hz)
    exact rtg_mono_cellRel (S := A) (S' := insert x (A ∪ B)) hsub (hA y hyA a ha)
  · have hsub : B ⊆ insert x (A ∪ B) := by
      intro z hz
      exact Finset.mem_insert_of_mem (Finset.mem_union_right A hz)
    have hyb : Relation.ReflTransGen (CellRel (insert x (A ∪ B))) y b :=
      rtg_mono_cellRel (S := B) (S' := insert x (A ∪ B)) hsub (hB y hyB b hb)
    exact (hyb.tail ⟨hbS, hxS, hbx⟩).tail ⟨hxS, haS, cellAdj_symm hax⟩

end FLatticePaper.Tiles
