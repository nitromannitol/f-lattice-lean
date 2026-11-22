import FLatticePaper.Tiles.AlmostTiling

/-! Task 53, step 2: edge-connectivity of cell sets from edge-connected pieces (no geometry).

`EdgeConnectedIn S`: any two cells of `S` are joined inside `S` by a chain of edge-adjacent cells. The union of two
edge-connected pieces with a common cell is edge-connected, and a cell set that contains an edge-connected core, with
every other cell edge-adjacent to the core, is edge-connected. -/

namespace FLatticePaper.Tiles

/-- Adjacent cells inside a set. -/
def CellRel (S : CellTile) (a b : GInt) : Prop := a ∈ S ∧ b ∈ S ∧ CellAdj a b

/-- Edge-connectivity of a set of cells: any two of its cells are joined by a chain inside the set. -/
def EdgeConnectedIn (S : CellTile) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, Relation.ReflTransGen (CellRel S) x y

theorem edgeConnected_iff (T : CellTile) : EdgeConnected T ↔ EdgeConnectedIn T := Iff.rfl

theorem cellAdj_symm {a b : GInt} (h : CellAdj a b) : CellAdj b a := by
  unfold CellAdj at h ⊢
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl (by rw [h]; abel))
  · exact Or.inl (by rw [h]; abel)
  · exact Or.inr (Or.inr (Or.inr (by rw [h]; abel)))
  · exact Or.inr (Or.inr (Or.inl (by rw [h]; abel)))

theorem cellRel_symm (S : CellTile) : ∀ _a _b : GInt, CellRel S _a _b → CellRel S _b _a := by
  intro _a _b h
  exact ⟨h.2.1, h.1, cellAdj_symm h.2.2⟩

/-- Monotonicity of the reflexive transitive closure in the relation. -/
theorem rtg_mono' {r p : GInt → GInt → Prop} (hrp : ∀ a b, r a b → p a b) {x y : GInt}
    (h : Relation.ReflTransGen r x y) : Relation.ReflTransGen p x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hrp _ _ hbc)

/-- The reflexive transitive closure of a symmetric relation is symmetric. -/
theorem rtg_symm' {r : GInt → GInt → Prop} (hr : ∀ a b, r a b → r b a) {x y : GInt}
    (h : Relation.ReflTransGen r x y) : Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hr _ _ hbc) ih

theorem rtg_mono_cellRel {S S' : CellTile} (hSS : S ⊆ S') {x y : GInt}
    (h : Relation.ReflTransGen (CellRel S) x y) : Relation.ReflTransGen (CellRel S') x y :=
  rtg_mono' (fun _a _b hab => ⟨hSS hab.1, hSS hab.2.1, hab.2.2⟩) h

/-- Every cell of an edge-connected set reaches any given cell of it. -/
theorem reach_of_mem {S : CellTile} (hS : EdgeConnectedIn S) {c x : GInt} (hc : c ∈ S) (hx : x ∈ S) :
    Relation.ReflTransGen (CellRel S) x c := hS x hx c hc

/-- The union of two edge-connected sets with a common cell is edge-connected. -/
theorem edgeConnectedIn_union {A B : CellTile} (hA : EdgeConnectedIn A) (hB : EdgeConnectedIn B) {c : GInt}
    (hcA : c ∈ A) (hcB : c ∈ B) : EdgeConnectedIn (A ∪ B) := by
  have toC : ∀ x ∈ A ∪ B, Relation.ReflTransGen (CellRel (A ∪ B)) x c := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact rtg_mono_cellRel Finset.subset_union_left (hA x hxA c hcA)
    · exact rtg_mono_cellRel Finset.subset_union_right (hB x hxB c hcB)
  intro x hx y hy
  exact (toC x hx).trans (rtg_symm' (cellRel_symm (A ∪ B)) (toC y hy))

/-- A set that contains an edge-connected core and whose other cells are edge-adjacent to the core is edge-connected. -/
theorem edgeConnectedIn_of_core {T S : CellTile} (hS : EdgeConnectedIn S) (hST : S ⊆ T)
    (hT : ∀ x ∈ T, x ∈ S ∨ ∃ s ∈ S, CellAdj s x) : EdgeConnectedIn T := by
  have toS : ∀ x ∈ T, ∃ s ∈ S, Relation.ReflTransGen (CellRel T) x s := by
    intro x hx
    rcases hT x hx with hxS | ⟨s, hsS, hadj⟩
    · exact ⟨x, hxS, Relation.ReflTransGen.refl⟩
    · exact ⟨s, hsS, Relation.ReflTransGen.single ⟨hx, hST hsS, cellAdj_symm hadj⟩⟩
  intro x hx y hy
  obtain ⟨s, hs, hxs⟩ := toS x hx
  obtain ⟨s', hs', hys⟩ := toS y hy
  have hss : Relation.ReflTransGen (CellRel T) s s' := rtg_mono_cellRel hST (hS s hs s' hs')
  exact hxs.trans (hss.trans (rtg_symm' (cellRel_symm T) hys))

end FLatticePaper.Tiles
