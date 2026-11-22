import FLatticePaper.Tiles.AlmostTiling

/-! Task 53, step 1: vertex simplicity of a boundary walk from the absence of checkerboard vertices.

A vertex `v` of a cell tile `T` is a checkerboard vertex when the four cells around `v` (with lower-left corners `v`,
`v - 1`, `v - 1 - i`, `v - i`) are two opposite cells of `T` and the other two are not. At a vertex with no checkerboard
pattern at most one directed boundary edge of `T` leaves `v`; hence a boundary walk, whose directed edges are distinct,
visits no vertex twice. -/

namespace FLatticePaper.Tiles

/-- `v` is a checkerboard vertex of `T`: two opposite cells around `v` lie in `T`, the other two do not. -/
def CheckerboardAt (T : CellTile) (v : GInt) : Prop :=
  (v ∈ T ∧ v - gOne - gI ∈ T ∧ v - gOne ∉ T ∧ v - gI ∉ T) ∨
    (v - gOne ∈ T ∧ v - gI ∈ T ∧ v ∉ T ∧ v - gOne - gI ∉ T)

theorem mem_boundaryEdges_iff (T : CellTile) (e : GInt × GInt) :
    e ∈ T.boundaryEdges ↔ ∃ c ∈ T, ∃ f ∈ cellEdgesWithOther c, f.2.2 ∉ T ∧ (f.1, f.2.1) = e := by
  unfold CellTile.boundaryEdges
  simp only [Finset.mem_biUnion, Finset.mem_image, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, f, ⟨hf, hnot⟩, rfl⟩
    exact ⟨c, hc, f, hf, hnot, rfl⟩
  · rintro ⟨c, hc, f, hf, hnot, rfl⟩
    exact ⟨c, hc, f, ⟨hf, hnot⟩, rfl⟩

/-- The directed boundary edges leaving a vertex `v`: each is decided by the cells around `v`. -/
theorem boundary_out (T : CellTile) (v b : GInt) (h : (v, b) ∈ T.boundaryEdges) :
    (b = v + gOne ∧ v ∈ T ∧ v - gI ∉ T) ∨ (b = v + gI ∧ v - gOne ∈ T ∧ v ∉ T) ∨
      (b = v - gOne ∧ v - gOne - gI ∈ T ∧ v - gOne ∉ T) ∨ (b = v - gI ∧ v - gI ∈ T ∧ v - gOne - gI ∉ T) := by
  rw [mem_boundaryEdges_iff] at h
  obtain ⟨c, hc, f, hf, hnot, hfe⟩ := h
  simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hfe
    dsimp only at h1 h2 hnot
    subst h1
    subst h2
    exact Or.inl ⟨rfl, hc, hnot⟩
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hfe
    dsimp only at h1 h2 hnot
    subst h1
    subst h2
    refine Or.inr (Or.inl ⟨rfl, ?_, hnot⟩)
    rw [add_sub_cancel_right]
    exact hc
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hfe
    dsimp only at h1 h2 hnot
    subst h1
    subst h2
    refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
    · abel
    · rw [show c + gOne + gI - gOne - gI = c by abel]
      exact hc
    · rw [show c + gOne + gI - gOne = c + gI by abel]
      exact hnot
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hfe
    dsimp only at h1 h2 hnot
    subst h1
    subst h2
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
    · abel
    · rw [show c + gI - gI = c by abel]
      exact hc
    · rw [show c + gI - gOne - gI = c - gOne by abel]
      exact hnot

/-- Two distinct directed boundary edges leaving `v` force a checkerboard vertex at `v`. -/
theorem checkerboard_of_two_out (T : CellTile) (v b₁ b₂ : GInt) (h₁ : (v, b₁) ∈ T.boundaryEdges)
    (h₂ : (v, b₂) ∈ T.boundaryEdges) (hne : b₁ ≠ b₂) : CheckerboardAt T v := by
  rcases boundary_out T v b₁ h₁ with ⟨rfl, p₁, q₁⟩ | ⟨rfl, p₁, q₁⟩ | ⟨rfl, p₁, q₁⟩ | ⟨rfl, p₁, q₁⟩ <;>
    rcases boundary_out T v b₂ h₂ with ⟨rfl, p₂, q₂⟩ | ⟨rfl, p₂, q₂⟩ | ⟨rfl, p₂, q₂⟩ | ⟨rfl, p₂, q₂⟩ <;>
    first
    | exact absurd rfl hne
    | exact absurd p₁ q₂
    | exact absurd p₂ q₁
    | exact Or.inl ⟨p₁, p₂, q₂, q₁⟩
    | exact Or.inl ⟨p₂, p₁, q₁, q₂⟩
    | exact Or.inr ⟨p₁, p₂, q₁, q₂⟩
    | exact Or.inr ⟨p₂, p₁, q₂, q₁⟩

/-- A list-level fact: a vertex with a successor in `L` has an edge in the zip of `L` with its tail. -/
theorem exists_succ_of_mem_dropLast {α : Type*} (x : α) : ∀ L : List α, x ∈ L.dropLast →
    ∃ u, (x, u) ∈ L.zip L.tail
  | [], h => by simp at h
  | [z], h => by simp at h
  | z :: w :: L', h => by
      rw [List.dropLast_cons_of_ne_nil (by simp)] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨w, by simp⟩
      · obtain ⟨u, hu⟩ := exists_succ_of_mem_dropLast x (w :: L') h
        exact ⟨u, by simp only [List.zip_cons_cons, List.tail_cons, List.mem_cons]; exact Or.inr hu⟩

/-- A walk whose edges are distinct and in which every vertex has at most one outgoing edge visits no vertex twice
(except the closing one). -/
theorem nodup_dropLast_of_functional {α : Type*} [DecidableEq α] : ∀ (W : List α),
    (W.zip W.tail).Nodup → (∀ x y y', (x, y) ∈ W.zip W.tail → (x, y') ∈ W.zip W.tail → y = y') →
      W.dropLast.Nodup
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | x :: y :: W', hnd, hfun => by
      have hE : (x :: y :: W').zip (x :: y :: W').tail = (x, y) :: (y :: W').zip W' := by simp
      have hE' : (y :: W').zip (y :: W').tail = (y :: W').zip W' := by simp
      rw [hE] at hnd hfun
      have ih := nodup_dropLast_of_functional (y :: W') (by
          rw [hE']; exact (List.nodup_cons.mp hnd).2) (by
          intro a b b' h₁ h₂
          rw [hE'] at h₁ h₂
          exact hfun a b b' (List.mem_cons_of_mem _ h₁) (List.mem_cons_of_mem _ h₂))
      rw [List.dropLast_cons_of_ne_nil (by simp)]
      refine List.nodup_cons.mpr ⟨fun hx => ?_, ih⟩
      obtain ⟨u, hu⟩ := exists_succ_of_mem_dropLast x (y :: W') hx
      rw [hE'] at hu
      have huy : u = y := (hfun x y u (by simp) (List.mem_cons_of_mem _ hu)).symm
      rw [huy] at hu
      exact (List.nodup_cons.mp hnd).1 hu

/-- A boundary walk of a tile without checkerboard vertices is vertex simple: `(walk c w).dropLast` is nodup. -/
theorem walk_dropLast_nodup (T : CellTile) (c : GInt) (w : F2Word) (h : IsBoundaryWordAt T c w)
    (hNC : ∀ v, ¬ CheckerboardAt T v) : ((F2Word.walk c w).dropLast).Nodup := by
  obtain ⟨-, -, hnd, hset⟩ := h
  apply nodup_dropLast_of_functional _ hnd
  intro x y y' h₁ h₂
  by_contra hne
  have hb₁ : (x, y) ∈ T.boundaryEdges := by
    rw [← hset]
    exact List.mem_toFinset.mpr h₁
  have hb₂ : (x, y') ∈ T.boundaryEdges := by
    rw [← hset]
    exact List.mem_toFinset.mpr h₂
  exact hNC x (checkerboard_of_two_out T x y y' hb₁ hb₂ hne)

end FLatticePaper.Tiles
