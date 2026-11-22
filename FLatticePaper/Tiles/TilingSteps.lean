import FLatticePaper.Tiles.TilingCount

/-! Task 32, part 4: the cell counts of a tile are constant on the cosets of the lattice, given the boundary edge balance.

The balance `edgeCount N T Q D = edgeCount N T (Q + [D]) (-D)` is a hypothesis here (it is proved from the boundary word in
`TilingCriteria`). For the two unit steps `1` and `i`, a cell `t` of coset `Q` either has its right (or upper) neighbour in `T`
or not. The neighbours inside correspond bijectively to the cells of the next coset with the left (or lower) neighbour inside,
and the neighbours outside give boundary edges, which the balance identifies. -/

namespace FLatticePaper.Tiles
open Classical

theorem card_filter_split {α : Type*} (T : Finset α) (P p : α → Prop) [DecidablePred P] [DecidablePred p] :
    (T.filter P).card = (T.filter fun t => P t ∧ p t).card + (T.filter fun t => P t ∧ ¬ p t).card := by
  have h := Finset.card_filter_add_card_filter_not (s := T.filter P) (p := p)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  exact h.symm

theorem cellOther_one (t : GInt) : cellOther t 1 = t + gOne := rfl

theorem cellOther_two (t : GInt) : cellOther t 2 = t + gI := rfl

theorem cellOther_three (t : GInt) : cellOther t 3 = t - gOne := rfl

theorem cellOther_zero (t : GInt) : cellOther t 0 = t - gI := rfl

/-- The horizontal neighbour bijection: a cell `t` of coset `Q` with `t + 1` in `T` corresponds to the cell `t + 1` of
coset `Q + [1]` with `(t + 1) - 1 ∈ T`. -/
theorem card_inner_horizontal (N : AddSubgroup GInt) (T : CellTile) (Q : GInt ⧸ N) :
    (T.filter fun t => qmk N t = Q ∧ cellOther t 1 ∈ T).card =
      (T.filter fun s => qmk N s = Q + qmk N gOne ∧ cellOther s 3 ∈ T).card := by
  apply Finset.card_nbij (fun t => t + gOne)
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, cellOther_one, cellOther_three] at ht ⊢
    refine ⟨ht.2.2, ?_, ?_⟩
    · rw [map_add, ht.2.1]
    · simpa using ht.1
  · intro t _ t' _ h
    exact add_right_cancel h
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_filter, cellOther_three] at hs
    refine ⟨s - gOne, ?_, by simp⟩
    simp only [Finset.mem_coe, Finset.mem_filter, cellOther_one]
    refine ⟨hs.2.2, ?_, ?_⟩
    · have : qmk N (s - gOne) = qmk N s - qmk N gOne := map_sub _ _ _
      rw [this, hs.2.1]
      abel
    · simpa using hs.1

/-- The vertical neighbour bijection: a cell `t` of coset `Q` with `t + i` in `T` corresponds to the cell `t + i` of coset
`Q + [i]` with `(t + i) - i ∈ T`. -/
theorem card_inner_vertical (N : AddSubgroup GInt) (T : CellTile) (Q : GInt ⧸ N) :
    (T.filter fun t => qmk N t = Q ∧ cellOther t 2 ∈ T).card =
      (T.filter fun s => qmk N s = Q + qmk N gI ∧ cellOther s 0 ∈ T).card := by
  apply Finset.card_nbij (fun t => t + gI)
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, cellOther_two, cellOther_zero] at ht ⊢
    refine ⟨ht.2.2, ?_, ?_⟩
    · rw [map_add, ht.2.1]
    · simpa using ht.1
  · intro t _ t' _ h
    exact add_right_cancel h
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_filter, cellOther_zero] at hs
    refine ⟨s - gI, ?_, by simp⟩
    simp only [Finset.mem_coe, Finset.mem_filter, cellOther_two]
    refine ⟨hs.2.2, ?_, ?_⟩
    · have : qmk N (s - gI) = qmk N s - qmk N gI := map_sub _ _ _
      rw [this, hs.2.1]
      abel
    · simpa using hs.1

/-- Horizontal step: the cell counts of a coset and of the next coset along `1` agree, given the balance. -/
theorem cellCount_step_h (N : AddSubgroup GInt) (T : CellTile)
    (hbal : ∀ (Q : GInt ⧸ N) (D : GInt), edgeCount N T Q D = edgeCount N T (Q + qmk N D) (-D))
    (Q : GInt ⧸ N) : cellCount N T Q = cellCount N T (Q + qmk N gOne) := by
  unfold cellCount
  rw [card_filter_split T (fun t => qmk N t = Q) (fun t => cellOther t 1 ∈ T),
    card_filter_split T (fun s => qmk N s = Q + qmk N gOne) (fun s => cellOther s 3 ∈ T),
    card_inner_horizontal N T Q, cellCount_outside N T Q 1,
    cellCount_outside N T (Q + qmk N gOne) 3]
  have e1 : edgeCount N T (Q + qmk N (off1 1)) (dirJ 1) = edgeCount N T (Q + qmk N gOne) gI := rfl
  have e3 : edgeCount N T (Q + qmk N gOne + qmk N (off1 3)) (dirJ 3) =
      edgeCount N T (Q + qmk N gOne + qmk N gI) (-gI) := rfl
  rw [e1, e3, hbal (Q + qmk N gOne) gI]

/-- Vertical step: the cell counts of a coset and of the next coset along `i` agree, given the balance. -/
theorem cellCount_step_v (N : AddSubgroup GInt) (T : CellTile)
    (hbal : ∀ (Q : GInt ⧸ N) (D : GInt), edgeCount N T Q D = edgeCount N T (Q + qmk N D) (-D))
    (Q : GInt ⧸ N) : cellCount N T Q = cellCount N T (Q + qmk N gI) := by
  unfold cellCount
  rw [card_filter_split T (fun t => qmk N t = Q) (fun t => cellOther t 2 ∈ T),
    card_filter_split T (fun s => qmk N s = Q + qmk N gI) (fun s => cellOther s 0 ∈ T),
    card_inner_vertical N T Q, cellCount_outside N T Q 2,
    cellCount_outside N T (Q + qmk N gI) 0]
  have e2 : edgeCount N T (Q + qmk N (off1 2)) (dirJ 2) =
      edgeCount N T (Q + qmk N gI + qmk N gOne) (-gOne) := by
    rw [show Q + qmk N gI + qmk N gOne = Q + qmk N (gOne + gI) by rw [map_add]; abel]
    rfl
  have e0 : edgeCount N T (Q + qmk N gI + qmk N (off1 0)) (dirJ 0) = edgeCount N T (Q + qmk N gI) gOne := by
    rw [show (off1 0 : GInt) = 0 from rfl, map_zero, add_zero]
    rfl
  rw [e2, e0, hbal (Q + qmk N gI) gOne]

/-- The cell count is invariant under translation of the coset by `n` times the first generator. -/
theorem cellCount_add_int_one (N : AddSubgroup GInt) (T : CellTile)
    (hbal : ∀ (Q : GInt ⧸ N) (D : GInt), edgeCount N T Q D = edgeCount N T (Q + qmk N D) (-D))
    (Q : GInt ⧸ N) (n : ℤ) : cellCount N T (Q + n • qmk N gOne) = cellCount N T Q := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [add_zsmul, one_zsmul, ← add_assoc, ← cellCount_step_h N T hbal, ih]
  | pred k ih =>
    have hs := cellCount_step_h N T hbal (Q + (-(k : ℤ) - 1) • qmk N gOne)
    have e : Q + (-(k : ℤ) - 1) • qmk N gOne + qmk N gOne = Q + (-(k : ℤ)) • qmk N gOne := by
      rw [sub_zsmul, one_zsmul]
      abel
    rw [e] at hs
    rw [hs, ih]

/-- The cell count is invariant under translation of the coset by `n` times the second generator. -/
theorem cellCount_add_int_i (N : AddSubgroup GInt) (T : CellTile)
    (hbal : ∀ (Q : GInt ⧸ N) (D : GInt), edgeCount N T Q D = edgeCount N T (Q + qmk N D) (-D))
    (Q : GInt ⧸ N) (n : ℤ) : cellCount N T (Q + n • qmk N gI) = cellCount N T Q := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [add_zsmul, one_zsmul, ← add_assoc, ← cellCount_step_v N T hbal, ih]
  | pred k ih =>
    have hs := cellCount_step_v N T hbal (Q + (-(k : ℤ) - 1) • qmk N gI)
    have e : Q + (-(k : ℤ) - 1) • qmk N gI + qmk N gI = Q + (-(k : ℤ)) • qmk N gI := by
      rw [sub_zsmul, one_zsmul]
      abel
    rw [e] at hs
    rw [hs, ih]

/-- The cell count of a coset is unchanged by adding the class of any Gaussian integer. -/
theorem cellCount_add_qmk (N : AddSubgroup GInt) (T : CellTile)
    (hbal : ∀ (Q : GInt ⧸ N) (D : GInt), edgeCount N T Q D = edgeCount N T (Q + qmk N D) (-D))
    (Q : GInt ⧸ N) (x : GInt) : cellCount N T (Q + qmk N x) = cellCount N T Q := by
  have hx : x = x.1 • gOne + x.2 • gI := by
    ext <;> simp [gOne, gI]
  have hq : Q + qmk N x = (Q + x.1 • qmk N gOne) + x.2 • qmk N gI := by
    conv_lhs => rw [hx]
    rw [map_add, map_zsmul, map_zsmul]
    abel
  rw [hq, cellCount_add_int_i N T hbal, cellCount_add_int_one N T hbal]

/-- The cell counts over the whole quotient add up to the number of cells. -/
theorem sum_cellCount (N : AddSubgroup GInt) [Fintype (GInt ⧸ N)] (T : CellTile) :
    ∑ Q : GInt ⧸ N, cellCount N T Q = T.card := by
  unfold cellCount
  rw [← Finset.card_eq_sum_card_fiberwise (f := qmk N) (s := T) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]

end FLatticePaper.Tiles
