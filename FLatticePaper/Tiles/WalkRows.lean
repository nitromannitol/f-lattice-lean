import FLatticePaper.Tiles.RowScan

/-! Walks and rows. The edges of the walk of a word are listed recursively; the boundary edges of a tile traced by its
boundary word are exactly these edges, so the row count of the tile is a sum over the walk. -/

namespace FLatticePaper.Tiles

/-- The directed edges of the walk of `w` from `c`: the `k`-th edge goes from the `k`-th vertex to the next one. -/
def edgesFrom : GInt → F2Word → List (GInt × GInt)
  | _, [] => []
  | c, x :: w => (c, c + x.vec) :: edgesFrom (c + x.vec) w

theorem walkCons (c : GInt) (x : Unit4) (w : F2Word) :
    F2Word.walk c (x :: w) = c :: F2Word.walk (c + x.vec) w := by
  simp [F2Word.walk]

theorem walk_eq_cons (c : GInt) (w : F2Word) : ∃ t, F2Word.walk c w = c :: t := by
  cases w with
  | nil => exact ⟨[], by simp [F2Word.walk]⟩
  | cons x w => exact ⟨_, walkCons c x w⟩

/-- The consecutive pairs of the walk are the walk's edges. -/
theorem zip_walk_eq (c : GInt) (w : F2Word) :
    (F2Word.walk c w).zip (F2Word.walk c w).tail = edgesFrom c w := by
  induction w generalizing c with
  | nil => simp [F2Word.walk, edgesFrom]
  | cons x w ih =>
    obtain ⟨t, ht⟩ := walk_eq_cons (c + x.vec) w
    have ih' := ih (c + x.vec)
    rw [ht, List.tail_cons] at ih'
    rw [walkCons, ht, List.tail_cons, List.zip_cons_cons]
    simp only [edgesFrom]
    rw [ih']

/-- The row count of a tile is the sum over the edges of its boundary word. -/
theorem rowCount_eq_edges {T : CellTile} {c : GInt} {w : F2Word} (h : IsBoundaryWordAt T c w) (b a : ℤ) :
    rowCount T.boundaryEdges b a = ((edgesFrom c w).map (vsgn b a)).sum := by
  obtain ⟨-, -, hnd, hset⟩ := h
  unfold rowCount
  rw [← hset, List.sum_toFinset _ hnd, zip_walk_eq]

/-- A vertical unit step counts only in its own row and column range; a horizontal step never counts. -/
theorem vsgn_one (b a : ℤ) (c : GInt) : vsgn b a (c, c + Unit4.vec .one) = 0 := by
  obtain ⟨c1, c2⟩ := c
  simp [vsgn, Unit4.vec]

theorem vsgn_negOne (b a : ℤ) (c : GInt) : vsgn b a (c, c + Unit4.vec .negOne) = 0 := by
  obtain ⟨c1, c2⟩ := c
  simp [vsgn, Unit4.vec]

theorem vsgn_i (b a : ℤ) (c : GInt) :
    vsgn b a (c, c + Unit4.vec .i) = if c.2 = b ∧ c.1 ≤ a then 1 else 0 := by
  obtain ⟨c1, c2⟩ := c
  simp only [vsgn, Unit4.vec, Prod.mk_add_mk, add_zero, true_and]
  split_ifs <;> omega

theorem vsgn_negI (b a : ℤ) (c : GInt) :
    vsgn b a (c, c + Unit4.vec .negI) = if c.2 = b + 1 ∧ c.1 ≤ a then -1 else 0 := by
  obtain ⟨c1, c2⟩ := c
  simp only [vsgn, Unit4.vec, Prod.mk_add_mk, add_zero, true_and]
  split_ifs <;> omega

/-- The edges of a concatenation: the second part starts where the first one ends. -/
theorem edgesFrom_append (c : GInt) (u v : F2Word) :
    edgesFrom c (u ++ v) = edgesFrom c u ++ edgesFrom (c + F2Word.sum u) v := by
  induction u generalizing c with
  | nil => simp [edgesFrom, F2Word.sum]
  | cons x u ih =>
    simp only [List.cons_append, edgesFrom, ih (c + x.vec), F2Word.sum, List.map_cons, List.sum_cons,
      add_assoc, List.cons_append]

end FLatticePaper.Tiles
