import FLatticePaper.Tiles.TilingWalk
import FLatticePaper.Tiles.TilingGreen
import FLatticePaper.Tiles.TilingCount

/-! Task 32, part 5: the boundary edge balance from the boundary word `w₁ * w₂ * ŵ₁ * ŵ₂`.

The directed boundary edges of the tile form the list `edges c (w₁ ++ w₂ ++ ŵ₁ ++ ŵ₂)` (each once, by the boundary word).
Its four pieces are the walk of `w₁`, the walk of `w₂` translated by `Σw₁`, the reversed walk of `w₁` translated by `Σw₂`, and
the reversed walk of `w₂`. Since `Σw₁` and `Σw₂` lie in the lattice `N`, translation does not change the coset of a tail, and
reversal exchanges the coset `Q` with `Q + [D]` and the direction `D` with `-D`. The two forward pieces and the two reversed
pieces therefore have equal counts in the two classes, which is the balance `edgeCount N T Q D = edgeCount N T (Q + [D]) (-D)`.
The area identity `#T = det(Σw₁, Σw₂)` is read off the same list with the shoelace form. -/

namespace FLatticePaper.Tiles
open Classical

theorem qmk_eq_zero_of_mem {N : AddSubgroup GInt} {g : GInt} (hg : g ∈ N) : qmk N g = 0 :=
  (QuotientAddGroup.eq_zero_iff g).mpr hg

/-- The number of entries of the list `X` in the coset `Q` with direction `D`. -/
noncomputable def listCount (N : AddSubgroup GInt) (X : List (GInt × GInt)) (Q : GInt ⧸ N) (D : GInt) : ℕ :=
  X.countP fun a => decide (qmk N a.1 = Q ∧ a.2 - a.1 = D)

theorem listCount_eq_edgeCount (N : AddSubgroup GInt) (T : CellTile) {X : List (GInt × GInt)}
    (hn : X.Nodup) (hf : X.toFinset = T.boundaryEdges) (Q : GInt ⧸ N) (D : GInt) :
    listCount N X Q D = edgeCount N T Q D := by
  unfold listCount edgeCount
  rw [← hf, List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hn.filter _), List.toFinset_filter]
  simp

theorem listCount_append (N : AddSubgroup GInt) (X Y : List (GInt × GInt)) (Q : GInt ⧸ N) (D : GInt) :
    listCount N (X ++ Y) Q D = listCount N X Q D + listCount N Y Q D := by
  unfold listCount
  rw [List.countP_append]

theorem listCount_cons (N : AddSubgroup GInt) (a : GInt × GInt) (X : List (GInt × GInt)) (Q : GInt ⧸ N)
    (D : GInt) : listCount N (a :: X) Q D = listCount N [a] Q D + listCount N X Q D :=
  listCount_append N [a] X Q D

theorem listCount_nil (N : AddSubgroup GInt) (Q : GInt ⧸ N) (D : GInt) : listCount N [] Q D = 0 := by
  simp [listCount]

theorem pred_shift (N : AddSubgroup GInt) {g : GInt} (hg : g ∈ N) (Q : GInt ⧸ N) (D : GInt) (a : GInt × GInt) :
    (qmk N (a.1 + g) = Q ∧ a.2 + g - (a.1 + g) = D) ↔ (qmk N a.1 = Q ∧ a.2 - a.1 = D) := by
  rw [map_add, qmk_eq_zero_of_mem hg, add_zero, add_sub_add_right_eq_sub]

/-- Translation by a vector of `N` does not change the counts. -/
theorem listCount_shift (N : AddSubgroup GInt) (X : List (GInt × GInt)) {g : GInt} (hg : g ∈ N)
    (Q : GInt ⧸ N) (D : GInt) : listCount N (X.map (edgeShift g)) Q D = listCount N X Q D := by
  induction X with
  | nil => simp [listCount]
  | cons a X ih =>
    unfold listCount at ih ⊢
    simp only [List.map_cons, List.countP_cons, edgeShift, decide_eq_true_eq, pred_shift N hg] at ih ⊢
    rw [ih]

/-- The reversal of a single edge exchanges the coset `Q` with `Q + [D]` and the direction `D` with `-D`. -/
theorem listCount_single_rev (N : AddSubgroup GInt) (a : GInt × GInt) (Q : GInt ⧸ N) (D : GInt) :
    listCount N [edgeRev a] Q D = listCount N [a] (Q + qmk N D) (-D) := by
  have hP : (qmk N a.2 = Q ∧ a.1 - a.2 = D) ↔ (qmk N a.1 = Q + qmk N D ∧ a.2 - a.1 = -D) := by
    constructor
    · rintro ⟨h1, h2⟩
      have e : a.1 = a.2 + D := by
        rw [← h2]
        abel
      refine ⟨?_, ?_⟩
      · rw [e, map_add, h1]
      · rw [← h2]
        abel
    · rintro ⟨h1, h2⟩
      have e : a.2 = a.1 + -D := by
        rw [← h2]
        abel
      refine ⟨?_, ?_⟩
      · rw [e, map_add, map_neg, h1]
        abel
      · rw [← neg_sub a.2 a.1, h2, neg_neg]
  unfold listCount
  simp only [List.countP_cons, List.countP_nil, edgeRev, hP]

theorem listCount_reverse_rev (N : AddSubgroup GInt) (X : List (GInt × GInt)) (Q : GInt ⧸ N) (D : GInt) :
    listCount N (X.reverse.map edgeRev) Q D = listCount N X (Q + qmk N D) (-D) := by
  induction X with
  | nil => simp [listCount]
  | cons a X ih =>
    rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, listCount_append, ih,
      listCount_single_rev, listCount_cons N a X, add_comm]

/-- The four pieces of the boundary edge list of `w₁ * w₂ * ŵ₁ * ŵ₂`, counted in the class `(Q, D)`. -/
theorem listCount_boundary (N : AddSubgroup GInt) (c : GInt) (w₁ w₂ : F2Word)
    (hg₁ : F2Word.sum w₁ ∈ N) (hg₂ : F2Word.sum w₂ ∈ N) (Q : GInt ⧸ N) (D : GInt) :
    listCount N (F2Word.edges c (w₁ ++ w₂ ++ F2Word.hat w₁ ++ F2Word.hat w₂)) Q D =
      listCount N (F2Word.edges c w₁) Q D + listCount N (F2Word.edges c w₂) Q D +
        listCount N (F2Word.edges c w₁) (Q + qmk N D) (-D) +
        listCount N (F2Word.edges c w₂) (Q + qmk N D) (-D) := by
  rw [F2Word.edges_boundary, listCount_append, listCount_append, listCount_append,
    listCount_shift N _ hg₁, listCount_reverse_rev, listCount_shift N _ hg₂, listCount_reverse_rev]

/-- The boundary edge balance of a tile whose boundary word is `w₁ * w₂ * ŵ₁ * ŵ₂`. -/
theorem edgeCount_balance (N : AddSubgroup GInt) (T : CellTile) (c : GInt) (w₁ w₂ : F2Word)
    (hw : IsBoundaryWordAt T c (w₁ ++ w₂ ++ F2Word.hat w₁ ++ F2Word.hat w₂))
    (hg₁ : F2Word.sum w₁ ∈ N) (hg₂ : F2Word.sum w₂ ∈ N) (Q : GInt ⧸ N) (D : GInt) :
    edgeCount N T Q D = edgeCount N T (Q + qmk N D) (-D) := by
  obtain ⟨_, _, hn, hf⟩ := hw
  have hn' : (F2Word.edges c (w₁ ++ w₂ ++ F2Word.hat w₁ ++ F2Word.hat w₂)).Nodup := hn
  have hf' : (F2Word.edges c (w₁ ++ w₂ ++ F2Word.hat w₁ ++ F2Word.hat w₂)).toFinset = T.boundaryEdges := hf
  rw [← listCount_eq_edgeCount N T hn' hf' Q D, ← listCount_eq_edgeCount N T hn' hf' (Q + qmk N D) (-D),
    listCount_boundary N c w₁ w₂ hg₁ hg₂, listCount_boundary N c w₁ w₂ hg₁ hg₂, map_neg, add_neg_cancel_right,
    neg_neg]
  ring

/-- The area identity: the number of cells of a tile with boundary word `w₁ * w₂ * ŵ₁ * ŵ₂` is `det(Σw₁, Σw₂)`. -/
theorem card_eq_detG (T : CellTile) (c : GInt) (w₁ w₂ : F2Word)
    (hw : IsBoundaryWordAt T c (w₁ ++ w₂ ++ F2Word.hat w₁ ++ F2Word.hat w₂)) :
    (T.card : ℤ) = detG (F2Word.sum w₁) (F2Word.sum w₂) := by
  obtain ⟨_, _, hn, hf⟩ := hw
  have hn' : (F2Word.edges c (w₁ ++ w₂ ++ F2Word.hat w₁ ++ F2Word.hat w₂)).Nodup := hn
  have hf' : (F2Word.edges c (w₁ ++ w₂ ++ F2Word.hat w₁ ++ F2Word.hat w₂)).toFinset = T.boundaryEdges := hf
  have h1 := green_boundary T
  have h2 : ∑ e ∈ T.boundaryEdges, omegaE e =
      ((F2Word.edges c (w₁ ++ w₂ ++ F2Word.hat w₁ ++ F2Word.hat w₂)).map omegaE).sum := by
    rw [← hf']
    exact List.sum_toFinset omegaE hn'
  have h3 := omega_sum_boundary c w₁ w₂
  omega

end FLatticePaper.Tiles
