import FLatticePaper.Tiles.NeighbourDisjoint

/-! The edge clause of `lemma:almost_square_tiling`: a nonzero lattice translate of the tile sharing an edge with it is
`± g1` or `± g2`. The diagonal translates `± (g1 + g2)` and `± (g1 - g2)` share no edge with the tile, by the row range
and the column range of the tile. The remaining global input is `NoFarAdjacency`: a cell adjacent to the tile across a
boundary edge lies in a surround translate, or in no lattice translate (an almost tiling has gap cells). -/

namespace FLatticePaper.Tiles

/-- The global input `NoFarAdjacency` of `lemma:almost_square_tiling`: every cell outside the tile and adjacent to it
across a boundary edge lies in a surround translate `T + s`, or in no lattice translate of the tile. This is the
topological step of the paper (the closure of the surrounding is simply connected); it is stated as a hypothesis. -/
structure NoFarAdjacency (T : CellTile) (v₁ v₂ : GInt) : Prop where
  gap : ∀ d : GInt, (∃ c ∈ T, ∃ e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)], c + e = d) → d ∉ T →
    (∃ s ∈ surroundVectors v₁ v₂, d - s ∈ T) ∨ (∀ u ∈ latticeOf v₁ v₂, d - u ∉ T)

/-- Sharing an edge is symmetric under negation of the translate. -/
theorem sharesEdge_neg {T : CellTile} {v : GInt} (h : SharesEdge T v) : SharesEdge T (-v) := by
  obtain ⟨c, hc, e, he, hx⟩ := h
  refine ⟨c + e - v, hx, -e, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
    rcases he with rfl | rfl | rfl | rfl <;> simp
  · have : c + e - v + -e - -v = c := by abel
    rw [this]
    exact hc

/-- The first coordinate sum and the cell columns: every cell of the tile lies in the columns `[X2, P)` and the rows
`[c.2, c.2 + Q)`, relative to the lower-left corner. -/
theorem cell_bounds {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (x : GInt) (hx : x ∈ T) :
    c.1 + (F2Word.sum w2).1 ≤ x.1 ∧ x.1 < c.1 + (F2Word.sum w1).1 ∧
      c.2 ≤ x.2 ∧ x.2 < c.2 + (cntI w1 + cntI w2) := by
  obtain ⟨a, b⟩ := x
  rw [mem_iff_nr hT h1 h2] at hx
  obtain ⟨⟨h0, h3⟩, hS, hN⟩ := hx
  have hs := Srow_ge c w1 w2 h1 h2 (b - c.2)
  have hn := Nrow_le c w1 w2 h1 h2 (b - c.2)
  exact ⟨by show c.1 + (F2Word.sum w2).1 ≤ a; linarith, by show a < c.1 + (F2Word.sum w1).1; linarith,
    by show c.2 ≤ b; omega, by show b < c.2 + (cntI w1 + cntI w2); omega⟩

/-- The diagonal translate `g1 + g2 = (P + (X2 - 1), (q + 1) + r)` shares no edge with the tile: its row offset exceeds the
height of the tile by one. -/
theorem not_sharesEdge_sum {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (v : GInt) (_hv1 : v.1 = (F2Word.sum w1).1 + ((F2Word.sum w2).1 - 1))
    (_hv2 : v.2 = cntI w1 + 1 + cntI w2) : ¬ SharesEdge T v := by
  rintro ⟨x, hx, e, he, hxv⟩
  have hxb := cell_bounds hT h1 h2 _ hxv
  have hcb := cell_bounds hT h1 h2 x hx
  have he2 : e.2 ≤ 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> norm_num
  have hsub : (x + e - v).2 = x.2 + e.2 - v.2 := by simp
  rw [hsub] at hxb
  omega

/-- The diagonal translate `g1 - g2 = (P - (X2 - 1), (q + 1) - r)` shares no edge with the tile: its column offset
exceeds the width of the tile by one. -/
theorem not_sharesEdge_diff {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (v : GInt) (_hv1 : v.1 = (F2Word.sum w1).1 - ((F2Word.sum w2).1 - 1))
    (_hv2 : v.2 = cntI w1 + 1 - cntI w2) : ¬ SharesEdge T v := by
  rintro ⟨x, hx, e, he, hxv⟩
  have hxb := cell_bounds hT h1 h2 _ hxv
  have hcb := cell_bounds hT h1 h2 x hx
  have he1 : e.1 ≤ 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> norm_num
  have hsub : (x + e - v).1 = x.1 + e.1 - v.1 := by simp
  rw [hsub] at hxb
  omega

/-- The first admissible inequality packaged for the edge clause: the two lattice generators of the tile. -/
theorem almostV₁_eq (w1 : F2Word) (hn1 : ∀ x ∈ w1, x ≠ .negI) :
    almostV₁ w1 = ((F2Word.sum w1).1, cntI w1 + 1) := by
  ext <;> simp [almostV₁, gI, sum_snd w1 hn1]

theorem almostV₂_eq (w2 : F2Word) (hn2 : ∀ x ∈ w2, x ≠ .negI) :
    almostV₂ w2 = ((F2Word.sum w2).1 - 1, cntI w2) := by
  ext <;> simp [almostV₂, gOne, sum_snd w2 hn2]

theorem surround_mem_lattice {v₁ v₂ s : GInt} (hs : s ∈ surroundVectors v₁ v₂) : s ∈ latticeOf v₁ v₂ := by
  obtain ⟨k, k', -, -, -, -, -, rfl⟩ := hs
  exact ⟨k, k', rfl⟩

theorem zero_mem_lattice (v₁ v₂ : GInt) : (0 : GInt) ∈ latticeOf v₁ v₂ := ⟨0, 0, by ext <;> simp⟩

/-- The edge clause: a nonzero lattice translate of the tile sharing an edge with it is `± g1` or `± g2`. It follows from
uniqueness (through the first-crossing input `NoFirstCrossing`), the gap clause `NoFarAdjacency`, and the diagonal
exclusions above. -/
theorem edge_clause {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2)) (hA1 : Admissible w1)
    (hA2 : Admissible (w2.map Unit4.mulNegI))
    (hF : NoFirstCrossing T (almostV₁ w1) (almostV₂ w2))
    (hG : NoFarAdjacency T (almostV₁ w1) (almostV₂ w2)) :
    EdgeSharingClause T (almostV₁ w1) (almostV₂ w2) := by
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have hmono : ∀ y ∈ w2.map Unit4.mulNegI, y = .one ∨ y = .i := hA2.1
  have h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne := by
    intro x hx
    have hm := hmono x.mulNegI (List.mem_map_of_mem hx)
    have hxe : x = Unit4.mulI (Unit4.mulNegI x) := by cases x <;> rfl
    rcases hm with h | h
    · rw [hxe, h]; simp [Unit4.mulI]
    · rw [hxe, h]; simp [Unit4.mulI]
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by
    rcases h1 x hx with h | h <;> simp [h]
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by
    rcases h2 x hx with h | h <;> simp [h]
  have hN := neighbour_disjoint hT hA1 hA2
  have hU := uniqueness_of_neighbours hN hF
  intro v hv hv0 hsh
  obtain ⟨x, hx, e, he, hxv⟩ := hsh
  have hd_notin : x + e ∉ T := by
    intro hdT
    have := hU (x + e) v hv 0 (zero_mem_lattice _ _) hxv (by rw [sub_zero]; exact hdT)
    exact hv0 this
  rcases hG.gap (x + e) ⟨x, hx, e, he, rfl⟩ hd_notin with ⟨s, hs, hds⟩ | hnone
  · have hvs : v = s := hU (x + e) v hv s (surround_mem_lattice hs) hxv hds
    obtain ⟨k, k', hk1, hk2, hk3, hk4, hk5, hsk⟩ := hs
    have hvpair : v = (k * (F2Word.sum w1).1 + k' * ((F2Word.sum w2).1 - 1),
        k * (cntI w1 + 1) + k' * cntI w2) := by
      rw [hvs, hsk, almostV₁_eq w1 hn1, almostV₂_eq w2 hn2]
    have hsh' : SharesEdge T v := ⟨x, hx, e, he, hxv⟩
    rw [almostV₁_eq w1 hn1, almostV₂_eq w2 hn2]
    rcases (show k = -1 ∨ k = 0 ∨ k = 1 by omega) with rfl | rfl | rfl <;>
      rcases (show k' = -1 ∨ k' = 0 ∨ k' = 1 by omega) with rfl | rfl | rfl
    · -- (-1, -1): minus the diagonal g1 + g2
      exfalso
      have hneg := sharesEdge_neg hsh'
      refine not_sharesEdge_sum hT h1 h2 (-v) ?_ ?_ hneg
      · rw [hvpair]; simp; ring
      · rw [hvpair]; simp; ring
    · -- (-1, 0): minus g1
      right; left
      rw [hvpair]; ext <;> simp
    · -- (-1, 1): minus the diagonal g1 - g2
      exfalso
      have hneg := sharesEdge_neg hsh'
      refine not_sharesEdge_diff hT h1 h2 (-v) ?_ ?_ hneg
      · rw [hvpair]; simp; ring
      · rw [hvpair]; simp; ring
    · -- (0, -1): minus g2
      right; right; right
      rw [hvpair]; ext <;> simp
    · exact absurd rfl hk5
    · -- (0, 1): g2
      right; right; left
      rw [hvpair]; ext <;> simp
    · -- (1, -1): the diagonal g1 - g2
      exfalso
      refine not_sharesEdge_diff hT h1 h2 v ?_ ?_ hsh'
      · rw [hvpair]; simp; ring
      · rw [hvpair]; simp; ring
    · -- (1, 0): g1
      left
      rw [hvpair]; ext <;> simp
    · -- (1, 1): the diagonal g1 + g2
      exfalso
      refine not_sharesEdge_sum hT h1 h2 v ?_ ?_ hsh'
      · rw [hvpair]; simp
      · rw [hvpair]; simp
  · exact absurd hxv (hnone v hv)

end FLatticePaper.Tiles
