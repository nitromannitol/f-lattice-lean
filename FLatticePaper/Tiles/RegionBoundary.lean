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

/-! ### No-EW words of the four-arc loop -/

theorem noEW_of_no_negOne : ∀ u : F2Word, (∀ y ∈ u, y ≠ .negOne) → NoEWChain u
  | [], _ => trivial
  | [_], _ => trivial
  | x :: y :: u, h => by
    show NoEWAdj x y ∧ NoEWChain (y :: u)
    refine ⟨?_, noEW_of_no_negOne (y :: u) (fun z hz => h z (List.mem_cons_of_mem _ hz))⟩
    show ¬((x = .one ∧ y = .negOne) ∨ (x = .negOne ∧ y = .one))
    rintro (⟨-, hy⟩ | ⟨hx, -⟩)
    · exact h y (by simp) hy
    · exact h x (by simp) hx

theorem noEW_of_no_one : ∀ u : F2Word, (∀ y ∈ u, y ≠ .one) → NoEWChain u
  | [], _ => trivial
  | [_], _ => trivial
  | x :: y :: u, h => by
    show NoEWAdj x y ∧ NoEWChain (y :: u)
    refine ⟨?_, noEW_of_no_one (y :: u) (fun z hz => h z (List.mem_cons_of_mem _ hz))⟩
    show ¬((x = .one ∧ y = .negOne) ∨ (x = .negOne ∧ y = .one))
    rintro (⟨hx, -⟩ | ⟨-, hy⟩)
    · exact h x (by simp) hx
    · exact h y (by simp) hy

theorem noEW_append : ∀ u v : F2Word, NoEWChain u → NoEWChain v →
    (∀ y ∈ u.getLast?, ∀ x ∈ v.head?, NoEWAdj y x) → NoEWChain (u ++ v)
  | [], v, _, hv, _ => by simpa using hv
  | [_], [], _, _, _ => trivial
  | [x], y :: v, _, hv, h => by
    show NoEWAdj x y ∧ NoEWChain (y :: v)
    exact ⟨h x (by simp) y (by simp), hv⟩
  | x :: y :: u, v, hu, hv, h => by
    obtain ⟨hxy, hu'⟩ : NoEWAdj x y ∧ NoEWChain (y :: u) := hu
    show NoEWAdj x y ∧ NoEWChain (y :: (u ++ v))
    refine ⟨hxy, ?_⟩
    have := noEW_append (y :: u) v hu' hv (fun z hz w hw => h z (by simpa using hz) w hw)
    simpa using this

/-! ### The walk of the four-arc loop, edge type by edge type -/

theorem FF_eq_colN (u : F2Word) (j : ℤ) (hj0 : 0 ≤ j) (hj : j < cntI u) : FF u j = colN u (0, 0) j := by
  unfold FF
  rw [if_neg (not_lt.mpr hj0), if_pos hj]

/-- The walk of a word with letters `one`, `i`, `negOne` has no south edge. -/
theorem no_S (w1 w2 : F2Word) (hU : ∀ x ∈ w1 ++ w2, x = .one ∨ x = .i ∨ x = .negOne) (a b : ℤ) :
    ((a, b + 1), (a, b)) ∉ edgesFrom (0, 0) (w1 ++ w2) := by
  intro h
  obtain ⟨x, hx, hv⟩ := edge_shape (0, 0) (w1 ++ w2) _ h
  rcases hU x hx with rfl | rfl | rfl
  all_goals simp [Unit4.vec, Prod.ext_iff] at hv
  all_goals omega

theorem walk_E (w1 w2 : F2Word) (RD : RunData (w1 ++ w2)) (c : ℤ)
    (hz : F2Word.sum (w1 ++ w2) = (c, cntI (w1 ++ w2))) (q k : ℤ) :
    ((q, k), (q + 1, k)) ∈ edgesFrom (0, 0) (boundaryWordOf w1 w2) ↔
      ((0 ≤ k ∧ k ≤ cntI (w1 ++ w2) ∧ FF (w1 ++ w2) (k - 1) ≤ q ∧ q < FF (w1 ++ w2) k) ∨
        (0 ≤ cntI (w1 ++ w2) - k ∧ cntI (w1 ++ w2) - k ≤ cntI (w1 ++ w2) ∧
          FF (w1 ++ w2) (cntI (w1 ++ w2) - k) ≤ c - q - 1 ∧
          c - q - 1 < FF (w1 ++ w2) (cntI (w1 ++ w2) - k - 1))) := by
  have key : halfE (c, cntI (w1 ++ w2)) ((q, k), (q + 1, k)) =
      ((c - (q + 1) + 1, cntI (w1 ++ w2) - k), (c - (q + 1), cntI (w1 ++ w2) - k)) := by
    ext <;> simp [halfE]
    all_goals ring
  rw [mem_walk_iff, hz, key, show c - q - 1 = c - (q + 1) by ring]
  constructor
  · rintro (h | h)
    · exact Or.inl ((RD.E q k).1 h)
    · exact Or.inr ((RD.W _ _).1 h)
  · rintro (h | h)
    · exact Or.inl ((RD.E q k).2 h)
    · exact Or.inr ((RD.W _ _).2 h)

theorem walk_W (w1 w2 : F2Word) (RD : RunData (w1 ++ w2)) (c : ℤ)
    (hz : F2Word.sum (w1 ++ w2) = (c, cntI (w1 ++ w2))) (q k : ℤ) :
    ((q + 1, k), (q, k)) ∈ edgesFrom (0, 0) (boundaryWordOf w1 w2) ↔
      ((0 ≤ k ∧ k ≤ cntI (w1 ++ w2) ∧ FF (w1 ++ w2) k ≤ q ∧ q < FF (w1 ++ w2) (k - 1)) ∨
        (0 ≤ cntI (w1 ++ w2) - k ∧ cntI (w1 ++ w2) - k ≤ cntI (w1 ++ w2) ∧
          FF (w1 ++ w2) (cntI (w1 ++ w2) - k - 1) ≤ c - q - 1 ∧
          c - q - 1 < FF (w1 ++ w2) (cntI (w1 ++ w2) - k))) := by
  have key : halfE (c, cntI (w1 ++ w2)) ((q + 1, k), (q, k)) =
      ((c - (q + 1), cntI (w1 ++ w2) - k), (c - (q + 1) + 1, cntI (w1 ++ w2) - k)) := by
    ext <;> simp [halfE]
    all_goals ring
  rw [mem_walk_iff, hz, key, show c - q - 1 = c - (q + 1) by ring]
  constructor
  · rintro (h | h)
    · exact Or.inl ((RD.W q k).1 h)
    · exact Or.inr ((RD.E _ _).1 h)
  · rintro (h | h)
    · exact Or.inl ((RD.W q k).2 h)
    · exact Or.inr ((RD.E _ _).2 h)

theorem walk_N (w1 w2 : F2Word) (RD : RunData (w1 ++ w2)) (hU : ∀ x ∈ w1 ++ w2, x = .one ∨ x = .i ∨ x = .negOne)
    (c : ℤ) (hz : F2Word.sum (w1 ++ w2) = (c, cntI (w1 ++ w2))) (x k : ℤ) :
    ((x, k), (x, k + 1)) ∈ edgesFrom (0, 0) (boundaryWordOf w1 w2) ↔
      (0 ≤ k ∧ k < cntI (w1 ++ w2) ∧ x = colN (w1 ++ w2) (0, 0) k) := by
  have key : halfE (c, cntI (w1 ++ w2)) ((x, k), (x, k + 1)) =
      ((c - x, cntI (w1 ++ w2) - k - 1 + 1), (c - x, cntI (w1 ++ w2) - k - 1)) := by
    ext <;> simp [halfE]
    all_goals ring
  rw [mem_walk_iff, hz, key, or_iff_left (no_S w1 w2 hU (c - x) (cntI (w1 ++ w2) - k - 1))]
  exact RD.N x k

theorem walk_S (w1 w2 : F2Word) (RD : RunData (w1 ++ w2)) (hU : ∀ x ∈ w1 ++ w2, x = .one ∨ x = .i ∨ x = .negOne)
    (c : ℤ) (hz : F2Word.sum (w1 ++ w2) = (c, cntI (w1 ++ w2))) (x k : ℤ) :
    ((x, k + 1), (x, k)) ∈ edgesFrom (0, 0) (boundaryWordOf w1 w2) ↔
      (0 ≤ cntI (w1 ++ w2) - k - 1 ∧ cntI (w1 ++ w2) - k - 1 < cntI (w1 ++ w2) ∧
        c - x = colN (w1 ++ w2) (0, 0) (cntI (w1 ++ w2) - k - 1)) := by
  have key : halfE (c, cntI (w1 ++ w2)) ((x, k + 1), (x, k)) =
      ((c - x, cntI (w1 ++ w2) - k - 1), (c - x, cntI (w1 ++ w2) - k - 1 + 1)) := by
    ext <;> simp [halfE]
    all_goals ring
  rw [mem_walk_iff, hz, key, or_iff_right (no_S w1 w2 hU x k)]
  exact RD.N (c - x) (cntI (w1 ++ w2) - k - 1)

end FLatticePaper.Tiles.RegionBoundary
