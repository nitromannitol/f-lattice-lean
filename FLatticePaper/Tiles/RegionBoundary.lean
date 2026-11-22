import FLatticePaper.Tiles.RegionRuns
import FLatticePaper.Tiles.FourWalks
import FLatticePaper.Tiles.ArcInequality
import FLatticePaper.Tiles.RegionArith

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

/-! ### Shapes of edges -/

theorem bdry_shape (T : CellTile) (e : GInt × GInt) (he : e ∈ T.boundaryEdges) :
    (∃ q k : ℤ, e = ((q, k), (q + 1, k))) ∨ (∃ q k : ℤ, e = ((q + 1, k), (q, k))) ∨
      (∃ x k : ℤ, e = ((x, k), (x, k + 1))) ∨ (∃ x k : ℤ, e = ((x, k + 1), (x, k))) := by
  obtain ⟨c, hc, f, hf, -, hfe⟩ := (mem_boundaryEdges_iff T e).mp he
  obtain ⟨a, b⟩ := c
  simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · refine Or.inl ⟨a, b, ?_⟩
    rw [← hfe]
    simp [gOne]
  · refine Or.inr (Or.inr (Or.inl ⟨a + 1, b, ?_⟩))
    rw [← hfe]
    simp [gOne, gI]
  · refine Or.inr (Or.inl ⟨a, b + 1, ?_⟩)
    rw [← hfe]
    simp [gOne, gI]
  · refine Or.inr (Or.inr (Or.inr ⟨a, b, ?_⟩))
    rw [← hfe]
    simp [gI]

/-- The walk of `w1 ++ w2` has letters `one`, `i`, `negOne`: its edges are east, west or north. -/
theorem U_shape (w1 w2 : F2Word) (hU : ∀ x ∈ w1 ++ w2, x = .one ∨ x = .i ∨ x = .negOne) (e : GInt × GInt)
    (he : e ∈ edgesFrom (0, 0) (w1 ++ w2)) :
    (∃ q k : ℤ, e = ((q, k), (q + 1, k))) ∨ (∃ q k : ℤ, e = ((q + 1, k), (q, k))) ∨
      (∃ x k : ℤ, e = ((x, k), (x, k + 1))) := by
  obtain ⟨x, hx, hv⟩ := edge_shape (0, 0) (w1 ++ w2) e he
  obtain ⟨⟨p1, p2⟩, ⟨p3, p4⟩⟩ := e
  rcases hU x hx with rfl | rfl | rfl
  · simp [Unit4.vec, Prod.ext_iff] at hv
    obtain ⟨h3, h4⟩ := hv
    have e1 : p3 = p1 + 1 := by omega
    have e2 : p4 = p2 := by omega
    exact Or.inl ⟨p1, p2, by rw [e1, e2]⟩
  · simp [Unit4.vec, Prod.ext_iff] at hv
    obtain ⟨h3, h4⟩ := hv
    have e1 : p3 = p1 := by omega
    have e2 : p4 = p2 + 1 := by omega
    exact Or.inr (Or.inr ⟨p1, p2, by rw [e1, e2]⟩)
  · simp [Unit4.vec, Prod.ext_iff] at hv
    obtain ⟨h3, h4⟩ := hv
    have e1 : p1 = p3 + 1 := by omega
    have e2 : p4 = p2 := by omega
    exact Or.inr (Or.inl ⟨p3, p2, by rw [e1, e2]⟩)

/-- Every edge of the four-arc walk has one of the four unit shapes. -/
theorem walk_shape (w1 w2 : F2Word) (hU : ∀ x ∈ w1 ++ w2, x = .one ∨ x = .i ∨ x = .negOne)
    (c : ℤ) (hz : F2Word.sum (w1 ++ w2) = (c, cntI (w1 ++ w2))) (e : GInt × GInt)
    (he : e ∈ edgesFrom (0, 0) (boundaryWordOf w1 w2)) :
    (∃ q k : ℤ, e = ((q, k), (q + 1, k))) ∨ (∃ q k : ℤ, e = ((q + 1, k), (q, k))) ∨
      (∃ x k : ℤ, e = ((x, k), (x, k + 1))) ∨ (∃ x k : ℤ, e = ((x, k + 1), (x, k))) := by
  rw [mem_walk_iff] at he
  rcases he with h | h
  · rcases U_shape w1 w2 hU e h with ⟨q, k, hq⟩ | ⟨q, k, hq⟩ | ⟨x, k, hq⟩
    · exact Or.inl ⟨q, k, hq⟩
    · exact Or.inr (Or.inl ⟨q, k, hq⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨x, k, hq⟩))
  · rw [hz] at h
    obtain ⟨x, hx, hv⟩ := edge_shape (0, 0) (w1 ++ w2) _ h
    obtain ⟨⟨p1, p2⟩, ⟨p3, p4⟩⟩ := e
    rcases hU x hx with rfl | rfl | rfl
    · simp [halfE, Unit4.vec, Prod.ext_iff] at hv
      obtain ⟨h3, h4⟩ := hv
      have e1 : p1 = p3 + 1 := by omega
      have e2 : p4 = p2 := by omega
      exact Or.inr (Or.inl ⟨p3, p2, by rw [e1, e2]⟩)
    · simp [halfE, Unit4.vec, Prod.ext_iff] at hv
      obtain ⟨h3, h4⟩ := hv
      have e1 : p3 = p1 := by omega
      have e2 : p2 = p4 + 1 := by omega
      exact Or.inr (Or.inr (Or.inr ⟨p1, p4, by rw [e1, e2]⟩))
    · simp [halfE, Unit4.vec, Prod.ext_iff] at hv
      obtain ⟨h3, h4⟩ := hv
      have e1 : p3 = p1 + 1 := by omega
      have e2 : p4 = p2 := by omega
      exact Or.inl ⟨p1, p2, by rw [e1, e2]⟩

/-! ### The half-turns of the four-arc walk, as conditions on FF -/

theorem half_E_iff (w1 w2 : F2Word) (RD : RunData (w1 ++ w2)) (c : ℤ)
    (hz : F2Word.sum (w1 ++ w2) = (c, cntI (w1 ++ w2))) (q k : ℤ) :
    halfE (F2Word.sum (w1 ++ w2)) ((q, k), (q + 1, k)) ∈ edgesFrom (0, 0) (w1 ++ w2) ↔
      (0 ≤ cntI (w1 ++ w2) - k ∧ cntI (w1 ++ w2) - k ≤ cntI (w1 ++ w2) ∧
        FF (w1 ++ w2) (cntI (w1 ++ w2) - k) ≤ c - q - 1 ∧
        c - q - 1 < FF (w1 ++ w2) (cntI (w1 ++ w2) - k - 1)) := by
  have key : halfE (F2Word.sum (w1 ++ w2)) ((q, k), (q + 1, k)) =
      ((c - (q + 1) + 1, cntI (w1 ++ w2) - k), (c - (q + 1), cntI (w1 ++ w2) - k)) := by
    rw [hz]
    ext <;> simp [halfE]
    all_goals ring
  rw [key, show c - q - 1 = c - (q + 1) by ring]
  exact RD.W _ _

theorem half_W_iff (w1 w2 : F2Word) (RD : RunData (w1 ++ w2)) (c : ℤ)
    (hz : F2Word.sum (w1 ++ w2) = (c, cntI (w1 ++ w2))) (q k : ℤ) :
    halfE (F2Word.sum (w1 ++ w2)) ((q + 1, k), (q, k)) ∈ edgesFrom (0, 0) (w1 ++ w2) ↔
      (0 ≤ cntI (w1 ++ w2) - k ∧ cntI (w1 ++ w2) - k ≤ cntI (w1 ++ w2) ∧
        FF (w1 ++ w2) (cntI (w1 ++ w2) - k - 1) ≤ c - q - 1 ∧
        c - q - 1 < FF (w1 ++ w2) (cntI (w1 ++ w2) - k)) := by
  have key : halfE (F2Word.sum (w1 ++ w2)) ((q + 1, k), (q, k)) =
      ((c - (q + 1), cntI (w1 ++ w2) - k), (c - (q + 1) + 1, cntI (w1 ++ w2) - k)) := by
    rw [hz]
    ext <;> simp [halfE]
    all_goals ring
  rw [key, show c - q - 1 = c - (q + 1) by ring]
  exact RD.E _ _

/-- The walk of `w1 ++ w2` contains no edge whose half-turn is also in it. -/
theorem no_cross (w1 w2 : F2Word) (RD : RunData (w1 ++ w2))
    (hU : ∀ x ∈ w1 ++ w2, x = .one ∨ x = .i ∨ x = .negOne) (c : ℤ)
    (hz : F2Word.sum (w1 ++ w2) = (c, cntI (w1 ++ w2)))
    (D : RegionArith.ArcData (FF (w1 ++ w2)) (cntI (w1 ++ w2)) c) (e : GInt × GInt)
    (he : e ∈ edgesFrom (0, 0) (w1 ++ w2)) :
    halfE (F2Word.sum (w1 ++ w2)) e ∉ edgesFrom (0, 0) (w1 ++ w2) := by
  intro hh
  rcases U_shape w1 w2 hU e he with ⟨q, k, rfl⟩ | ⟨q, k, rfl⟩ | ⟨x, k, rfl⟩
  · exact RegionArith.ArcData.cross_E D q k ⟨(RD.E q k).1 he, (half_E_iff w1 w2 RD c hz q k).1 hh⟩
  · exact RegionArith.ArcData.cross_W D q k ⟨(RD.W q k).1 he, (half_W_iff w1 w2 RD c hz q k).1 hh⟩
  · have hS := no_S w1 w2 hU (c - x) (cntI (w1 ++ w2) - k - 1)
    apply hS
    have key : halfE (F2Word.sum (w1 ++ w2)) ((x, k), (x, k + 1)) =
        ((c - x, cntI (w1 ++ w2) - k - 1 + 1), (c - x, cntI (w1 ++ w2) - k - 1)) := by
      rw [hz]
      ext <;> simp [halfE]
      all_goals ring
    rw [key] at hh
    exact hh

/-- The lower-left vertex of the region: `FF 0 ≥ 1` when the first arc begins with a unit east step. -/
theorem colN_head_one (w : F2Word) (h1 : ∀ x ∈ w, x = .one ∨ x = .i) (hhead : w.head? = some .one) :
    1 ≤ colN w (0, 0) 0 := by
  cases w with
  | nil => simp at hhead
  | cons x rest =>
    simp at hhead
    subst hhead
    rw [arc_colN_cons_one]
    have := arc_colN_nonneg rest (fun y hy => h1 y (List.mem_cons_of_mem _ hy)) 0
    omega

/-- The four-arc tile: the cell set whose rows are the arc intervals of `w1 ++ w2` has the four-arc loop as its
boundary word, with lower-left vertex `(0, 0)`. -/
theorem region_boundary_word (T : CellTile) (w1 w2 : F2Word)
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (hhead : w1.head? = some .one)
    (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hn : (F2Word.sum w1).2 < (F2Word.sum w2).2) (ha : 0 < (F2Word.sum w1).1 + (F2Word.sum w2).1)
    (hRa : ¬ (w1.getLast? = some .one ∧ w2.head? = some .negOne))
    (hRb : ¬ (w1.head? = some .i ∧ w2.getLast? = some .i))
    (hlast : w2.getLast? = some .i)
    (hmem : ∀ x k : ℤ, ((x, k) : GInt) ∈ T ↔ 0 ≤ k ∧ k < cntI (w1 ++ w2) ∧
        (F2Word.sum (w1 ++ w2)).1 - FF (w1 ++ w2) (cntI (w1 ++ w2) - k - 1) ≤ x ∧
        x < FF (w1 ++ w2) k) :
    IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2) := by
  have hw1n : ∀ x ∈ w1, x ≠ .negI := fun x hx => by
    rcases h1 x hx with rfl | rfl <;> simp
  have hw2n : ∀ x ∈ w2, x ≠ .negI := fun x hx => by
    rcases h2 x hx with rfl | rfl <;> simp
  have hU : ∀ x ∈ w1 ++ w2, x = .one ∨ x = .i ∨ x = .negOne := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases h1 x hx with rfl | rfl <;> simp
    · rcases h2 x hx with rfl | rfl <;> simp
  have hUn : ∀ x ∈ w1 ++ w2, x ≠ .negI := fun x hx => by
    rcases hU x hx with rfl | rfl | rfl <;> simp
  have hNC : NoEWChain (w1 ++ w2) := by
    apply noEW_append w1 w2
    · exact noEW_of_no_negOne w1 (fun y hy => by rcases h1 y hy with rfl | rfl <;> simp)
    · exact noEW_of_no_one w2 (fun y hy => by rcases h2 y hy with rfl | rfl <;> simp)
    · intro y hy x hx
      rw [Option.mem_def] at hy hx
      show ¬((y = .one ∧ x = .negOne) ∨ (y = .negOne ∧ x = .one))
      rintro (⟨rfl, rfl⟩ | ⟨rfl, hx1⟩)
      · exact hRa ⟨hy, hx⟩
      · rcases h1 _ (List.mem_of_mem_getLast? hy) with h | h <;> cases h
  have RD := runData_of (w1 ++ w2) hU hNC
  have hsnd : (F2Word.sum (w1 ++ w2)).2 = cntI (w1 ++ w2) := sum_snd (w1 ++ w2) hUn
  have hz : F2Word.sum (w1 ++ w2) = ((F2Word.sum (w1 ++ w2)).1, cntI (w1 ++ w2)) := Prod.ext rfl hsnd
  have hcnt : cntI (w1 ++ w2) = (F2Word.sum w1).2 + (F2Word.sum w2).2 := by
    rw [cntI_append, sum_snd w1 hw1n, sum_snd w2 hw2n]
  have hsum1 : (F2Word.sum (w1 ++ w2)).1 = (F2Word.sum w1).1 + (F2Word.sum w2).1 := by
    rw [arc_sum_append, Prod.fst_add]
  have hn0 : 0 ≤ (F2Word.sum w1).2 := by
    rw [sum_snd w1 hw1n]
    exact cntI_nonneg w1
  have hH1 : 1 ≤ cntI (w1 ++ w2) := by omega
  have hFneg : FF (w1 ++ w2) (-1) = 0 := by simp [FF]
  have hFH : FF (w1 ++ w2) (cntI (w1 ++ w2)) = (F2Word.sum (w1 ++ w2)).1 := by
    unfold FF
    rw [if_neg (by have := cntI_nonneg (w1 ++ w2); omega), if_neg (lt_irrefl _)]
  have hl : (w1 ++ w2).getLast? = some .i := by simp [List.getLast?_append, hlast]
  have hF1 : FF (w1 ++ w2) (cntI (w1 ++ w2) - 1) = (F2Word.sum (w1 ++ w2)).1 :=
    le_antisymm (RD.inv1 (by rw [hl]; simp)) (RD.inv2 (by rw [hl]; simp))
  have hF0 : ∀ j : ℤ, 0 ≤ j → j < cntI (w1 ++ w2) → 0 ≤ FF (w1 ++ w2) j := by
    intro j hj0 hj
    rw [FF_eq_colN _ _ hj0 hj]
    by_cases hjn : j < cntI w1
    · rw [arc_F_lo w1 w2 h1 j hj0 hjn]
      exact arc_colN_nonneg w1 h1 j
    · rw [arc_F_hi w1 w2 h1 j (not_lt.mp hjn)]
      have := arc_colN_ge_sum w2 h2 (j - cntI w1)
      omega
  have hkey : ∀ q r : ℤ, 0 ≤ q → q < cntI (w1 ++ w2) → 0 ≤ r → r < cntI (w1 ++ w2) →
      cntI (w1 ++ w2) - 2 ≤ q + r → q + r ≤ cntI (w1 ++ w2) →
      (F2Word.sum (w1 ++ w2)).1 + 1 ≤ FF (w1 ++ w2) q + FF (w1 ++ w2) r := by
    intro q r hq0 hq hr0 hr hs1 hs2
    rw [FF_eq_colN _ _ hq0 hq, FF_eq_colN _ _ hr0 hr, hsum1]
    exact arc_key w1 w2 h1 h2 hn ha hRb hq0 (by omega) hr0 (by omega) (by omega) (by omega)
  have D : RegionArith.ArcData (FF (w1 ++ w2)) (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 :=
    ⟨hH1, hFneg, hFH, hF1, hF0, hkey⟩
  have hcol : ∀ y j : ℤ, (0 ≤ j ∧ j < cntI (w1 ++ w2) ∧ y = colN (w1 ++ w2) (0, 0) j) ↔
      (0 ≤ j ∧ j < cntI (w1 ++ w2) ∧ y = FF (w1 ++ w2) j) := by
    intro y j
    constructor
    · rintro ⟨hj0, hj1, hj2⟩
      exact ⟨hj0, hj1, by rw [FF_eq_colN _ _ hj0 hj1]; exact hj2⟩
    · rintro ⟨hj0, hj1, hj2⟩
      exact ⟨hj0, hj1, by rw [← FF_eq_colN _ _ hj0 hj1]; exact hj2⟩
  have hmem' : ∀ q k : ℤ, ((q, k - 1) : GInt) ∈ T ↔
      (0 ≤ k - 1 ∧ k - 1 < cntI (w1 ++ w2) ∧
        (F2Word.sum (w1 ++ w2)).1 - FF (w1 ++ w2) (cntI (w1 ++ w2) - k) ≤ q ∧
        q < FF (w1 ++ w2) (k - 1)) := by
    intro q k
    rw [hmem q (k - 1), show cntI (w1 ++ w2) - (k - 1) - 1 = cntI (w1 ++ w2) - k by ring]
  -- the four edge types: walk side and boundary side agree
  have E_eq : ∀ q k : ℤ, ((q, k), (q + 1, k)) ∈ edgesFrom (0, 0) (boundaryWordOf w1 w2) ↔
      ((q, k), (q + 1, k)) ∈ T.boundaryEdges := by
    intro q k
    rw [walk_E w1 w2 RD _ hz q k, bdry_E_iff, hmem q k, hmem' q k]
    exact RegionArith.ArcData.east_iff D q k
  have W_eq : ∀ q k : ℤ, ((q + 1, k), (q, k)) ∈ edgesFrom (0, 0) (boundaryWordOf w1 w2) ↔
      ((q + 1, k), (q, k)) ∈ T.boundaryEdges := by
    intro q k
    rw [walk_W w1 w2 RD _ hz q k, bdry_W_iff, hmem' q k, hmem q k]
    exact RegionArith.ArcData.west_iff D q k
  have N_eq : ∀ x k : ℤ, ((x, k), (x, k + 1)) ∈ edgesFrom (0, 0) (boundaryWordOf w1 w2) ↔
      ((x, k), (x, k + 1)) ∈ T.boundaryEdges := by
    intro x k
    rw [walk_N w1 w2 RD hU _ hz x k, hcol x k, bdry_N_iff, hmem (x - 1) k, hmem x k]
    exact RegionArith.ArcData.north_iff D x k
  have S_eq : ∀ x k : ℤ, ((x, k + 1), (x, k)) ∈ edgesFrom (0, 0) (boundaryWordOf w1 w2) ↔
      ((x, k + 1), (x, k)) ∈ T.boundaryEdges := by
    intro x k
    rw [walk_S w1 w2 RD hU _ hz x k, hcol _ _, bdry_S_iff, hmem x k, hmem (x - 1) k]
    exact RegionArith.ArcData.south_iff D x k
  -- the walk is nodup: the two halves are nodup, and no edge of the first half has its half-turn in the first half
  have hinj : Function.Injective (halfE (F2Word.sum (w1 ++ w2))) := by
    intro a b hab
    have := congrArg (halfE (F2Word.sum (w1 ++ w2))) hab
    rwa [halfE_halfE, halfE_halfE] at this
  have hnd : (edgesFrom (0, 0) (boundaryWordOf w1 w2)).Nodup := by
    rw [walk_split, List.nodup_append]
    refine ⟨RD.nodup, RD.nodup.map hinj, ?_⟩
    intro a ha b hb hab
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hb
    exact no_cross w1 w2 RD hU _ hz D a ha (by rw [hab, halfE_halfE]; exact hf)
  -- the boundary edges of the region are the edges of the walk
  have hset : ((F2Word.walk (0, 0) (boundaryWordOf w1 w2)).zip
      (F2Word.walk (0, 0) (boundaryWordOf w1 w2)).tail).toFinset = T.boundaryEdges := by
    rw [zip_walk_eq]
    ext e
    rw [List.mem_toFinset]
    constructor
    · intro he
      rcases walk_shape w1 w2 hU _ hz e he with ⟨q, k, rfl⟩ | ⟨q, k, rfl⟩ | ⟨x, k, rfl⟩ | ⟨x, k, rfl⟩
      · exact (E_eq q k).1 he
      · exact (W_eq q k).1 he
      · exact (N_eq x k).1 he
      · exact (S_eq x k).1 he
    · intro he
      rcases bdry_shape T e he with ⟨q, k, rfl⟩ | ⟨q, k, rfl⟩ | ⟨x, k, rfl⟩ | ⟨x, k, rfl⟩
      · exact (E_eq q k).2 he
      · exact (W_eq q k).2 he
      · exact (N_eq x k).2 he
      · exact (S_eq x k).2 he
  -- the lower-left vertex is `(0, 0)`
  have hF00 : 1 ≤ FF (w1 ++ w2) 0 := by
    rw [FF_eq_colN _ _ le_rfl (by omega)]
    by_cases hn1 : 0 < cntI w1
    · rw [arc_F_lo w1 w2 h1 0 le_rfl hn1]
      exact colN_head_one w1 h1 hhead
    · rw [arc_F_hi w1 w2 h1 0 (by omega)]
      have := arc_colN_ge_sum w2 h2 (0 - cntI w1)
      omega
  have hlow : ∀ a b : ℤ, ((a, b) : GInt) ∈ T → 0 ≤ b ∧ (b = 0 → 0 ≤ a) := by
    intro a b hab
    obtain ⟨h0, -, h2', -⟩ := (hmem a b).1 hab
    refine ⟨h0, fun hb0 => ?_⟩
    subst hb0
    simp only [sub_zero] at h2'
    rw [hF1] at h2'
    omega
  have h00 : ((0, 0) : GInt) ∈ T :=
    (hmem 0 0).2 ⟨le_rfl, by omega, by simp [hF1], by omega⟩
  have hLL : IsLowerLeft T (0, 0) := by
    refine ⟨?_, ?_⟩
    · unfold CellTile.vertices
      exact Finset.mem_biUnion.2 ⟨(0, 0), h00, by simp [cellCorners]⟩
    · intro v hv
      unfold CellTile.vertices at hv
      obtain ⟨⟨a, b⟩, hab, hv⟩ := Finset.mem_biUnion.1 hv
      obtain ⟨hb0, hbz⟩ := hlow a b hab
      simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      all_goals
        try dsimp only
        try simp only [gOne, gI, Prod.fst_add, Prod.snd_add]
        refine ⟨by omega, fun h => ?_⟩
        have := hbz (by omega)
        omega
  exact ⟨hLL, sum_boundaryWordOf w1 w2, by rw [zip_walk_eq]; exact hnd, hset⟩

end FLatticePaper.Tiles.RegionBoundary
