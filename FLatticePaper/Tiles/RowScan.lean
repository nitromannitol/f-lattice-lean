import FLatticePaper.Tiles.AlmostTiling
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Row scan of a tile (the discrete form of the Jordan curve theorem used in Section 4). A cell `(a, b)` of a tile `T`
lies in `T` exactly when the signed count of the vertical boundary edges of `T` in row `b`, at columns up to `a`, is
`-1`. A north edge counts `+1` and a south edge `-1`: the boundary is traversed counterclockwise with the cell on the
left, so a south edge is the left side of a cell of `T`. -/

namespace FLatticePaper.Tiles

/-- The signed contribution of the directed edge `e` to row `b`, counting columns up to `a`. -/
def vsgn (b a : ℤ) (e : GInt × GInt) : ℤ :=
  if e.1.1 = e.2.1 ∧ e.1.1 ≤ a ∧ e.1.2 = b ∧ e.2.2 = b + 1 then 1
  else if e.1.1 = e.2.1 ∧ e.1.1 ≤ a ∧ e.1.2 = b + 1 ∧ e.2.2 = b then -1
  else 0

/-- The signed count of an edge set in row `b`, at columns up to `a`. -/
def rowCount (E : Finset (GInt × GInt)) (b a : ℤ) : ℤ := ∑ e ∈ E, vsgn b a e

/-- The indicator of the cell `(a, b)` in `T`. -/
def cellInd (T : CellTile) (a b : ℤ) : ℤ := if ((a, b) : GInt) ∈ T then 1 else 0

/-- Advancing the column changes the contribution of an edge only at the two edges of column `a` in row `b`. -/
theorem vsgn_sub_pointwise (b a : ℤ) (e : GInt × GInt) :
    vsgn b a e - vsgn b (a - 1) e =
      (if e = ((a, b), (a, b + 1)) then 1 else 0) - (if e = ((a, b + 1), (a, b)) then 1 else 0) := by
  obtain ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩ := e
  simp only [vsgn, Prod.mk.injEq]
  split_ifs <;> omega

/-- The step of the scan: the count at column `a` minus the count at column `a - 1`. -/
theorem rowCount_sub (E : Finset (GInt × GInt)) (b a : ℤ) :
    rowCount E b a - rowCount E b (a - 1) =
      (if ((a, b), (a, b + 1)) ∈ E then 1 else 0) - (if ((a, b + 1), (a, b)) ∈ E then 1 else 0) := by
  unfold rowCount
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun e _ => vsgn_sub_pointwise b a e),
    Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq']

/-- Membership of a boundary edge: it is the edge of a cell of `T` whose other side is not in `T`. -/
theorem mem_boundaryEdges_iff (T : CellTile) (e : GInt × GInt) :
    e ∈ T.boundaryEdges ↔ ∃ c ∈ T, ∃ f ∈ cellEdgesWithOther c, f.2.2 ∉ T ∧ (f.1, f.2.1) = e := by
  unfold CellTile.boundaryEdges
  simp only [Finset.mem_biUnion, Finset.mem_image, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, f, ⟨hf, hnot⟩, hfe⟩
    exact ⟨c, hc, f, hf, hnot, hfe⟩
  · rintro ⟨c, hc, f, hf, hnot, hfe⟩
    exact ⟨c, hc, f, ⟨hf, hnot⟩, hfe⟩

/-- The north edge of the cell `(a, b)` is the right side of the cell `(a - 1, b)`. -/
theorem north_mem (T : CellTile) (a b : ℤ) :
    ((a, b), (a, b + 1)) ∈ T.boundaryEdges ↔ ((a - 1, b) : GInt) ∈ T ∧ ((a, b) : GInt) ∉ T := by
  rw [mem_boundaryEdges_iff]
  constructor
  · rintro ⟨c, hc, f, hf, hnot, hfe⟩
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exfalso
      simp [gOne, Prod.ext_iff] at hfe
      omega
    · have hc' : c = (a - 1, b) := by
        simp [gOne, gI, Prod.ext_iff] at hfe
        exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)
      subst hc'
      refine ⟨hc, ?_⟩
      have h1 : ((a - 1, b) : GInt) + gOne = (a, b) := by simp [gOne]
      rw [h1] at hnot
      exact hnot
    · exfalso
      simp [gOne, gI, Prod.ext_iff] at hfe
      omega
    · exfalso
      simp [gI, Prod.ext_iff] at hfe
      omega
  · rintro ⟨hc, hnot⟩
    refine ⟨(a - 1, b), hc, ((a - 1, b) + gOne, (a - 1, b) + gOne + gI, (a - 1, b) + gOne), ?_, ?_, ?_⟩
    · simp [cellEdgesWithOther]
    · have h1 : ((a - 1, b) : GInt) + gOne = (a, b) := by simp [gOne]
      rw [h1]
      exact hnot
    · simp [gOne, gI]

/-- The south edge of the cell `(a, b)` is its left side, with the cell `(a - 1, b)` on the other side. -/
theorem south_mem (T : CellTile) (a b : ℤ) :
    ((a, b + 1), (a, b)) ∈ T.boundaryEdges ↔ ((a, b) : GInt) ∈ T ∧ ((a - 1, b) : GInt) ∉ T := by
  rw [mem_boundaryEdges_iff]
  constructor
  · rintro ⟨c, hc, f, hf, hnot, hfe⟩
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exfalso
      simp [gOne, Prod.ext_iff] at hfe
      omega
    · exfalso
      simp [gOne, gI, Prod.ext_iff] at hfe
      omega
    · exfalso
      simp [gOne, gI, Prod.ext_iff] at hfe
      omega
    · have hc' : c = (a, b) := by
        simp [gI, Prod.ext_iff] at hfe
        exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)
      subst hc'
      refine ⟨hc, ?_⟩
      have h1 : ((a, b) : GInt) - gOne = (a - 1, b) := by simp [gOne]
      rw [h1] at hnot
      exact hnot
  · rintro ⟨hc, hnot⟩
    refine ⟨(a, b), hc, ((a, b) + gI, (a, b), (a, b) - gOne), ?_, ?_, ?_⟩
    · simp [cellEdgesWithOther]
    · have h1 : ((a, b) : GInt) - gOne = (a - 1, b) := by simp [gOne]
      rw [h1]
      exact hnot
    · simp [gI]

/-- Every lattice point of `T` has column at least `L`, so the boundary edges start at columns at least `L`. -/
theorem boundaryEdges_fst_ge {T : CellTile} {L : ℤ} (hL : ∀ x ∈ T, L ≤ x.1) {e : GInt × GInt}
    (he : e ∈ T.boundaryEdges) : L ≤ e.1.1 := by
  obtain ⟨c, hc, f, hf, -, rfl⟩ := (mem_boundaryEdges_iff T e).mp he
  have h1 := hL c hc
  simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> simp [gOne, gI] <;> omega

/-- A finite set of cells has a column lower bound. -/
theorem exists_lower (T : Finset GInt) : ∃ L : ℤ, ∀ x ∈ T, L ≤ x.1 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert x s hx ih =>
    obtain ⟨L, hL⟩ := ih
    refine ⟨min L x.1, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hL y hy')

/-- Left of every cell of `T`, the count is zero. -/
theorem rowCount_zero_of_low {T : CellTile} {L : ℤ} (hL : ∀ x ∈ T, L ≤ x.1) (b a : ℤ) (ha : a < L) :
    rowCount T.boundaryEdges b a = 0 := by
  unfold rowCount
  apply Finset.sum_eq_zero
  intro e he
  have := boundaryEdges_fst_ge hL he
  unfold vsgn
  split_ifs <;> omega

/-- The row count is `-1` exactly on the cells of `T`, from the first column onward (induction on the column). -/
theorem rowCount_eq {T : CellTile} {L : ℤ} (hL : ∀ x ∈ T, L ≤ x.1) (b : ℤ) (a : ℤ) (ha : L - 1 ≤ a) :
    rowCount T.boundaryEdges b a = -cellInd T a b := by
  induction a, ha using Int.leInduction with
  | base =>
    rw [rowCount_zero_of_low hL b (L - 1) (by omega)]
    have hout : ((L - 1, b) : GInt) ∉ T := fun h => by
      have := hL _ h
      dsimp only at this
      omega
    simp [cellInd, hout]
  | succ n hn ih =>
    have h := rowCount_sub T.boundaryEdges b (n + 1)
    rw [show n + 1 - 1 = n by ring, ih] at h
    simp only [north_mem, south_mem, add_sub_cancel_right] at h
    unfold cellInd at h ⊢
    by_cases hA : ((n, b) : GInt) ∈ T <;> by_cases hB : ((n + 1, b) : GInt) ∈ T <;>
      simp [hA, hB] at h ⊢ <;> omega

/-- The row scan: the cell `(a, b)` lies in `T` exactly when the signed count of the boundary in row `b` up to column
`a` is `-1`. This is the row-scan lemma of the tile layer. -/
theorem row_scan (T : CellTile) (b a : ℤ) : rowCount T.boundaryEdges b a = -cellInd T a b := by
  obtain ⟨L, hL⟩ := exists_lower T
  rcases le_or_gt (L - 1) a with h | h
  · exact rowCount_eq hL b a h
  · rw [rowCount_zero_of_low hL b a (by omega)]
    have hout : ((a, b) : GInt) ∉ T := fun hm => by
      have := hL _ hm
      dsimp only at this
      omega
    simp [cellInd, hout]

end FLatticePaper.Tiles
