import FLatticePaper.Tiles.SubCriteria
import FLatticePaper.Tiles.CellIntervals
import FLatticePaper.Tiles.RowScan

/-! Task Q25 (completeness of the seam), the generic cover and nodup of a closed walk along the boundary of a cell tile
(`fixes/Q25.md`, "The cell boundary").

A directed boundary edge of the cell tile `T` is one of four kinds: east `(p, p+E)` (bottom side of the cell `p`), north `(p, p+N)`
(right side of the cell `p−E`), west `(p, p−E)` (top side of the cell `p−E−N`), south `(p, p−N)` (left side of the cell `p−N`).
The criteria are `east_mem_boundaryEdges_iff`, `north_mem_boundaryEdges_iff` (SubCriteria), `west_mem_boundaryEdges_iff` and
`south_mem_boundaryEdges_iff` below. If the cells of `T` form an interval in every column and every row, each line carries at most one
boundary edge of each kind. So a list `W` of boundary edges that meets every line of the box exactly once in each kind covers the
boundary and has no repeated edge (`cover_nodup_of`). -/

namespace FLatticePaper.Tiles.WalkCover

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause

/-- The west criterion: `(p, p − E)` is a boundary edge iff the cell `p − E − N` is in `T` and the cell `p − E` is not. -/
theorem west_mem_boundaryEdges_iff (T : CellTile) (p : GInt) :
    (p, p - gOne) ∈ T.boundaryEdges ↔ p - gOne - gI ∈ T ∧ p - gOne ∉ T := by
  rw [mem_boundaryEdges_iff]
  constructor
  · rintro ⟨c, hc, f, hf, hnot, he⟩
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exfalso
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, gOne] at h1 h2
      omega
    · exfalso
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, gOne, gI] at h1 h2
      omega
    · simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      have hc' : c = p - gOne - gI := by
        rw [← h1]
        abel
      rw [hc'] at hc
      refine ⟨hc, ?_⟩
      rw [← h2]
      exact hnot
    · exfalso
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, gOne, gI] at h1 h2
      omega
  · rintro ⟨hc, hnot⟩
    refine ⟨p - gOne - gI, hc, (p - gOne - gI + gOne + gI, p - gOne - gI + gI, p - gOne - gI + gI), ?_, ?_, ?_⟩
    · simp [cellEdgesWithOther]
    · have h3 : p - gOne - gI + gI = p - gOne := by abel
      rw [h3]
      exact hnot
    · have h4 : p - gOne - gI + gOne + gI = p := by abel
      have h3 : p - gOne - gI + gI = p - gOne := by abel
      rw [h4, h3]

/-- The south criterion: `(p, p − N)` is a boundary edge iff the cell `p − N` is in `T` and the cell `p − N − E` is not. -/
theorem south_mem_boundaryEdges_iff (T : CellTile) (p : GInt) :
    (p, p - gI) ∈ T.boundaryEdges ↔ p - gI ∈ T ∧ p - gI - gOne ∉ T := by
  rw [mem_boundaryEdges_iff]
  constructor
  · rintro ⟨c, hc, f, hf, hnot, he⟩
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exfalso
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, gOne, gI] at h1 h2
      omega
    · exfalso
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, gOne, gI] at h1 h2
      omega
    · exfalso
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, gOne, gI] at h1 h2
      omega
    · simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      have hc' : c = p - gI := h2
      rw [hc'] at hc
      refine ⟨hc, ?_⟩
      rw [hc'] at hnot
      exact hnot
  · rintro ⟨hc, hnot⟩
    refine ⟨p - gI, hc, (p - gI + gI, p - gI, p - gI - gOne), ?_, ?_, ?_⟩
    · simp [cellEdgesWithOther]
    · exact hnot
    · have h3 : p - gI + gI = p := by abel
      rw [h3]

/-! ### Shifts of a point by the unit steps -/

theorem sub_gI_pair (x y : ℤ) : ((x, y) : GInt) - gI = (x, y - 1) :=
  Prod.ext (by simp [gI]) (by simp [gI])

theorem add_gI_pair (x y : ℤ) : ((x, y) : GInt) + gI = (x, y + 1) :=
  Prod.ext (by simp [gI]) (by simp [gI])

theorem add_gOne_pair (x y : ℤ) : ((x, y) : GInt) + gOne = (x + 1, y) :=
  Prod.ext (by simp [gOne]) (by simp [gOne])

theorem sub_gOne_pair (x y : ℤ) : ((x, y) : GInt) - gOne = (x - 1, y) :=
  Prod.ext (by simp [gOne]) (by simp [gOne])

/-! ### Uniqueness of the sides of a cell per line (the interval property) -/

/-- Two bottom sides in one column coincide. -/
theorem uB (T : CellTile)
    (hcol : ∀ x y1 y2 y3 : ℤ, y1 ≤ y2 → y2 ≤ y3 → ((x, y1) : GInt) ∈ T → ((x, y3) : GInt) ∈ T → ((x, y2) : GInt) ∈ T)
    (p q : GInt) (hp : p ∈ T) (hp' : p - gI ∉ T) (hq : q ∈ T) (hq' : q - gI ∉ T) (hx : p.1 = q.1) : p = q := by
  obtain ⟨px, py⟩ := p
  obtain ⟨qx, qy⟩ := q
  simp only at hx
  subst hx
  rcases lt_trichotomy py qy with h | h | h
  · exfalso
    have hm := hcol px py (qy - 1) qy (by omega) (by omega) hp hq
    apply hq'
    rw [sub_gI_pair]
    exact hm
  · subst h
    rfl
  · exfalso
    have hm := hcol px qy (py - 1) py (by omega) (by omega) hq hp
    apply hp'
    rw [sub_gI_pair]
    exact hm

/-- Two top sides in one column coincide. -/
theorem uT (T : CellTile)
    (hcol : ∀ x y1 y2 y3 : ℤ, y1 ≤ y2 → y2 ≤ y3 → ((x, y1) : GInt) ∈ T → ((x, y3) : GInt) ∈ T → ((x, y2) : GInt) ∈ T)
    (p q : GInt) (hp : p ∈ T) (hp' : p + gI ∉ T) (hq : q ∈ T) (hq' : q + gI ∉ T) (hx : p.1 = q.1) : p = q := by
  obtain ⟨px, py⟩ := p
  obtain ⟨qx, qy⟩ := q
  simp only at hx
  subst hx
  rcases lt_trichotomy py qy with h | h | h
  · exfalso
    have hm := hcol px py (py + 1) qy (by omega) (by omega) hp hq
    apply hp'
    rw [add_gI_pair]
    exact hm
  · subst h
    rfl
  · exfalso
    have hm := hcol px qy (qy + 1) py (by omega) (by omega) hq hp
    apply hq'
    rw [add_gI_pair]
    exact hm

/-- Two right sides in one row coincide. -/
theorem uR (T : CellTile)
    (hrow : ∀ y x1 x2 x3 : ℤ, x1 ≤ x2 → x2 ≤ x3 → ((x1, y) : GInt) ∈ T → ((x3, y) : GInt) ∈ T → ((x2, y) : GInt) ∈ T)
    (p q : GInt) (hp : p ∈ T) (hp' : p + gOne ∉ T) (hq : q ∈ T) (hq' : q + gOne ∉ T) (hy : p.2 = q.2) : p = q := by
  obtain ⟨px, py⟩ := p
  obtain ⟨qx, qy⟩ := q
  simp only at hy
  subst hy
  rcases lt_trichotomy px qx with h | h | h
  · exfalso
    have hm := hrow py px (px + 1) qx (by omega) (by omega) hp hq
    apply hp'
    rw [add_gOne_pair]
    exact hm
  · subst h
    rfl
  · exfalso
    have hm := hrow py qx (qx + 1) px (by omega) (by omega) hq hp
    apply hq'
    rw [add_gOne_pair]
    exact hm

/-- Two left sides in one row coincide. -/
theorem uL (T : CellTile)
    (hrow : ∀ y x1 x2 x3 : ℤ, x1 ≤ x2 → x2 ≤ x3 → ((x1, y) : GInt) ∈ T → ((x3, y) : GInt) ∈ T → ((x2, y) : GInt) ∈ T)
    (p q : GInt) (hp : p ∈ T) (hp' : p - gOne ∉ T) (hq : q ∈ T) (hq' : q - gOne ∉ T) (hy : p.2 = q.2) : p = q := by
  obtain ⟨px, py⟩ := p
  obtain ⟨qx, qy⟩ := q
  simp only at hy
  subst hy
  rcases lt_trichotomy px qx with h | h | h
  · exfalso
    have hm := hrow py px (qx - 1) qx (by omega) (by omega) hp hq
    apply hq'
    rw [sub_gOne_pair]
    exact hm
  · subst h
    rfl
  · exfalso
    have hm := hrow py qx (px - 1) px (by omega) (by omega) hq hp
    apply hp'
    rw [sub_gOne_pair]
    exact hm

/-! ### The four kinds of boundary edges -/

/-- Every directed boundary edge is east, north, west or south. -/
theorem boundary_type (T : CellTile) (g : GInt × GInt) (h : g ∈ T.boundaryEdges) :
    g.2 = g.1 + gOne ∨ g.2 = g.1 + gI ∨ g.2 = g.1 - gOne ∨ g.2 = g.1 - gI := by
  rw [mem_boundaryEdges_iff] at h
  obtain ⟨c, hc, f, hf, hnot, hfe⟩ := h
  simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · left
    subst hfe
    simp
  · right; left
    subst hfe
    simp
  · right; right; left
    subst hfe
    simp only
    abel
  · right; right; right
    subst hfe
    simp only
    abel

/-- The number of edges of `W` that are east steps in the column `x`. -/
def cntE (W : List (GInt × GInt)) (x : ℤ) : ℕ :=
  W.countP fun g => decide (g.2 = g.1 + gOne) && decide (g.1.1 = x)

/-- The number of edges of `W` that are west steps in the column `x` (their end column). -/
def cntW (W : List (GInt × GInt)) (x : ℤ) : ℕ :=
  W.countP fun g => decide (g.2 = g.1 - gOne) && decide (g.2.1 = x)

/-- The number of edges of `W` that are north steps in the row `y`. -/
def cntN (W : List (GInt × GInt)) (y : ℤ) : ℕ :=
  W.countP fun g => decide (g.2 = g.1 + gI) && decide (g.1.2 = y)

/-- The number of edges of `W` that are south steps in the row `y` (their end row). -/
def cntS (W : List (GInt × GInt)) (y : ℤ) : ℕ :=
  W.countP fun g => decide (g.2 = g.1 - gI) && decide (g.2.2 = y)

/-- The count of an edge is at most the count of a predicate it satisfies. -/
theorem count_le_countP (W : List (GInt × GInt)) (g : GInt × GInt) (P : GInt × GInt → Bool) (hg : P g = true) :
    W.count g ≤ W.countP P := by
  unfold List.count
  apply List.countP_mono_left
  intro x _ hx
  rw [beq_iff_eq] at hx
  subst hx
  exact hg

/-- A positive count gives an element satisfying the predicate. -/
theorem exists_of_countP_pos (W : List (GInt × GInt)) (P : GInt × GInt → Bool) (h : 0 < W.countP P) :
    ∃ g ∈ W, P g = true := by
  induction W with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : P x = true
    · exact ⟨x, by simp, hx⟩
    · have hxs : 0 < xs.countP P := by
        simpa [List.countP_cons, hx] using h
      obtain ⟨g, hg, hPg⟩ := ih hxs
      exact ⟨g, by simp [hg], hPg⟩

/-- **Cover and nodup from the lines.** If the cells of `T` form intervals in the columns and the rows, `T` lies in the box
`[a, b] × [r0, r1]`, and the list `W` of boundary edges meets each column of `[a, b]` once in each of the east and west kinds, and
each row of `[r0, r1]` once in each of the north and south kinds (and at most once everywhere), then `W` covers the boundary of `T`
and has no repeated edge. -/
theorem cover_nodup_of (T : CellTile) (W : List (GInt × GInt)) (a b r0 r1 : ℤ)
    (hcol : ∀ x y1 y2 y3 : ℤ, y1 ≤ y2 → y2 ≤ y3 → ((x, y1) : GInt) ∈ T → ((x, y3) : GInt) ∈ T → ((x, y2) : GInt) ∈ T)
    (hrow : ∀ y x1 x2 x3 : ℤ, x1 ≤ x2 → x2 ≤ x3 → ((x1, y) : GInt) ∈ T → ((x3, y) : GInt) ∈ T → ((x2, y) : GInt) ∈ T)
    (hbox : ∀ p : GInt, p ∈ T → a ≤ p.1 ∧ p.1 ≤ b ∧ r0 ≤ p.2 ∧ p.2 ≤ r1)
    (hsub : ∀ g ∈ W, g ∈ T.boundaryEdges)
    (hE1 : ∀ x, cntE W x ≤ 1) (hE2 : ∀ x, a ≤ x → x ≤ b → 1 ≤ cntE W x)
    (hW1 : ∀ x, cntW W x ≤ 1) (hW2 : ∀ x, a ≤ x → x ≤ b → 1 ≤ cntW W x)
    (hN1 : ∀ y, cntN W y ≤ 1) (hN2 : ∀ y, r0 ≤ y → y ≤ r1 → 1 ≤ cntN W y)
    (hS1 : ∀ y, cntS W y ≤ 1) (hS2 : ∀ y, r0 ≤ y → y ≤ r1 → 1 ≤ cntS W y) :
    (∀ e ∈ T.boundaryEdges, e ∈ W) ∧ W.Nodup := by
  constructor
  · rintro ⟨p, q⟩ he
    rcases boundary_type T (p, q) he with hq | hq | hq | hq
    · -- east: the bottom side of the cell `p`
      have hq' : q = p + gOne := hq
      subst hq'
      have hcell := (SubCriteria.east_mem_boundaryEdges_iff T p).mp he
      obtain ⟨hx1, hx2, -, -⟩ := hbox p hcell.1
      obtain ⟨⟨g1, g2⟩, hgW, hgp⟩ := exists_of_countP_pos _ _ (lt_of_lt_of_le Nat.zero_lt_one (hE2 p.1 hx1 hx2))
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hgp
      obtain ⟨hgE, hgx⟩ := hgp
      subst hgE
      have hg1 := (SubCriteria.east_mem_boundaryEdges_iff T g1).mp (hsub _ hgW)
      have heq : g1 = p := uB T hcol g1 p hg1.1 hg1.2 hcell.1 hcell.2 hgx
      subst heq
      exact hgW
    · -- north: the right side of the cell `p − E`
      have hq' : q = p + gI := hq
      subst hq'
      have hcell := (SubCriteria.north_mem_boundaryEdges_iff T p).mp he
      have hy1 := hbox (p - gOne) hcell.1
      have hpy : (p - gOne).2 = p.2 := by simp [gOne]
      obtain ⟨⟨g1, g2⟩, hgW, hgp⟩ := exists_of_countP_pos _ _ (lt_of_lt_of_le Nat.zero_lt_one (hN2 p.2 (by omega) (by omega)))
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hgp
      obtain ⟨hgE, hgy⟩ := hgp
      subst hgE
      have hg1 := (SubCriteria.north_mem_boundaryEdges_iff T g1).mp (hsub _ hgW)
      have hc : g1 - gOne = p - gOne := by
        apply uR T hrow (g1 - gOne) (p - gOne) hg1.1 (by rw [sub_add_cancel]; exact hg1.2) hcell.1
          (by rw [sub_add_cancel]; exact hcell.2)
        rw [hpy]
        simp [gOne] at hgy ⊢
        exact hgy
      have heq : g1 = p := sub_left_inj.mp hc
      subst heq
      exact hgW
    · -- west: the top side of the cell `p − E − N`
      have hq' : q = p - gOne := hq
      subst hq'
      have hcell := (west_mem_boundaryEdges_iff T p).mp he
      obtain ⟨hx1, hx2, -, -⟩ := hbox (p - gOne - gI) hcell.1
      have hpx : (p - gOne - gI).1 = p.1 - 1 := by simp [gOne, gI]
      obtain ⟨⟨g1, g2⟩, hgW, hgp⟩ :=
        exists_of_countP_pos _ _ (lt_of_lt_of_le Nat.zero_lt_one (hW2 (p.1 - 1) (by omega) (by omega)))
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hgp
      obtain ⟨hgE, hgx⟩ := hgp
      subst hgE
      have hg1 := (west_mem_boundaryEdges_iff T g1).mp (hsub _ hgW)
      have hcol' : (g1 - gOne - gI).1 = (p - gOne - gI).1 := by
        rw [hpx]
        simp [gOne, gI] at hgx ⊢
        omega
      have hc : g1 - gOne - gI = p - gOne - gI := by
        apply uT T hcol (g1 - gOne - gI) (p - gOne - gI) hg1.1
          (by rw [sub_add_cancel]; exact hg1.2) hcell.1
          (by rw [sub_add_cancel]; exact hcell.2) hcol'
      have heq : g1 = p := sub_left_inj.mp (sub_left_inj.mp hc)
      subst heq
      exact hgW
    · -- south: the left side of the cell `p − N`
      have hq' : q = p - gI := hq
      subst hq'
      have hcell := (south_mem_boundaryEdges_iff T p).mp he
      obtain ⟨hx1, hx2, hy1, hy2⟩ := hbox (p - gI) hcell.1
      have hpy : (p - gI).2 = p.2 - 1 := by simp [gI]
      obtain ⟨⟨g1, g2⟩, hgW, hgp⟩ :=
        exists_of_countP_pos _ _ (lt_of_lt_of_le Nat.zero_lt_one (hS2 (p.2 - 1) (by omega) (by omega)))
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hgp
      obtain ⟨hgE, hgy⟩ := hgp
      subst hgE
      have hg1 := (south_mem_boundaryEdges_iff T g1).mp (hsub _ hgW)
      have hrow' : (g1 - gI).2 = (p - gI).2 := by
        rw [hpy]
        simp [gI] at hgy ⊢
        omega
      have hc : g1 - gI = p - gI := by
        apply uL T hrow (g1 - gI) (p - gI) hg1.1 hg1.2 hcell.1 hcell.2 hrow'
      have heq : g1 = p := sub_left_inj.mp hc
      subst heq
      exact hgW
  · rw [List.nodup_iff_count_le_one]
    intro g
    by_cases hg : g ∈ W
    · rcases g with ⟨g1, g2⟩
      rcases boundary_type T (g1, g2) (hsub _ hg) with h | h | h | h
      · have h' : g2 = g1 + gOne := h
        have hP : (fun g : GInt × GInt => decide (g.2 = g.1 + gOne) && decide (g.1.1 = g1.1)) (g1, g2) = true := by
          simp [h']
        exact le_trans (count_le_countP W (g1, g2) _ hP) (hE1 g1.1)
      · have h' : g2 = g1 + gI := h
        have hP : (fun g : GInt × GInt => decide (g.2 = g.1 + gI) && decide (g.1.2 = g1.2)) (g1, g2) = true := by
          simp [h']
        exact le_trans (count_le_countP W (g1, g2) _ hP) (hN1 g1.2)
      · have h' : g2 = g1 - gOne := h
        have hP : (fun g : GInt × GInt => decide (g.2 = g.1 - gOne) && decide (g.2.1 = g2.1)) (g1, g2) = true := by
          simp [h']
        exact le_trans (count_le_countP W (g1, g2) _ hP) (hW1 g2.1)
      · have h' : g2 = g1 - gI := h
        have hP : (fun g : GInt × GInt => decide (g.2 = g.1 - gI) && decide (g.2.2 = g2.2)) (g1, g2) = true := by
          simp [h']
        exact le_trans (count_le_countP W (g1, g2) _ hP) (hS1 g2.2)
    · rw [List.count_eq_zero.mpr hg]
      exact Nat.zero_le _

end FLatticePaper.Tiles.WalkCover
