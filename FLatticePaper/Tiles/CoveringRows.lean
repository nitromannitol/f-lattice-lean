import FLatticePaper.Tiles.NeighbourDisjoint
import FLatticePaper.Tiles.AlmostTilingCover
import FLatticePaper.Tiles.EdgeClause

/-! Covering of the lattice points by the vertices of the translates of a tile, row by row. A point is covered when it is a
vertex of a translate `T + u`, `u` in the lattice. The covered points of a row are closed under moving one step to the
right, provided the right end of every row of the tile has a covered successor (`SuccCover`, the one combinatorial
input still to be proved). The row is periodic under the horizontal lattice vector `(D, 0)`, `D = r P - (q+1)(X2-1) ≥ 1`,
and nonempty. Hence every lattice point is covered. -/

namespace FLatticePaper.Tiles

/-- A lattice point is covered: it is a vertex of some translate `T + u`, `u` in the lattice `L`. -/
def Cov (T : CellTile) (L : Set GInt) (x : GInt) : Prop :=
  ∃ u ∈ L, x - u ∈ T.vertices

/-- The right ends of the rows of the tile have covered successors (the bottom and the top corner of each row end). -/
def SuccCover (c : GInt) (w1 w2 : F2Word) (T : CellTile) (L : Set GInt) : Prop :=
  ∀ t : ℤ, 0 ≤ t → t < cntI w1 + cntI w2 →
    Cov T L (Nrow c w1 w2 t + 1, c.2 + t) ∧ Cov T L (Nrow c w1 w2 t + 1, c.2 + t + 1)

theorem latticeOf_add {v₁ v₂ a b : GInt} (ha : a ∈ latticeOf v₁ v₂) (hb : b ∈ latticeOf v₁ v₂) :
    a + b ∈ latticeOf v₁ v₂ := by
  obtain ⟨k, k', rfl⟩ := ha
  obtain ⟨m, m', rfl⟩ := hb
  exact ⟨k + m, k' + m', by ext <;> simp <;> ring⟩

theorem latticeOf_zero (v₁ v₂ : GInt) : (0 : GInt) ∈ latticeOf v₁ v₂ := ⟨0, 0, by ext <;> simp⟩

/-- The sum of a word with letters `1` and `i` has nonnegative first coordinate; with letters `i` and `-1` it is
nonpositive. -/
theorem sum_fst_nonpos (u : F2Word) (hu : ∀ x ∈ u, x = .i ∨ x = .negOne) : (F2Word.sum u).1 ≤ 0 := by
  induction u with
  | nil => simp [F2Word.sum]
  | cons x u ih =>
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .i ∨ y = .negOne := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    have hs : F2Word.sum (x :: u) = x.vec + F2Word.sum u := by simp [F2Word.sum]
    rw [hs, Prod.fst_add]
    rcases hx with rfl | rfl <;> simp [Unit4.vec] <;> linarith [ih hu']

/-- The north steps of a word without south steps: the step starting in row `b` is an edge of the walk from `p`. -/
theorem north_edge_walk (u : F2Word) (hu : ∀ x ∈ u, x ≠ .negI) :
    ∀ (p : GInt) (b : ℤ), p.2 ≤ b → b < p.2 + cntI u →
      ((colN u p b, b), (colN u p b, b + 1)) ∈ edgesFrom p u := by
  induction u with
  | nil => intro p b h1 h2; simp [cntI] at h2; omega
  | cons x u ih =>
    have hx : x ≠ .negI := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y ≠ .negI := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    intro p b h1 h2
    have hn := cntI_nonneg u
    cases x with
    | negI => exact absurd rfl hx
    | one =>
      have hc : cntI (Unit4.one :: u) = cntI u := by simp [cntI]
      rw [hc] at h2
      have hp : (p + Unit4.vec .one).2 = p.2 := by simp [Unit4.vec]
      have := ih hu' (p + Unit4.vec .one) b (by rw [hp]; exact h1) (by rw [hp]; exact h2)
      simp only [colN, edgesFrom]
      rw [if_neg (by simp)]
      exact List.mem_cons_of_mem _ this
    | negOne =>
      have hc : cntI (Unit4.negOne :: u) = cntI u := by simp [cntI]
      rw [hc] at h2
      have hp : (p + Unit4.vec .negOne).2 = p.2 := by simp [Unit4.vec]
      have := ih hu' (p + Unit4.vec .negOne) b (by rw [hp]; exact h1) (by rw [hp]; exact h2)
      simp only [colN, edgesFrom]
      rw [if_neg (by simp)]
      exact List.mem_cons_of_mem _ this
    | i =>
      have hc : cntI (Unit4.i :: u) = 1 + cntI u := by simp [cntI]
      rw [hc] at h2
      by_cases hpb : p.2 = b
      · have hcol : colN (Unit4.i :: u) p b = p.1 := by simp [colN, hpb]
        rw [hcol]
        have e : ((p.1, b), (p.1, b + 1)) = (p, p + Unit4.vec .i) := by
          simp [Prod.ext_iff, Unit4.vec, hpb]
        rw [e, edgesFrom]
        exact List.mem_cons_self
      · have hlt : p.2 < b := lt_of_le_of_ne h1 hpb
        have hp : (p + Unit4.vec .i).2 = p.2 + 1 := by simp [Unit4.vec]
        have := ih hu' (p + Unit4.vec .i) b (by rw [hp]; omega) (by rw [hp]; omega)
        simp only [colN, edgesFrom]
        rw [if_neg (fun h => hpb h.2)]
        exact List.mem_cons_of_mem _ this

theorem vert_of_mem_cell {T : CellTile} {y z : GInt} (hy : y ∈ T) (hz : z ∈ cellCorners y) :
    z ∈ T.vertices :=
  Finset.mem_biUnion.mpr ⟨y, hy, hz⟩

theorem cov_of_vertex {T : CellTile} {L : Set GInt} (hL : (0 : GInt) ∈ L) {x : GInt} (hx : x ∈ T.vertices) :
    Cov T L x :=
  ⟨0, hL, by simpa using hx⟩

/-- The rows of the tile are nonempty: the north step of each row is a boundary edge, so the cell left of it is in the
tile. -/
theorem rows_nonempty {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (t : ℤ) (ht0 : 0 ≤ t) (ht1 : t < cntI w1 + cntI w2) :
    Srow c w1 w2 t < Nrow c w1 w2 t := by
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by
    rcases h1 x hx with h | h <;> simp [h]
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by
    rcases h2 x hx with h | h <;> simp [h]
  have hnoNeg : ∀ x ∈ w1 ++ w2, x ≠ .negI := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hn1 x hx
    · exact hn2 x hx
  have hedge := north_edge_walk (w1 ++ w2) hnoNeg c (c.2 + t) (by omega)
    (by rw [cntI_append]; omega)
  have hword : boundaryWordOf w1 w2 = (w1 ++ w2) ++ (w1.map Unit4.neg ++ w2.map Unit4.neg) := by
    simp [boundaryWordOf, hat_rev, List.append_assoc]
  have hset := hT.2.2.2
  have hmem : ((colN (w1 ++ w2) c (c.2 + t), c.2 + t), (colN (w1 ++ w2) c (c.2 + t), c.2 + t + 1))
      ∈ T.boundaryEdges := by
    rw [← hset, zip_walk_eq, hword, edgesFrom_append]
    exact List.mem_toFinset.mpr (List.mem_append_left _ hedge)
  have hcol := N_eq c w1 w2 hn1 (c.2 + t) (by omega)
  rw [add_sub_cancel_left] at hcol
  have hnm := (north_mem T _ _).mp hmem
  obtain ⟨hcell, -⟩ := hnm
  have hc := (mem_iff_nr hT h1 h2 _ _).mp hcell
  rw [show c.2 + t - c.2 = t by ring] at hc
  obtain ⟨-, hS, hN⟩ := hc
  rw [← hcol] at *
  omega

/-- The successor of a vertex of the tile is covered: either it is again a vertex of the tile, or the vertex is the right
end of a row of the tile, and the successor of a right end is covered by `SuccCover`. -/
theorem succ_cov {T : CellTile} {c : GInt} {w1 w2 : F2Word} {L : Set GInt}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hL : (0 : GInt) ∈ L) (hS : SuccCover c w1 w2 T L) {z : GInt} (hz : z ∈ T.vertices) :
    Cov T L (z + gOne) := by
  rw [CellTile.vertices, Finset.mem_biUnion] at hz
  obtain ⟨⟨a0, b0⟩, hy0, hzc⟩ := hz
  have hm0 := (mem_iff_nr hT h1 h2 a0 b0).mp hy0
  obtain ⟨⟨hr0, hr1⟩, hS0, hN0⟩ := hm0
  have hb0 : c.2 + (b0 - c.2) = b0 := by ring
  have hright : ¬ ((a0 + 1, b0) : GInt) ∈ T → Nrow c w1 w2 (b0 - c.2) = a0 + 1 := by
    intro hn
    rw [mem_iff_nr hT h1 h2] at hn
    by_contra hne
    exact hn ⟨⟨hr0, hr1⟩, by omega, by omega⟩
  simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton] at hzc
  rcases hzc with rfl | rfl | rfl | rfl
  · -- z = y0
    apply cov_of_vertex hL
    apply vert_of_mem_cell hy0
    simp [cellCorners, gOne]
  · -- z = y0 + (1,0)
    by_cases hc : ((a0 + 1, b0) : GInt) ∈ T
    · apply cov_of_vertex hL
      apply vert_of_mem_cell hc
      simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton]
      right; left
      ext <;> simp [gOne]
    · have hR := hright hc
      have hw := (hS (b0 - c.2) hr0 hr1).1
      rw [hb0, hR] at hw
      have e : ((a0, b0) + gOne + gOne : GInt) = (a0 + 1 + 1, b0) := by
        ext <;> simp [gOne]
      rw [e]
      exact hw
  · -- z = y0 + (0,1)
    apply cov_of_vertex hL
    apply vert_of_mem_cell hy0
    simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton]
    right; right; right
    ext <;> simp [gOne, gI]
  · -- z = y0 + (1,1)
    by_cases hc : ((a0 + 1, b0) : GInt) ∈ T
    · apply cov_of_vertex hL
      apply vert_of_mem_cell hc
      simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton]
      right; right; right
      ext <;> simp [gOne, gI]
    · have hR := hright hc
      have hw := (hS (b0 - c.2) hr0 hr1).2
      rw [hb0, hR] at hw
      have e : ((a0, b0) + (gOne + gI) + gOne : GInt) = (a0 + 1 + 1, b0 + 1) := by
        ext <;> simp [gOne, gI]
      rw [e]
      exact hw

/-- Covered points are closed under the successor. -/
theorem cov_succ {T : CellTile} {c : GInt} {w1 w2 : F2Word} {L : Set GInt}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hL : (0 : GInt) ∈ L) (hLadd : ∀ a b : GInt, a ∈ L → b ∈ L → a + b ∈ L)
    (hS : SuccCover c w1 w2 T L) {x : GInt} (hx : Cov T L x) : Cov T L (x + gOne) := by
  obtain ⟨u, hu, hxu⟩ := hx
  obtain ⟨u', hu', h'⟩ := succ_cov hT h1 h2 hL hS hxu
  refine ⟨u + u', hLadd u u' hu hu', ?_⟩
  convert h' using 1
  abel

/-- Covered points are invariant under the lattice. -/
theorem cov_lattice {T : CellTile} {L : Set GInt} (hLadd : ∀ a b : GInt, a ∈ L → b ∈ L → a + b ∈ L)
    {x ℓ : GInt} (hx : Cov T L x) (hℓ : ℓ ∈ L) : Cov T L (x + ℓ) := by
  obtain ⟨u, hu, h⟩ := hx
  refine ⟨u + ℓ, hLadd u ℓ hu hℓ, ?_⟩
  convert h using 1
  abel

/-- The horizontal period of the lattice: `D = r P - (q+1)(X2-1)` where `P`, `X2` are the first coordinate sums of
`w1`, `w2`, and `q`, `r` the numbers of north steps. -/
def coverD (w1 w2 : F2Word) : ℤ := cntI w2 * (F2Word.sum w1).1 - (cntI w1 + 1) * ((F2Word.sum w2).1 - 1)

theorem coverD_pos {w1 w2 : F2Word} (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) :
    1 ≤ coverD w1 w2 := by
  have hP := sum_fst_nonneg w1 h1
  have hX := sum_fst_nonpos w2 h2
  have hr := cntI_nonneg w2
  have hq := cntI_nonneg w1
  unfold coverD
  nlinarith

theorem lattice_coverD_mem {w1 w2 : F2Word} (hn1 : ∀ x ∈ w1, x ≠ .negI) (hn2 : ∀ x ∈ w2, x ≠ .negI) (k : ℤ) :
    ((k * coverD w1 w2, 0) : GInt) ∈ latticeOf (almostV₁ w1) (almostV₂ w2) := by
  rw [almostV₁_eq w1 hn1, almostV₂_eq w2 hn2]
  refine ⟨k * cntI w2, -(k * (cntI w1 + 1)), ?_⟩
  unfold coverD
  ext <;> simp <;> ring

theorem lattice_g2_mul {w1 w2 : F2Word} (hn1 : ∀ x ∈ w1, x ≠ .negI) (hn2 : ∀ x ∈ w2, x ≠ .negI) (k : ℤ) :
    ((k * ((F2Word.sum w2).1 - 1), k * cntI w2) : GInt) ∈ latticeOf (almostV₁ w1) (almostV₂ w2) := by
  rw [almostV₁_eq w1 hn1, almostV₂_eq w2 hn2]
  exact ⟨0, k, by ext <;> simp⟩

/-- Every row of lattice points has a covered point. -/
theorem cov_row_nonempty {T : CellTile} {c : GInt} {w1 w2 : F2Word} {L : Set GInt}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hr : 1 ≤ cntI w2) (hL : L = latticeOf (almostV₁ w1) (almostV₂ w2)) (y : ℤ) :
    ∃ a : ℤ, Cov T L (a, y) := by
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by
    rcases h1 x hx with h | h <;> simp [h]
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by
    rcases h2 x hx with h | h <;> simp [h]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = (y - c.2) / cntI w2 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = (y - c.2) - k * cntI w2 := ⟨_, rfl⟩
  have htdef : t = (y - c.2) % cntI w2 := by
    rw [ht, hk, Int.emod_def]
    ring
  have ht0 : 0 ≤ t := by rw [htdef]; exact Int.emod_nonneg _ (by omega)
  have ht1 : t < cntI w2 := by rw [htdef]; exact Int.emod_lt_of_pos _ (by omega)
  have ht2 : t < cntI w1 + cntI w2 := by have := cntI_nonneg w1; omega
  have hne := rows_nonempty hT h1 h2 t ht0 ht2
  have hzT : ((Srow c w1 w2 t, c.2 + t) : GInt) ∈ T := by
    rw [mem_iff_nr hT h1 h2, show c.2 + t - c.2 = t by ring]
    exact ⟨⟨ht0, ht2⟩, le_refl _, hne⟩
  have hzV : ((Srow c w1 w2 t, c.2 + t) : GInt) ∈ T.vertices :=
    vert_of_mem_cell hzT (by simp [cellCorners])
  refine ⟨Srow c w1 w2 t + k * ((F2Word.sum w2).1 - 1), ?_⟩
  refine ⟨(k * ((F2Word.sum w2).1 - 1), k * cntI w2), ?_, ?_⟩
  · rw [hL]
    exact lattice_g2_mul hn1 hn2 k
  · have e : ((Srow c w1 w2 t + k * ((F2Word.sum w2).1 - 1), y) - (k * ((F2Word.sum w2).1 - 1), k * cntI w2) : GInt)
        = (Srow c w1 w2 t, c.2 + t) := by
      ext
      · simp
      · simp only [Prod.snd_sub]
        rw [ht]
        ring
    rw [e]
    exact hzV

/-- Every lattice point is covered, given the successor condition: every row of lattice points is covered at one point,
covered points step to the right, and the row is periodic under the horizontal period. -/
theorem cov_all {T : CellTile} {c : GInt} {w1 w2 : F2Word} {L : Set GInt}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hr : 1 ≤ cntI w2) (hL : L = latticeOf (almostV₁ w1) (almostV₂ w2))
    (hS : SuccCover c w1 w2 T L) (a y : ℤ) : Cov T L (a, y) := by
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by
    rcases h1 x hx with h | h <;> simp [h]
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by
    rcases h2 x hx with h | h <;> simp [h]
  have hL0 : (0 : GInt) ∈ L := by rw [hL]; exact latticeOf_zero _ _
  have hLadd : ∀ a b : GInt, a ∈ L → b ∈ L → a + b ∈ L := fun a b ha hb => by
    rw [hL] at ha hb ⊢
    exact latticeOf_add ha hb
  obtain ⟨a0, ha0⟩ := cov_row_nonempty hT h1 h2 hr hL y
  have hsucc : ∀ n : ℕ, Cov T L (a0 + n, y) := by
    intro n
    induction n with
    | zero => simpa using ha0
    | succ n ih =>
      have hc := cov_succ hT h1 h2 hL0 hLadd hS ih
      have e : ((a0 + (n : ℤ), y) + gOne : GInt) = (a0 + ((n + 1 : ℕ) : ℤ), y) := by
        ext <;> simp [gOne]; ring
      rw [e] at hc
      exact hc
  have hD := coverD_pos h1 h2
  have hper : ∀ k : ℤ, ((k * coverD w1 w2, 0) : GInt) ∈ L := fun k => by
    rw [hL]
    exact lattice_coverD_mem hn1 hn2 k
  set D := coverD w1 w2 with hDdef
  set n : ℕ := (a0 - a).toNat with hn
  have hnn : (n : ℤ) ≥ a0 - a := by rw [hn]; omega
  have hnD : (n : ℤ) ≤ (n : ℤ) * D := by
    have : (0 : ℤ) ≤ n := by positivity
    nlinarith
  set m : ℕ := (a + (n : ℤ) * D - a0).toNat with hm
  have hmeq : a0 + (m : ℤ) = a + (n : ℤ) * D := by
    rw [hm]
    omega
  have h2' : Cov T L (a + (n : ℤ) * D, y) := by
    rw [← hmeq]
    exact hsucc m
  have h3 := cov_lattice hLadd h2' (hper (-(n : ℤ)))
  have e2 : ((a + (n : ℤ) * D, y) + ((-(n : ℤ)) * D, 0) : GInt) = (a, y) := by
    ext <;> simp
  rw [e2] at h3
  exact h3

/-- The covering clause of the almost tiling, from the successor condition. -/
theorem covering_clause_of_succ {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hr : 1 ≤ cntI w2)
    (hS : SuccCover c w1 w2 T (latticeOf (almostV₁ w1) (almostV₂ w2))) :
    ∀ x : GInt, ∃ v ∈ latticeOf (almostV₁ w1) (almostV₂ w2), ∃ y ∈ T, x ∈ cellCorners (y + v) := by
  rw [covering_iff_vertices]
  intro x
  obtain ⟨a, y⟩ := x
  exact cov_all hT h1 h2 hr rfl hS a y

end FLatticePaper.Tiles
