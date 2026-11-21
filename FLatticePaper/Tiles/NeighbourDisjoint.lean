import FLatticePaper.Tiles.RowAdmiss

/-! Neighbour disjointness: no surrounding translate of a tile overlaps it. The rows of the tile are intervals `[S, N)`
(`mem_iff_interval`); the north and south ends of row `t` are `Nrow` and `Srow`, which are the walk columns of
`mem_iff_interval` read relative to the lower-left row `c.2`. The four vectors up to sign are excluded by row inequalities:
`g1` and `g2` by the two admissibility inequalities, `g1 - g2` and `g1 + g2` by the column bounds and the row count. -/

namespace FLatticePaper.Tiles

/-- The north end of row `t` of the tile (relative to the lower-left row `c.2`). -/
def Nrow (c : GInt) (w1 w2 : F2Word) (t : ℤ) : ℤ :=
  c.1 + (if t < cntI w1 then colN w1 (0, 0) t else (F2Word.sum w1).1 + colN w2 (0, 0) (t - cntI w1))

/-- The south end of row `t` of the tile (relative to the lower-left row `c.2`). -/
def Srow (c : GInt) (w1 w2 : F2Word) (t : ℤ) : ℤ :=
  c.1 + (if t < cntI w2 then (F2Word.sum w2).1 - colN w2 (0, 0) (cntI w2 - 1 - t)
    else (F2Word.sum (w1 ++ w2)).1 - colN w1 (0, 0) (cntI w1 + cntI w2 - 1 - t))

theorem sum_append_fst (u v : F2Word) : (F2Word.sum (u ++ v)).1 = (F2Word.sum u).1 + (F2Word.sum v).1 := by
  rw [sum_append', Prod.fst_add]

theorem sumMapNeg (u : F2Word) : F2Word.sum (u.map Unit4.neg) = -F2Word.sum u := by
  induction u with
  | nil => simp [F2Word.sum]
  | cons x u ih =>
    have e1 : F2Word.sum ((x :: u).map Unit4.neg) = (Unit4.neg x).vec + F2Word.sum (u.map Unit4.neg) := by
      simp [F2Word.sum]
    have e2 : F2Word.sum (x :: u) = x.vec + F2Word.sum u := by simp [F2Word.sum]
    rw [e1, e2, ih]
    cases x <;> simp [Unit4.neg, Unit4.vec] <;> abel

theorem sum_map_neg_fst (u : F2Word) : (F2Word.sum (u.map Unit4.neg)).1 = -(F2Word.sum u).1 := by
  rw [sumMapNeg, Prod.fst_neg]

theorem sum_map_neg_snd (u : F2Word) (hu : ∀ x ∈ u, x ≠ .negI) :
    (F2Word.sum (u.map Unit4.neg)).2 = -cntI u := by
  rw [sumMapNeg, Prod.snd_neg, sum_snd u hu]

/-- The north end of row `b`, from the walk of `w1 ++ w2` from `c`. -/
theorem N_eq (c : GInt) (w1 w2 : F2Word) (h1 : ∀ x ∈ w1, x ≠ .negI) (b : ℤ) (hb1 : c.2 ≤ b) :
    colN (w1 ++ w2) c b = Nrow c w1 w2 (b - c.2) := by
  unfold Nrow
  by_cases ht : b - c.2 < cntI w1
  · rw [if_pos ht, colN_lo w1 w2 h1 c b hb1 (by omega), colN_trans]
  · rw [if_neg ht, colN_hi w1 w2 h1 c b (by omega), colN_trans, Prod.fst_add, Prod.snd_add,
      sum_snd w1 h1, show b - (c.2 + cntI w1) = b - c.2 - cntI w1 by ring]
    ring

/-- The south end of row `b`, from the walk of `w1.map neg ++ w2.map neg` from `c + sum (w1 ++ w2)`. -/
theorem S_eq (c : GInt) (w1 w2 : F2Word) (h1 : ∀ x ∈ w1, x ≠ .negI) (h2 : ∀ x ∈ w2, x ≠ .negI) (b : ℤ)
    (hb2 : b < c.2 + (cntI w1 + cntI w2)) :
    colS (w1.map Unit4.neg ++ w2.map Unit4.neg) (c + F2Word.sum (w1 ++ w2)) b = Srow c w1 w2 (b - c.2) := by
  have hw1 : ∀ x ∈ w1.map Unit4.neg, x ≠ .i := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    intro hcontra
    apply h1 y hy
    cases y <;> simp_all [Unit4.neg]
  have hsnd : (c + F2Word.sum (w1 ++ w2)).2 = c.2 + (cntI w1 + cntI w2) := by
    rw [Prod.snd_add, sum_snd (w1 ++ w2) (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact h1 x hx
      · exact h2 x hx), cntI_append]
  have hneg1 : cntNegI (w1.map Unit4.neg) = cntI w1 := cntNegI_map_neg w1
  unfold Srow
  by_cases ht : b - c.2 < cntI w2
  · rw [if_pos ht]
    rw [colS_hi (w1.map Unit4.neg) (w2.map Unit4.neg) hw1 _ b (by rw [hsnd, hneg1]; omega), colS_trans,
      colS_map_neg]
    have hD1 : (c + F2Word.sum (w1 ++ w2) + F2Word.sum (w1.map Unit4.neg)).1 = c.1 + (F2Word.sum w2).1 := by
      rw [Prod.fst_add, Prod.fst_add, sum_append_fst, sum_map_neg_fst]
      ring
    have hD2 : (c + F2Word.sum (w1 ++ w2) + F2Word.sum (w1.map Unit4.neg)).2 = c.2 + cntI w2 := by
      rw [Prod.snd_add (c + F2Word.sum (w1 ++ w2)), hsnd, sum_map_neg_snd w1 h1]
      ring
    rw [hD1, hD2, show -(b - (c.2 + cntI w2)) - 1 = cntI w2 - 1 - (b - c.2) by ring]
    ring
  · rw [if_neg ht]
    rw [colS_lo (w1.map Unit4.neg) (w2.map Unit4.neg) hw1 _ b (by rw [hsnd, hneg1]; omega) (by rw [hsnd]; omega),
      colS_trans, colS_map_neg, hsnd, Prod.fst_add, sum_append_fst]
    rw [show -(b - (c.2 + (cntI w1 + cntI w2))) - 1 = cntI w1 + cntI w2 - 1 - (b - c.2) by ring]
    ring

/-- Membership in the tile, row by row: the row `b - c.2` lies in the range of the walk, and the cell `a` lies between
the south and north ends of the row. -/
theorem mem_iff_nr {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (a b : ℤ) :
    ((a, b) : GInt) ∈ T ↔
      (0 ≤ b - c.2 ∧ b - c.2 < cntI w1 + cntI w2) ∧ Srow c w1 w2 (b - c.2) ≤ a ∧ a < Nrow c w1 w2 (b - c.2) := by
  rw [mem_iff_interval hT h1 h2 a b, cntI_append]
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by
    rcases h1 x hx with h | h <;> simp [h]
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by
    rcases h2 x hx with h | h <;> simp [h]
  by_cases hr : c.2 ≤ b ∧ b < c.2 + (cntI w1 + cntI w2)
  · rw [N_eq c w1 w2 hn1 b hr.1, S_eq c w1 w2 hn1 hn2 b hr.2]
    exact ⟨fun h => ⟨⟨by omega, by omega⟩, h.2⟩, fun h => ⟨⟨by omega, by omega⟩, h.2⟩⟩
  · constructor
    · rintro ⟨hr', -, -⟩
      exact absurd ⟨hr'.1, hr'.2⟩ hr
    · rintro ⟨hr', -, -⟩
      exact absurd ⟨by omega, by omega⟩ hr

theorem Nrow_le (c : GInt) (w1 w2 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i)
    (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (t : ℤ) :
    Nrow c w1 w2 t ≤ c.1 + (F2Word.sum w1).1 := by
  unfold Nrow
  split_ifs with ht
  · have := colN_le_sum w1 h1 t; linarith
  · have := colN_nonpos w2 h2 (t - cntI w1); linarith

theorem Srow_ge (c : GInt) (w1 w2 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i)
    (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (t : ℤ) :
    c.1 + (F2Word.sum w2).1 ≤ Srow c w1 w2 t := by
  unfold Srow
  split_ifs with ht
  · have := colN_nonpos w2 h2 (cntI w2 - 1 - t); linarith
  · have := colN_le_sum w1 h1 (cntI w1 + cntI w2 - 1 - t)
    rw [sum_append_fst] at *
    linarith

/-- The overlap of the tile with a translate: a common cell. -/
theorem not_overlap_of {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (n1 n2 : ℤ)
    (hdisj : ∀ t : ℤ, 0 ≤ t → t < cntI w1 + cntI w2 → 0 ≤ t - n2 → t - n2 < cntI w1 + cntI w2 →
      Nrow c w1 w2 t ≤ Srow c w1 w2 (t - n2) + n1 ∨ Nrow c w1 w2 (t - n2) + n1 ≤ Srow c w1 w2 t) :
    ¬ Overlap T (n1, n2) := by
  rintro ⟨⟨a, b⟩, hx, hxn⟩
  have hxn' : ((a - n1, b - n2) : GInt) ∈ T := by
    simpa using hxn
  rw [mem_iff_nr hT h1 h2] at hx hxn'
  obtain ⟨⟨hx0, hx1⟩, hxs, hxN⟩ := hx
  obtain ⟨⟨hy0, hy1⟩, hys, hyN⟩ := hxn'
  have hsh : b - n2 - c.2 = (b - c.2) - n2 := by ring
  rw [hsh] at hys hyN hy0 hy1
  rcases hdisj (b - c.2) hx0 hx1 hy0 hy1 with d | d <;> linarith

/-- The translate by `-u` overlaps the tile exactly when the translate by `u` does. -/
theorem overlap_neg_iff (T : CellTile) (u : GInt) : Overlap T (-u) ↔ Overlap T u := by
  constructor
  · rintro ⟨x, hx, hxu⟩
    exact ⟨x - -u, hxu, by simpa using hx⟩
  · rintro ⟨x, hx, hxu⟩
    exact ⟨x - u, hxu, by simpa using hx⟩

/-- The translate by `g1 = (P, q + 1)` does not overlap the tile: the row inequality of `L_g1`. -/
theorem disj_g1 {T : CellTile} {c : GInt} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hA2 : Admissible (w2.map Unit4.mulNegI)) (n1 n2 : ℤ)
    (e1 : n1 = (F2Word.sum w1).1) (e2 : n2 = cntI w1 + 1) : ¬ Overlap T (n1, n2) := by
  subst e1 e2
  apply not_overlap_of hT h1 h2
  intro t ht0 ht1 hd0 hd1
  left
  have hq := cntI_nonneg w1
  have hr := cntI_nonneg w2
  unfold Nrow Srow
  rw [if_neg (by omega), if_pos (by omega)]
  have key := L_g1 w2 hA2 (fun x hx => (h2 x hx)) (t - cntI w1) (by omega) (by omega)
  rw [show cntI w2 - 1 - (t - (cntI w1 + 1)) = cntI w2 - (t - cntI w1) by ring]
  linarith

/-- The translate by `g2 = (X - 1, r)` does not overlap the tile: the row inequality of `L_g2`. -/
theorem disj_g2 {T : CellTile} {c : GInt} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hA1 : Admissible w1) (n1 n2 : ℤ)
    (e1 : n1 = (F2Word.sum w2).1 - 1) (e2 : n2 = cntI w2) : ¬ Overlap T (n1, n2) := by
  subst e1 e2
  apply not_overlap_of hT h1 h2
  intro t ht0 ht1 hd0 hd1
  right
  have hq := cntI_nonneg w1
  have hr := cntI_nonneg w2
  unfold Nrow Srow
  rw [if_pos (by omega), if_neg (by omega), sum_append_fst]
  have key := L_g2 w1 hA1 (t - cntI w2) (by omega) (by omega)
  rw [show cntI w1 + cntI w2 - 1 - t = cntI w1 - 1 - (t - cntI w2) by ring]
  linarith

/-- The translate by `g1 - g2` does not overlap the tile: the north end is bounded by the first coordinate sum, and the
south end is at least the second coordinate sum. -/
theorem disj_g1g2 {T : CellTile} {c : GInt} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (n1 n2 : ℤ)
    (e1 : n1 = (F2Word.sum w1).1 - ((F2Word.sum w2).1 - 1)) (e2 : n2 = cntI w1 + 1 - cntI w2) :
    ¬ Overlap T (n1, n2) := by
  subst e1 e2
  apply not_overlap_of hT h1 h2
  intro t ht0 ht1 hd0 hd1
  left
  have hN := Nrow_le c w1 w2 h1 h2 t
  have hS := Srow_ge c w1 w2 h1 h2 (t - (cntI w1 + 1 - cntI w2))
  linarith

/-- The translate by `g1 + g2` does not overlap the tile: its row offset exceeds the height of the tile. -/
theorem disj_g1plusg2 {T : CellTile} {c : GInt} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (n1 n2 : ℤ)
    (e1 : n1 = (F2Word.sum w1).1 + ((F2Word.sum w2).1 - 1)) (e2 : n2 = cntI w1 + 1 + cntI w2) :
    ¬ Overlap T (n1, n2) := by
  subst e1 e2
  apply not_overlap_of hT h1 h2
  intro t ht0 ht1 hd0 hd1
  exfalso
  omega

theorem overlap_of_neg {T : CellTile} {u v : GInt} (h : u = -v) (hov : Overlap T u) : Overlap T v := by
  rw [h] at hov
  exact (overlap_neg_iff T v).mp hov

/-- The neighbour disjointness: no translate by a surrounding vector overlaps the tile. -/
theorem neighbour_disjoint {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2)) (hA1 : Admissible w1)
    (hA2 : Admissible (w2.map Unit4.mulNegI)) :
    ∀ n ∈ surroundVectors (almostV₁ w1) (almostV₂ w2), ¬ Overlap T n := by
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
  have hv1 : almostV₁ w1 = ((F2Word.sum w1).1, cntI w1 + 1) := by
    ext <;> simp [almostV₁, gI, sum_snd w1 hn1]
  have hv2 : almostV₂ w2 = ((F2Word.sum w2).1 - 1, cntI w2) := by
    ext <;> simp [almostV₂, gOne, sum_snd w2 hn2]
  intro n hn
  simp only [surroundVectors, Set.mem_setOf_eq, hv1, hv2] at hn
  obtain ⟨k, k', hk1, hk2, hk3, hk4, hk5, rfl⟩ := hn
  rcases (show k = -1 ∨ k = 0 ∨ k = 1 by omega) with rfl | rfl | rfl <;>
    rcases (show k' = -1 ∨ k' = 0 ∨ k' = 1 by omega) with rfl | rfl | rfl
  · -- (-1, -1): minus g1 + g2
    intro hov
    exact disj_g1plusg2 hT h1 h2 ((F2Word.sum w1).1 + ((F2Word.sum w2).1 - 1)) (cntI w1 + 1 + cntI w2) rfl rfl
      (overlap_of_neg (Prod.ext (by simp only [Prod.fst_neg]; ring) (by simp only [Prod.snd_neg]; ring)) hov)
  · -- (-1, 0): minus g1
    intro hov
    exact disj_g1 hT h1 h2 hA2 ((F2Word.sum w1).1) (cntI w1 + 1) rfl rfl
      (overlap_of_neg (Prod.ext (by simp only [Prod.fst_neg]; ring) (by simp only [Prod.snd_neg]; ring)) hov)
  · -- (-1, 1): minus g1 - g2
    intro hov
    exact disj_g1g2 hT h1 h2 ((F2Word.sum w1).1 - ((F2Word.sum w2).1 - 1)) (cntI w1 + 1 - cntI w2) rfl rfl
      (overlap_of_neg (Prod.ext (by simp only [Prod.fst_neg]; ring) (by simp only [Prod.snd_neg]; ring)) hov)
  · -- (0, -1): minus g2
    intro hov
    exact disj_g2 hT h1 h2 hA1 ((F2Word.sum w2).1 - 1) (cntI w2) rfl rfl
      (overlap_of_neg (Prod.ext (by simp only [Prod.fst_neg]; ring) (by simp only [Prod.snd_neg]; ring)) hov)
  · exact absurd rfl hk5
  · -- (0, 1): g2
    exact disj_g2 hT h1 h2 hA1 _ _ (by ring) (by ring)
  · -- (1, -1): g1 - g2
    exact disj_g1g2 hT h1 h2 _ _ (by ring) (by ring)
  · -- (1, 0): g1
    exact disj_g1 hT h1 h2 hA2 _ _ (by ring) (by ring)
  · -- (1, 1): g1 + g2
    exact disj_g1plusg2 hT h1 h2 _ _ (by ring) (by ring)

end FLatticePaper.Tiles
