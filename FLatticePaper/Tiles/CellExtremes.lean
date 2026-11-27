import FLatticePaper.Tiles.OverlapSides
import FLatticePaper.Tiles.WordFacts2
import FLatticePaper.Tiles.CoveringRows

/-! The extremes of a linear functional over a tile lie on the four sides of its boundary walk (step 2 of the proof of (H3) in
item (d) of `lemma:standard_tile_properties`).

Let `T` be a cell tile with boundary word `w1 * w2 * hat(rev w1) * hat(rev w2)` from `(0,0)`, with `w1` and `w2.map mulNegI`
admissible, and let `a, b ≥ 0`. For a corner `z` of a cell of `T`:
* `a y - b x` at `z` is at least its value at a point of the bottom walk (`lam_min_bottom`) and at most its value at a point of
  the top side `Σ w1 + Σ w2 - p`, `p` on the bottom walk (`lam_max_top`);
* `a x + b y` at `z` is at least its value at a point of the left side `Σ w2 - p` and at most its value at a point of the right
  side `Σ w1 + p`, `p` on the walk of `w2` (`sig_min_left`, `sig_max_right`).

The text proves the first two for a tile with a simple closed boundary walk, through the letter pattern of the walk at an extreme
point. Here they are read off the cell rows of the tile (`mem_iff_nr`, through `OverlapSides.corner_row`): in each row of corners
the functional is extreme at an end of the row, and these ends lie on the four sides, along which the functional is monotone. The
last two are the same statements for the functional of the vertical direction, used for the same-sign pairs of (H3) in place of
the quarter turn of the text.

The points of the walk are corners of cells of `T` (`walk_corner`, from the boundary edges of `IsBoundaryWordAt`), and the
coordinates of the walk of a word in `1` and `i` (in `i` and `-1`) range between `0` and its sum (`walk_range_one_i`,
`walk_range_i_neg`). -/

namespace FLatticePaper.Tiles.CellExtremes

open FLatticePaper FLatticePaper.Tiles FLatticePaper.Tiles.OverlapSides

/-! ### Points of walks -/

theorem mem_walk_start (c : GInt) (u : F2Word) : c ∈ F2Word.walk c u := by
  obtain ⟨t, ht⟩ := walk_eq_cons c u
  rw [ht]
  exact List.mem_cons_self ..

theorem mem_walk_last (c : GInt) (u : F2Word) : c + F2Word.sum u ∈ F2Word.walk c u := by
  induction u generalizing c with
  | nil => simp [F2Word.walk, F2Word.sum]
  | cons x u ih =>
    rw [WalkDecomp.walk_cons]
    have h := ih (c + x.vec)
    have e : c + x.vec + F2Word.sum u = c + F2Word.sum (x :: u) := by
      simp [F2Word.sum, add_assoc]
    rw [e] at h
    exact List.mem_cons_of_mem _ h

theorem mem_walk_append_left (c : GInt) (u v : F2Word) (z : GInt) (h : z ∈ F2Word.walk c u) :
    z ∈ F2Word.walk c (u ++ v) := by
  rw [WalkDecomp.walk_append]
  exact List.mem_append_left _ h

theorem mem_walk_append_right (c : GInt) (u v : F2Word) (z : GInt) (h : z ∈ F2Word.walk (c + F2Word.sum u) v) :
    z ∈ F2Word.walk c (u ++ v) := by
  rw [WalkDecomp.walk_append]
  obtain ⟨t, ht⟩ := walk_eq_cons (c + F2Word.sum u) v
  rw [ht] at h ⊢
  rcases List.mem_cons.1 h with h0 | h'
  · rw [h0]
    exact List.mem_append_left _ (mem_walk_last c u)
  · exact List.mem_append_right _ (by simpa using h')

/-- A point of a nonempty walk is an end of one of its edges. -/
theorem mem_walk_edge (W : F2Word) (p : GInt) :
    ∀ c : GInt, W ≠ [] → p ∈ F2Word.walk c W →
      ∃ e ∈ (F2Word.walk c W).zip (F2Word.walk c W).tail, p = e.1 ∨ p = e.2 := by
  induction W with
  | nil => intro c hW; exact absurd rfl hW
  | cons x W ih =>
    intro c _ hp
    have hwc : F2Word.walk c (x :: W) = c :: F2Word.walk (c + x.vec) W := WalkDecomp.walk_cons c x W
    obtain ⟨t, ht⟩ := walk_eq_cons (c + x.vec) W
    rw [hwc, ht] at hp ⊢
    rw [List.tail_cons, List.zip_cons_cons]
    rcases List.mem_cons.1 hp with h0 | h1
    · exact ⟨(c, c + x.vec), List.mem_cons_self .., Or.inl h0⟩
    · rcases List.mem_cons.1 h1 with h2 | h3
      · exact ⟨(c, c + x.vec), List.mem_cons_self .., Or.inr h2⟩
      · have hW' : W ≠ [] := by
          rintro rfl
          have : t = [] := by simpa [F2Word.walk] using ht.symm
          rw [this] at h3
          simp at h3
        have hpw : p ∈ F2Word.walk (c + x.vec) W := by
          rw [ht]
          exact List.mem_cons_of_mem _ h3
        obtain ⟨e, he, hpe⟩ := ih (c + x.vec) hW' hpw
        rw [ht, List.tail_cons] at he
        exact ⟨e, List.mem_cons_of_mem _ he, hpe⟩

/-- The two ends of a boundary edge of a cell tile are corners of one of its cells. -/
theorem corners_of_boundaryEdge (T : CellTile) (e : GInt × GInt) (he : e ∈ T.boundaryEdges) :
    ∃ s ∈ T, e.1 ∈ cellCorners s ∧ e.2 ∈ cellCorners s := by
  unfold CellTile.boundaryEdges at he
  rw [Finset.mem_biUnion] at he
  obtain ⟨s, hs, he⟩ := he
  rw [Finset.mem_image] at he
  obtain ⟨e', he', rfl⟩ := he
  rw [List.mem_toFinset, List.mem_filter] at he'
  obtain ⟨he', -⟩ := he'
  refine ⟨s, hs, ?_⟩
  simp only [cellEdgesWithOther, List.mem_cons, List.not_mem_nil, or_false] at he'
  rcases he' with rfl | rfl | rfl | rfl <;> simp [cellCorners, add_assoc]

/-- A point of a boundary walk is a corner of a cell of the tile. -/
theorem walk_corner {T : CellTile} {c : GInt} {W : F2Word} (hT : IsBoundaryWordAt T c W) (hW : W ≠ [])
    (p : GInt) (hp : p ∈ F2Word.walk c W) : ∃ s ∈ T, p ∈ cellCorners s := by
  obtain ⟨e, he, hpe⟩ := mem_walk_edge W p c hW hp
  have he' : e ∈ T.boundaryEdges := by
    rw [← hT.2.2.2]
    exact List.mem_toFinset.2 he
  obtain ⟨s, hs, h1, h2⟩ := corners_of_boundaryEdge T e he'
  rcases hpe with h | h
  · exact ⟨s, hs, h ▸ h1⟩
  · exact ⟨s, hs, h ▸ h2⟩

theorem boundaryWord_ne_nil (w1 w2 : F2Word) (hA1 : Admissible w1) : boundaryWordOf w1 w2 ≠ [] := by
  obtain ⟨-, hhead, -⟩ := hA1
  cases w1 with
  | nil => simp at hhead
  | cons x w1 => simp [boundaryWordOf]

/-- A point of the bottom walk is a corner of a cell of the tile. -/
theorem bottom_corner {T : CellTile} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (p : GInt) (hp : p ∈ F2Word.walk (0, 0) w1) : ∃ s ∈ T, p ∈ cellCorners s := by
  refine walk_corner hT (boundaryWord_ne_nil w1 w2 hA1) p ?_
  unfold boundaryWordOf
  exact mem_walk_append_left _ _ _ p (mem_walk_append_left _ _ _ p (mem_walk_append_left _ _ _ p hp))

/-- A point of the right walk is a corner of a cell of the tile. -/
theorem right_corner {T : CellTile} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (p : GInt) (hp : p ∈ F2Word.walk (F2Word.sum w1) w2) : ∃ s ∈ T, p ∈ cellCorners s := by
  refine walk_corner hT (boundaryWord_ne_nil w1 w2 hA1) p ?_
  unfold boundaryWordOf
  have e : ((0, 0) : GInt) + F2Word.sum w1 = F2Word.sum w1 := by simp
  have h12 : p ∈ F2Word.walk (0, 0) (w1 ++ w2) := mem_walk_append_right _ _ _ p (by rw [e]; exact hp)
  exact mem_walk_append_left _ _ _ p (mem_walk_append_left _ _ _ p h12)

/-! ### Ranges of the walks of monotone words -/

theorem walk_range_one_i (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) :
    ∀ (c p : GInt), p ∈ F2Word.walk c u →
      c.1 ≤ p.1 ∧ p.1 ≤ c.1 + (F2Word.sum u).1 ∧ c.2 ≤ p.2 ∧ p.2 ≤ c.2 + cntI u := by
  induction u with
  | nil =>
    intro c p hp
    simp [F2Word.walk] at hp
    subst hp
    simp [F2Word.sum, cntI]
  | cons x u ih =>
    intro c p hp
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .one ∨ y = .i := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    rw [WalkDecomp.walk_cons] at hp
    have hs : F2Word.sum (x :: u) = x.vec + F2Word.sum u := by simp [F2Word.sum]
    have hn := sum_fst_nonneg u hu'
    have hc := cntI_nonneg u
    rcases List.mem_cons.1 hp with h0 | hp'
    · subst h0
      rcases hx with rfl | rfl <;> simp [hs, cntI, Unit4.vec] <;> omega
    · have := ih hu' (c + x.vec) p hp'
      rcases hx with rfl | rfl <;> simp [hs, cntI, Unit4.vec] at this ⊢ <;> omega

theorem walk_range_i_neg (u : F2Word) (hu : ∀ x ∈ u, x = .i ∨ x = .negOne) :
    ∀ (c p : GInt), p ∈ F2Word.walk c u →
      c.1 + (F2Word.sum u).1 ≤ p.1 ∧ p.1 ≤ c.1 ∧ c.2 ≤ p.2 ∧ p.2 ≤ c.2 + cntI u := by
  induction u with
  | nil =>
    intro c p hp
    simp [F2Word.walk] at hp
    subst hp
    simp [F2Word.sum, cntI]
  | cons x u ih =>
    intro c p hp
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .i ∨ y = .negOne := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    rw [WalkDecomp.walk_cons] at hp
    have hs : F2Word.sum (x :: u) = x.vec + F2Word.sum u := by simp [F2Word.sum]
    have hn := sum_fst_nonpos u hu'
    have hc := cntI_nonneg u
    rcases List.mem_cons.1 hp with h0 | hp'
    · subst h0
      rcases hx with rfl | rfl <;> simp [hs, cntI, Unit4.vec] <;> omega
    · have := ih hu' (c + x.vec) p hp'
      rcases hx with rfl | rfl <;> simp [hs, cntI, Unit4.vec] at this ⊢ <;> omega

/-! ### The four extremes -/

/-- The points `(colN w1 Y, Y)`, `0 ≤ Y ≤ cntI w1`, are on the bottom walk. -/
theorem col_on_bottom (w1 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (Y : ℤ) (hY0 : 0 ≤ Y)
    (hY1 : Y ≤ cntI w1) : ((colN w1 (0, 0) Y, Y) : GInt) ∈ F2Word.walk (0, 0) w1 := by
  apply mem_walk_one_i w1 h1 (0, 0)
  · exact hY0
  · simpa using hY1
  · intro _
    exact colN_nonneg w1 h1 Y
  · intro hY
    have hY' : 0 < Y := hY
    exact colN_mono w1 h1 (Y - 1) Y (by omega) (by omega)
  · exact le_rfl

/-- The points `(colN w2 (Y - 1), Y)`, `1 ≤ Y ≤ cntI w2`, are on the walk of `w2`. -/
theorem col_on_right (w2 : F2Word) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (Y : ℤ) (hY1 : 1 ≤ Y)
    (hY2 : Y ≤ cntI w2) : ((colN w2 (0, 0) (Y - 1), Y) : GInt) ∈ F2Word.walk (0, 0) w2 := by
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by rcases h2 x hx with h | h <;> simp [h]
  apply mem_walk_i_neg w2 h2 (0, 0)
  · show 0 ≤ Y
    omega
  · simpa using hY2
  · intro hY
    have hY' : Y = 0 := hY
    omega
  · intro _
    exact le_rfl
  · by_cases hYK : Y < cntI w2
    · exact colN_anti w2 h2 (Y - 1) Y (by omega) (by omega) hYK
    · rw [colN_top w2 hn2 Y (by omega)]
      exact sum_fst_le_colN_neg w2 h2 (Y - 1) (by omega) (by omega)

/-- **Minimum on the bottom walk.** -/
theorem lam_min_bottom {T : CellTile} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (z : GInt) (hz : ∃ s ∈ T, z ∈ cellCorners s) :
    ∃ p ∈ F2Word.walk (0, 0) w1, a * p.2 - b * p.1 ≤ a * z.2 - b * z.1 := by
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 := letters_w2 hA2
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by rcases h1 x hx with h | h <;> simp [h]
  obtain ⟨x, y⟩ := z
  obtain ⟨s, hs, hzs⟩ := hz
  obtain ⟨t, ht, ht0, hth, hS, hN⟩ := corner_row hT h1 h2 hs hzs
  simp only at ht hS hN
  by_cases hy : y ≤ cntI w1
  · refine ⟨(colN w1 (0, 0) y, y), col_on_bottom w1 h1 y (by omega) hy, ?_⟩
    have hx : x ≤ colN w1 (0, 0) y := by
      by_cases htk : t < cntI w1
      · rw [nrow_lo htk] at hN
        have := colN_mono w1 h1 t y ht0 (by omega)
        linarith
      · have := nrow_le' w1 w2 h1 h2 t
        rw [colN_top w1 hn1 y (by omega)]
        linarith
    show a * y - b * colN w1 (0, 0) y ≤ a * y - b * x
    linarith [mul_le_mul_of_nonneg_left hx hb]
  · refine ⟨(colN w1 (0, 0) (cntI w1), cntI w1), col_on_bottom w1 h1 _ (cntI_nonneg w1) le_rfl, ?_⟩
    rw [colN_top w1 hn1 (cntI w1) le_rfl]
    have hx := nrow_le' w1 w2 h1 h2 t
    show a * cntI w1 - b * (F2Word.sum w1).1 ≤ a * y - b * x
    nlinarith [mul_le_mul_of_nonneg_left (show x ≤ (F2Word.sum w1).1 by linarith) hb,
      mul_le_mul_of_nonneg_left (show cntI w1 ≤ y by omega) ha]

/-- **Maximum on the top side.** -/
theorem lam_max_top {T : CellTile} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (z : GInt) (hz : ∃ s ∈ T, z ∈ cellCorners s) :
    ∃ p ∈ F2Word.walk (0, 0) w1, a * z.2 - b * z.1 ≤
      a * (F2Word.sum w1 + F2Word.sum w2 - p).2 - b * (F2Word.sum w1 + F2Word.sum w2 - p).1 := by
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 := letters_w2 hA2
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by rcases h1 x hx with h | h <;> simp [h]
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by rcases h2 x hx with h | h <;> simp [h]
  have hs1 := sum_snd w1 hn1
  have hs2 := sum_snd w2 hn2
  obtain ⟨x, y⟩ := z
  obtain ⟨s, hs, hzs⟩ := hz
  obtain ⟨t, ht, ht0, hth, hS, hN⟩ := corner_row hT h1 h2 hs hzs
  simp only at ht hS hN
  have e2 : ∀ p : GInt, (F2Word.sum w1 + F2Word.sum w2 - p).2 = cntI w1 + cntI w2 - p.2 := by
    intro p
    simp [hs1, hs2]
  have e1 : ∀ p : GInt, (F2Word.sum w1 + F2Word.sum w2 - p).1 = (F2Word.sum w1).1 + (F2Word.sum w2).1 - p.1 := by
    intro p
    simp
  by_cases hy : cntI w2 + 1 ≤ y
  · refine ⟨(colN w1 (0, 0) (cntI w1 + cntI w2 - y), cntI w1 + cntI w2 - y),
      col_on_bottom w1 h1 _ (by omega) (by omega), ?_⟩
    rw [e1, e2]
    show a * y - b * x ≤ a * (cntI w1 + cntI w2 - (cntI w1 + cntI w2 - y)) -
      b * ((F2Word.sum w1).1 + (F2Word.sum w2).1 - colN w1 (0, 0) (cntI w1 + cntI w2 - y))
    have ht2 : cntI w2 ≤ t := by omega
    rw [srow_hi ht2] at hS
    have hm := colN_mono w1 h1 (cntI w1 + cntI w2 - 1 - t) (cntI w1 + cntI w2 - y) (by omega) (by omega)
    have hx : (F2Word.sum w1).1 + (F2Word.sum w2).1 - colN w1 (0, 0) (cntI w1 + cntI w2 - y) ≤ x := by linarith
    rw [show cntI w1 + cntI w2 - (cntI w1 + cntI w2 - y) = y by ring]
    linarith [mul_le_mul_of_nonneg_left hx hb]
  · refine ⟨(colN w1 (0, 0) (cntI w1), cntI w1), col_on_bottom w1 h1 _ (cntI_nonneg w1) le_rfl, ?_⟩
    rw [e1, e2]
    show a * y - b * x ≤ a * (cntI w1 + cntI w2 - cntI w1) -
      b * ((F2Word.sum w1).1 + (F2Word.sum w2).1 - colN w1 (0, 0) (cntI w1))
    rw [colN_top w1 hn1 (cntI w1) le_rfl]
    have hx := srow_ge' w1 w2 h1 h2 t
    have hx' : (F2Word.sum w2).1 ≤ x := by linarith
    have hy' : y ≤ cntI w2 := by omega
    nlinarith [mul_le_mul_of_nonneg_left hx' hb, mul_le_mul_of_nonneg_left hy' ha]

/-- **Minimum of the vertical functional on the left side.** -/
theorem sig_min_left {T : CellTile} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (z : GInt) (hz : ∃ s ∈ T, z ∈ cellCorners s) :
    ∃ p ∈ F2Word.walk (0, 0) w2, a * (F2Word.sum w2 - p).1 + b * (F2Word.sum w2 - p).2 ≤ a * z.1 + b * z.2 := by
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 := letters_w2 hA2
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by rcases h2 x hx with h | h <;> simp [h]
  have hs2 := sum_snd w2 hn2
  obtain ⟨x, y⟩ := z
  obtain ⟨s, hs, hzs⟩ := hz
  obtain ⟨t, ht, ht0, hth, hS, hN⟩ := corner_row hT h1 h2 hs hzs
  simp only at ht hS hN
  have e : ∀ p : GInt, (F2Word.sum w2 - p) = ((F2Word.sum w2).1 - p.1, cntI w2 - p.2) := by
    intro p
    ext <;> simp [hs2]
  by_cases hy : y ≤ cntI w2 - 1
  · refine ⟨(colN w2 (0, 0) (cntI w2 - y - 1), cntI w2 - y), col_on_right w2 h2 _ (by omega) (by omega), ?_⟩
    rw [e]
    show a * ((F2Word.sum w2).1 - colN w2 (0, 0) (cntI w2 - y - 1)) + b * (cntI w2 - (cntI w2 - y)) ≤ a * x + b * y
    have htK : t < cntI w2 := by omega
    rw [srow_lo htK] at hS
    have hm := colN_anti w2 h2 (cntI w2 - y - 1) (cntI w2 - 1 - t) (by omega) (by omega) (by omega)
    have hx : (F2Word.sum w2).1 - colN w2 (0, 0) (cntI w2 - y - 1) ≤ x := by linarith
    rw [show cntI w2 - (cntI w2 - y) = y by ring]
    linarith [mul_le_mul_of_nonneg_left hx ha]
  · refine ⟨(0, 0), mem_walk_start _ _, ?_⟩
    rw [e]
    show a * ((F2Word.sum w2).1 - 0) + b * (cntI w2 - 0) ≤ a * x + b * y
    have hx := srow_ge' w1 w2 h1 h2 t
    have hx' : (F2Word.sum w2).1 ≤ x := by linarith
    have hy' : cntI w2 ≤ y := by omega
    nlinarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hy' hb]

/-- **Maximum of the vertical functional on the right side.** -/
theorem sig_max_right {T : CellTile} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (z : GInt) (hz : ∃ s ∈ T, z ∈ cellCorners s) :
    ∃ p ∈ F2Word.walk (0, 0) w2, a * z.1 + b * z.2 ≤ a * (F2Word.sum w1 + p).1 + b * (F2Word.sum w1 + p).2 := by
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 := letters_w2 hA2
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by rcases h1 x hx with h | h <;> simp [h]
  have hs1 := sum_snd w1 hn1
  obtain ⟨x, y⟩ := z
  obtain ⟨s, hs, hzs⟩ := hz
  obtain ⟨t, ht, ht0, hth, hS, hN⟩ := corner_row hT h1 h2 hs hzs
  simp only at ht hS hN
  have e : ∀ p : GInt, (F2Word.sum w1 + p) = ((F2Word.sum w1).1 + p.1, cntI w1 + p.2) := by
    intro p
    ext <;> simp [hs1]
  by_cases hy : cntI w1 + 1 ≤ y
  · refine ⟨(colN w2 (0, 0) (y - cntI w1 - 1), y - cntI w1), col_on_right w2 h2 _ (by omega) (by omega), ?_⟩
    rw [e]
    show a * x + b * y ≤ a * ((F2Word.sum w1).1 + colN w2 (0, 0) (y - cntI w1 - 1)) + b * (cntI w1 + (y - cntI w1))
    have htk : cntI w1 ≤ t := by omega
    rw [nrow_hi htk] at hN
    have hm := colN_anti w2 h2 (y - cntI w1 - 1) (t - cntI w1) (by omega) (by omega) (by omega)
    have hx : x ≤ (F2Word.sum w1).1 + colN w2 (0, 0) (y - cntI w1 - 1) := by linarith
    rw [show cntI w1 + (y - cntI w1) = y by ring]
    linarith [mul_le_mul_of_nonneg_left hx ha]
  · refine ⟨(0, 0), mem_walk_start _ _, ?_⟩
    rw [e]
    show a * x + b * y ≤ a * ((F2Word.sum w1).1 + 0) + b * (cntI w1 + 0)
    have hx := nrow_le' w1 w2 h1 h2 t
    have hx' : x ≤ (F2Word.sum w1).1 := by linarith
    have hy' : y ≤ cntI w1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hy' hb]

end FLatticePaper.Tiles.CellExtremes
