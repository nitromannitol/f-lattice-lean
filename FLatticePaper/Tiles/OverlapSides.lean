import FLatticePaper.Tiles.SuccessorProof
import FLatticePaper.Tiles.WalkDecomp
import FLatticePaper.Tiles.StandardAll
import FLatticePaper.Tiles.StandardCornerCells
import FLatticePaper.Tiles.PointNonNeighbour
import FLatticePaper.Tiles.OverlapStrings
import FLatticePaper.Tiles.HorizontalTop

/-! The overlap of a standard tile with its four edge translates lies on the four sides of its boundary walk.

Let `T` be a cell tile with boundary word `w1 * w2 * hat(rev w1) * hat(rev w2)` from `(0,0)`, with `w1` and `w2.map mulNegI`
admissible. Its cell rows are the intervals `[Srow t, Nrow t)` (`mem_iff_nr`), so a corner of a cell of `T` at height `y` lies
between `Srow` and `Nrow` of the cell row `y - 1` or `y` (`corner_row`). The walk of a word in `1` and `i` visits every point of
height `y` between the columns of its north steps at `y - 1` and `y` (`mem_walk_one_i`), and the same holds for a word in `i`
and `-1` with the columns in the other order (`mem_walk_i_neg`). With `v = -(Σ w2 - 1)` and `v₁ = Σ w1 + i`, a point that is a
corner of a cell of `T` and of a cell of a translate then lies on:
* the bottom side (the walk of `w1`), for the translate `T + v` (`bottom_of_overlap`);
* the top side (the reflection of the walk of `w1` through `Σ w1 + Σ w2`), for `T - v` (`top_of_overlap`);
* the right side (the walk of `w2` from `Σ w1`), for `T + v₁` (`right_of_overlap`);
* the left side (the reflection of the walk of `w2` through `Σ w2`), for `T - v₁` (`left_of_overlap`).
The inequalities used are the two row inequalities of the admissible words, `L_g2` (horizontal pair) and `L_g1` (vertical
pair), with the monotonicity of the north columns.

For the standard tiles the hypotheses hold for every word (`standardBoundaryWord_all`, `admissible_oddStandard`), and every point
of the tile is a corner of one of its cells (`oddTile_hcc`), so the statements hold for the point sets: a common point of `P` and
`P + v` lies on the bottom side of `P`, and so on (`odd_bottom_of_overlap` and the other instances). With the covering of the
bottom side by the forward horizontal string and of the translated top side by the reversed string (`bottom_covered_odd`,
`top_covered_odd`), this gives the horizontal covering hypotheses `H2X_h`, `H2Y_h` of the standard extension of
`lemma:global_odometers` (`horizontal_H2X_odd`, `horizontal_H2Y_odd`, and the even ones). -/

namespace FLatticePaper.Tiles.OverlapSides

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.Standard FLatticePaper.Tiles.CellDerivation
  FLatticePaper.Tiles.SiteStrings

/-! ### The walks of monotone words -/

/-- A point on a horizontal run of the walk of a word in `1` and `i` from `p`: at a height `y` between `p.2` and the top, the walk
passes every column from the north step below `y` (or `p.1` at the start height) to the north step at `y`. -/
theorem mem_walk_one_i (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) :
    ∀ (p : GInt) (x y : ℤ), p.2 ≤ y → y ≤ p.2 + cntI u → (y = p.2 → p.1 ≤ x) →
      (p.2 < y → colN u p (y - 1) ≤ x) → x ≤ colN u p y → ((x, y) : GInt) ∈ F2Word.walk p u := by
  induction u with
  | nil =>
    intro p x y h0 h1 hlo0 _ hhi
    have hy : y = p.2 := by simp [cntI] at h1; omega
    have hx : x ≤ p.1 := by simpa [colN] using hhi
    have hx' := hlo0 hy
    have e : ((x, y) : GInt) = p := Prod.ext (by simp; omega) (by simp; omega)
    simp [F2Word.walk, e]
  | cons a u ih =>
    have ha := hu a (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .one ∨ y = .i := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    intro p x y h0 h1 hlo0 hlo hhi
    rw [WalkDecomp.walk_cons]
    rcases ha with rfl | rfl
    · have hc : cntI (Unit4.one :: u) = cntI u := by simp [cntI]
      rw [hc] at h1
      have hcol : ∀ b, colN (Unit4.one :: u) p b = colN u (p + Unit4.vec .one) b := by
        intro b
        simp [colN]
      rw [hcol] at hhi
      by_cases hp : ((x, y) : GInt) = p
      · rw [hp]
        exact List.mem_cons_self ..
      · refine List.mem_cons_of_mem _ (ih hu' _ x y (by simp [Unit4.vec]; omega) (by simp [Unit4.vec]; omega) ?_ ?_ hhi)
        · intro hy
          simp only [Unit4.vec, Prod.snd_add, Prod.fst_add, add_zero] at hy ⊢
          have hx := hlo0 hy
          by_contra hcon
          exact hp (Prod.ext (by simp; omega) (by simp; omega))
        · intro hy
          rw [← hcol]
          exact hlo (by simpa [Unit4.vec] using hy)
    · have hc : cntI (Unit4.i :: u) = 1 + cntI u := by simp [cntI]
      rw [hc] at h1
      have hcol : ∀ b, colN (Unit4.i :: u) p b = if p.2 = b then p.1 else colN u (p + Unit4.vec .i) b := by
        intro b
        simp [colN]
      by_cases hy : y = p.2
      · have hx1 : x ≤ p.1 := by
          have := hhi
          rw [hcol, if_pos hy.symm] at this
          exact this
        have hx2 := hlo0 hy
        have e : ((x, y) : GInt) = p := Prod.ext (by simp; omega) (by simp; omega)
        rw [e]
        exact List.mem_cons_self ..
      · have hpy : p.2 < y := by omega
        refine List.mem_cons_of_mem _ (ih hu' _ x y (by simp [Unit4.vec]; omega) (by simp [Unit4.vec]; omega) ?_ ?_ ?_)
        · intro hy'
          have h := hlo hpy
          simp only [Unit4.vec, Prod.snd_add, Prod.fst_add, add_zero] at hy' ⊢
          rw [hcol, if_pos (by omega)] at h
          exact h
        · intro hy'
          have h := hlo hpy
          simp only [Unit4.vec, Prod.snd_add] at hy'
          rw [hcol, if_neg (by omega)] at h
          exact h
        · rw [hcol, if_neg (fun h => hy h.symm)] at hhi
          exact hhi

/-- A point on a horizontal run of the walk of a word in `i` and `-1` from `p`: at a height `y`, the walk passes every column from
the north step at `y` to the north step below `y` (or `p.1` at the start height). -/
theorem mem_walk_i_neg (u : F2Word) (hu : ∀ x ∈ u, x = .i ∨ x = .negOne) :
    ∀ (p : GInt) (x y : ℤ), p.2 ≤ y → y ≤ p.2 + cntI u → (y = p.2 → x ≤ p.1) →
      (p.2 < y → x ≤ colN u p (y - 1)) → colN u p y ≤ x → ((x, y) : GInt) ∈ F2Word.walk p u := by
  induction u with
  | nil =>
    intro p x y h0 h1 hhi0 _ hlo
    have hy : y = p.2 := by simp [cntI] at h1; omega
    have hx : p.1 ≤ x := by simpa [colN] using hlo
    have hx' := hhi0 hy
    have e : ((x, y) : GInt) = p := Prod.ext (by simp; omega) (by simp; omega)
    simp [F2Word.walk, e]
  | cons a u ih =>
    have ha := hu a (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .i ∨ y = .negOne := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    intro p x y h0 h1 hhi0 hhi hlo
    rw [WalkDecomp.walk_cons]
    rcases ha with rfl | rfl
    · have hc : cntI (Unit4.i :: u) = 1 + cntI u := by simp [cntI]
      rw [hc] at h1
      have hcol : ∀ b, colN (Unit4.i :: u) p b = if p.2 = b then p.1 else colN u (p + Unit4.vec .i) b := by
        intro b
        simp [colN]
      by_cases hy : y = p.2
      · have hx1 : p.1 ≤ x := by
          have := hlo
          rw [hcol, if_pos hy.symm] at this
          exact this
        have hx2 := hhi0 hy
        have e : ((x, y) : GInt) = p := Prod.ext (by simp; omega) (by simp; omega)
        rw [e]
        exact List.mem_cons_self ..
      · have hpy : p.2 < y := by omega
        refine List.mem_cons_of_mem _ (ih hu' _ x y (by simp [Unit4.vec]; omega) (by simp [Unit4.vec]; omega) ?_ ?_ ?_)
        · intro hy'
          have h := hhi hpy
          simp only [Unit4.vec, Prod.snd_add, Prod.fst_add, add_zero] at hy' ⊢
          rw [hcol, if_pos (by omega)] at h
          exact h
        · intro hy'
          have h := hhi hpy
          simp only [Unit4.vec, Prod.snd_add] at hy'
          rw [hcol, if_neg (by omega)] at h
          exact h
        · rw [hcol, if_neg (fun h => hy h.symm)] at hlo
          exact hlo
    · have hc : cntI (Unit4.negOne :: u) = cntI u := by simp [cntI]
      rw [hc] at h1
      have hcol : ∀ b, colN (Unit4.negOne :: u) p b = colN u (p + Unit4.vec .negOne) b := by
        intro b
        simp [colN]
      rw [hcol] at hlo
      by_cases hp : ((x, y) : GInt) = p
      · rw [hp]
        exact List.mem_cons_self ..
      · refine List.mem_cons_of_mem _ (ih hu' _ x y (by simp [Unit4.vec]; omega) (by simp [Unit4.vec]; omega) ?_ ?_ hlo)
        · intro hy
          simp only [Unit4.vec, Prod.snd_add, Prod.fst_add, add_zero] at hy ⊢
          have hx := hhi0 hy
          by_contra hcon
          exact hp (Prod.ext (by simp; omega) (by simp; omega))
        · intro hy
          rw [← hcol]
          exact hhi (by simpa [Unit4.vec] using hy)

/-! ### Columns of the two words -/

/-- Above the north steps of a word without `-i`, the column is the end column. -/
theorem colN_top (u : F2Word) (hu : ∀ x ∈ u, x ≠ .negI) (b : ℤ) (hb : cntI u ≤ b) :
    colN u (0, 0) b = (F2Word.sum u).1 := by
  have h := colN_hi u [] hu (0, 0) b (by simpa using hb)
  rw [List.append_nil] at h
  rw [h]
  simp [colN]

/-- The north columns of a word in `1` and `i` do not decrease, also past the last north step. -/
theorem colN_mono (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) (a b : ℤ) (ha : 0 ≤ a) (hab : a ≤ b) :
    colN u (0, 0) a ≤ colN u (0, 0) b := by
  by_cases hb : b < cntI u
  · exact colN_mono_le' u hu a b ha hab hb
  · have hn : ∀ x ∈ u, x ≠ .negI := fun x hx => by rcases hu x hx with h | h <;> simp [h]
    rw [colN_top u hn b (by omega)]
    exact colN_le_sum u hu a

/-- The north columns of a word in `i` and `-1` do not increase along its north steps. -/
theorem colN_anti (u : F2Word) (hu : ∀ x ∈ u, x = .i ∨ x = .negOne) (a b : ℤ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b < cntI u) : colN u (0, 0) b ≤ colN u (0, 0) a := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  subst hn
  exact colN_anti_le u hu a ha n hb

/-! ### Corners of the cells of a tile -/

/-- A corner `z` of a cell of the tile lies between the south and north ends of the cell row `z.2 - 1` or `z.2`. -/
theorem corner_row {T : CellTile} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) {s z : GInt} (hs : s ∈ T)
    (hz : z ∈ cellCorners s) :
    ∃ t : ℤ, (t = z.2 - 1 ∨ t = z.2) ∧ 0 ≤ t ∧ t < cntI w1 + cntI w2 ∧
      Srow (0, 0) w1 w2 t ≤ z.1 ∧ z.1 ≤ Nrow (0, 0) w1 w2 t := by
  obtain ⟨a, b⟩ := s
  have hm : (0 ≤ b ∧ b < cntI w1 + cntI w2) ∧ Srow (0, 0) w1 w2 b ≤ a ∧ a < Nrow (0, 0) w1 w2 b := by
    simpa using (mem_iff_nr hT h1 h2 a b).1 hs
  obtain ⟨⟨hb0, hb1⟩, hS, hN⟩ := hm
  have hz' : (z.1 = a ∨ z.1 = a + 1) ∧ (z.2 = b ∨ z.2 = b + 1) := by
    rw [FLatticePaper.Tiles.Standard.mem_cellCorners_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp [gOne, gI]
  refine ⟨b, by omega, hb0, hb1, by omega, by omega⟩

/-! ### The four sides -/

/-- The letters of `w2` are `i` and `-1` when `w2.map mulNegI` is admissible. -/
theorem letters_w2 {w2 : F2Word} (hA2 : Admissible (w2.map Unit4.mulNegI)) : ∀ x ∈ w2, x = .i ∨ x = .negOne := by
  have hmono : ∀ y ∈ w2.map Unit4.mulNegI, y = .one ∨ y = .i := hA2.1
  intro x hx
  have hm := hmono x.mulNegI (List.mem_map_of_mem hx)
  have hxe : x = Unit4.mulI (Unit4.mulNegI x) := by cases x <;> rfl
  rcases hm with h | h
  · rw [hxe, h]; simp [Unit4.mulI]
  · rw [hxe, h]; simp [Unit4.mulI]

theorem nrow_lo {w1 w2 : F2Word} {j : ℤ} (h : j < cntI w1) : Nrow (0, 0) w1 w2 j = colN w1 (0, 0) j := by
  rw [wNrowLt h]; simp

theorem nrow_hi {w1 w2 : F2Word} {j : ℤ} (h : cntI w1 ≤ j) :
    Nrow (0, 0) w1 w2 j = (F2Word.sum w1).1 + colN w2 (0, 0) (j - cntI w1) := by
  rw [wNrowGe h]; simp

theorem srow_lo {w1 w2 : F2Word} {j : ℤ} (h : j < cntI w2) :
    Srow (0, 0) w1 w2 j = (F2Word.sum w2).1 - colN w2 (0, 0) (cntI w2 - 1 - j) := by
  rw [wSrowLt h]; simp

theorem srow_hi {w1 w2 : F2Word} {j : ℤ} (h : cntI w2 ≤ j) :
    Srow (0, 0) w1 w2 j = (F2Word.sum w1).1 + (F2Word.sum w2).1 - colN w1 (0, 0) (cntI w1 + cntI w2 - 1 - j) := by
  rw [wSrowGe h]; simp

theorem srow_ge' (w1 w2 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (t : ℤ) :
    (F2Word.sum w2).1 ≤ Srow (0, 0) w1 w2 t := by
  have := Srow_ge (0, 0) w1 w2 h1 h2 t
  simpa using this

theorem nrow_le' (w1 w2 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (t : ℤ) :
    Nrow (0, 0) w1 w2 t ≤ (F2Word.sum w1).1 := by
  have := Nrow_le (0, 0) w1 w2 h1 h2 t
  simpa using this

/-- **The bottom side.** A corner of a cell of `T` that is also a corner of a cell of the translate `T + v`, `v = -(Σ w2 - 1)`,
lies on the walk of `w1` from `(0,0)`. -/
theorem bottom_of_overlap {T : CellTile} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) (z : GInt)
    (hz : ∃ s ∈ T, z ∈ cellCorners s) (hzv : ∃ s ∈ T, z - (-almostV₂ w2) ∈ cellCorners s) :
    z ∈ F2Word.walk (0, 0) w1 := by
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 := letters_w2 hA2
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by rcases h2 x hx with h | h <;> simp [h]
  have hs2 := sum_snd w2 hn2
  obtain ⟨x, y⟩ := z
  obtain ⟨s, hs, hzs⟩ := hz
  obtain ⟨t1, ht1, ht10, ht1h, hS1, hN1⟩ := corner_row hT h1 h2 hs hzs
  obtain ⟨s', hs', hzs'⟩ := hzv
  obtain ⟨t2, ht2, ht20, ht2h, hS2, hN2⟩ := corner_row hT h1 h2 hs' hzs'
  have e1 : ((x, y) - -almostV₂ w2 : GInt).1 = x + (F2Word.sum w2).1 - 1 := by
    simp [almostV₂, gOne]; ring
  have e2 : ((x, y) - -almostV₂ w2 : GInt).2 = y + cntI w2 := by
    simp [almostV₂, gOne, hs2]
  rw [e1] at hS2 hN2
  rw [e2] at ht2
  simp only at ht1 hS1 hN1
  have hK := w2_cntI_pos hA2
  apply mem_walk_one_i w1 h1 (0, 0) x y
  · show 0 ≤ y; omega
  · show y ≤ 0 + cntI w1; omega
  · intro hy
    show 0 ≤ x
    have := srow_ge' w1 w2 h1 h2 t2
    linarith
  · intro hy
    have hy' : 0 < y := hy
    have ht2K : cntI w2 ≤ t2 := by omega
    rw [srow_hi ht2K] at hS2
    have hm := colN_mono w1 h1 (cntI w1 + cntI w2 - 1 - t2) (cntI w1 - y) (by omega) (by omega)
    have hL := L_g2 w1 hA1 (y - 1) (by omega) (by omega)
    rw [show cntI w1 - 1 - (y - 1) = cntI w1 - y by ring] at hL
    linarith
  · by_cases ht : t1 < cntI w1
    · rw [nrow_lo ht] at hN1
      have := colN_mono w1 h1 t1 y ht10 (by omega)
      linarith
    · have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by rcases h1 x hx with h | h <;> simp [h]
      rw [colN_top w1 hn1 y (by omega)]
      have := nrow_le' w1 w2 h1 h2 t1
      linarith

/-- **The top side.** A corner of a cell of `T` that is also a corner of a cell of the translate `T - v` lies on the top side:
its reflection through `Σ w1 + Σ w2` is on the walk of `w1`. -/
theorem top_of_overlap {T : CellTile} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) (z : GInt)
    (hz : ∃ s ∈ T, z ∈ cellCorners s) (hzv : ∃ s ∈ T, z + (-almostV₂ w2) ∈ cellCorners s) :
    F2Word.sum w1 + F2Word.sum w2 - z ∈ F2Word.walk (0, 0) w1 := by
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 := letters_w2 hA2
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by rcases h1 x hx with h | h <;> simp [h]
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by rcases h2 x hx with h | h <;> simp [h]
  have hs1 := sum_snd w1 hn1
  have hs2 := sum_snd w2 hn2
  obtain ⟨x, y⟩ := z
  obtain ⟨s, hs, hzs⟩ := hz
  obtain ⟨t1, ht1, ht10, ht1h, hS1, hN1⟩ := corner_row hT h1 h2 hs hzs
  obtain ⟨s', hs', hzs'⟩ := hzv
  obtain ⟨t2, ht2, ht20, ht2h, hS2, hN2⟩ := corner_row hT h1 h2 hs' hzs'
  have e1 : ((x, y) + -almostV₂ w2 : GInt).1 = x + 1 - (F2Word.sum w2).1 := by
    simp [almostV₂, gOne]; ring
  have e2 : ((x, y) + -almostV₂ w2 : GInt).2 = y - cntI w2 := by
    simp [almostV₂, gOne, hs2]; ring
  rw [e1] at hS2 hN2
  rw [e2] at ht2
  simp only at ht1 hS1 hN1
  have ept : F2Word.sum w1 + F2Word.sum w2 - ((x, y) : GInt) =
      ((F2Word.sum w1).1 + (F2Word.sum w2).1 - x, cntI w1 + cntI w2 - y) := by
    ext <;> simp [hs1, hs2]
  rw [ept]
  have hK := w2_cntI_pos hA2
  apply mem_walk_one_i w1 h1 (0, 0)
  · show 0 ≤ cntI w1 + cntI w2 - y; omega
  · show cntI w1 + cntI w2 - y ≤ 0 + cntI w1; omega
  · intro hy
    show 0 ≤ (F2Word.sum w1).1 + (F2Word.sum w2).1 - x
    have := nrow_le' w1 w2 h1 h2 t2
    linarith
  · intro hy
    have hy' : 0 < cntI w1 + cntI w2 - y := hy
    have ht2k : t2 < cntI w1 := by omega
    rw [nrow_lo ht2k] at hN2
    have hm := colN_mono w1 h1 t2 (y - cntI w2) ht20 (by omega)
    have hL := L_g2 w1 hA1 (y - cntI w2) (by omega) (by omega)
    rw [show cntI w1 - 1 - (y - cntI w2) = cntI w1 + cntI w2 - y - 1 by ring] at hL
    linarith
  · by_cases ht : cntI w2 ≤ t1
    · rw [srow_hi ht] at hS1
      have := colN_mono w1 h1 (cntI w1 + cntI w2 - 1 - t1) (cntI w1 + cntI w2 - y) (by omega) (by omega)
      linarith
    · rw [colN_top w1 hn1 (cntI w1 + cntI w2 - y) (by omega)]
      have := srow_ge' w1 w2 h1 h2 t1
      linarith

/-- **The right side.** A corner of a cell of `T` that is also a corner of a cell of the translate `T + v₁`, `v₁ = Σ w1 + i`,
lies on the walk of `w2` from `Σ w1`: its difference with `Σ w1` is on the walk of `w2` from `(0,0)`. -/
theorem right_of_overlap {T : CellTile} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) (z : GInt)
    (hz : ∃ s ∈ T, z ∈ cellCorners s) (hzv : ∃ s ∈ T, z - almostV₁ w1 ∈ cellCorners s) :
    z - F2Word.sum w1 ∈ F2Word.walk (0, 0) w2 := by
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 := letters_w2 hA2
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by rcases h1 x hx with h | h <;> simp [h]
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by rcases h2 x hx with h | h <;> simp [h]
  have hs1 := sum_snd w1 hn1
  obtain ⟨x, y⟩ := z
  obtain ⟨s, hs, hzs⟩ := hz
  obtain ⟨t1, ht1, ht10, ht1h, hS1, hN1⟩ := corner_row hT h1 h2 hs hzs
  obtain ⟨s', hs', hzs'⟩ := hzv
  obtain ⟨t2, ht2, ht20, ht2h, hS2, hN2⟩ := corner_row hT h1 h2 hs' hzs'
  have e1 : ((x, y) - almostV₁ w1 : GInt).1 = x - (F2Word.sum w1).1 := by
    simp [almostV₁, gI]
  have e2 : ((x, y) - almostV₁ w1 : GInt).2 = y - cntI w1 - 1 := by
    simp [almostV₁, gI, hs1]; ring
  rw [e1] at hS2 hN2
  rw [e2] at ht2
  simp only at ht1 hS1 hN1
  have ept : ((x, y) : GInt) - F2Word.sum w1 = (x - (F2Word.sum w1).1, y - cntI w1) := by
    ext <;> simp [hs1]
  rw [ept]
  have hK := w2_cntI_pos hA2
  apply mem_walk_i_neg w2 h2 (0, 0)
  · show 0 ≤ y - cntI w1; omega
  · show y - cntI w1 ≤ 0 + cntI w2; omega
  · intro hy
    exfalso
    have : y - cntI w1 = 0 := hy
    omega
  · intro hy
    have ht : cntI w1 ≤ t1 := by omega
    rw [nrow_hi ht] at hN1
    have := colN_anti w2 h2 (y - cntI w1 - 1) (t1 - cntI w1) (by omega) (by omega) (by omega)
    show x - (F2Word.sum w1).1 ≤ colN w2 (0, 0) (y - cntI w1 - 1)
    linarith
  · show colN w2 (0, 0) (y - cntI w1) ≤ x - (F2Word.sum w1).1
    by_cases hY : y - cntI w1 ≤ cntI w2 - 1
    · have ht : t2 < cntI w2 := by omega
      rw [srow_lo ht] at hS2
      have hm := colN_anti w2 h2 (cntI w2 - (y - cntI w1)) (cntI w2 - 1 - t2) (by omega) (by omega) (by omega)
      have hL := L_g1 w2 hA2 h2 (y - cntI w1) (by omega) hY
      linarith
    · rw [colN_top w2 hn2 (y - cntI w1) (by omega)]
      have := srow_ge' w1 w2 h1 h2 t2
      linarith

/-- **The left side.** A corner of a cell of `T` that is also a corner of a cell of the translate `T - v₁` lies on the left
side: its reflection through `Σ w2` is on the walk of `w2`. -/
theorem left_of_overlap {T : CellTile} {w1 w2 : F2Word} (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) (z : GInt)
    (hz : ∃ s ∈ T, z ∈ cellCorners s) (hzv : ∃ s ∈ T, z + almostV₁ w1 ∈ cellCorners s) :
    F2Word.sum w2 - z ∈ F2Word.walk (0, 0) w2 := by
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 := letters_w2 hA2
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by rcases h1 x hx with h | h <;> simp [h]
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by rcases h2 x hx with h | h <;> simp [h]
  have hs1 := sum_snd w1 hn1
  have hs2 := sum_snd w2 hn2
  obtain ⟨x, y⟩ := z
  obtain ⟨s, hs, hzs⟩ := hz
  obtain ⟨t1, ht1, ht10, ht1h, hS1, hN1⟩ := corner_row hT h1 h2 hs hzs
  obtain ⟨s', hs', hzs'⟩ := hzv
  obtain ⟨t2, ht2, ht20, ht2h, hS2, hN2⟩ := corner_row hT h1 h2 hs' hzs'
  have e1 : ((x, y) + almostV₁ w1 : GInt).1 = x + (F2Word.sum w1).1 := by
    simp [almostV₁, gI]
  have e2 : ((x, y) + almostV₁ w1 : GInt).2 = y + cntI w1 + 1 := by
    simp [almostV₁, gI, hs1]; ring
  rw [e1] at hS2 hN2
  rw [e2] at ht2
  simp only at ht1 hS1 hN1
  have ept : F2Word.sum w2 - ((x, y) : GInt) = ((F2Word.sum w2).1 - x, cntI w2 - y) := by
    ext <;> simp [hs2]
  rw [ept]
  have hK := w2_cntI_pos hA2
  apply mem_walk_i_neg w2 h2 (0, 0)
  · show 0 ≤ cntI w2 - y; omega
  · show cntI w2 - y ≤ 0 + cntI w2; omega
  · intro hy
    exfalso
    have : cntI w2 - y = 0 := hy
    omega
  · intro hy
    have ht : t1 < cntI w2 := by omega
    rw [srow_lo ht] at hS1
    have := colN_anti w2 h2 (cntI w2 - 1 - y) (cntI w2 - 1 - t1) (by omega) (by omega) (by omega)
    rw [show cntI w2 - y - 1 = cntI w2 - 1 - y by ring]
    show (F2Word.sum w2).1 - x ≤ colN w2 (0, 0) (cntI w2 - 1 - y)
    linarith
  · show colN w2 (0, 0) (cntI w2 - y) ≤ (F2Word.sum w2).1 - x
    have ht : cntI w1 ≤ t2 := by omega
    rw [nrow_hi ht] at hN2
    by_cases hy : 1 ≤ y
    · have hm := colN_anti w2 h2 y (t2 - cntI w1) (by omega) (by omega) (by omega)
      have hL := L_g1 w2 hA2 h2 y hy (by omega)
      linarith
    · rw [colN_top w2 hn2 (cntI w2 - y) (by omega)]
      have := colN_nonpos w2 h2 (t2 - cntI w1)
      linarith

/-! ### The standard tiles -/

/-- A point of a site set with H1 is a corner of a cell of its cell tile. -/
theorem corner_of_hcc {P : Finset GInt} (hP : HasCornerCell P) {z : GInt} (hz : z ∈ P) :
    ∃ s ∈ cellTileOf P, z ∈ cellCorners s := by
  obtain ⟨c, hzc, hall⟩ := hP z hz
  exact ⟨c, FLatticePaper.Tiles.PointNonNeighbour.mem_cellTileOf_of_cell hall, hzc⟩

/-- A walk from `c` contains `z` when the walk from `0` contains `z - c`. -/
theorem mem_walk_of_sub (c z : GInt) (u : F2Word) (h : z - c ∈ F2Word.walk (0, 0) u) : z ∈ F2Word.walk c u := by
  rw [WalkDecomp.walk_translate]
  exact List.mem_map.2 ⟨z - c, h, by abel⟩

/-- A boundary vertex of the cell region of `P` is a point of `P`. -/
theorem mem_of_boundaryVertex {P : Finset GInt} {z : GInt}
    (h : BoundaryVertex (↑(cellTileOf P) : Set GInt) z) : z ∈ P := by
  obtain ⟨⟨s, hs, hsz⟩, -⟩ := h
  have hs' : s ∈ P.filter (fun a => cellCorners a ⊆ P) := hs
  have hzc : z ∈ cellCorners s := (FLatticePaper.Tiles.OverlapStrings.hasCorner_iff_mem s z).1 hsz
  exact (Finset.mem_filter.1 hs').2 hzc

/-- A boundary vertex of the cell region of the translate `P + v` lies in `P + v`. -/
theorem mem_sub_of_boundaryVertex {P : Finset GInt} {v z : GInt}
    (h : BoundaryVertex ({t : GInt | t - v ∈ cellTileOf P} : Set GInt) z) : z - v ∈ P := by
  obtain ⟨⟨s, hs, hsz⟩, -⟩ := h
  have hs' : s - v ∈ P.filter (fun a => cellCorners a ⊆ P) := hs
  have hsz' : HasCorner (s - v) (z - v) :=
    (FLatticePaper.Tiles.OverlapStrings.hasCorner_add_sub_iff (s - v) z v).1 (by rwa [sub_add_cancel])
  have hzc : z - v ∈ cellCorners (s - v) := (FLatticePaper.Tiles.OverlapStrings.hasCorner_iff_mem _ _).1 hsz'
  exact (Finset.mem_filter.1 hs').2 hzc

theorem boundary_odd (w : Word) :
    IsBoundaryWordAt (cellTileOf (oddTile w)) (0, 0) (boundaryWordOf (oddBottom w) (oddRight w)) :=
  (FLatticePaper.Tiles.StandardAll.standardBoundaryWord_all w).1

theorem boundary_even (w : Word) :
    IsBoundaryWordAt (cellTileOf (evenTile w)) (0, 0) (boundaryWordOf (evenBottom w) (evenRight w)) :=
  (FLatticePaper.Tiles.StandardAll.standardBoundaryWord_all w).2

/-- **Bottom side, odd tile.** A common point of `P` and `P + v`, `v = -texV2`, lies on the bottom walk of `P`. -/
theorem odd_bottom_of_overlap (w : Word) :
    ∀ z ∈ oddTile w, z - (-texV2 (fracOdd w)) ∈ oddTile w → z ∈ F2Word.walk 0 (oddBottom w) := by
  intro z hz hzv
  rw [← FLatticePaper.Tiles.StandardBoundary.sum_oddRight w] at hzv
  exact bottom_of_overlap (boundary_odd w) (admissible_oddStandard w).1 (admissible_oddStandard w).2 z
    (corner_of_hcc (oddTile_hcc w) hz) (corner_of_hcc (oddTile_hcc w) hzv)

/-- **Top side, odd tile.** A common point of `P` and `P - v` lies on the top side of `P`: its reflection through
`Σ w1 + Σ w2` is on the bottom walk. -/
theorem odd_top_of_overlap (w : Word) :
    ∀ z ∈ oddTile w, z + (-texV2 (fracOdd w)) ∈ oddTile w →
      F2Word.sum (oddBottom w) + F2Word.sum (oddRight w) - z ∈ F2Word.walk 0 (oddBottom w) := by
  intro z hz hzv
  rw [← FLatticePaper.Tiles.StandardBoundary.sum_oddRight w] at hzv
  exact top_of_overlap (boundary_odd w) (admissible_oddStandard w).1 (admissible_oddStandard w).2 z
    (corner_of_hcc (oddTile_hcc w) hz) (corner_of_hcc (oddTile_hcc w) hzv)

/-- **Right side, odd tile.** A common point of `P` and `P + v₁`, `v₁ = texV1Odd`, lies on the right walk of `P` (the walk of
`oddRight w` from `Σ oddBottom w`). -/
theorem odd_right_of_overlap (w : Word) :
    ∀ z ∈ oddTile w, z - texV1Odd (fracOdd w) ∈ oddTile w →
      z ∈ F2Word.walk (F2Word.sum (oddBottom w)) (oddRight w) := by
  intro z hz hzv
  rw [← FLatticePaper.Tiles.StandardBoundary.sum_oddBottom w] at hzv
  exact mem_walk_of_sub _ z _ (right_of_overlap (boundary_odd w) (admissible_oddStandard w).1
    (admissible_oddStandard w).2 z (corner_of_hcc (oddTile_hcc w) hz) (corner_of_hcc (oddTile_hcc w) hzv))

/-- **Left side, odd tile.** A common point of `P` and `P - v₁` lies on the left side of `P`: its reflection through
`Σ oddRight w` is on the walk of `oddRight w`. -/
theorem odd_left_of_overlap (w : Word) :
    ∀ z ∈ oddTile w, z + texV1Odd (fracOdd w) ∈ oddTile w →
      F2Word.sum (oddRight w) - z ∈ F2Word.walk 0 (oddRight w) := by
  intro z hz hzv
  rw [← FLatticePaper.Tiles.StandardBoundary.sum_oddBottom w] at hzv
  exact left_of_overlap (boundary_odd w) (admissible_oddStandard w).1 (admissible_oddStandard w).2 z
    (corner_of_hcc (oddTile_hcc w) hz) (corner_of_hcc (oddTile_hcc w) hzv)

/-- **Bottom side, even tile.** -/
theorem even_bottom_of_overlap (w : Word) :
    ∀ z ∈ evenTile w, z - (-texV2 (fracEven w)) ∈ evenTile w → z ∈ F2Word.walk 0 (evenBottom w) := by
  intro z hz hzv
  rw [← FLatticePaper.Tiles.StandardBoundary.sum_evenRight w] at hzv
  exact bottom_of_overlap (boundary_even w) (admissible_evenStandard w).1 (admissible_evenStandard w).2 z
    (corner_of_hcc (evenTile_hcc w) hz) (corner_of_hcc (evenTile_hcc w) hzv)

/-- **Top side, even tile.** -/
theorem even_top_of_overlap (w : Word) :
    ∀ z ∈ evenTile w, z + (-texV2 (fracEven w)) ∈ evenTile w →
      F2Word.sum (evenBottom w) + F2Word.sum (evenRight w) - z ∈ F2Word.walk 0 (evenBottom w) := by
  intro z hz hzv
  rw [← FLatticePaper.Tiles.StandardBoundary.sum_evenRight w] at hzv
  exact top_of_overlap (boundary_even w) (admissible_evenStandard w).1 (admissible_evenStandard w).2 z
    (corner_of_hcc (evenTile_hcc w) hz) (corner_of_hcc (evenTile_hcc w) hzv)

/-- **Right side, even tile.** -/
theorem even_right_of_overlap (w : Word) :
    ∀ z ∈ evenTile w, z - texV1Even (fracEven w) ∈ evenTile w →
      z ∈ F2Word.walk (F2Word.sum (evenBottom w)) (evenRight w) := by
  intro z hz hzv
  rw [← FLatticePaper.Tiles.StandardBoundary.sum_evenBottom w] at hzv
  exact mem_walk_of_sub _ z _ (right_of_overlap (boundary_even w) (admissible_evenStandard w).1
    (admissible_evenStandard w).2 z (corner_of_hcc (evenTile_hcc w) hz) (corner_of_hcc (evenTile_hcc w) hzv))

/-- **Left side, even tile.** -/
theorem even_left_of_overlap (w : Word) :
    ∀ z ∈ evenTile w, z + texV1Even (fracEven w) ∈ evenTile w →
      F2Word.sum (evenRight w) - z ∈ F2Word.walk 0 (evenRight w) := by
  intro z hz hzv
  rw [← FLatticePaper.Tiles.StandardBoundary.sum_evenBottom w] at hzv
  exact left_of_overlap (boundary_even w) (admissible_evenStandard w).1 (admissible_evenStandard w).2 z
    (corner_of_hcc (evenTile_hcc w) hz) (corner_of_hcc (evenTile_hcc w) hzv)

/-! ### The horizontal covering hypotheses -/

/-- **`H2X_h`, odd child.** A boundary vertex of the cell region of `P` that lies in `P + v` is covered by the forward
horizontal string: it is on the bottom walk (`odd_bottom_of_overlap`), which the string covers (`bottom_covered_odd`). -/
theorem horizontal_H2X_odd (w : Word) :
    ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z → z - (-texV2 (fracOdd w)) ∈ oddTile w →
      tileCovers (hStringAt (hWordOf w false) 0) z := by
  intro z hz hzv
  exact FLatticePaper.Tiles.HorizontalSides.bottom_covered_odd w z
    (odd_bottom_of_overlap w z (mem_of_boundaryVertex hz) hzv)

/-- **`H2Y_h`, odd child.** A boundary vertex of the cell region of `P + v` that lies in `P` is covered by the reversed
horizontal string: it is `t + v` for a point `t` of the top side of `P` (`odd_top_of_overlap`), and the translated top side
is covered by the reversed string (`top_covered_odd`). -/
theorem horizontal_H2Y_odd (w : Word) :
    ∀ z, BoundaryVertex ({t : GInt | t - (-texV2 (fracOdd w)) ∈ cellTileOf (oddTile w)} : Set GInt) z →
      z ∈ oddTile w → tileCovers (hRevStringAt (hWordOf w false).reverse (1, -2)) z := by
  intro z hz hzP
  have hz' := mem_sub_of_boundaryVertex hz
  have hb := odd_top_of_overlap w (z - (-texV2 (fracOdd w))) hz' (by rwa [sub_add_cancel])
  have hc := FLatticePaper.Tiles.HorizontalTop.top_covered_odd w _ hb
  have e : F2Word.sum (oddBottom w) + F2Word.sum (oddRight w) -
      (F2Word.sum (oddBottom w) + F2Word.sum (oddRight w) - (z - (-texV2 (fracOdd w)))) + (-texV2 (fracOdd w)) = z := by
    abel
  rwa [e] at hc

/-- **`H2X_h`, even child.** -/
theorem horizontal_H2X_even (w : Word) :
    ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z → z - (-texV2 (fracEven w)) ∈ evenTile w →
      tileCovers (hStringAt (hWordOf w true) 0) z := by
  intro z hz hzv
  exact FLatticePaper.Tiles.HorizontalSides.bottom_covered_even w z
    (even_bottom_of_overlap w z (mem_of_boundaryVertex hz) hzv)

/-- **`H2Y_h`, even child.** -/
theorem horizontal_H2Y_even (w : Word) :
    ∀ z, BoundaryVertex ({t : GInt | t - (-texV2 (fracEven w)) ∈ cellTileOf (evenTile w)} : Set GInt) z →
      z ∈ evenTile w → tileCovers (hRevStringAt (hWordOf w true).reverse (1, -2)) z := by
  intro z hz hzP
  have hz' := mem_sub_of_boundaryVertex hz
  have hb := even_top_of_overlap w (z - (-texV2 (fracEven w))) hz' (by rwa [sub_add_cancel])
  have hc := FLatticePaper.Tiles.HorizontalTop.top_covered_even w _ hb
  have e : F2Word.sum (evenBottom w) + F2Word.sum (evenRight w) -
      (F2Word.sum (evenBottom w) + F2Word.sum (evenRight w) - (z - (-texV2 (fracEven w)))) + (-texV2 (fracEven w)) = z := by
    abel
  rwa [e] at hc

end FLatticePaper.Tiles.OverlapSides
