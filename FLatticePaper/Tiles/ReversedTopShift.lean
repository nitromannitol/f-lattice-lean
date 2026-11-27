import FLatticePaper.Tiles.StackedMoreover
import FLatticePaper.Tiles.TileListBridge
import FLatticePaper.Tiles.SurgicalCornerThird

/-! The top reversed list of a corner and the stacked reversed string of the Moreover differ by the vertical shift
`v_{n/d,2} = (n - d, n + d)`, with `n = #q(w_v)` and `d = |w_v|`.

* `zoReversedStackedE_eq`: the reversed enlarged zero-one string of `w` (the letters `lettersOf w true`, stacked by
  `horizontalStackShift`) is the reversed horizontal string `hRevStringAt w.reverse (1, -2)`.
* `vRev_last_top`: for a vertical word `wv` starting with `p` and ending with `q`, the last position of the vertical reversed
  string of `wv.reverse` from `0` is `(1 + n - d, n + d - 2) = (1, -2) + v_{n/d,2}`.

Hence the top reversed list of the corner is the stacked reversed string shifted by `v_{n/d,2}`. -/

namespace FLatticePaper.Tiles

theorem stepOf_hor_rev (a b : Letter) : stepOf Orientation.horizontal true a b = hRevOffset a b := by
  cases a <;> cases b <;> rfl

theorem scanl_getD_succ_gen : ∀ (L : List GInt) (c : GInt) (k : ℕ), k < L.length →
    (List.scanl (· + ·) c L).getD (k + 1) 0 = (List.scanl (· + ·) c L).getD k 0 + L.getD k 0 := by
  intro L
  induction L with
  | nil => intro c k hk; simp at hk
  | cons x L' ih =>
    intro c k hk
    cases k with
    | zero => simp [List.scanl_cons]
    | succ k' =>
      have hk' : k' < L'.length := by simpa using hk
      simpa [List.scanl_cons] using ih (c + x) k' hk'

theorem hRev_zip_getD (u : BinaryWord) (k : ℕ) (hk : k + 1 < u.length) :
    ((u.zip u.tail).map fun ab => hRevOffset ab.1 ab.2).getD k 0 =
      hRevOffset (u.getD k Letter.p) (u.getD (k + 1) Letter.p) := by
  have h1 : k < (u.zip u.tail).length := by simp; omega
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]
  simp only [List.getElem_map, List.getElem_zip, List.getElem_tail]
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

theorem hRev_pos_gen (u : BinaryWord) (c : GInt) : ∀ k, k < u.length →
    (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => hRevOffset ab.1 ab.2)).getD k 0 =
      c + posF Orientation.horizontal true (fun j => u.getD j Letter.p) k := by
  intro k
  induction k with
  | zero => intro _; simp [posF]
  | succ k ih =>
    intro hk
    rw [scanl_getD_succ_gen _ c k (by simp; omega), ih (by omega), hRev_zip_getD u k hk]
    simp only [posF, stepOf_hor_rev]
    abel

theorem shift_stack (p : GInt) : p - horizontalStackShift = (1, -2) + p := by
  unfold horizontalStackShift
  apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> omega

theorem zoReversedStackedE_eq (w : BinaryWord) :
    zoReversedStackedE (lettersOf w true) w.length = hRevStringAt w.reverse (1, -2) := by
  have hT : ∀ k, k < w.reverse.length →
      (tileSeq w.reverse).getD k ZTile.zero = hTileAt (lettersOf w true) k := by
    intro k hk
    unfold tileSeq
    rw [tileSeqAux_none_eq, tileSeqAux_getD w.reverse Letter.p k hk]
    simp [hTileAt, hPrev, lettersOf, tlPrev]
  have hP : ∀ k, k < w.reverse.length →
      (List.scanl (· + ·) (1, -2) ((w.reverse.zip w.reverse.tail).map fun ab => hRevOffset ab.1 ab.2)).getD k 0 =
        (1, -2) + posF Orientation.horizontal true (lettersOf w true) k := by
    intro k hk
    rw [hRev_pos_gen w.reverse (1, -2) k hk]
    rfl
  have hlen : (tileSeq w.reverse).length = w.length := by
    simp [tileSeq, tileSeqAux_length]
  unfold zoReversedStackedE hRevStringAt
  refine List.ext_getElem ?_ ?_
  · simp only [List.length_map, List.length_range, List.length_zip, List.length_scanl,
      List.length_tail, List.length_reverse, hlen]
    omega
  · intro k h1 h2
    have hk : k < w.length := by simpa using h1
    have hkR : k < w.reverse.length := by simpa using hk
    have hk1 : k < (tileSeq w.reverse).length := by rw [hlen]; exact hk
    have hk2 : k < (List.scanl (· + ·) (1, -2)
        ((w.reverse.zip w.reverse.tail).map fun ab => hRevOffset ab.1 ab.2)).length := by
      simp only [List.length_scanl, List.length_map, List.length_zip, List.length_tail, List.length_reverse]
      omega
    have e1 := hT k hkR
    have e2 := hP k hkR
    rw [List.getD_eq_getElem _ _ hk1] at e1
    rw [List.getD_eq_getElem _ _ hk2] at e2
    simp only [List.getElem_map, List.getElem_range, List.getElem_zip]
    rw [e1, e2, shift_stack]

/-! ### The last position of a vertical reversed string -/

theorem lastPosOf_cons_ne (x : ZTile × GInt) (L : List (ZTile × GInt)) (h : L ≠ []) :
    lastPosOf (x :: L) = lastPosOf L := by
  cases L with
  | nil => exact absurd rfl h
  | cons y ys => simp [lastPosOf]

theorem vRevStringAt_cons_cons (a b : Letter) (r : BinaryWord) (c : GInt) :
    vRevStringAt (a :: b :: r) c = (letterZTile a, c) :: vRevStringAt (b :: r) (c + vRevOffset a b) := by
  simp [vRevStringAt, List.scanl_cons]

theorem vRev_last_gen : ∀ (u : BinaryWord) (c : GInt), u ≠ [] →
    lastPosOf (vRevStringAt u c) =
      c + ((-((u.dropLast.count Letter.p : ℕ) : ℤ)), ((u.length : ℤ) - 1 + ((u.tail.count Letter.q : ℕ) : ℤ)))
  | [], _, h => absurd rfl h
  | [a], c, _ => by simp [vRevStringAt, lastPosOf]
  | a :: b :: r, c, _ => by
      have hne : vRevStringAt (b :: r) (c + vRevOffset a b) ≠ [] := by
        intro h
        have h2 := vRevStringAt_length (b :: r) (c + vRevOffset a b)
        rw [h] at h2
        simp at h2
      rw [vRevStringAt_cons_cons, lastPosOf_cons_ne _ _ hne, vRev_last_gen (b :: r) _ (List.cons_ne_nil b r)]
      have hd : (a :: b :: r).dropLast = a :: (b :: r).dropLast := rfl
      rw [hd]
      apply Prod.ext
      · cases a <;> cases b <;> simp [vRevOffset] <;> omega
      · cases a <;> cases b <;> simp [vRevOffset] <;> omega

/-! ### The vertical last position for `w_v` from `p` to `q` -/

theorem count_eq_dropLast_add (x : Letter) : ∀ u : BinaryWord, u ≠ [] → u.getLast? = some x →
    u.count x = u.dropLast.count x + 1
  | [], h, _ => absurd rfl h
  | [a], _, hl => by
      simp at hl
      subst hl
      simp
  | a :: b :: r, _, hl => by
      have ih := count_eq_dropLast_add x (b :: r) (List.cons_ne_nil b r) (by simpa using hl)
      have hd : (a :: b :: r).dropLast = a :: (b :: r).dropLast := rfl
      rw [hd]
      by_cases h : a = x
      · subst h
        simp at ih ⊢
        omega
      · simp [h] at ih ⊢
        omega

theorem count_eq_tail_add (x : Letter) (u : BinaryWord) (h : u.head? = some x) :
    u.count x = u.tail.count x + 1 := by
  cases u with
  | nil => simp at h
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    simp

/-- The last position of the vertical reversed string of `w_v.reverse` from `0`, for `w_v` starting with `p` and ending
with `q` (surgical lines 1336-1342, with `n = #q(w_v)`, `d = |w_v|`): `(1 + n - d, n + d - 2) = (1, -2) + v_{n/d,2}`. -/
theorem vRev_last_top (wv : BinaryWord) (hh : wv.head? = some Letter.p) (hl : wv.getLast? = some Letter.q) :
    lastPosOf (vRevStringAt wv.reverse 0) =
      (1 + (wv.count Letter.q : ℤ) - (wv.length : ℤ), (wv.count Letter.q : ℤ) + (wv.length : ℤ) - 2) := by
  have hne : wv ≠ [] := by
    intro h
    subst h
    simp at hh
  have hu : wv.reverse ≠ [] := by simpa using hne
  have hlast : wv.reverse.getLast? = some Letter.p := by
    rw [List.getLast?_reverse]
    exact hh
  have hhead : wv.reverse.head? = some Letter.q := by
    rw [List.head?_reverse]
    exact hl
  rw [vRev_last_gen wv.reverse 0 hu]
  have c1 := count_eq_dropLast_add Letter.p wv.reverse hu hlast
  have c2 : wv.reverse.count Letter.p = wv.count Letter.p := (List.reverse_perm wv).count_eq _
  have c3 := count_eq_tail_add Letter.q wv.reverse hhead
  have c4 : wv.reverse.count Letter.q = wv.count Letter.q := (List.reverse_perm wv).count_eq _
  have c5 := length_eq_counts wv
  have hlen : wv.reverse.length = wv.length := by simp
  rw [zero_add]
  apply Prod.ext
  · dsimp only
    omega
  · dsimp only
    omega

end FLatticePaper.Tiles
