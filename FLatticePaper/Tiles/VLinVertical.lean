import FLatticePaper.Tiles.HLinHorizontal

/-! The vertical linear hypothesis, in the lead's frame: `v = v_{n/d,1}` and `a = 0`.

The forward family `FA` lies on the right vertical side `vStringAt wv (lastPosOf (hStringAt wh 0))` of the standard tile,
whose first tile is the bottom-right corner `B = lastPosOf (hStringAt wh 0)` (a zero tile). The reversed family `FB` lies on
the left side of the translate `T + v`, which is `vRevStringAt wv.reverse v`; translating back by `-v` gives the family `G`
of `S` on the left side `vRevStringAt wv.reverse 0`, whose first tile is the bottom-left corner `A = (one, 0)`. The Moreover
offset is `P.a 0 = M.a 0` (`VerticalMoreover`), so `alpha = gamma` is `tileAffine(B) = tileAffine(A)`, which is `corner_fwd`. -/

namespace FLatticePaper.Tiles

theorem vStringAt_length (w : BinaryWord) (c : GInt) : (vStringAt w c).length = w.length := by
  unfold vStringAt
  simp only [List.length_zip, List.length_map, List.length_scanl, List.length_tail]
  omega

theorem vRevStringAt_add (u : BinaryWord) (c e : GInt) :
    vRevStringAt u (c + e) = (vRevStringAt u c).map (fun p => (p.1, p.2 + e)) := by
  unfold vRevStringAt
  have hs : ∀ (L : List GInt) (c : GInt),
      List.scanl (· + ·) (c + e) L = (List.scanl (· + ·) c L).map (· + e) := by
    intro L
    induction L with
    | nil => intro c; simp
    | cons x L' ih =>
      intro c
      simp only [List.scanl_cons, List.map_cons]
      congr 1
      rw [show c + e + x = c + x + e by abel]
      exact ih (c + x)
  rw [hs, List.zip_map_right]
  congr 1

theorem scan_cons_eq (c : GInt) (L : List GInt) : ∃ t, List.scanl (· + ·) c L = c :: t := by
  cases L with
  | nil => exact ⟨[], rfl⟩
  | cons x L' => exact ⟨_, List.scanl_cons⟩

theorem vRevStringAt_headD_q (u : BinaryWord) (c : GInt) (h : u.head? = some Letter.q) :
    (vRevStringAt u c).headD (ZTile.zero, 0) = (ZTile.one, c) := by
  cases u with
  | nil => simp at h
  | cons a l =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    obtain ⟨t, ht⟩ := scan_cons_eq c
      (List.map (fun ab => vRevOffset ab.1 ab.2) ((Letter.q :: l).zip (Letter.q :: l).tail))
    unfold vRevStringAt
    rw [ht]
    simp [letterZTile]

theorem vStringAt_headD_p (u : BinaryWord) (c : GInt) (h : u.head? = some Letter.p) :
    (vStringAt u c).headD (ZTile.zero, 0) = (ZTile.zero, c) := by
  cases u with
  | nil => simp at h
  | cons a l =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    obtain ⟨t, ht⟩ := scan_cons_eq c (List.map vOffset (List.tail (Letter.p :: l)))
    unfold vStringAt
    rw [ht]
    simp [letterZTile]

theorem hStringAt_length (w : BinaryWord) (c : GInt) : (hStringAt w c).length = w.length := by
  unfold hStringAt
  simp only [List.length_zip, tileSeq, tileSeqAux_length, List.length_scanl, List.length_map, List.length_tail]
  omega

theorem hStringAt_map_fst (w : BinaryWord) (c : GInt) : (hStringAt w c).map Prod.fst = tileSeq w := by
  unfold hStringAt
  apply List.map_fst_zip
  simp only [List.length_scanl, List.length_map, List.length_tail, tileSeq, tileSeqAux_length]
  omega

theorem hStringAt_getD_fst (w : BinaryWord) (c : GInt) (i : ℕ) :
    ((hStringAt w c).getD i (ZTile.zero, (0 : GInt))).1 = (tileSeq w).getD i ZTile.zero := by
  have e1 : ((hStringAt w c).map Prod.fst).getD i ZTile.zero =
      ((hStringAt w c).getD i (ZTile.zero, (0 : GInt))).1 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    generalize (hStringAt w c)[i]? = o
    cases o <;> simp
  rw [← e1, hStringAt_map_fst]

/-- The last tile of a horizontal string whose word ends with `p` is a zero tile. -/
theorem tileSeq_getD_last_zero (w : BinaryWord) (hw : w ≠ []) (hl : w.getLast? = some Letter.p) :
    (tileSeq w).getD (w.length - 1) ZTile.zero = ZTile.zero := by
  have hi : w.length - 1 < w.length := by
    have := List.length_pos_of_ne_nil hw
    omega
  have hp : w.getD (w.length - 1) Letter.p = Letter.p := by
    rw [List.getD_eq_getElem _ _ hi]
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hi] at hl
    exact Option.some.inj hl
  unfold tileSeq
  rw [tileSeqAux_none_eq, tileSeqAux_getD w Letter.p (w.length - 1) hi, hp]
  generalize tlPrev Letter.p w (w.length - 1) = x
  cases x <;> rfl

/-- The bottom-right corner: the last tile of the forward horizontal string is a zero tile at its last position. -/
theorem hStringAt_getLastD_zero (w : BinaryWord) (c : GInt) (hw : w ≠ []) (hl : w.getLast? = some Letter.p) :
    (hStringAt w c).getLastD (ZTile.zero, 0) = (ZTile.zero, lastPosOf (hStringAt w c)) := by
  rw [getLastD_eq_getD', lastPosOf_eq_getD]
  have key : ((hStringAt w c).getD ((hStringAt w c).length - 1) (ZTile.zero, (0 : GInt))).1 = ZTile.zero := by
    rw [hStringAt_length, hStringAt_getD_fst, tileSeq_getD_last_zero w hw hl]
  exact Prod.ext key rfl

/-- The vertical linear hypothesis in the frame `v = v_{n/d,1}`, `a = 0`. -/
theorem vlin_vertical (S : GInt → ℤ) (wh wv : BinaryWord) (v : GInt)
    (hh : wh.head? = some Letter.q) (hl : wh.getLast? = some Letter.p)
    (hvh : wv.head? = some Letter.p) (hvl : wv.getLast? = some Letter.q)
    (hBv : lastPosOf (hStringAt wh 0) = v + (-1, -1))
    (hA : RespectsTiles Orientation.horizontal false (hStringAt wh 0) S)
    (FA P M FB : PTFamily)
    (hFA : ∀ k < FA.n, ∀ x ∈ FA.dom k, S x = FA.odo k x)
    (hFB : ∀ k < FB.n, ∀ x ∈ FB.dom k, S (x - v) = FB.odo k x)
    (htsFA : FA.ts = vStringAt wv (lastPosOf (hStringAt wh 0)))
    (htsP : P.ts = FA.ts) (htsM : M.ts = FB.ts)
    (hFBts : FB.ts = vRevStringAt wv.reverse v)
    (hPM : P.a 0 = M.a 0) :
    ∀ (α γ : GInt) (β δ : ℤ),
      (∀ k < P.n, ∀ x : GInt, FA.odo k x = P.odo k x + α.1 * x.1 + α.2 * x.2 + β) →
      (∀ j < M.n, ∀ x : GInt, FB.odo j x = M.odo j x + γ.1 * x.1 + γ.2 * x.2 + δ) →
      α = γ := by
  intro α γ β δ hα hγ
  have hwv : wv ≠ [] := by
    intro h
    subst h
    simp at hvh
  have hwh : wh ≠ [] := by
    intro h
    subst h
    simp at hh
  have hFAn : FA.n = wv.length := by
    unfold PTFamily.n
    rw [htsFA, vStringAt_length]
  have hFBn : FB.n = wv.length := by
    unfold PTFamily.n
    rw [hFBts, vRevStringAt_length, List.length_reverse]
  have hPn : P.n = FA.n := by
    unfold PTFamily.n
    rw [htsP]
  have hMn : M.n = FB.n := by
    unfold PTFamily.n
    rw [htsM]
  have hLpos : 0 < wv.length := List.length_pos_of_ne_nil hwv
  have hFA0 : 0 < FA.n := by rw [hFAn]; exact hLpos
  have hP0 : 0 < P.n := by rw [hPn]; exact hFA0
  have hM0 : 0 < M.n := by rw [hMn, hFBn]; exact hLpos
  -- the translate of `FB` back by `-v`, a family of `S` on the left side `vRevStringAt wv.reverse 0`
  obtain ⟨G, hG⟩ : ∃ G : PTFamily, G = FB.translate (-v) := ⟨_, rfl⟩
  have hGn : G.n = FB.n := by
    rw [hG, PTFamily.translate_n]
  have hG0 : 0 < G.n := by rw [hGn, hFBn]; exact hLpos
  have hGts : G.ts = vRevStringAt wv.reverse 0 := by
    have e : G.ts = FB.ts.map (fun p => (p.1, p.2 + -v)) := by
      rw [hG]
      rfl
    rw [e, hFBts, ← vRevStringAt_add, add_neg_cancel]
  have hGS : ∀ k < G.n, ∀ x ∈ G.dom k, S x = G.odo k x := by
    intro k hk x hx
    have hk' : k < FB.n := by rw [← hGn]; exact hk
    have hdom : G.dom k = (FB.dom k).map (· + -v) := by
      rw [hG, PTFamily.translate_dom _ _ k hk']
    rw [hdom] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hodo : G.odo k (y + -v) = FB.odo k y := by
      rw [hG, PTFamily.translate_odo _ _ k hk', add_sub_cancel_right]
    rw [hodo, ← sub_eq_add_neg]
    exact hFB k hk' y hy
  have hGtile : G.tile 0 = (ZTile.one, 0) := by
    unfold PTFamily.tile
    rw [hGts, getD_zero_eq_headD, vRevStringAt_headD_q wv.reverse 0 (by rw [List.head?_reverse]; exact hvl)]
  have hFAtile : FA.tile 0 = (ZTile.zero, lastPosOf (hStringAt wh 0)) := by
    unfold PTFamily.tile
    rw [htsFA, getD_zero_eq_headD, vStringAt_headD_p wv _ hvh]
  have hcf := corner_fwd wh S hA
  rw [hStringAt_getLastD_zero wh 0 hwh hl, hStringAt_head_q wh 0 hh] at hcf
  have hFAa : tileAffine S (FA.tile 0) = (((FA.a 0).1 : ℚ), ((FA.a 0).2 : ℚ)) :=
    tileAffine_family FA S 0 (fun x hx => hFA 0 hFA0 x hx) (unitSquares_tileShape_ne _)
  have hGa : tileAffine S (G.tile 0) = (((G.a 0).1 : ℚ), ((G.a 0).2 : ℚ)) :=
    tileAffine_family G S 0 (fun x hx => hGS 0 hG0 x hx) (unitSquares_tileShape_ne _)
  rw [hFAtile] at hFAa
  rw [hGtile] at hGa
  have hFAG : FA.a 0 = G.a 0 := by
    have h := hFAa.symm.trans (hcf.trans hGa)
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    apply Prod.ext
    · exact_mod_cast h1
    · exact_mod_cast h2
  have hGFB : G.a 0 = FB.a 0 := by
    rw [hG]
    rfl
  have hαv := alpha_eq_of_diff FA P htsP 0 α β (fun x => hα 0 hP0 x)
  have hγv := alpha_eq_of_diff FB M htsM 0 γ δ (fun x => hγ 0 hM0 x)
  rw [hαv, hγv, hPM, ← hGFB, hFAG]

end FLatticePaper.Tiles
