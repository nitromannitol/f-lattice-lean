import FLatticePaper.Tiles.ReversedTopShift
import FLatticePaper.Tiles.CornerAlpha
import FLatticePaper.Tiles.FirstSentenceSurgical
import FLatticePaper.Tiles.PTAffineTransport

/-! The linear hypothesis `hlin` of `PTFamily.hkappa_of_families` for the horizontal Moreover pair, in the frame
`v = -v_{n/d,2}`, `a = -a_{n/d,2}` (paper convention, lead's frame).

The forward family `FA` (on the bottom string `hStringAt wh 0`) is paired with the forward Moreover `P`; the family `FB`
of `S(x - v) + a·x` on the stacked reversed string is paired with the reversed Moreover `M`. Translating `FB` back by `-v`
and removing `a` gives the family `G` of `S` on the top reversed string `hRevStringAt wh.reverse (lastPosOf …)`. The
corner identity `D - A - a_{n/d,2} = (0,1)` (`CornerAlpha.D_sub_A_sub_a2`) then gives `α = γ`. -/

namespace FLatticePaper.Tiles

theorem getD_zero_eq_headD (l : List (ZTile × GInt)) :
    l.getD 0 (ZTile.zero, (0 : GInt)) = l.headD (ZTile.zero, (0 : GInt)) := by
  cases l <;> rfl

theorem hRevStringAt_add (u : BinaryWord) (c e : GInt) :
    hRevStringAt u (c + e) = (hRevStringAt u c).map (fun p => (p.1, p.2 + e)) := by
  unfold hRevStringAt
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

theorem odo_sub_same_ts (F G : PTFamily) (hts : G.ts = F.ts) (k : ℕ) (x : GInt) :
    F.odo k x - G.odo k x =
      ((F.a k).1 - (G.a k).1) * x.1 + ((F.a k).2 - (G.a k).2) * x.2 + (F.b k - G.b k) := by
  unfold PTFamily.odo PTFamily.tile
  rw [hts]
  ring

/-- Two families on the same tile list: an affine relation between their odometers has the affine factors' difference as
its linear part. -/
theorem alpha_eq_of_diff (F G : PTFamily) (hts : G.ts = F.ts) (k : ℕ) (α : GInt) (β : ℤ)
    (h : ∀ x : GInt, F.odo k x = G.odo k x + α.1 * x.1 + α.2 * x.2 + β) :
    α = (F.a k) - (G.a k) := by
  have h0 := h 0
  have d0 := odo_sub_same_ts F G hts k 0
  have h1 := h (1, 0)
  have d1 := odo_sub_same_ts F G hts k (1, 0)
  have h2 := h (0, 1)
  have d2 := odo_sub_same_ts F G hts k (0, 1)
  simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero, zero_add] at h0 d0
  dsimp only at h1 d1 h2 d2
  apply Prod.ext
  · simp only [Prod.fst_sub]
    omega
  · simp only [Prod.snd_sub]
    omega

theorem hlin_horizontal (S : GInt → ℤ) (wh wv : BinaryWord) (n d : ℤ) (v a : GInt)
    (hh : wh.head? = some Letter.q) (hl : wh.getLast? = some Letter.p)
    (hvh : wv.head? = some Letter.p) (hvl : wv.getLast? = some Letter.q)
    (hn : (wv.count Letter.q : ℤ) = n) (hdd : (wv.length : ℤ) = d)
    (hv : v = (-(n - d), -(n + d))) (ha : a = (-n, d))
    (FA P M FB : PTFamily)
    (hFA : ∀ k < FA.n, ∀ x ∈ FA.dom k, S x = FA.odo k x)
    (hFB : ∀ k < FB.n, ∀ x ∈ FB.dom k, S (x - v) + a.1 * x.1 + a.2 * x.2 = FB.odo k x)
    (hPts : P.ts = zoForwardE (lettersOf wh false) wh.length)
    (htsP : P.ts = FA.ts) (htsM : M.ts = FB.ts)
    (hMts : M.ts = zoReversedStackedE (lettersOf wh true) wh.length)
    (hFAR : FA.Respects Orientation.horizontal false) (hFBR : FB.Respects Orientation.horizontal true)
    (hPa : P.a 0 - M.a 0 = (0, -1))
    (hC3 : tileAffine S (cornerTiles wh wv 0).2.2.1 - tileAffine S (cornerTiles wh wv 0).2.1 =
      ((n : ℚ) - 1, 1 - (d : ℚ))) :
    ∀ (α γ : GInt) (β δ : ℤ),
      (∀ k < P.n, ∀ x : GInt, FA.odo k x = P.odo k x + α.1 * x.1 + α.2 * x.2 + β) →
      (∀ j < M.n, ∀ x : GInt, FB.odo j x = M.odo j x + γ.1 * x.1 + γ.2 * x.2 + δ) →
      α = γ := by
  intro α γ β δ hα hγ
  have hwh : wh ≠ [] := by
    intro h
    subst h
    simp at hh
  have hPn : P.n = wh.length := by
    unfold PTFamily.n
    rw [hPts]
    simp [zoForwardE]
  have hMn : M.n = wh.length := by
    unfold PTFamily.n
    rw [hMts]
    simp [zoReversedStackedE]
  have hFAn : FA.n = wh.length := by
    unfold PTFamily.n
    rw [← htsP, hPts]
    simp [zoForwardE]
  have hFBn : FB.n = wh.length := by
    unfold PTFamily.n
    rw [← htsM, hMts]
    simp [zoReversedStackedE]
  have hLpos : 0 < wh.length := List.length_pos_of_ne_nil hwh
  have hP0 : 0 < P.n := by rw [hPn]; exact hLpos
  have hM0 : 0 < M.n := by rw [hMn]; exact hLpos
  have hFA0 : 0 < FA.n := by rw [hFAn]; exact hLpos
  have hFAts : FA.ts = hStringAt wh 0 := by
    rw [← htsP, hPts]
    exact zoForwardE_eq_hStringAt wh
  have hFBts : FB.ts = hRevStringAt wh.reverse (1, -2) := by
    rw [← htsM, hMts]
    exact zoReversedStackedE_eq wh
  -- the translated family `G` of `S` on the top reversed string
  obtain ⟨G, hG⟩ : ∃ G : PTFamily, G = (FB.affineAdd (-a) 0).translate (-v) := ⟨_, rfl⟩
  have hGn : G.n = FB.n := by
    rw [hG, PTFamily.translate_n, PTFamily.affineAdd_n]
  have hG0 : 0 < G.n := by rw [hGn, hFBn]; exact hLpos
  have hpos : lastPosOf (vRevStringAt wv.reverse 0) = (1, -2) + -v := by
    rw [vRev_last_top wv hvh hvl, hn, hdd, hv]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_neg]
      ring
    · simp only [Prod.snd_add, Prod.snd_neg]
      ring
  have hGts : G.ts = hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0)) := by
    have e1 : G.ts = FB.ts.map (fun p => (p.1, p.2 + -v)) := by
      rw [hG]
      rfl
    rw [e1, hFBts, ← hRevStringAt_add, hpos]
  have hGS : ∀ k < G.n, ∀ x ∈ G.dom k, S x = G.odo k x := by
    intro k hk x hx
    have hk' : k < FB.n := by rw [← hGn]; exact hk
    have hkA : k < (FB.affineAdd (-a) 0).n := by rw [PTFamily.affineAdd_n]; exact hk'
    have hdom : G.dom k = (FB.dom k).map (· + -v) := by
      rw [hG, PTFamily.translate_dom _ _ k hkA, PTFamily.affineAdd_dom]
    rw [hdom] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hodo : G.odo k (y + -v) = FB.odo k y + (-a).1 * y.1 + (-a).2 * y.2 + 0 := by
      rw [hG, PTFamily.translate_odo _ _ k hkA, add_sub_cancel_right, PTFamily.affineAdd_odo]
    rw [hodo, ← sub_eq_add_neg]
    have e := hFB k hk' y hy
    simp only [Prod.fst_neg, Prod.snd_neg]
    linear_combination e
  have hGR : G.Respects Orientation.horizontal true := by
    rw [hG]
    exact PTFamily.translate_respects _ _ _ _
      (PTFamily.affineAdd_respects FB Orientation.horizontal true (-a) 0 hFBR)
  have hA : RespectsTiles Orientation.horizontal false (hStringAt wh 0) S := ⟨FA, hFAts, hFA, hFAR⟩
  have hC : RespectsTiles Orientation.horizontal true
      (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))) S := ⟨G, hGts, hGS, hGR⟩
  obtain ⟨hB, hCD⟩ := corner_affine_12 wh wv S hh hl hA hC
  have hK := CornerAlpha.D_sub_A_sub_a2 (tileAffine S (cornerTiles wh wv 0).1)
    (tileAffine S (cornerTiles wh wv 0).2.1) (tileAffine S (cornerTiles wh wv 0).2.2.1)
    (tileAffine S (cornerTiles wh wv 0).2.2.2) (n : ℚ) (d : ℚ) hB hCD hC3
  -- the tiles of the corner are the first tiles of `FA` and `G`
  have hAtile : FA.tile 0 = (cornerTiles wh wv 0).1 := by
    unfold PTFamily.tile
    rw [hFAts, getD_zero_eq_headD]
    rfl
  have hDtile : G.tile 0 = (cornerTiles wh wv 0).2.2.2 := by
    unfold PTFamily.tile
    rw [hGts, getD_zero_eq_headD]
    rfl
  have hSA : tileAffine S (FA.tile 0) = (((FA.a 0).1 : ℚ), ((FA.a 0).2 : ℚ)) :=
    tileAffine_family FA S 0 (fun x hx => hFA 0 hFA0 x hx) (unitSquares_tileShape_ne _)
  have hSD : tileAffine S (G.tile 0) = (((G.a 0).1 : ℚ), ((G.a 0).2 : ℚ)) :=
    tileAffine_family G S 0 (fun x hx => hGS 0 hG0 x hx) (unitSquares_tileShape_ne _)
  rw [← hDtile, ← hAtile, hSD, hSA] at hK
  have k1 : ((G.a 0).1 : ℚ) - ((FA.a 0).1 : ℚ) = (n : ℚ) := by
    have := congrArg Prod.fst hK
    simp at this
    linarith
  have k2 : ((G.a 0).2 : ℚ) - ((FA.a 0).2 : ℚ) = 1 - (d : ℚ) := by
    have := congrArg Prod.snd hK
    simp at this
    linarith
  have i1 : (G.a 0).1 - (FA.a 0).1 = n := by exact_mod_cast k1
  have i2 : (G.a 0).2 - (FA.a 0).2 = 1 - d := by exact_mod_cast k2
  have hGa : G.a 0 = FB.a 0 + -a := by
    rw [hG]
    rfl
  have hGa1 : (G.a 0).1 = (FB.a 0).1 - a.1 := by
    rw [hGa]
    simp only [Prod.fst_add, Prod.fst_neg]
    ring
  have hGa2 : (G.a 0).2 = (FB.a 0).2 - a.2 := by
    rw [hGa]
    simp only [Prod.snd_add, Prod.snd_neg]
    ring
  have ha1 : a.1 = -n := by rw [ha]
  have ha2 : a.2 = d := by rw [ha]
  have hPa1 : (P.a 0).1 - (M.a 0).1 = 0 := by
    have := congrArg Prod.fst hPa
    simpa using this
  have hPa2 : (P.a 0).2 - (M.a 0).2 = -1 := by
    have := congrArg Prod.snd hPa
    simpa using this
  have hαv := alpha_eq_of_diff FA P htsP 0 α β (fun x => hα 0 hP0 x)
  have hγv := alpha_eq_of_diff FB M htsM 0 γ δ (fun x => hγ 0 hM0 x)
  rw [hαv, hγv]
  apply Prod.ext
  · simp only [Prod.fst_sub]
    omega
  · simp only [Prod.snd_sub]
    omega

end FLatticePaper.Tiles
