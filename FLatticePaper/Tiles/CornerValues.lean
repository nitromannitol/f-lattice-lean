import FLatticePaper.Tiles.VerticalStepOne

/-! # The corner values `eq:std_corner_values` from the boundary strings

Surgical edition 274ad18, proof of `lemma:tile-odometer-existence`, first paragraph: for an odometer that respects
`(w_h(n/d), w_v(n/d))` (`RespectsAnchored`), normalised so that it is `o_{1/1}` on the first tile `A` at `c(T) = 0`, the formula
for horizontal strings along `w_h` gives `o(0) = o(1) = o(X - i) = o(X) = 0`, and the formula for vertical strings along
`rev(w_v)` (from `A`, so `a_0 = 0` and `K^- = 0`) on the tile `D` at `c(D) = Y + 1 - 2i`, and along `w_v` (from the last bottom tile
`B` at `X - 1 - i`) on the tile `C` at `c(C) = X + Y - 2i`, with the shift identities of `h_0`, give
`o(Y + 1) = F(Y) + e_1`, `o(Y + 1 - i) = o(D_{n/d}) = F(Y) + e_1 - e_2`, `o(D_{n/d} - 1) = F(Y) - e_2`, where `X = v_{n/d,1}`,
`Y = v_{n/d,2} = (n - d, n + d)`, `e = a_{n/d,2} = (n, -d)`, `F = -h_0`, `D_{n/d} = X + Y + 1 - i`.

The positions of the last tiles of the strings (`hX`, `hY`, `hC`) and the parity of `X` are hypotheses, as in
`ClosedPathCorners.corner_diffs`. The result `std_corner_values` gives `StdCornerValues`, so with `tileTranslation_of_corners`
(a) of `lemma:tile-odometer-existence` follows from (c) of the weak lemma. -/

namespace FLatticePaper.Tiles.CornerValues

open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily (normed FirstTileNormal h0)
open FLatticePaper.Tiles.TileTranslation (StdCornerValues)
open FLatticePaper.Tiles.HorizontalStepOne (bottom_corner_values)
open FLatticePaper.Tiles.VerticalStepOne
open FLatticePaper.Tiles.SurgicalWeak (RespectsAnchored)

/-- `ℓ(v)` of the shift identity of `h_0`. -/
def ellOf (v : GInt) : GInt := ((-v.1 - v.2) / 2, (v.2 - v.1) / 2)

theorem h0_shift (x v : GInt) (hv : (v.1 + v.2) % 2 = 0) :
    zoH0 (x + v) = zoH0 x + (ellOf v).1 * x.1 + (ellOf v).2 * x.2 + zoH0 v := by
  have := zoH0_shift_even x v (ellOf v).1 (ellOf v).2 (by unfold ellOf; omega) (by unfold ellOf; omega) hv
  linarith

theorem vAux_last_fst (rev : Bool) : ∀ (w : BinaryWord) (c : GInt),
    (vAux rev w c).getLast?.map (·.1) = w.getLast?.map letterZTile := by
  intro w
  induction w with
  | nil => intro c; rfl
  | cons a rest ih =>
    intro c
    cases rest with
    | nil => rfl
    | cons b rest' =>
      have := ih (c + stepV rev a b)
      have hh : ∃ tl, vAux rev (b :: rest') (c + stepV rev a b) = (letterZTile b, c + stepV rev a b) :: tl := by
        cases rest' <;> exact ⟨_, rfl⟩
      obtain ⟨tl, htl⟩ := hh
      show (((letterZTile a, c) :: vAux rev (b :: rest') (c + stepV rev a b)).getLast?.map (·.1)) = _
      rw [htl] at this ⊢
      simpa [List.getLast?_cons_cons] using this

/-- The last element of a list of placed tiles, from the type of its last tile and `lastPosOf`. -/
theorem getD_last (L : List (ZTile × GInt)) (t : ZTile) (P : GInt) (ht : L.getLast?.map (·.1) = some t)
    (hP : lastPosOf L = P) : L.getD (L.length - 1) (ZTile.zero, 0) = (t, P) := by
  rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]
  cases h : L.getLast? with
  | none => rw [h] at ht; simp at ht
  | some e =>
    rw [h] at ht
    unfold lastPosOf at hP
    rw [h] at hP
    simp only [Option.map_some, Option.some.injEq, Option.getD_some] at ht hP ⊢
    exact Prod.ext ht hP

theorem getD_mem_of_lt (L : List (ZTile × GInt)) (k : ℕ) (h : k < L.length) : L.getD k (ZTile.zero, 0) ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

theorem len_pos_of_ne {L : List (ZTile × GInt)} {t : ZTile} (ht : L.getLast?.map (·.1) = some t) : 0 < L.length := by
  cases L with
  | nil => simp at ht
  | cons _ _ => simp

/-- **`eq:std_corner_values`** for an odometer respecting `(w_h, w_v)`, from the four boundary-string formulas of Step 1. -/
theorem std_corner_values (o : PartialOdometer) (wh wv : BinaryWord) (n d : ℤ) (X : GInt)
    (hR : RespectsAnchored o.dom wh wv o.val)
    (hhh : wh.head? = some Letter.q) (hhl : wh.getLast? = some Letter.p)
    (hvh : wv.head? = some Letter.p) (hvl : wv.getLast? = some Letter.q)
    (hX : lastPosOf (hStringAt wh 0) = X - (1, 1))
    (hY : lastPosOf (vRevStringAt wv.reverse 0) = (n - d, n + d) + (1, -2))
    (hC : lastPosOf (vStringAt wv (X - (1, 1))) = X + (n - d, n + d) + (0, -2))
    (hXp : (X.1 + X.2) % 2 = 0) :
    ∃ (α : GInt) (β : ℤ), FirstTileNormal o α β ∧ StdCornerValues o α β X (n - d, n + d) (n, -d) := by
  obtain ⟨hIn, hH, -, hVm, hVp⟩ := hR
  rw [hX] at hVp hIn
  set Y : GInt := (n - d, n + d) with hYdef
  -- the bottom string
  obtain ⟨α, β, hA, h0v, h1v, hXiv, hXv, hB⟩ := bottom_corner_values wh o.val X hhh hhl hX hH
  have mem : ∀ x, x ∈ placedSites (hStringAt wh 0 ++ hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0)) ++
      vRevStringAt wv.reverse 0 ++ vStringAt wv (X - (1, 1))) → x ∈ o.dom := fun x hx => hIn x hx
  have memL : ∀ (ts : List (ZTile × GInt)) (t : ZTile × GInt), t ∈ ts → ∀ u ∈ tileShape t.1,
      t.2 + u ∈ placedSites ts := by
    intro ts t ht u hu
    unfold placedSites
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨t, ht, u, hu, add_comm u t.2⟩
  have memApp : ∀ x, (x ∈ placedSites (hStringAt wh 0) ∨ x ∈ placedSites (vRevStringAt wv.reverse 0) ∨
      x ∈ placedSites (vStringAt wv (X - (1, 1)))) → x ∈ o.dom := by
    intro x hx
    apply mem
    unfold placedSites at hx ⊢
    simp only [List.flatMap_append, List.mem_append] at hx ⊢
    rcases hx with h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hFN : FirstTileNormal o α β := by
    intro x hx
    refine ⟨memApp x (Or.inl ?_), by unfold normed dotS; have := hA x hx; unfold ptDot at this; linarith⟩
    have hmemA : (ZTile.one, (0 : GInt)) ∈ hStringAt wh 0 := by
      obtain ⟨rest, rfl⟩ : ∃ rest, wh = Letter.q :: rest := by
        cases wh with
        | nil => simp at hhh
        | cons a rest => simp only [List.head?_cons, Option.some.injEq] at hhh; exact ⟨rest, by rw [hhh]⟩
      rw [HorizontalStepOne.hStringAt_eq]
      cases rest <;> exact List.mem_cons_self
    have := memL (hStringAt wh 0) (ZTile.one, 0) hmemA x hx
    simpa using this
  refine ⟨α, β, hFN, ?_⟩
  -- the left string `rev(w_v)` from `A`
  have hwvr : wv.reverse ≠ [] := by intro h; rw [List.reverse_eq_nil_iff] at h; subst h; simp at hvh
  have hpar1 : ((0 : GInt) - cstarV (wv.reverse.headD Letter.p) true).1 +
      ((0 : GInt) - cstarV (wv.reverse.headD Letter.p) true).2 = 0 := by
    have : wv.reverse.headD Letter.p = Letter.q := by
      rw [List.headD_eq_head?_getD, List.head?_reverse, hvl]; rfl
    rw [this]; rfl
  obtain ⟨a1, K1, hL⟩ := reversed_vertical_formula wv.reverse 0 o.val hwvr hVm (by rw [hpar1]; rfl)
  have hfirstL : (vRevStringAt wv.reverse 0).getD 0 (ZTile.zero, 0) = (ZTile.one, 0) := by
    obtain ⟨a, rest, hr⟩ : ∃ a rest, wv.reverse = a :: rest := by
      cases h : wv.reverse with
      | nil => exact absurd h hwvr
      | cons a rest => exact ⟨a, rest, rfl⟩
    have ha : a = Letter.q := by
      have := congrArg List.head? hr
      rw [List.head?_reverse, hvl] at this
      simpa using this.symm
    rw [hr, vRevStringAt_eq, vAux_head, ha]; rfl
  have hlenL : 0 < (vRevStringAt wv.reverse 0).length := by
    rw [vRevStringAt_eq]; apply len_pos_of_ne (t := letterZTile (wv.head?.getD Letter.p))
    rw [vAux_last_fst, List.getLast?_reverse, hvh]; rfl
  have eA : ∀ u ∈ tileShape ZTile.one, o.val u + zoH0 u - (a1.1 * u.1 + a1.2 * u.2) = K1 := by
    intro u hu
    have := hL 0 hlenL u (by rw [hfirstL]; exact hu)
    rw [hfirstL] at this
    simpa [vV, zTileLetter] using this
  have eA00 := eA (0, 0) (by decide)
  have eA10 := eA (1, 0) (by decide)
  have eA01 := eA (0, 1) (by decide)
  have oA00 := hA (0, 0) (by decide)
  have oA10 := hA (1, 0) (by decide)
  have oA01 := hA (0, 1) (by decide)
  have z00 : zoH0 (0, 0) = 0 := by decide
  have z10 : zoH0 (1, 0) = 0 := by decide
  have z01 : zoH0 (0, 1) = 1 := by decide
  have t00 : zTileOdo ZTile.one (0, 0) = 0 := by decide
  have t10 : zTileOdo ZTile.one (1, 0) = 0 := by decide
  have t01 : zTileOdo ZTile.one (0, 1) = -1 := by decide
  unfold ptDot at oA00 oA10 oA01
  simp only [z00, z10, z01, t00, t10, t01] at eA00 eA10 eA01 oA00 oA10 oA01
  have hK1 : K1 = β := by linarith
  have ha11 : a1.1 = α.1 := by linarith
  have ha12 : a1.2 = α.2 := by linarith
  -- the tile `D` at the top of the left string
  have hDt : (vRevStringAt wv.reverse 0).getD ((vRevStringAt wv.reverse 0).length - 1) (ZTile.zero, 0) =
      (ZTile.zero, Y + (1, -2)) := by
    apply getD_last _ _ _ _ hY
    rw [vRevStringAt_eq, vAux_last_fst, List.getLast?_reverse, hvh]; rfl
  have eD : ∀ u ∈ tileShape ZTile.zero, o.val (Y + (1, -2) + u) + zoH0 (Y + (1, -2) + u) -
      (α.1 * (Y + (1, -2) + u).1 + α.2 * (Y + (1, -2) + u).2) = vV Letter.p true u + β := by
    intro u hu
    have := hL ((vRevStringAt wv.reverse 0).length - 1) (by omega) u (by rw [hDt]; exact hu)
    rw [hDt, ha11, ha12, hK1] at this
    simpa [zTileLetter] using this
  have memD : ∀ u ∈ tileShape ZTile.zero, Y + (1, -2) + u ∈ o.dom := by
    intro u hu
    refine memApp _ (Or.inr (Or.inl ?_))
    have := memL (vRevStringAt wv.reverse 0) _
      (getD_mem_of_lt _ ((vRevStringAt wv.reverse 0).length - 1) (by omega)) u (by rw [hDt]; exact hu)
    rw [hDt] at this
    exact this
  -- the right string `w_v` from `B`
  have hwv : wv ≠ [] := by intro h; subst h; simp at hvh
  have hpar2 : ((X - (1, 1) - cstarV (wv.headD Letter.p) false).1 + (X - (1, 1) - cstarV (wv.headD Letter.p) false).2) % 2
      = 0 := by
    have : wv.headD Letter.p = Letter.p := by rw [List.headD_eq_head?_getD, hvh]; rfl
    rw [this]
    simp only [cstarV, Prod.fst_sub, Prod.snd_sub]
    omega
  obtain ⟨a2, K2, hRt⟩ := vertical_formula wv (X - (1, 1)) o.val hwv hVp hpar2
  have hfirstR : (vStringAt wv (X - (1, 1))).getD 0 (ZTile.zero, 0) = (ZTile.zero, X - (1, 1)) := by
    obtain ⟨a, rest, rfl⟩ : ∃ a rest, wv = a :: rest := by
      cases wv with
      | nil => exact absurd rfl hwv
      | cons a rest => exact ⟨a, rest, rfl⟩
    simp only [List.head?_cons, Option.some.injEq] at hvh
    rw [vStringAt_eq, vAux_head, hvh]; rfl
  have hlenR : 0 < (vStringAt wv (X - (1, 1))).length := by
    rw [vStringAt_eq]; apply len_pos_of_ne (t := letterZTile (wv.getLast?.getD Letter.q))
    rw [vAux_last_fst, hvl]; rfl
  have eB : ∀ u ∈ tileShape ZTile.zero, o.val (X - (1, 1) + u) + zoH0 (X - (1, 1) + u) -
      (a2.1 * (X - (1, 1) + u).1 + a2.2 * (X - (1, 1) + u).2) = vV Letter.p false u + K2 := by
    intro u hu
    have := hRt 0 hlenR u (by rw [hfirstR]; exact hu)
    rw [hfirstR] at this
    simpa [zTileLetter] using this
  have hCt : (vStringAt wv (X - (1, 1))).getD ((vStringAt wv (X - (1, 1))).length - 1) (ZTile.zero, 0) =
      (ZTile.one, X + Y + (0, -2)) := by
    apply getD_last _ _ _ _ hC
    rw [vStringAt_eq, vAux_last_fst, hvl]; rfl
  have eC : ∀ u ∈ tileShape ZTile.one, o.val (X + Y + (0, -2) + u) + zoH0 (X + Y + (0, -2) + u) -
      (a2.1 * (X + Y + (0, -2) + u).1 + a2.2 * (X + Y + (0, -2) + u).2) = K2 := by
    intro u hu
    have := hRt ((vStringAt wv (X - (1, 1))).length - 1) (by omega) u (by rw [hCt]; exact hu)
    rw [hCt] at this
    simpa [zTileLetter, vV] using this
  have memC : ∀ u ∈ tileShape ZTile.one, X + Y + (0, -2) + u ∈ o.dom := by
    intro u hu
    refine memApp _ (Or.inr (Or.inr ?_))
    have := memL (vStringAt wv (X - (1, 1))) _
      (getD_mem_of_lt _ ((vStringAt wv (X - (1, 1))).length - 1) (by omega)) u (by rw [hCt]; exact hu)
    rw [hCt] at this
    exact this
  -- the affine factor and the constant of the right string, from the tile `B`
  have hBo : ∀ y ∈ tileShape ZTile.zero, o.val (X - (1, 1) + y) - ptDot α (X - (1, 1) + y) - β = zTileOdo ZTile.zero y :=
    fun y hy => by rw [add_comm (X - (1, 1)) y]; exact hB y hy
  have eB00 := eB (0, 0) (by decide)
  have eB10 := eB (1, 0) (by decide)
  have eB01 := eB (0, 1) (by decide)
  have oB00 := hBo (0, 0) (by decide)
  have oB10 := hBo (1, 0) (by decide)
  have oB01 := hBo (0, 1) (by decide)
  have sh : ∀ y : GInt, zoH0 (X - (1, 1) + y) = zoH0 (y - (1, 1)) + (ellOf X).1 * (y - (1, 1)).1 +
      (ellOf X).2 * (y - (1, 1)).2 + zoH0 X := by
    intro y
    have e : X - (1, 1) + y = (y - (1, 1)) + X := by abel
    rw [e, h0_shift _ X hXp]
  rw [sh] at eB00 eB10 eB01
  have zm11 : zoH0 ((0, 0) - (1, 1)) = -1 := by decide
  have zm01 : zoH0 ((1, 0) - (1, 1)) = 0 := by decide
  have zm10 : zoH0 ((0, 1) - (1, 1)) = 0 := by decide
  have tz00 : zTileOdo ZTile.zero (0, 0) = 0 := by decide
  have tz10 : zTileOdo ZTile.zero (1, 0) = 0 := by decide
  have tz01 : zTileOdo ZTile.zero (0, 1) = 0 := by decide
  have v00 : vV Letter.p false (0, 0) = -1 := by decide
  have v10 : vV Letter.p false (1, 0) = 0 := by decide
  have v01 : vV Letter.p false (0, 1) = 0 := by decide
  rw [zm11, v00] at eB00
  rw [zm01, v10] at eB10
  rw [zm10, v01] at eB01
  rw [tz00] at oB00
  rw [tz10] at oB10
  rw [tz01] at oB01
  unfold ptDot at oB00 oB10 oB01
  norm_num at eB00 eB10 eB01 oB00 oB10 oB01
  have ha21 : a2.1 = α.1 + (ellOf X).1 := by linear_combination eB00 - eB10 + oB10 - oB00
  have ha22 : a2.2 = α.2 + (ellOf X).2 := by linear_combination eB00 - eB01 + oB01 - oB00
  have hK2 : K2 = β + zoH0 X - ((ellOf X).1 * X.1 + (ellOf X).2 * X.2) := by
    rw [ha21, ha22] at eB00
    linear_combination -eB00 + oB00
  -- the values at the top corners
  have hYp : (Y.1 + Y.2) % 2 = 0 := by rw [hYdef]; simp only; omega
  have ellY : ellOf Y = (-n, d) := by
    rw [hYdef]; unfold ellOf; ext <;> simp <;> omega
  have shY : ∀ y : GInt, zoH0 (y + Y) = zoH0 y + (-n) * y.1 + d * y.2 + zoH0 Y := by
    intro y; rw [h0_shift y Y hYp, ellY]
  have shX : ∀ y : GInt, zoH0 (y + X) = zoH0 y + (ellOf X).1 * y.1 + (ellOf X).2 * y.2 + zoH0 X :=
    fun y => h0_shift y X hXp
  have hh : h0 Y = zoH0 Y := rfl
  have memB : ∀ u ∈ tileShape ZTile.zero, X - (1, 1) + u ∈ o.dom := by
    intro u hu
    refine memApp _ (Or.inr (Or.inr ?_))
    have := memL (vStringAt wv (X - (1, 1))) _ (getD_mem_of_lt _ 0 hlenR) u (by rw [hfirstR]; exact hu)
    rw [hfirstR] at this
    exact this
  have pt : ∀ (a b c : GInt), a = b + c → b + c = a := fun _ _ _ h => h.symm
  have p3 : X - (1, 1) + (1, 0) = X - (0, 1) := by ext <;> simp
  have p4 : X - (1, 1) + (1, 1) = X := by ext <;> simp
  have p5 : Y + (1, -2) + (0, 2) = Y + (1, 0) := by ext <;> simp
  have p6 : Y + (1, -2) + (0, 1) = Y + (1, -1) := by ext <;> first | (simp; done) | (simp; ring)
  have p7 : X + Y + (0, -2) + (1, 1) = X + Y + (1, -1) := by
    ext <;> first | (simp; done) | (simp; ring)
  have p8 : X + Y + (0, -2) + (0, 1) = X + Y + (1, -1) - (1, 0) := by
    ext <;> first | (simp; done) | (simp; ring)
  have eD02 := eD (0, 2) (by decide)
  have eD01 := eD (0, 1) (by decide)
  have eC11 := eC (1, 1) (by decide)
  have eC01 := eC (0, 1) (by decide)
  rw [p5] at eD02
  rw [p6] at eD01
  rw [p7] at eC11
  rw [p8] at eC01
  have vD02 : vV Letter.p true (0, 2) = 0 := by decide
  have vD01 : vV Letter.p true (0, 1) = 0 := by decide
  rw [vD02] at eD02
  rw [vD01] at eD01
  have s5 := shY (1, 0)
  have s6 := shY (1, -1)
  have s8 := shY (0, -1)
  have z10' : zoH0 (1, 0) = 0 := by decide
  have z1m : zoH0 (1, -1) = 0 := by decide
  have z0m : zoH0 (0, -1) = 0 := by decide
  rw [z10', add_comm (1, 0) Y] at s5
  rw [z1m, add_comm (1, -1) Y] at s6
  rw [z0m, add_comm (0, -1) Y] at s8
  have s7 := shX (Y + (1, -1))
  have s7' := shX (Y + (0, -1))
  have e7 : Y + (1, -1) + X = X + Y + (1, -1) := by abel
  have e8 : Y + (0, -1) + X = X + Y + (1, -1) - (1, 0) := by
    ext <;> first | (simp; done) | (simp; ring)
  rw [e7] at s7
  rw [e8] at s7'
  norm_num at eD02 eD01 eC11 eC01 s5 s6 s8 s7 s7'
  refine ⟨⟨(hFN (0, 0) (by decide)).1, ?_⟩, ⟨(hFN (1, 0) (by decide)).1, ?_⟩,
    ⟨by rw [← p3]; exact memB (1, 0) (by decide), ?_⟩, ⟨by rw [← p4]; exact memB (1, 1) (by decide), ?_⟩,
    ⟨by rw [← p5]; exact memD (0, 2) (by decide), ?_⟩, ⟨by rw [← p6]; exact memD (0, 1) (by decide), ?_⟩,
    ⟨by rw [← p7]; exact memC (1, 1) (by decide), ?_⟩, ⟨by rw [← p8]; exact memC (0, 1) (by decide), ?_⟩⟩
  · unfold normed dotS; unfold ptDot at h0v; linarith
  · unfold normed dotS; unfold ptDot at h1v; linarith
  · unfold normed dotS; unfold ptDot at hXiv; linarith
  · unfold normed dotS; unfold ptDot at hXv; linarith
  · unfold normed dotS; rw [hh]
    simp only [Prod.fst_add, Prod.snd_add]
    linarith
  · unfold normed dotS; rw [hh]
    simp only [Prod.fst_add, Prod.snd_add]
    linarith
  · unfold normed dotS
    rw [ha21, ha22, hK2] at eC11
    generalize zoH0 (X + Y + (1, -1)) = zD at eC11 s7
    generalize zoH0 (Y + (1, -1)) = zZ at s6 s7
    generalize zoH0 X = zX at eC11 s7
    rw [hh]
    generalize zoH0 Y = zY at s6 ⊢
    norm_num at eC11 ⊢
    linear_combination eC11 - s7 - s6
  · unfold normed dotS
    rw [ha21, ha22, hK2] at eC01
    generalize zoH0 (X + Y + (1, -1) - (1, 0)) = zD at eC01 s7'
    generalize zoH0 (Y + (0, -1)) = zZ at s8 s7'
    generalize zoH0 X = zX at eC01 s7'
    rw [hh]
    generalize zoH0 Y = zY at s8 ⊢
    norm_num at eC01 ⊢
    linear_combination eC01 - s7' - s8

/-- (a) of `lemma:tile-odometer-existence` for an odometer respecting `(w_h, w_v)`: from the corner values and the compatibility of
lattice adjacent copies ((c) of the weak lemma) in both directions. -/
theorem tileTranslation_of_respects (o : PartialOdometer) (wh wv : BinaryWord) (n d : ℤ) (X : GInt)
    (hR : RespectsAnchored o.dom wh wv o.val)
    (hhh : wh.head? = some Letter.q) (hhl : wh.getLast? = some Letter.p)
    (hvh : wv.head? = some Letter.p) (hvl : wv.getLast? = some Letter.q)
    (hX : lastPosOf (hStringAt wh 0) = X - (1, 1))
    (hY : lastPosOf (vRevStringAt wv.reverse 0) = (n - d, n + d) + (1, -2))
    (hC : lastPosOf (vStringAt wv (X - (1, 1))) = X + (n - d, n + d) + (0, -2))
    (hXp : (X.1 + X.2) % 2 = 0)
    (hcX : JointFamily.LatticeSelfCompatible o X 0) (hcY : JointFamily.LatticeSelfCompatible o (n - d, n + d) (n, -d)) :
    JointFamily.TileTranslation o X (n - d, n + d) (n, -d) := by
  obtain ⟨α, β, hN, hV⟩ := std_corner_values o wh wv n d X hR hhh hhl hvh hvl hX hY hC hXp
  exact TileTranslation.tileTranslation_of_corners o X _ _ α β hN hV hcX hcY

end FLatticePaper.Tiles.CornerValues
