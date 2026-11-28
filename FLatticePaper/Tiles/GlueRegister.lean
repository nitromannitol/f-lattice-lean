import FLatticePaper.Tiles.GlueEnds

/-! # The end tiles and the affine factors of the four families of a register

For a register odometer `o` that respects the strings of words `wh`, `wv` (first and last letters `q … p` and `p … q`, the
corners at `0`, `X - (1, 1)`, `X + Y + (0, -2)`, `Y + (1, -2)`), and whose affine factors at the corners `A, B, C, D` are
`0, 0, (n - 1, 1 - d), (n, 1 - d)` (`GlueCorners`), each of the four families carrying its strings has the following first and
last tiles and affine factors:

* bottom: `(T_{1/1}, 0)` with `0`, `(T_{0/1}, X - (1, 1))` with `0`;
* left: `(T_{1/1}, 0)` with `0`, `(T_{0/1}, Y + (1, -2))` with `(n, 1 - d)`;
* top: `(T_{0/1}, Y + (1, -2))` with `(n, 1 - d)`, `(T_{1/1}` or `T^d_{1/1}, X + Y + (0, -2))` with `(n - 1, 1 - d)`;
* right: `(T_{0/1}, X - (1, 1))` with `0`, `(T_{1/1}, X + Y + (0, -2))` with `(n - 1, 1 - d)`. -/

namespace FLatticePaper.Tiles.GlueRegister

open FLatticePaper.Tiles FLatticePaper.Tiles.GlueEnds FLatticePaper.Tiles.GlueCorners

/-- The data of a register: its words, corner positions and corner affine factors. -/
structure RegData (wh wv : BinaryWord) (o : GInt → ℤ) (X Y : GInt) (n d : ℤ) : Prop where
  hh : wh.head? = some Letter.q
  hl : wh.getLast? = some Letter.p
  vh : wv.head? = some Letter.p
  vl : wv.getLast? = some Letter.q
  pX : lastPosOf (hStringAt wh 0) = X - (1, 1)
  pY : lastPosOf (vRevStringAt wv.reverse 0) = Y + (1, -2)
  pC : lastPosOf (vStringAt wv (X - (1, 1))) = X + Y + (0, -2)
  cA : tileAffine o (cornerTiles wh wv 0).1 = 0
  cB : tileAffine o (cornerTiles wh wv 0).2.1 = 0
  cC : tileAffine o (cornerTiles wh wv 0).2.2.1 = ((n : ℚ) - 1, 1 - (d : ℚ))
  cD : tileAffine o (cornerTiles wh wv 0).2.2.2 = ((n : ℚ), 1 - (d : ℚ))

theorem a_of (F : PTFamily) (o : GInt → ℤ) (hv : ∀ k < F.n, ∀ y ∈ F.dom k, o y = F.odo k y) (k : ℕ) (hk : k < F.n)
    (v : ℤ × ℤ) (h : tileAffine o (F.tile k) = ((v.1 : ℚ), (v.2 : ℚ))) : F.a k = v := by
  rw [family_tileAffine F o hv k hk] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only at h1 h2
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

theorem n_pos (F : PTFamily) (s : List (ZTile × GInt)) (h : F.ts = s) (hs : s ≠ []) : 0 < F.n := by
  unfold PTFamily.n
  rw [h]
  exact List.length_pos_of_ne_nil hs

theorem wh_ne (wh : BinaryWord) (h : wh.head? = some Letter.q) : wh ≠ [] := by
  rintro rfl; simp at h

theorem wv_ne (wv : BinaryWord) (h : wv.head? = some Letter.p) : wv ≠ [] := by
  rintro rfl; simp at h

/-- **The bottom family.** -/
theorem bot_family {wh wv : BinaryWord} {o : GInt → ℤ} {X Y : GInt} {n d : ℤ} (R : RegData wh wv o X Y n d)
    (F : PTFamily) (hts : F.ts = hStringAt wh 0) (hv : ∀ k < F.n, ∀ y ∈ F.dom k, o y = F.odo k y) :
    0 < F.n ∧ F.tile 0 = (ZTile.one, 0) ∧ F.a 0 = 0 ∧ F.tile (F.n - 1) = (ZTile.zero, X - (1, 1)) ∧
      F.a (F.n - 1) = 0 := by
  have hpos := n_pos F _ hts (GlueStringDecomp.hStringAt_ne _ _ (wh_ne wh R.hh))
  have h0 : F.tile 0 = (cornerTiles wh wv 0).1 := family_head F _ hts
  have hl : F.tile (F.n - 1) = (cornerTiles wh wv 0).2.1 := family_last F _ hts
  refine ⟨hpos, ?_, a_of F o hv 0 hpos 0 (by rw [h0, R.cA]; rfl), ?_,
    a_of F o hv _ (by omega) 0 (by rw [hl, R.cB]; rfl)⟩
  · rw [h0]; exact bot_head wh 0 R.hh
  · rw [hl]
    show (hStringAt wh 0).getLastD _ = _
    rw [bot_last wh 0 R.hl, R.pX]

/-- **The left family.** -/
theorem left_family {wh wv : BinaryWord} {o : GInt → ℤ} {X Y : GInt} {n d : ℤ} (R : RegData wh wv o X Y n d)
    (F : PTFamily) (hts : F.ts = vRevStringAt wv.reverse 0) (hv : ∀ k < F.n, ∀ y ∈ F.dom k, o y = F.odo k y) :
    0 < F.n ∧ F.tile 0 = (ZTile.one, 0) ∧ F.a 0 = 0 ∧ F.tile (F.n - 1) = (ZTile.zero, Y + (1, -2)) ∧
      F.a (F.n - 1) = (n, 1 - d) := by
  have hrh : wv.reverse.head? = some Letter.q := by rw [List.head?_reverse]; exact R.vl
  have hrl : wv.reverse.getLast? = some Letter.p := by rw [List.getLast?_reverse]; exact R.vh
  have hpos := n_pos F _ hts (GlueStringDecomp.vRevStringAt_ne _ _ (by simpa using wv_ne wv R.vh))
  have h0 : F.tile 0 = (ZTile.one, 0) := by rw [family_head F _ hts]; exact left_head _ 0 hrh
  have hl : F.tile (F.n - 1) = (ZTile.zero, Y + (1, -2)) := by
    rw [family_last F _ hts, left_last _ 0 hrl, R.pY]
  have hA : (cornerTiles wh wv 0).1 = (ZTile.one, 0) := bot_head wh 0 R.hh
  have hD : (cornerTiles wh wv 0).2.2.2 = (ZTile.zero, Y + (1, -2)) := by
    show (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))).headD _ = _
    rw [top_head _ _ (by rw [List.head?_reverse]; exact R.hl), R.pY]
  refine ⟨hpos, h0, a_of F o hv 0 hpos 0 (by rw [h0, ← hA, R.cA]; rfl), hl,
    a_of F o hv _ (by omega) (n, 1 - d) (by rw [hl, ← hD, R.cD]; push_cast; rfl)⟩

/-- **The top family.** -/
theorem top_family {wh wv : BinaryWord} {o : GInt → ℤ} {X Y : GInt} {n d : ℤ} (R : RegData wh wv o X Y n d)
    (F : PTFamily) (hts : F.ts = hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0)))
    (hv : ∀ k < F.n, ∀ y ∈ F.dom k, o y = F.odo k y) :
    0 < F.n ∧ F.tile 0 = (ZTile.zero, Y + (1, -2)) ∧ F.a 0 = (n, 1 - d) ∧
      (∃ t, (t = ZTile.one ∨ t = ZTile.oneD) ∧ F.tile (F.n - 1) = (t, X + Y + (0, -2))) ∧
      F.a (F.n - 1) = (n - 1, 1 - d) := by
  have hpos := n_pos F _ hts (GlueStringDecomp.hRevStringAt_ne _ _ (by simpa using wh_ne wh R.hh))
  have h0 : F.tile 0 = (cornerTiles wh wv 0).2.2.2 := family_head F _ hts
  have hl : F.tile (F.n - 1) = (cornerTiles wh wv 0).2.2.1 := family_last F _ hts
  refine ⟨hpos, ?_, a_of F o hv 0 hpos (n, 1 - d) (by rw [h0, R.cD]; push_cast; rfl), ?_,
    a_of F o hv _ (by omega) (n - 1, 1 - d) (by rw [hl, R.cC]; push_cast; rfl)⟩
  · rw [h0]
    show (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))).headD _ = _
    rw [top_head _ _ (by rw [List.head?_reverse]; exact R.hl), R.pY]
  · obtain ⟨t, ht, he⟩ := top_last wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))
      (by rw [List.getLast?_reverse]; exact R.hh)
    refine ⟨t, ht, ?_⟩
    rw [hl]
    show (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))).getLastD _ = _
    rw [he, ClosedPathCorners.hRev_lastPos_reverse _ _ R.hh R.hl, R.pY]
    have hX0 : lastPosOf (hStringAt wh 0) = X - (1, 1) := R.pX
    rw [hX0]
    congr 1
    ext <;> simp <;> ring

/-- **The right family.** -/
theorem right_family {wh wv : BinaryWord} {o : GInt → ℤ} {X Y : GInt} {n d : ℤ} (R : RegData wh wv o X Y n d)
    (F : PTFamily) (hts : F.ts = vStringAt wv (lastPosOf (hStringAt wh 0)))
    (hv : ∀ k < F.n, ∀ y ∈ F.dom k, o y = F.odo k y) :
    0 < F.n ∧ F.tile 0 = (ZTile.zero, X - (1, 1)) ∧ F.a 0 = 0 ∧ F.tile (F.n - 1) = (ZTile.one, X + Y + (0, -2)) ∧
      F.a (F.n - 1) = (n - 1, 1 - d) := by
  have hpos := n_pos F _ hts (GlueStringDecomp.vStringAt_ne _ _ (wv_ne wv R.vh))
  have h0 : F.tile 0 = (ZTile.zero, X - (1, 1)) := by
    rw [family_head F _ hts, right_head _ _ R.vh, R.pX]
  have hl : F.tile (F.n - 1) = (ZTile.one, X + Y + (0, -2)) := by
    rw [family_last F _ hts, right_last _ _ R.vl, R.pX, R.pC]
  have hB : (cornerTiles wh wv 0).2.1 = (ZTile.zero, X - (1, 1)) := by
    show (hStringAt wh 0).getLastD _ = _
    rw [bot_last wh 0 R.hl, R.pX]
  obtain ⟨t, ht, hC⟩ : ∃ t, (t = ZTile.one ∨ t = ZTile.oneD) ∧
      (cornerTiles wh wv 0).2.2.1 = (t, X + Y + (0, -2)) := by
    obtain ⟨t, ht, he⟩ := top_last wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))
      (by rw [List.getLast?_reverse]; exact R.hh)
    refine ⟨t, ht, ?_⟩
    show (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))).getLastD _ = _
    rw [he, ClosedPathCorners.hRev_lastPos_reverse _ _ R.hh R.hl, R.pY]
    have hX0 : lastPosOf (hStringAt wh 0) = X - (1, 1) := R.pX
    rw [hX0]
    congr 1
    ext <;> simp <;> ring
  have hCone : tileAffine o (ZTile.one, X + Y + (0, -2)) = ((n : ℚ) - 1, 1 - (d : ℚ)) := by
    rw [← R.cC, hC]
    rcases ht with rfl | rfl
    · rfl
    · exact (tileAffine_oneD o _).symm
  refine ⟨hpos, h0, a_of F o hv 0 hpos 0 (by rw [h0, ← hB, R.cB]; rfl), hl,
    a_of F o hv _ (by omega) (n - 1, 1 - d) (by rw [hl, hCone]; push_cast; rfl)⟩

/-! ### The registers of a word -/

open FLatticePaper.Farey FLatticePaper.Construction
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)

/-- The data of the odd register `u` with a normalised odometer respecting its strings. -/
theorem regData_odd (u : Word) (T : Finset GInt) (o : GInt → ℤ)
    (hR : SurgicalWeak.RespectsAnchored T (hWordOf u false) (vWordOf u false) o) (β : ℤ)
    (hN : ∀ x ∈ tileShape ZTile.one, o x = zTileOdo ZTile.one x + β) :
    RegData (hWordOf u false) (vWordOf u false) o (texV1Odd (fracOdd u)) (texV2 (fracOdd u)) (fracOdd u).num
      (fracOdd u).den := by
  obtain ⟨cA, cB, cC, cD⟩ := register_corners_odd u T o hR β hN
  exact ⟨(hWordOf_head_last u false).1, (hWordOf_head_last u false).2, (StringCorners.vertWord_head_last u).1,
    (StringCorners.vertWord_head_last u).2, TexVPositions.lastPos_hWordOf_false_tex u, StdCornerAnchors.stdAnchorY_odd u,
    StdCornerAnchors.stdAnchorC_odd u, cA, cB, cC, cD⟩

/-- The data of the even register `u` with a normalised odometer respecting its strings. -/
theorem regData_even (u : Word) (T : Finset GInt) (o : GInt → ℤ)
    (hR : SurgicalWeak.RespectsAnchored T (hWordOf u true) (vWordOf u true) o) (β : ℤ)
    (hN : ∀ x ∈ tileShape ZTile.one, o x = zTileOdo ZTile.one x + β) :
    RegData (hWordOf u true) (vWordOf u true) o (texV1Even (fracEven u)) (texV2 (fracEven u)) (fracEven u).num
      (fracEven u).den := by
  obtain ⟨cA, cB, cC, cD⟩ := register_corners_even u T o hR β hN
  exact ⟨(hWordOf_head_last u true).1, (hWordOf_head_last u true).2, (StringCorners.vWord_even_head_last u).1,
    (StringCorners.vWord_even_head_last u).2, TexVPositions.lastPos_hWordOf_true_tex u, StdCornerAnchors.stdAnchorY_even u,
    StdCornerAnchors.stdAnchorC_even u, cA, cB, cC, cD⟩

/-! ### Assembling the respect of a child string from placed blocks -/

theorem mem_placedSites_of_dom (F : PTFamily) (k : ℕ) (hk : k < F.n) (x : GInt) (hx : x ∈ F.dom k) :
    x ∈ placedSites F.ts := by
  unfold placedSites
  refine List.mem_flatMap.2 ⟨F.tile k, ?_, hx⟩
  unfold PTFamily.tile
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

/-- The value clause of a placed block from the values of the glued odometer on its sites. -/
theorem block_val (F : PTFamily) (o g : GInt → ℤ) (off a : GInt) (c : ℤ)
    (hF : ∀ k < F.n, ∀ y ∈ F.dom k, o y = F.odo k y)
    (hg : ∀ x ∈ placedSites (F.placed off a c).ts, g x = o (x - off) + a.1 * x.1 + a.2 * x.2 + c) :
    ∀ k < (F.placed off a c).n, ∀ x ∈ (F.placed off a c).dom k, g x = (F.placed off a c).odo k x :=
  GlueChain.placed_val F o g off a c hF fun k hk x hx =>
    hg x (mem_placedSites_of_dom _ k (by rw [PTFamily.placed_n]; exact hk) x hx)

/-- **A child string of two placed blocks respects its string.** -/
theorem respects_two (or : Orientation) (rev : Bool) (g : GInt → ℤ) (ts : List (ZTile × GInt))
    (F1 F2 : PTFamily) (o1 o2 : GInt → ℤ) (off1 off2 a1 a2 : GInt) (c1 c2 : ℤ)
    (hv1 : ∀ k < F1.n, ∀ y ∈ F1.dom k, o1 y = F1.odo k y) (hR1 : F1.Respects or rev) (h01 : 0 < F1.n)
    (hv2 : ∀ k < F2.n, ∀ y ∈ F2.dom k, o2 y = F2.odo k y) (hR2 : F2.Respects or rev) (h02 : 0 < F2.n)
    (hts : (F1.placed off1 a1 c1).ts ++ (F2.placed off2 a2 c2).ts = ts)
    (hg1 : ∀ x ∈ placedSites (F1.placed off1 a1 c1).ts, g x = o1 (x - off1) + a1.1 * x.1 + a1.2 * x.2 + c1)
    (hg2 : ∀ x ∈ placedSites (F2.placed off2 a2 c2).ts, g x = o2 (x - off2) + a2.1 * x.1 + a2.2 * x.2 + c2)
    (hseam : PTFamily.SeamClause or rev (F1.placed off1 a1 c1) (F2.placed off2 a2 c2)) :
    RespectsTiles or rev ts g := by
  refine ⟨PTFamily.chainR (F1.placed off1 a1 c1) [F2.placed off2 a2 c2], hts, ?_, ?_⟩
  · exact GlueChain.chainR_val g _ _ (block_val F1 o1 g off1 a1 c1 hv1 hg1) (fun C hC => by
      simp only [List.mem_singleton] at hC
      subst hC
      exact block_val F2 o2 g off2 a2 c2 hv2 hg2)
  · refine PTFamily.chainR_respects or rev _ _ (PTFamily.placed_respects _ _ _ _ _ _ hR1)
      (by rw [PTFamily.placed_n]; exact h01) (fun C hC => ?_) ⟨hseam, trivial⟩
    simp only [List.mem_singleton] at hC
    subst hC
    exact ⟨PTFamily.placed_respects _ _ _ _ _ _ hR2, by rw [PTFamily.placed_n]; exact h02⟩

/-- **A child string of three placed blocks respects its string.** -/
theorem respects_three (or : Orientation) (rev : Bool) (g : GInt → ℤ) (ts : List (ZTile × GInt))
    (F1 F2 F3 : PTFamily) (o1 o2 o3 : GInt → ℤ) (off1 off2 off3 a1 a2 a3 : GInt) (c1 c2 c3 : ℤ)
    (hv1 : ∀ k < F1.n, ∀ y ∈ F1.dom k, o1 y = F1.odo k y) (hR1 : F1.Respects or rev) (h01 : 0 < F1.n)
    (hv2 : ∀ k < F2.n, ∀ y ∈ F2.dom k, o2 y = F2.odo k y) (hR2 : F2.Respects or rev) (h02 : 0 < F2.n)
    (hv3 : ∀ k < F3.n, ∀ y ∈ F3.dom k, o3 y = F3.odo k y) (hR3 : F3.Respects or rev) (h03 : 0 < F3.n)
    (hts : (F1.placed off1 a1 c1).ts ++ (F2.placed off2 a2 c2).ts ++ (F3.placed off3 a3 c3).ts = ts)
    (hg1 : ∀ x ∈ placedSites (F1.placed off1 a1 c1).ts, g x = o1 (x - off1) + a1.1 * x.1 + a1.2 * x.2 + c1)
    (hg2 : ∀ x ∈ placedSites (F2.placed off2 a2 c2).ts, g x = o2 (x - off2) + a2.1 * x.1 + a2.2 * x.2 + c2)
    (hg3 : ∀ x ∈ placedSites (F3.placed off3 a3 c3).ts, g x = o3 (x - off3) + a3.1 * x.1 + a3.2 * x.2 + c3)
    (hs12 : PTFamily.SeamClause or rev (F1.placed off1 a1 c1) (F2.placed off2 a2 c2))
    (hs23 : PTFamily.SeamClause or rev (F2.placed off2 a2 c2) (F3.placed off3 a3 c3)) :
    RespectsTiles or rev ts g := by
  refine ⟨PTFamily.chainR (F1.placed off1 a1 c1) [F2.placed off2 a2 c2, F3.placed off3 a3 c3],
    by rw [GlueChain.chainR_ts_three]; exact hts, ?_, ?_⟩
  · exact GlueChain.chainR_val g _ _ (block_val F1 o1 g off1 a1 c1 hv1 hg1) (fun C hC => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl
      · exact block_val F2 o2 g off2 a2 c2 hv2 hg2
      · exact block_val F3 o3 g off3 a3 c3 hv3 hg3)
  · refine PTFamily.chainR_respects or rev _ _ (PTFamily.placed_respects _ _ _ _ _ _ hR1)
      (by rw [PTFamily.placed_n]; exact h01) (fun C hC => ?_) ⟨hs12, hs23, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · exact ⟨PTFamily.placed_respects _ _ _ _ _ _ hR2, by rw [PTFamily.placed_n]; exact h02⟩
    · exact ⟨PTFamily.placed_respects _ _ _ _ _ _ hR3, by rw [PTFamily.placed_n]; exact h03⟩

end FLatticePaper.Tiles.GlueRegister
