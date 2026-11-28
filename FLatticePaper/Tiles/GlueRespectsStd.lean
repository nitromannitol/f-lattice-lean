import FLatticePaper.Tiles.GlueRegister

/-! # The four boundary strings of a glued standard child respect its words, given the values on the blocks

Each boundary string of a standard child is a chain of whole strings of the copies of its registers (`GlueStringDecomp`).
Placing the families of the register strings at the offsets of the copies, with the affine factors of the pieces and the
constants of the glue, gives a family for the child string (`GlueRegister.respects_two`, `respects_three`): its blocks respect
their strings, its seams hold by the corner affine factors of the registers (`GlueRegister`, `GlueSeams`), and the glued
odometer `g` is its odometer wherever it is the placed subodometer of the copy on that copy's block. The last condition is
the hypothesis of the theorems below (one per block); it holds on the kept parts of the copies and on the overlaps where the
copies agree. -/

namespace FLatticePaper.Tiles.GlueRespectsStd

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.GlueRegister
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.SurgicalWeak (regsAt RespectsAnchored)

/-- A placed subodometer: `o(x - off) + α^T x + κ`. -/
def pl (o : GInt → ℤ) (off α : GInt) (κ : ℤ) (x : GInt) : ℤ := o (x - off) + α.1 * x.1 + α.2 * x.2 + κ

theorem vals (F : PTFamily) (s s' : List (ZTile × GInt)) (o g : GInt → ℤ) (off α : GInt) (κ : ℤ) (hts : F.ts = s)
    (hs : s.map (fun p => (p.1, p.2 + off)) = s') (h : ∀ x ∈ placedSites s', g x = pl o off α κ x) :
    ∀ x ∈ placedSites (F.placed off α κ).ts, g x = o (x - off) + α.1 * x.1 + α.2 * x.2 + κ := by
  intro x hx
  rw [GlueChain.placed_ts, hts, hs] at hx
  exact h x hx

theorem tss (F : PTFamily) (s s' : List (ZTile × GInt)) (off α : GInt) (κ : ℤ) (hts : F.ts = s)
    (hs : s.map (fun p => (p.1, p.2 + off)) = s') : (F.placed off α κ).ts = s' := by
  rw [GlueChain.placed_ts, hts, hs]

theorem tile_last (F : PTFamily) (off α : GInt) (κ : ℤ) (t : ZTile) (P : GInt) (h0 : 0 < F.n)
    (h : F.tile (F.n - 1) = (t, P)) :
    (F.placed off α κ).tile ((F.placed off α κ).n - 1) = (t, P + off) := by
  rw [PTFamily.placed_n, GlueSeams.placed_tile _ _ _ _ _ (by omega), h]

theorem tile_first (F : PTFamily) (off α : GInt) (κ : ℤ) (t : ZTile) (P : GInt) (h0 : 0 < F.n)
    (h : F.tile 0 = (t, P)) : (F.placed off α κ).tile 0 = (t, P + off) := by
  rw [GlueSeams.placed_tile _ _ _ _ _ h0, h]

theorem a_last (F : PTFamily) (off α : GInt) (κ : ℤ) :
    (F.placed off α κ).a ((F.placed off α κ).n - 1) = F.a (F.n - 1) + α := by
  rw [PTFamily.placed_n, GlueSeams.placed_a]

theorem tile_eq {t : ZTile} {P Q : GInt} (h : P = Q) : ((t, P) : ZTile × GInt) = (t, Q) := by rw [h]

/-- **The four strings of the odd child, W_1 even**, from the values of the glued odometer on the blocks. -/
theorem odd_ef_respects (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2)) (hph : phase w ≠ 1)
    (TP TQ : Finset GInt) (oP oQ : GInt → ℤ)
    (hRP : RespectsAnchored TP (hWordOf u1 false) (vWordOf u1 false) oP) (βP : ℤ) (hNP : ∀ x ∈ tileShape ZTile.one, oP x = zTileOdo ZTile.one x + βP)
    (hRQ : RespectsAnchored TQ (hWordOf u2 true) (vWordOf u2 true) oQ) (βQ : ℤ) (hNQ : ∀ x ∈ tileShape ZTile.one, oQ x = zTileOdo ZTile.one x + βQ)
    (g : GInt → ℤ) (κ : ℕ → ℤ)
    (v2b : ∀ x ∈ placedSites (hStringAt (hWordOf u2 true) (0)), g x = pl oQ (0) (0) (κ 2) x)
    (v3b : ∀ x ∈ placedSites (hStringAt (hWordOf u2 true) (texV1Even (fracEven u2))), g x = pl oQ (texV1Even (fracEven u2)) (0) (κ 3) x)
    (v0b : ∀ x ∈ placedSites (hStringAt (hWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2))), g x = pl oP (texV1Even (fracEven u2) + texV1Even (fracEven u2)) (0) (κ 0) x)
    (v1t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u1 false).reverse (texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2)))), g x = pl oP (texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 1) x)
    (v4t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))), g x = pl oQ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 4) x)
    (v5t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV2 (fracEven u2) + (1, -2)))), g x = pl oQ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) x)
    (v2l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u2 true).reverse (0)), g x = pl oQ (0) (0) (κ 2) x)
    (v1l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2))), g x = pl oP (texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 1) x)
    (v0r : ∀ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))), g x = pl oP (texV1Even (fracEven u2) + texV1Even (fracEven u2)) (0) (κ 0) x)
    (v5r : ∀ x ∈ placedSites (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1)))), g x = pl oQ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) x)
    :
    RespectsTiles .horizontal false (hStringAt (hWordOf w false) 0) g ∧
      RespectsTiles .horizontal true (hRevStringAt (hWordOf w false).reverse (lastPosOf (vRevStringAt (vWordOf w false).reverse 0))) g ∧
      RespectsTiles .vertical true (vRevStringAt (vWordOf w false).reverse 0) g ∧
      RespectsTiles .vertical false (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) g := by
  obtain ⟨dbot, dleft, dright, dtop⟩ := GlueStringDecomp.odd_ef w u1 u2 hreg hph
  have RP := regData_odd u1 TP oP hRP βP hNP
  have RQ := regData_even u2 TQ oQ hRQ βQ hNQ
  obtain ⟨-, ⟨FbP, hbPts, hbPv, hbPR⟩, ⟨FtP, htPts, htPv, htPR⟩, ⟨FlP, hlPts, hlPv, hlPR⟩, ⟨FrP, hrPts, hrPv, hrPR⟩⟩ := id hRP
  obtain ⟨bP0, bP1, bP2, bP3, bP4⟩ := bot_family RP FbP hbPts hbPv
  obtain ⟨lP0, lP1, lP2, lP3, lP4⟩ := left_family RP FlP hlPts hlPv
  obtain ⟨tP0, tP1, tP2, tP3, tP4⟩ := top_family RP FtP htPts htPv
  obtain ⟨rP0, rP1, rP2, rP3, rP4⟩ := right_family RP FrP hrPts hrPv
  obtain ⟨-, ⟨FbQ, hbQts, hbQv, hbQR⟩, ⟨FtQ, htQts, htQv, htQR⟩, ⟨FlQ, hlQts, hlQv, hlQR⟩, ⟨FrQ, hrQts, hrQv, hrQR⟩⟩ := id hRQ
  obtain ⟨bQ0, bQ1, bQ2, bQ3, bQ4⟩ := bot_family RQ FbQ hbQts hbQv
  obtain ⟨lQ0, lQ1, lQ2, lQ3, lQ4⟩ := left_family RQ FlQ hlQts hlQv
  obtain ⟨tQ0, tQ1, tQ2, tQ3, tQ4⟩ := top_family RQ FtQ htQts htQv
  obtain ⟨rQ0, rQ1, rQ2, rQ3, rQ4⟩ := right_family RQ FrQ hrQts hrQv
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine respects_three .horizontal false g (hStringAt (hWordOf w false) 0) FbQ FbQ FbP oQ oQ oP (0) (texV1Even (fracEven u2)) (texV1Even (fracEven u2) + texV1Even (fracEven u2)) (0) (0) (0) (κ 2) (κ 3) (κ 0)
      hbQv hbQR bQ0
      hbQv hbQR bQ0
      hbPv hbPR bP0
      (by rw [tss FbQ _ _ (0) (0) (κ 2) hbQts (by rw [GlueChain.hStringAt_shift, zero_add]), tss FbQ _ _ (texV1Even (fracEven u2)) (0) (κ 3) hbQts (by rw [GlueChain.hStringAt_shift, zero_add]), tss FbP _ _ (texV1Even (fracEven u2) + texV1Even (fracEven u2)) (0) (κ 0) hbPts (by rw [GlueChain.hStringAt_shift, zero_add]), dbot]) ?_ ?_ ?_ ?_ ?_
    · exact vals FbQ _ _ oQ g (0) (0) (κ 2) hbQts (by rw [GlueChain.hStringAt_shift, zero_add]) v2b
    · exact vals FbQ _ _ oQ g (texV1Even (fracEven u2)) (0) (κ 3) hbQts (by rw [GlueChain.hStringAt_shift, zero_add]) v3b
    · exact vals FbP _ _ oP g (texV1Even (fracEven u2) + texV1Even (fracEven u2)) (0) (κ 0) hbPts (by rw [GlueChain.hStringAt_shift, zero_add]) v0b
    · refine GlueSeams.seam_bot _ _ (texV1Even (fracEven u2) - (1, 1) + (0)) (tile_last _ _ _ _ _ _ bQ0 bQ3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ bQ0 bQ1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, bQ2, bQ4]
    · refine GlueSeams.seam_bot _ _ (texV1Even (fracEven u2) - (1, 1) + (texV1Even (fracEven u2))) (tile_last _ _ _ _ _ _ bQ0 bQ3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ bP0 bP1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, bP2, bQ4]
  · refine respects_three .horizontal true g (hRevStringAt (hWordOf w false).reverse (lastPosOf (vRevStringAt (vWordOf w false).reverse 0))) FtP FtQ FtQ oP oQ oQ (texV2 (fracEven u2)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (((fracOdd u1).num, -(fracOdd u1).den)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 1) (κ 4) (κ 5)
      htPv htPR tP0
      htQv htQR tQ0
      htQv htQR tQ0
      (by rw [tss FtP _ _ (texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 1) htPts (by rw [GlueChain.hRevStringAt_shift, RP.pY, add_comm (texV2 (fracOdd u1) + (1, -2)) (texV2 (fracEven u2))]), tss FtQ _ _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 4) htQts (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1))]), tss FtQ _ _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) htQts (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2))]), dtop]) ?_ ?_ ?_ ?_ ?_
    · exact vals FtP _ _ oP g (texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 1) htPts (by rw [GlueChain.hRevStringAt_shift, RP.pY, add_comm (texV2 (fracOdd u1) + (1, -2)) (texV2 (fracEven u2))]) v1t
    · exact vals FtQ _ _ oQ g (texV1Odd (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 4) htQts (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1))]) v4t
    · exact vals FtQ _ _ oQ g (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) htQts (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2))]) v5t
    · obtain ⟨t, ht, hl⟩ := tP3
      refine GlueSeams.seam_top _ _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + (0, -2) + (texV2 (fracEven u2))) t ht (tile_last _ _ _ _ _ _ tP0 hl) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ tQ0 tQ1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, tQ2, tP4]
        ext <;> (simp; try ring)
    · obtain ⟨t, ht, hl⟩ := tQ3
      refine GlueSeams.seam_top _ _ (texV1Even (fracEven u2) + texV2 (fracEven u2) + (0, -2) + (texV1Odd (fracOdd u1) + texV2 (fracOdd u1))) t ht (tile_last _ _ _ _ _ _ tQ0 hl) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ tQ0 tQ1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, tQ2, tQ4]
        ext <;> (simp; try ring)
  · refine respects_two .vertical true g (vRevStringAt (vWordOf w false).reverse 0) FlQ FlP oQ oP (0) (texV2 (fracEven u2)) (0) (((fracEven u2).num, -(fracEven u2).den)) (κ 2) (κ 1)
      hlQv hlQR lQ0
      hlPv hlPR lP0
      (by rw [tss FlQ _ _ (0) (0) (κ 2) hlQts (by rw [GlueChain.vRevStringAt_shift, zero_add]), tss FlP _ _ (texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 1) hlPts (by rw [GlueChain.vRevStringAt_shift, zero_add]), dleft]) ?_ ?_ ?_
    · exact vals FlQ _ _ oQ g (0) (0) (κ 2) hlQts (by rw [GlueChain.vRevStringAt_shift, zero_add]) v2l
    · exact vals FlP _ _ oP g (texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 1) hlPts (by rw [GlueChain.vRevStringAt_shift, zero_add]) v1l
    · refine GlueSeams.seam_left _ _ (texV2 (fracEven u2) + (1, -2) + (0)) (tile_last _ _ _ _ _ _ lQ0 lQ3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ lP0 lP1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, lP2, lQ4]
        ext <;> (simp; try ring)
  · refine respects_two .vertical false g (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) FrP FrQ oP oQ (texV1Even (fracEven u2) + texV1Even (fracEven u2)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2)) (0) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 0) (κ 5)
      hrPv hrPR rP0
      hrQv hrQR rQ0
      (by rw [tss FrP _ _ (texV1Even (fracEven u2) + texV1Even (fracEven u2)) (0) (κ 0) hrPts (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV1Even (fracEven u2))]), tss FrQ _ _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) hrQts (by rw [GlueChain.vStringAt_shift, RQ.pX, add_comm (texV1Even (fracEven u2) - (1, 1)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2))]), dright]) ?_ ?_ ?_
    · exact vals FrP _ _ oP g (texV1Even (fracEven u2) + texV1Even (fracEven u2)) (0) (κ 0) hrPts (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV1Even (fracEven u2))]) v0r
    · exact vals FrQ _ _ oQ g (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) hrQts (by rw [GlueChain.vStringAt_shift, RQ.pX, add_comm (texV1Even (fracEven u2) - (1, 1)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2))]) v5r
    · refine GlueSeams.seam_right _ _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + (0, -2) + (texV1Even (fracEven u2) + texV1Even (fracEven u2))) (tile_last _ _ _ _ _ _ rP0 rP3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ rQ0 rQ1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, rQ2, rP4]
        ext <;> (simp; try ring)

/-- **The four strings of the odd child, W_1 odd**, from the values of the glued odometer on the blocks. -/
theorem odd_of_respects (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2)) (hph : phase w = 1)
    (TP TQ : Finset GInt) (oP oQ : GInt → ℤ)
    (hRP : RespectsAnchored TP (hWordOf u1 false) (vWordOf u1 false) oP) (βP : ℤ) (hNP : ∀ x ∈ tileShape ZTile.one, oP x = zTileOdo ZTile.one x + βP)
    (hRQ : RespectsAnchored TQ (hWordOf u2 true) (vWordOf u2 true) oQ) (βQ : ℤ) (hNQ : ∀ x ∈ tileShape ZTile.one, oQ x = zTileOdo ZTile.one x + βQ)
    (g : GInt → ℤ) (κ : ℕ → ℤ)
    (v0b : ∀ x ∈ placedSites (hStringAt (hWordOf u1 false) (0)), g x = pl oP (0) (0) (κ 0) x)
    (v2b : ∀ x ∈ placedSites (hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1))), g x = pl oQ (texV1Odd (fracOdd u1)) (0) (κ 2) x)
    (v3b : ∀ x ∈ placedSites (hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2))), g x = pl oQ (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) (0) (κ 3) x)
    (v4t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))), g x = pl oQ (texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 4) x)
    (v5t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV2 (fracEven u2) + (1, -2)))), g x = pl oQ (texV2 (fracOdd u1) + texV1Even (fracEven u2)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) x)
    (v1t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u1 false).reverse (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2)))), g x = pl oP (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 1) x)
    (v0l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (0)), g x = pl oP (0) (0) (κ 0) x)
    (v4l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u2 true).reverse (texV2 (fracOdd u1))), g x = pl oQ (texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 4) x)
    (v3r : ∀ x ∈ placedSites (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1)))), g x = pl oQ (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) (0) (κ 3) x)
    (v1r : ∀ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))), g x = pl oP (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 1) x)
    :
    RespectsTiles .horizontal false (hStringAt (hWordOf w false) 0) g ∧
      RespectsTiles .horizontal true (hRevStringAt (hWordOf w false).reverse (lastPosOf (vRevStringAt (vWordOf w false).reverse 0))) g ∧
      RespectsTiles .vertical true (vRevStringAt (vWordOf w false).reverse 0) g ∧
      RespectsTiles .vertical false (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) g := by
  obtain ⟨dbot, dleft, dright, dtop⟩ := GlueStringDecomp.odd_of w u1 u2 hreg hph
  have RP := regData_odd u1 TP oP hRP βP hNP
  have RQ := regData_even u2 TQ oQ hRQ βQ hNQ
  obtain ⟨-, ⟨FbP, hbPts, hbPv, hbPR⟩, ⟨FtP, htPts, htPv, htPR⟩, ⟨FlP, hlPts, hlPv, hlPR⟩, ⟨FrP, hrPts, hrPv, hrPR⟩⟩ := id hRP
  obtain ⟨bP0, bP1, bP2, bP3, bP4⟩ := bot_family RP FbP hbPts hbPv
  obtain ⟨lP0, lP1, lP2, lP3, lP4⟩ := left_family RP FlP hlPts hlPv
  obtain ⟨tP0, tP1, tP2, tP3, tP4⟩ := top_family RP FtP htPts htPv
  obtain ⟨rP0, rP1, rP2, rP3, rP4⟩ := right_family RP FrP hrPts hrPv
  obtain ⟨-, ⟨FbQ, hbQts, hbQv, hbQR⟩, ⟨FtQ, htQts, htQv, htQR⟩, ⟨FlQ, hlQts, hlQv, hlQR⟩, ⟨FrQ, hrQts, hrQv, hrQR⟩⟩ := id hRQ
  obtain ⟨bQ0, bQ1, bQ2, bQ3, bQ4⟩ := bot_family RQ FbQ hbQts hbQv
  obtain ⟨lQ0, lQ1, lQ2, lQ3, lQ4⟩ := left_family RQ FlQ hlQts hlQv
  obtain ⟨tQ0, tQ1, tQ2, tQ3, tQ4⟩ := top_family RQ FtQ htQts htQv
  obtain ⟨rQ0, rQ1, rQ2, rQ3, rQ4⟩ := right_family RQ FrQ hrQts hrQv
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine respects_three .horizontal false g (hStringAt (hWordOf w false) 0) FbP FbQ FbQ oP oQ oQ (0) (texV1Odd (fracOdd u1)) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) (0) (0) (0) (κ 0) (κ 2) (κ 3)
      hbPv hbPR bP0
      hbQv hbQR bQ0
      hbQv hbQR bQ0
      (by rw [tss FbP _ _ (0) (0) (κ 0) hbPts (by rw [GlueChain.hStringAt_shift, zero_add]), tss FbQ _ _ (texV1Odd (fracOdd u1)) (0) (κ 2) hbQts (by rw [GlueChain.hStringAt_shift, zero_add]), tss FbQ _ _ (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) (0) (κ 3) hbQts (by rw [GlueChain.hStringAt_shift, zero_add]), dbot]) ?_ ?_ ?_ ?_ ?_
    · exact vals FbP _ _ oP g (0) (0) (κ 0) hbPts (by rw [GlueChain.hStringAt_shift, zero_add]) v0b
    · exact vals FbQ _ _ oQ g (texV1Odd (fracOdd u1)) (0) (κ 2) hbQts (by rw [GlueChain.hStringAt_shift, zero_add]) v2b
    · exact vals FbQ _ _ oQ g (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) (0) (κ 3) hbQts (by rw [GlueChain.hStringAt_shift, zero_add]) v3b
    · refine GlueSeams.seam_bot _ _ (texV1Odd (fracOdd u1) - (1, 1) + (0)) (tile_last _ _ _ _ _ _ bP0 bP3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ bQ0 bQ1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, bQ2, bP4]
    · refine GlueSeams.seam_bot _ _ (texV1Even (fracEven u2) - (1, 1) + (texV1Odd (fracOdd u1))) (tile_last _ _ _ _ _ _ bQ0 bQ3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ bQ0 bQ1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, bQ2, bQ4]
  · refine respects_three .horizontal true g (hRevStringAt (hWordOf w false).reverse (lastPosOf (vRevStringAt (vWordOf w false).reverse 0))) FtQ FtQ FtP oQ oQ oP (texV2 (fracOdd u1)) (texV2 (fracOdd u1) + texV1Even (fracEven u2)) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) (((fracOdd u1).num, -(fracOdd u1).den)) (((fracOdd u1).num, -(fracOdd u1).den)) (((fracEven u2).num, -(fracEven u2).den)) (κ 4) (κ 5) (κ 1)
      htQv htQR tQ0
      htQv htQR tQ0
      htPv htPR tP0
      (by rw [tss FtQ _ _ (texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 4) htQts (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV2 (fracOdd u1))]), tss FtQ _ _ (texV2 (fracOdd u1) + texV1Even (fracEven u2)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) htQts (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV2 (fracOdd u1) + texV1Even (fracEven u2))]), tss FtP _ _ (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 1) htPts (by rw [GlueChain.hRevStringAt_shift, RP.pY, add_comm (texV2 (fracOdd u1) + (1, -2)) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2))]), dtop]) ?_ ?_ ?_ ?_ ?_
    · exact vals FtQ _ _ oQ g (texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 4) htQts (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV2 (fracOdd u1))]) v4t
    · exact vals FtQ _ _ oQ g (texV2 (fracOdd u1) + texV1Even (fracEven u2)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) htQts (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV2 (fracOdd u1) + texV1Even (fracEven u2))]) v5t
    · exact vals FtP _ _ oP g (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 1) htPts (by rw [GlueChain.hRevStringAt_shift, RP.pY, add_comm (texV2 (fracOdd u1) + (1, -2)) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2))]) v1t
    · obtain ⟨t, ht, hl⟩ := tQ3
      refine GlueSeams.seam_top _ _ (texV1Even (fracEven u2) + texV2 (fracEven u2) + (0, -2) + (texV2 (fracOdd u1))) t ht (tile_last _ _ _ _ _ _ tQ0 hl) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ tQ0 tQ1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, tQ2, tQ4]
        ext <;> (simp; try ring)
    · obtain ⟨t, ht, hl⟩ := tQ3
      refine GlueSeams.seam_top _ _ (texV1Even (fracEven u2) + texV2 (fracEven u2) + (0, -2) + (texV2 (fracOdd u1) + texV1Even (fracEven u2))) t ht (tile_last _ _ _ _ _ _ tQ0 hl) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ tP0 tP1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, tP2, tQ4]
        ext <;> (simp; try ring)
  · refine respects_two .vertical true g (vRevStringAt (vWordOf w false).reverse 0) FlP FlQ oP oQ (0) (texV2 (fracOdd u1)) (0) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 0) (κ 4)
      hlPv hlPR lP0
      hlQv hlQR lQ0
      (by rw [tss FlP _ _ (0) (0) (κ 0) hlPts (by rw [GlueChain.vRevStringAt_shift, zero_add]), tss FlQ _ _ (texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 4) hlQts (by rw [GlueChain.vRevStringAt_shift, zero_add]), dleft]) ?_ ?_ ?_
    · exact vals FlP _ _ oP g (0) (0) (κ 0) hlPts (by rw [GlueChain.vRevStringAt_shift, zero_add]) v0l
    · exact vals FlQ _ _ oQ g (texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 4) hlQts (by rw [GlueChain.vRevStringAt_shift, zero_add]) v4l
    · refine GlueSeams.seam_left _ _ (texV2 (fracOdd u1) + (1, -2) + (0)) (tile_last _ _ _ _ _ _ lP0 lP3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ lQ0 lQ1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, lQ2, lP4]
        ext <;> (simp; try ring)
  · refine respects_two .vertical false g (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) FrQ FrP oQ oP (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) (0) (((fracEven u2).num, -(fracEven u2).den)) (κ 3) (κ 1)
      hrQv hrQR rQ0
      hrPv hrPR rP0
      (by rw [tss FrQ _ _ (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) (0) (κ 3) hrQts (by rw [GlueChain.vStringAt_shift, RQ.pX, add_comm (texV1Even (fracEven u2) - (1, 1)) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2))]), tss FrP _ _ (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 1) hrPts (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2))]), dright]) ?_ ?_ ?_
    · exact vals FrQ _ _ oQ g (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) (0) (κ 3) hrQts (by rw [GlueChain.vStringAt_shift, RQ.pX, add_comm (texV1Even (fracEven u2) - (1, 1)) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2))]) v3r
    · exact vals FrP _ _ oP g (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 1) hrPts (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2))]) v1r
    · refine GlueSeams.seam_right _ _ (texV1Even (fracEven u2) + texV2 (fracEven u2) + (0, -2) + (texV1Odd (fracOdd u1) + texV1Even (fracEven u2))) (tile_last _ _ _ _ _ _ rQ0 rQ3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ rP0 rP1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, rP2, rQ4]
        ext <;> (simp; try ring)

/-- **The four strings of the even child, W_1 even**, from the values of the glued odometer on the blocks. -/
theorem even_ef_respects (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2)) (hph : phase w ≠ 1)
    (TP TQ : Finset GInt) (oP oQ : GInt → ℤ)
    (hRP : RespectsAnchored TP (hWordOf u1 false) (vWordOf u1 false) oP) (βP : ℤ) (hNP : ∀ x ∈ tileShape ZTile.one, oP x = zTileOdo ZTile.one x + βP)
    (hRQ : RespectsAnchored TQ (hWordOf u2 true) (vWordOf u2 true) oQ) (βQ : ℤ) (hNQ : ∀ x ∈ tileShape ZTile.one, oQ x = zTileOdo ZTile.one x + βQ)
    (g : GInt → ℤ) (κ : ℕ → ℤ)
    (v4b : ∀ x ∈ placedSites (hStringAt (hWordOf u2 true) (0)), g x = pl oQ (0) (0) (κ 4) x)
    (v0b : ∀ x ∈ placedSites (hStringAt (hWordOf u1 false) (texV1Even (fracEven u2))), g x = pl oP (texV1Even (fracEven u2)) (0) (κ 0) x)
    (v3t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u1 false).reverse (texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV2 (fracOdd u1) + (1, -2)))), g x = pl oP (texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 3) x)
    (v5t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))), g x = pl oQ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) x)
    (v4l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u2 true).reverse (0)), g x = pl oQ (0) (0) (κ 4) x)
    (v2l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2))), g x = pl oP (texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 2) x)
    (v3l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2) + texV2 (fracOdd u1))), g x = pl oP (texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 3) x)
    (v0r : ∀ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))), g x = pl oP (texV1Even (fracEven u2)) (0) (κ 0) x)
    (v1r : ∀ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV2 (fracOdd u1) + (texV1Odd (fracOdd u1) - (1, 1)))), g x = pl oP (texV1Even (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 1) x)
    (v5r : ∀ x ∈ placedSites (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1)))), g x = pl oQ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) x)
    :
    RespectsTiles .horizontal false (hStringAt (hWordOf w true) 0) g ∧
      RespectsTiles .horizontal true (hRevStringAt (hWordOf w true).reverse (lastPosOf (vRevStringAt (vWordOf w true).reverse 0))) g ∧
      RespectsTiles .vertical true (vRevStringAt (vWordOf w true).reverse 0) g ∧
      RespectsTiles .vertical false (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) g := by
  obtain ⟨dbot, dleft, dright, dtop⟩ := GlueStringDecomp.even_ef w u1 u2 hreg hph
  have RP := regData_odd u1 TP oP hRP βP hNP
  have RQ := regData_even u2 TQ oQ hRQ βQ hNQ
  obtain ⟨-, ⟨FbP, hbPts, hbPv, hbPR⟩, ⟨FtP, htPts, htPv, htPR⟩, ⟨FlP, hlPts, hlPv, hlPR⟩, ⟨FrP, hrPts, hrPv, hrPR⟩⟩ := id hRP
  obtain ⟨bP0, bP1, bP2, bP3, bP4⟩ := bot_family RP FbP hbPts hbPv
  obtain ⟨lP0, lP1, lP2, lP3, lP4⟩ := left_family RP FlP hlPts hlPv
  obtain ⟨tP0, tP1, tP2, tP3, tP4⟩ := top_family RP FtP htPts htPv
  obtain ⟨rP0, rP1, rP2, rP3, rP4⟩ := right_family RP FrP hrPts hrPv
  obtain ⟨-, ⟨FbQ, hbQts, hbQv, hbQR⟩, ⟨FtQ, htQts, htQv, htQR⟩, ⟨FlQ, hlQts, hlQv, hlQR⟩, ⟨FrQ, hrQts, hrQv, hrQR⟩⟩ := id hRQ
  obtain ⟨bQ0, bQ1, bQ2, bQ3, bQ4⟩ := bot_family RQ FbQ hbQts hbQv
  obtain ⟨lQ0, lQ1, lQ2, lQ3, lQ4⟩ := left_family RQ FlQ hlQts hlQv
  obtain ⟨tQ0, tQ1, tQ2, tQ3, tQ4⟩ := top_family RQ FtQ htQts htQv
  obtain ⟨rQ0, rQ1, rQ2, rQ3, rQ4⟩ := right_family RQ FrQ hrQts hrQv
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine respects_two .horizontal false g (hStringAt (hWordOf w true) 0) FbQ FbP oQ oP (0) (texV1Even (fracEven u2)) (0) (0) (κ 4) (κ 0)
      hbQv hbQR bQ0
      hbPv hbPR bP0
      (by rw [tss FbQ _ _ (0) (0) (κ 4) hbQts (by rw [GlueChain.hStringAt_shift, zero_add]), tss FbP _ _ (texV1Even (fracEven u2)) (0) (κ 0) hbPts (by rw [GlueChain.hStringAt_shift, zero_add]), dbot]) ?_ ?_ ?_
    · exact vals FbQ _ _ oQ g (0) (0) (κ 4) hbQts (by rw [GlueChain.hStringAt_shift, zero_add]) v4b
    · exact vals FbP _ _ oP g (texV1Even (fracEven u2)) (0) (κ 0) hbPts (by rw [GlueChain.hStringAt_shift, zero_add]) v0b
    · refine GlueSeams.seam_bot _ _ (texV1Even (fracEven u2) - (1, 1) + (0)) (tile_last _ _ _ _ _ _ bQ0 bQ3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ bP0 bP1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, bP2, bQ4]
  · refine respects_two .horizontal true g (hRevStringAt (hWordOf w true).reverse (lastPosOf (vRevStringAt (vWordOf w true).reverse 0))) FtP FtQ oP oQ (texV2 (fracEven u2) + texV2 (fracOdd u1)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 3) (κ 5)
      htPv htPR tP0
      htQv htQR tQ0
      (by rw [tss FtP _ _ (texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 3) htPts (by rw [GlueChain.hRevStringAt_shift, RP.pY, add_comm (texV2 (fracOdd u1) + (1, -2)) (texV2 (fracEven u2) + texV2 (fracOdd u1))]), tss FtQ _ _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) htQts (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1))]), dtop]) ?_ ?_ ?_
    · exact vals FtP _ _ oP g (texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 3) htPts (by rw [GlueChain.hRevStringAt_shift, RP.pY, add_comm (texV2 (fracOdd u1) + (1, -2)) (texV2 (fracEven u2) + texV2 (fracOdd u1))]) v3t
    · exact vals FtQ _ _ oQ g (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) htQts (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1))]) v5t
    · obtain ⟨t, ht, hl⟩ := tP3
      refine GlueSeams.seam_top _ _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + (0, -2) + (texV2 (fracEven u2) + texV2 (fracOdd u1))) t ht (tile_last _ _ _ _ _ _ tP0 hl) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ tQ0 tQ1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, tQ2, tP4]
        ext <;> (simp; try ring)
  · refine respects_three .vertical true g (vRevStringAt (vWordOf w true).reverse 0) FlQ FlP FlP oQ oP oP (0) (texV2 (fracEven u2)) (texV2 (fracEven u2) + texV2 (fracOdd u1)) (0) (((fracEven u2).num, -(fracEven u2).den)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 4) (κ 2) (κ 3)
      hlQv hlQR lQ0
      hlPv hlPR lP0
      hlPv hlPR lP0
      (by rw [tss FlQ _ _ (0) (0) (κ 4) hlQts (by rw [GlueChain.vRevStringAt_shift, zero_add]), tss FlP _ _ (texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 2) hlPts (by rw [GlueChain.vRevStringAt_shift, zero_add]), tss FlP _ _ (texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 3) hlPts (by rw [GlueChain.vRevStringAt_shift, zero_add]), dleft]) ?_ ?_ ?_ ?_ ?_
    · exact vals FlQ _ _ oQ g (0) (0) (κ 4) hlQts (by rw [GlueChain.vRevStringAt_shift, zero_add]) v4l
    · exact vals FlP _ _ oP g (texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 2) hlPts (by rw [GlueChain.vRevStringAt_shift, zero_add]) v2l
    · exact vals FlP _ _ oP g (texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 3) hlPts (by rw [GlueChain.vRevStringAt_shift, zero_add]) v3l
    · refine GlueSeams.seam_left _ _ (texV2 (fracEven u2) + (1, -2) + (0)) (tile_last _ _ _ _ _ _ lQ0 lQ3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ lP0 lP1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, lP2, lQ4]
        ext <;> (simp; try ring)
    · refine GlueSeams.seam_left _ _ (texV2 (fracOdd u1) + (1, -2) + (texV2 (fracEven u2))) (tile_last _ _ _ _ _ _ lP0 lP3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ lP0 lP1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, lP2, lP4]
        ext <;> (simp; try ring)
  · refine respects_three .vertical false g (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) FrP FrP FrQ oP oP oQ (texV1Even (fracEven u2)) (texV1Even (fracEven u2) + texV2 (fracOdd u1)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) (0) (((fracOdd u1).num, -(fracOdd u1).den)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 0) (κ 1) (κ 5)
      hrPv hrPR rP0
      hrPv hrPR rP0
      hrQv hrQR rQ0
      (by rw [tss FrP _ _ (texV1Even (fracEven u2)) (0) (κ 0) hrPts (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2))]), tss FrP _ _ (texV1Even (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 1) hrPts (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV2 (fracOdd u1))]), tss FrQ _ _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) hrQts (by rw [GlueChain.vStringAt_shift, RQ.pX, add_comm (texV1Even (fracEven u2) - (1, 1)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1))]), dright]) ?_ ?_ ?_ ?_ ?_
    · exact vals FrP _ _ oP g (texV1Even (fracEven u2)) (0) (κ 0) hrPts (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2))]) v0r
    · exact vals FrP _ _ oP g (texV1Even (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 1) hrPts (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV2 (fracOdd u1))]) v1r
    · exact vals FrQ _ _ oQ g (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) hrQts (by rw [GlueChain.vStringAt_shift, RQ.pX, add_comm (texV1Even (fracEven u2) - (1, 1)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1))]) v5r
    · refine GlueSeams.seam_right _ _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + (0, -2) + (texV1Even (fracEven u2))) (tile_last _ _ _ _ _ _ rP0 rP3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ rP0 rP1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, rP2, rP4]
        ext <;> (simp; try ring)
    · refine GlueSeams.seam_right _ _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + (0, -2) + (texV1Even (fracEven u2) + texV2 (fracOdd u1))) (tile_last _ _ _ _ _ _ rP0 rP3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ rQ0 rQ1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, rQ2, rP4]
        ext <;> (simp; try ring)

/-- **The four strings of the even child, W_1 odd**, from the values of the glued odometer on the blocks. -/
theorem even_of_respects (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2)) (hph : phase w = 1)
    (TP TQ : Finset GInt) (oP oQ : GInt → ℤ)
    (hRP : RespectsAnchored TP (hWordOf u1 false) (vWordOf u1 false) oP) (βP : ℤ) (hNP : ∀ x ∈ tileShape ZTile.one, oP x = zTileOdo ZTile.one x + βP)
    (hRQ : RespectsAnchored TQ (hWordOf u2 true) (vWordOf u2 true) oQ) (βQ : ℤ) (hNQ : ∀ x ∈ tileShape ZTile.one, oQ x = zTileOdo ZTile.one x + βQ)
    (g : GInt → ℤ) (κ : ℕ → ℤ)
    (v0b : ∀ x ∈ placedSites (hStringAt (hWordOf u1 false) (0)), g x = pl oP (0) (0) (κ 0) x)
    (v4b : ∀ x ∈ placedSites (hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1))), g x = pl oQ (texV1Odd (fracOdd u1)) (0) (κ 4) x)
    (v5t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))), g x = pl oQ (texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) x)
    (v3t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u1 false).reverse (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV2 (fracOdd u1) + (1, -2)))), g x = pl oP (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 3) x)
    (v0l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (0)), g x = pl oP (0) (0) (κ 0) x)
    (v1l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (texV2 (fracOdd u1))), g x = pl oP (texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 1) x)
    (v5l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u2 true).reverse (texV2 (fracOdd u1) + texV2 (fracOdd u1))), g x = pl oQ (texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) x)
    (v4r : ∀ x ∈ placedSites (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1)))), g x = pl oQ (texV1Odd (fracOdd u1)) (0) (κ 4) x)
    (v2r : ∀ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))), g x = pl oP (texV1Even (fracEven u2) + texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 2) x)
    (v3r : ∀ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV1Odd (fracOdd u1) - (1, 1)))), g x = pl oP (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 3) x)
    :
    RespectsTiles .horizontal false (hStringAt (hWordOf w true) 0) g ∧
      RespectsTiles .horizontal true (hRevStringAt (hWordOf w true).reverse (lastPosOf (vRevStringAt (vWordOf w true).reverse 0))) g ∧
      RespectsTiles .vertical true (vRevStringAt (vWordOf w true).reverse 0) g ∧
      RespectsTiles .vertical false (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) g := by
  obtain ⟨dbot, dleft, dright, dtop⟩ := GlueStringDecomp.even_of w u1 u2 hreg hph
  have RP := regData_odd u1 TP oP hRP βP hNP
  have RQ := regData_even u2 TQ oQ hRQ βQ hNQ
  obtain ⟨-, ⟨FbP, hbPts, hbPv, hbPR⟩, ⟨FtP, htPts, htPv, htPR⟩, ⟨FlP, hlPts, hlPv, hlPR⟩, ⟨FrP, hrPts, hrPv, hrPR⟩⟩ := id hRP
  obtain ⟨bP0, bP1, bP2, bP3, bP4⟩ := bot_family RP FbP hbPts hbPv
  obtain ⟨lP0, lP1, lP2, lP3, lP4⟩ := left_family RP FlP hlPts hlPv
  obtain ⟨tP0, tP1, tP2, tP3, tP4⟩ := top_family RP FtP htPts htPv
  obtain ⟨rP0, rP1, rP2, rP3, rP4⟩ := right_family RP FrP hrPts hrPv
  obtain ⟨-, ⟨FbQ, hbQts, hbQv, hbQR⟩, ⟨FtQ, htQts, htQv, htQR⟩, ⟨FlQ, hlQts, hlQv, hlQR⟩, ⟨FrQ, hrQts, hrQv, hrQR⟩⟩ := id hRQ
  obtain ⟨bQ0, bQ1, bQ2, bQ3, bQ4⟩ := bot_family RQ FbQ hbQts hbQv
  obtain ⟨lQ0, lQ1, lQ2, lQ3, lQ4⟩ := left_family RQ FlQ hlQts hlQv
  obtain ⟨tQ0, tQ1, tQ2, tQ3, tQ4⟩ := top_family RQ FtQ htQts htQv
  obtain ⟨rQ0, rQ1, rQ2, rQ3, rQ4⟩ := right_family RQ FrQ hrQts hrQv
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine respects_two .horizontal false g (hStringAt (hWordOf w true) 0) FbP FbQ oP oQ (0) (texV1Odd (fracOdd u1)) (0) (0) (κ 0) (κ 4)
      hbPv hbPR bP0
      hbQv hbQR bQ0
      (by rw [tss FbP _ _ (0) (0) (κ 0) hbPts (by rw [GlueChain.hStringAt_shift, zero_add]), tss FbQ _ _ (texV1Odd (fracOdd u1)) (0) (κ 4) hbQts (by rw [GlueChain.hStringAt_shift, zero_add]), dbot]) ?_ ?_ ?_
    · exact vals FbP _ _ oP g (0) (0) (κ 0) hbPts (by rw [GlueChain.hStringAt_shift, zero_add]) v0b
    · exact vals FbQ _ _ oQ g (texV1Odd (fracOdd u1)) (0) (κ 4) hbQts (by rw [GlueChain.hStringAt_shift, zero_add]) v4b
    · refine GlueSeams.seam_bot _ _ (texV1Odd (fracOdd u1) - (1, 1) + (0)) (tile_last _ _ _ _ _ _ bP0 bP3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ bQ0 bQ1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, bQ2, bP4]
  · refine respects_two .horizontal true g (hRevStringAt (hWordOf w true).reverse (lastPosOf (vRevStringAt (vWordOf w true).reverse 0))) FtQ FtP oQ oP (texV2 (fracOdd u1) + texV2 (fracOdd u1)) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 5) (κ 3)
      htQv htQR tQ0
      htPv htPR tP0
      (by rw [tss FtQ _ _ (texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) htQts (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV2 (fracOdd u1) + texV2 (fracOdd u1))]), tss FtP _ _ (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 3) htPts (by rw [GlueChain.hRevStringAt_shift, RP.pY, add_comm (texV2 (fracOdd u1) + (1, -2)) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1))]), dtop]) ?_ ?_ ?_
    · exact vals FtQ _ _ oQ g (texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) htQts (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV2 (fracOdd u1) + texV2 (fracOdd u1))]) v5t
    · exact vals FtP _ _ oP g (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 3) htPts (by rw [GlueChain.hRevStringAt_shift, RP.pY, add_comm (texV2 (fracOdd u1) + (1, -2)) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1))]) v3t
    · obtain ⟨t, ht, hl⟩ := tQ3
      refine GlueSeams.seam_top _ _ (texV1Even (fracEven u2) + texV2 (fracEven u2) + (0, -2) + (texV2 (fracOdd u1) + texV2 (fracOdd u1))) t ht (tile_last _ _ _ _ _ _ tQ0 hl) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ tP0 tP1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, tP2, tQ4]
        ext <;> (simp; try ring)
  · refine respects_three .vertical true g (vRevStringAt (vWordOf w true).reverse 0) FlP FlP FlQ oP oP oQ (0) (texV2 (fracOdd u1)) (texV2 (fracOdd u1) + texV2 (fracOdd u1)) (0) (((fracOdd u1).num, -(fracOdd u1).den)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 0) (κ 1) (κ 5)
      hlPv hlPR lP0
      hlPv hlPR lP0
      hlQv hlQR lQ0
      (by rw [tss FlP _ _ (0) (0) (κ 0) hlPts (by rw [GlueChain.vRevStringAt_shift, zero_add]), tss FlP _ _ (texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 1) hlPts (by rw [GlueChain.vRevStringAt_shift, zero_add]), tss FlQ _ _ (texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) hlQts (by rw [GlueChain.vRevStringAt_shift, zero_add]), dleft]) ?_ ?_ ?_ ?_ ?_
    · exact vals FlP _ _ oP g (0) (0) (κ 0) hlPts (by rw [GlueChain.vRevStringAt_shift, zero_add]) v0l
    · exact vals FlP _ _ oP g (texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den)) (κ 1) hlPts (by rw [GlueChain.vRevStringAt_shift, zero_add]) v1l
    · exact vals FlQ _ _ oQ g (texV2 (fracOdd u1) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracOdd u1).num, -(fracOdd u1).den)) (κ 5) hlQts (by rw [GlueChain.vRevStringAt_shift, zero_add]) v5l
    · refine GlueSeams.seam_left _ _ (texV2 (fracOdd u1) + (1, -2) + (0)) (tile_last _ _ _ _ _ _ lP0 lP3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ lP0 lP1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, lP2, lP4]
        ext <;> (simp; try ring)
    · refine GlueSeams.seam_left _ _ (texV2 (fracOdd u1) + (1, -2) + (texV2 (fracOdd u1))) (tile_last _ _ _ _ _ _ lP0 lP3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ lQ0 lQ1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, lQ2, lP4]
        ext <;> (simp; try ring)
  · refine respects_three .vertical false g (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) FrQ FrP FrP oQ oP oP (texV1Odd (fracOdd u1)) (texV1Even (fracEven u2) + texV2 (fracEven u2)) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1)) (0) (((fracEven u2).num, -(fracEven u2).den)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 4) (κ 2) (κ 3)
      hrQv hrQR rQ0
      hrPv hrPR rP0
      hrPv hrPR rP0
      (by rw [tss FrQ _ _ (texV1Odd (fracOdd u1)) (0) (κ 4) hrQts (by rw [GlueChain.vStringAt_shift, RQ.pX, add_comm (texV1Even (fracEven u2) - (1, 1)) (texV1Odd (fracOdd u1))]), tss FrP _ _ (texV1Even (fracEven u2) + texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 2) hrPts (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV2 (fracEven u2))]), tss FrP _ _ (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 3) hrPts (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1))]), dright]) ?_ ?_ ?_ ?_ ?_
    · exact vals FrQ _ _ oQ g (texV1Odd (fracOdd u1)) (0) (κ 4) hrQts (by rw [GlueChain.vStringAt_shift, RQ.pX, add_comm (texV1Even (fracEven u2) - (1, 1)) (texV1Odd (fracOdd u1))]) v4r
    · exact vals FrP _ _ oP g (texV1Even (fracEven u2) + texV2 (fracEven u2)) (((fracEven u2).num, -(fracEven u2).den)) (κ 2) hrPts (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV2 (fracEven u2))]) v2r
    · exact vals FrP _ _ oP g (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1)) (((fracOdd u1).num, -(fracOdd u1).den) + ((fracEven u2).num, -(fracEven u2).den)) (κ 3) hrPts (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1))]) v3r
    · refine GlueSeams.seam_right _ _ (texV1Even (fracEven u2) + texV2 (fracEven u2) + (0, -2) + (texV1Odd (fracOdd u1))) (tile_last _ _ _ _ _ _ rQ0 rQ3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ rP0 rP1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, rP2, rQ4]
        ext <;> (simp; try ring)
    · refine GlueSeams.seam_right _ _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + (0, -2) + (texV1Even (fracEven u2) + texV2 (fracEven u2))) (tile_last _ _ _ _ _ _ rP0 rP3) ?_ ?_
      · rw [tile_first _ _ _ _ _ _ rP0 rP1]
        exact tile_eq (by ext <;> (simp; try ring))
      · rw [GlueSeams.placed_a, a_last, rP2, rP4]
        ext <;> (simp; try ring)

end FLatticePaper.Tiles.GlueRespectsStd
