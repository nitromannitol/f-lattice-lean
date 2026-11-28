import FLatticePaper.Tiles.AltLatticeOddWFamily
import FLatticePaper.Tiles.SurgicalCornerThird
import FLatticePaper.Tiles.HorizontalAdjacency
import FLatticePaper.Tiles.ClosedWalkVertical
import FLatticePaper.Tiles.PTUniqueness
import FLatticePaper.Tiles.TileHalfTurnInput
import FLatticePaper.Tiles.AltItem3Strings

/-! # The alternate and the standard even tile odometers on the bottom string

The even alternate tile `T̂(q₀)` of a word that is not a base word is a `w_h(q₀)`-pseudo-square with the forward horizontal
string at `c(T̂) = 0` (`lemma:alternate_tile_properties` (3), `AltItem3.alt_item3_even`), the same string as the bottom
string of the standard tile `T(q₀)`. Both tile odometers respect it and are normalised with slope `0` on its first tile, so they
agree on it up to a constant: two families respecting one string differ by an affine function (`exists_affine_of_respects_gen`),
whose linear part vanishes on the first tile. -/

namespace FLatticePaper.Tiles.AltStdBottom

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.Standard (IsBase)
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow)

/-- The first tile of a forward horizontal string starting with `q` is the one tile at the start. -/
theorem first_mem (wh : BinaryWord) (hq : wh.head? = some .q) (x : GInt) (hx : x ∈ tileShape ZTile.one) :
    x ∈ placedSites (hStringAt wh 0) := by
  have hd := hStringAt_head_q wh 0 hq
  cases h : hStringAt wh 0 with
  | nil =>
    have hne := GlueStringDecomp.hStringAt_ne wh 0 (by intro e; simp [e] at hq)
    exact absurd h hne
  | cons t l =>
    rw [h] at hd
    simp only [List.headD_cons] at hd
    subst hd
    simp only [placedSites, List.flatMap_cons, List.mem_append, List.mem_map]
    exact Or.inl ⟨x, hx, by simp⟩

/-- **Two odometers respecting one forward horizontal string and normalised with slope `0` on its first tile agree on the string
up to a constant.** -/
theorem agree_on_hString (wh : BinaryWord) (hq : wh.head? = some .q) (S T : GInt → ℤ) (β β' : ℤ)
    (hS : RespectsTiles .horizontal false (hStringAt wh 0) S) (hT : RespectsTiles .horizontal false (hStringAt wh 0) T)
    (hNS : ∀ x ∈ tileShape ZTile.one, S x = zTileOdo ZTile.one x + β)
    (hNT : ∀ x ∈ tileShape ZTile.one, T x = zTileOdo ZTile.one x + β') :
    ∃ d : ℤ, ∀ x ∈ placedSites (hStringAt wh 0), T x = S x + d := by
  obtain ⟨F, hFts, hFv, hFr⟩ := hS
  obtain ⟨G, hGts, hGv, hGr⟩ := hT
  have hts : G.ts = F.ts := by rw [hGts, hFts]
  have hWF : ∀ k < F.n, ∀ j < F.n, ∀ x ∈ F.dom k, x ∈ F.dom j → F.odo k x = F.odo j x :=
    fun k hk j hj x h1 h2 => by rw [← hFv k hk x h1, hFv j hj x h2]
  have hWG : ∀ k < G.n, ∀ j < G.n, ∀ x ∈ G.dom k, x ∈ G.dom j → G.odo k x = G.odo j x :=
    fun k hk j hj x h1 h2 => by rw [← hGv k hk x h1, hGv j hj x h2]
  obtain ⟨a, c, hac⟩ := PTFamily.exists_affine_of_respects_gen .horizontal false F G hts hFr hGr hWF hWG
    (fun k hk => adj_hStringAt wh 0 F hFts k hk)
  have key : ∀ x ∈ placedSites (hStringAt wh 0), T x = S x + a.1 * x.1 + a.2 * x.2 + c := by
    intro x hx
    rw [StdPseudoAnchoredSets.mem_placedSites_iff_tileCovers, ← covers_iff_dom F _ hFts] at hx
    obtain ⟨k, hk, hxk⟩ := hx
    have hkG : k < G.n := by rw [PTFamily.n_eq_of_ts F G hts]; exact hk
    have hxG : x ∈ G.dom k := by rw [PTFamily.dom_eq_of_ts F G hts k]; exact hxk
    rw [hGv k hkG x hxG, hFv k hk x hxk, hac k hk x]
  have p0 : ((0 : ℤ), (0 : ℤ)) ∈ tileShape ZTile.one := by decide
  have p1 : ((1 : ℤ), (0 : ℤ)) ∈ tileShape ZTile.one := by decide
  have p2 : ((0 : ℤ), (1 : ℤ)) ∈ tileShape ZTile.one := by decide
  have e0 := key _ (first_mem wh hq _ p0)
  have e1 := key _ (first_mem wh hq _ p1)
  have e2 := key _ (first_mem wh hq _ p2)
  rw [hNS _ p0, hNT _ p0] at e0
  rw [hNS _ p1, hNT _ p1] at e1
  rw [hNS _ p2, hNT _ p2] at e2
  have ha1 : a.1 = 0 := by simp at e0 e1; linarith
  have ha2 : a.2 = 0 := by simp at e0 e2; linarith
  refine ⟨c, fun x hx => ?_⟩
  rw [key x hx, ha1, ha2]
  ring

/-- **The even alternate and the even standard tile odometers of a word below the current one agree on the bottom string of
the even standard tile up to a constant** (for the paper data, at a word that is not a base word). -/
theorem alt_std_bottom (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hAB : PaperAltBdry D) (hAnc : PaperAltAnc D) (f : Word → JSlice) (n : ℕ) (hgood : GoodBelow D f n) (u : Word)
    (hu : u.length < n) (hnb : ¬ IsBase u) :
    ∃ d : ℤ, ∀ x ∈ placedSites (hStringAt (hWordOf u true) 0),
      x ∈ (f u).aEven.dom ∧ x ∈ (f u).tEven.dom ∧ (f u).aEven.val x = (f u).tEven.val x + d := by
  have hJ := (hgood u hu).1
  have hRt := (WeakStepAssembly.slice_respects D f u hJ).2
  obtain ⟨-, -, hT, -⟩ := hJ
  obtain ⟨-, -, -, -, -, -, -, hRH, -, -, -, hdom⟩ := hT
  have hRa := hRH.1
  rw [SurgicalAlt.altFwdHAnchor, (hAnc u).1] at hRa
  obtain ⟨-, s2, -, s4⟩ := TileHalfTurnInput.slopes_below D hS hA f n hgood u hu
  obtain ⟨β, hNt⟩ := s2
  obtain ⟨β', hNa⟩ := s4
  have hq := (hWordOf_head_last u true).1
  obtain ⟨d, hd⟩ := agree_on_hString (hWordOf u true) hq (f u).tEven.val (f u).aEven.val β β' hRt.2.1 hRa
    (fun x hx => by have := (hNt x hx).2; simp only [normed, dotS, Prod.fst_zero, Prod.snd_zero] at this; linarith)
    (fun x hx => by have := (hNa x hx).2; simp only [normed, dotS, Prod.fst_zero, Prod.snd_zero] at this; linarith)
  refine ⟨d, fun x hx => ⟨?_, ?_, hd x hx⟩⟩
  · rw [hdom, (hAB u).2]
    exact (AltItem3.alt_item3_even hnb).1 x (by
      rw [hPartialTiles, placedSites_append, List.mem_append]; exact Or.inl hx)
  · have h := hRt.1 x
    simp only [placedSites_append, List.mem_append, Finset.mem_coe] at h
    exact h (by tauto)

end FLatticePaper.Tiles.AltStdBottom
