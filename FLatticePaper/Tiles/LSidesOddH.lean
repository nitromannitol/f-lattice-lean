import FLatticePaper.Tiles.LSidesOddTriple
import FLatticePaper.Tiles.AltStdBottom
import FLatticePaper.Tiles.SameParentAlt

/-! # The horizontal side of the elongated odd L-correction

For `w = pre 2^k` (`pre` not a base word and not ending in `2`) the bottom string of the odd child of `w` is the bottom string
of `2(k+1)` copies of the even register `u2` of `pre` and of one copy of its odd register `u1` (`GlueStringDecomp`, unrolled
through the trailing `2`s: the copies `Q^{+,1}`, `Q^{+,2}` of each level and the copy `P^+` of the odd child of the level below),
all placed with affine factor `0`. The heads of the elongated `-` odd L-correction are copies of the even alternate tile of `u2`
at exactly these `2(k+1)` places, with affine factor `0`, and its bridge is the copy of `u1`. On the bottom string of a copy the
alternate and the standard even odometers of `u2` agree up to a constant (`AltStdBottom.alt_std_bottom`), so the glued
L-corrected odometer and the tile odometer of the child differ by one constant on each copy, and the consecutive copies meet at
the ends of their strings. When `pre` ends in `3` the copy of `u2` on the bottom of the decomposition of `pre` is the short `+`
even L-correction of `pre` without its last letter, which agrees with the even tile odometer on its bottom side
(`lemma:l_correct_existence`, the L part of the joint family). -/

namespace FLatticePaper.Tiles.LSidesOddH

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (IsBase)
open FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointGlue (PiecesAgree gluedOdo pieceVal)
open FLatticePaper.Tiles.JointInduction (GoodBelow regsAt_lt)
open FLatticePaper.Tiles.WeakStepPaper (paperS)
open FLatticePaper.Tiles.SurgicalWeak (regsAt regOdo)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.LSidesOddV (PlacedEqA placedEqA_trans placedEqA_of_respects wk2 wk2_trailing side_mem_dom vA vU vV aQ)
open FLatticePaper.Tiles.ConnectedAltL (oStemPos oHeadPos)
open FLatticePaper.Tiles.TileHalfTurnL (oBridgePos oAffAt oStemC oBridgeC oHeadC)

/-! ### Copies on a string -/

/-- `o` contains the copy of `q` placed at `s` with affine factor `a`, up to one constant, on the sites of the string `ts` of
`q`. -/
def StrEq (o q : PartialOdometer) (ts : List (ZTile × GInt)) (s a : Site) : Prop :=
  ∃ b : ℤ, ∀ y ∈ placedSites ts, y + s ∈ o.dom ∧ o.val (y + s) = q.val y + dotS a (y + s) + b

theorem strEq_of_placed {o q : PartialOdometer} {ts : List (ZTile × GInt)} {s a : Site} (h : PlacedEqA o q s a)
    (hts : ∀ y ∈ placedSites ts, y ∈ q.dom) : StrEq o q ts s a := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun y hy => hb y (hts y hy)⟩

theorem strEq_trans {o q r : PartialOdometer} {ts : List (ZTile × GInt)} {s t a a' : Site} (h1 : PlacedEqA o q s a)
    (h2 : StrEq q r ts t a') : StrEq o r ts (t + s) (a + a') := by
  obtain ⟨b1, h1⟩ := h1
  obtain ⟨b2, h2⟩ := h2
  refine ⟨b1 + b2 - dotS a' s, fun y hy => ?_⟩
  obtain ⟨m2, e2⟩ := h2 y hy
  obtain ⟨m1, e1⟩ := h1 _ m2
  rw [← add_assoc]
  refine ⟨m1, ?_⟩
  rw [e1, e2]
  simp only [dotS, Prod.fst_add, Prod.snd_add]
  ring

/-- The end of a forward horizontal string ending in `p` lies on the string. -/
theorem last_mem (wh : BinaryWord) (hw : wh ≠ []) (hl : wh.getLast? = some Letter.p) (x : GInt)
    (hx : x ∈ tileShape ZTile.zero) : x + lastPosOf (hStringAt wh 0) ∈ placedSites (hStringAt wh 0) := by
  have hne : hStringAt wh 0 ≠ [] := GlueStringDecomp.hStringAt_ne wh 0 hw
  have h := hStringAt_getLastD_zero wh 0 hw hl
  have hmem : (hStringAt wh 0).getLastD (ZTile.zero, 0) ∈ hStringAt wh 0 := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    exact List.getLast_mem hne
  rw [h] at hmem
  simp only [placedSites, List.mem_flatMap, List.mem_map]
  exact ⟨_, hmem, x, hx, rfl⟩

/-- The start and the end of the bottom string of the even tile of `u`: `0` and `v_{q,1}`. -/
theorem bot_ends_even (u : Word) :
    (0 : GInt) ∈ placedSites (hStringAt (hWordOf u true) 0) ∧
      texV1Even (fracEven u) ∈ placedSites (hStringAt (hWordOf u true) 0) := by
  refine ⟨AltStdBottom.first_mem _ (hWordOf_head_last u true).1 _ (by decide), ?_⟩
  have h := last_mem (hWordOf u true) (GlueStringDecomp.hWord_ne u true) (hWordOf_head_last u true).2
    ((1 : ℤ), (1 : ℤ)) (by decide)
  rw [GlueStringDecomp.lp_bot_even u 0, zero_add] at h
  convert h using 1
  abel

/-- The start and the end of the bottom string of the odd tile of `u`: `0` and `v_{p,1}`. -/
theorem bot_ends_odd (u : Word) :
    (0 : GInt) ∈ placedSites (hStringAt (hWordOf u false) 0) ∧
      texV1Odd (fracOdd u) ∈ placedSites (hStringAt (hWordOf u false) 0) := by
  refine ⟨AltStdBottom.first_mem _ (hWordOf_head_last u false).1 _ (by decide), ?_⟩
  have h := last_mem (hWordOf u false) (GlueStringDecomp.hWord_ne u false) (hWordOf_head_last u false).2
    ((1 : ℤ), (1 : ℤ)) (by decide)
  rw [GlueStringDecomp.lp_bot_odd u 0, zero_add] at h
  convert h using 1
  abel

/-! ### The bottom string of the odd child, by copies -/

/-- **The bottom string of the odd child splits into the bottom strings of three copies**: `Q^{+,1}` and `Q^{+,2}` of the even
register and `P^+` of the odd register. -/
theorem hsplit (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2)) (z : GInt)
    (hz : z ∈ placedSites (hStringAt (hWordOf w false) 0)) :
    z - p0Off w .q1DPlus ∈ placedSites (hStringAt (hWordOf u2 true) 0) ∨
      z - (p0Off w .q1DPlus + vQ1 w) ∈ placedSites (hStringAt (hWordOf u2 true) 0) ∨
      z - p0Off w .p1Plus ∈ placedSites (hStringAt (hWordOf u1 false) 0) := by
  have hp : (parentsAt w).odd = fracOdd u1 := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])
  have hq : (parentsAt w).even = fracEven u2 := (WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])
  have sh : ∀ (X : BinaryWord) (c : GInt) (y : GInt), y ∈ placedSites (hStringAt X c) →
      y - c ∈ placedSites (hStringAt X 0) := by
    intro X c y hy
    rw [show c = (0 : GInt) + c by rw [zero_add], ← GlueChain.hStringAt_shift, AltItem3.mem_placedSites_map] at hy
    exact hy
  by_cases hph : phase w = 1
  · have hW : W1Odd w = true := by simp [W1Odd, hph]
    obtain ⟨h1, -, -, -⟩ := GlueStringDecomp.odd_of w u1 u2 hreg hph
    rw [h1, placedSites_append, placedSites_append, List.mem_append, List.mem_append] at hz
    have e0 : p0Off w .p1Plus = 0 := by simp [p0Off, SurgicalDict.offsetP0, hW]
    have e1 : p0Off w .q1DPlus = texV1Odd (fracOdd u1) := by simp [p0Off, SurgicalDict.offsetP0, hW, vP1, hp]
    have e2 : vQ1 w = texV1Even (fracEven u2) := by simp [vQ1, hq]
    rw [e0, e1, e2]
    rcases hz with (h | h) | h
    · right; right; rw [sub_zero]; exact h
    · left; exact sh _ _ _ h
    · right; left; exact sh _ _ _ h
  · have hW : W1Odd w = false := by simp [W1Odd, hph]
    obtain ⟨h1, -, -, -⟩ := GlueStringDecomp.odd_ef w u1 u2 hreg hph
    rw [h1, placedSites_append, placedSites_append, List.mem_append, List.mem_append] at hz
    have e0 : p0Off w .p1Plus = texV1Even (fracEven u2) + texV1Even (fracEven u2) := by
      simp [p0Off, SurgicalDict.offsetP0, hW, vQ1, hq]
    have e1 : p0Off w .q1DPlus = 0 := by simp [p0Off, SurgicalDict.offsetP0, hW]
    have e2 : vQ1 w = texV1Even (fracEven u2) := by simp [vQ1, hq]
    rw [e0, e1, e2, zero_add, sub_zero]
    rcases hz with (h | h) | h
    · left; exact h
    · right; left; exact sh _ _ _ h
    · right; right; exact sh _ _ _ h

/-! ### The entries of the decomposition on the bottom -/

theorem tOP_entry0 (S : SurgicalWeak.WeakData) (pO pE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (v : Word) : (tileOddPieces S pO pE lE v)[0]? =
      some (stdPiece (regOdo S pO pE (regsAt v).1 true) (p0Off v .p1Plus) (p0Aff v .p1Plus)) := by
  simp [tileOddPieces]

theorem tOP_entry2 (S : SurgicalWeak.WeakData) (pO pE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (v : Word) : (tileOddPieces S pO pE lE v)[2]? =
      some (stdPiece (if decide (v.getLast? = some Digit.three) && W1Odd v then lE v.dropLast true false
        else regOdo S pO pE (regsAt v).2 false) (p0Off v .q1DPlus) (p0Aff v .q1DPlus)) := by
  simp [tileOddPieces]

theorem tOP_entry3 (S : SurgicalWeak.WeakData) (pO pE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (v : Word) : (tileOddPieces S pO pE lE v)[3]? =
      some (stdPiece (if decide (v.getLast? = some Digit.three) && !W1Odd v then lE v.dropLast true false
        else regOdo S pO pE (regsAt v).2 false) (p0Off v .q1DPlus + vQ1 v) (p0Aff v .q1DPlus)) := by
  simp [tileOddPieces]

theorem p1PlusAff_zero (w : Word) : p0Aff w .p1Plus = 0 := by
  cases h : W1Odd w <;> simp [p0Aff, h, pairAffine, offsetA]

theorem q1DPlusAff_zero (w : Word) : p0Aff w .q1DPlus = 0 := by
  cases h : W1Odd w <;> simp [p0Aff, h, pairAffine, offsetA]

/-! ### The positions of the copies on the bottom string -/

/-- The copy `m` of the even register on the bottom string of the odd child of `pre 2^k` (`0 ≤ m ≤ 2k+1`). -/
def qPos (pre : Word) (m : ℕ) : Site := (if W1Odd pre then vA pre else 0) + (m : ℤ) • vU pre

/-- The copy of the odd register on the bottom string of the odd child of `pre 2^k`. -/
def brPos (pre : Word) (k : ℕ) : Site := if W1Odd pre then 0 else ((2 * k + 2 : ℕ) : ℤ) • vU pre

theorem p1Plus_G (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    p0Off (wk2 pre k) .p1Plus = if W1Odd pre then 0 else (2 : ℤ) • vU pre := by
  pos_alg

theorem q1DPlus_G (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    p0Off (wk2 pre k) .q1DPlus = if W1Odd pre then vA pre + ((2 * k : ℕ) : ℤ) • vU pre else 0 := by
  pos_alg

theorem vQ1_G (pre : Word) (k : ℕ) : vQ1 (wk2 pre k) = vU pre := by
  simp only [vQ1, JointRot.parents_append_twos pre k, vU]

/-- An entry `2` or `3` of the odd decomposition of `v` (the copies `Q^{+,1}`, `Q^{+,2}` of the even register `u2`) is, on the
bottom string of `u2`, a copy of the even tile odometer of `u2`: a standard copy, or after a `3` the short `+` even L-correction
of `v` without its last letter, which agrees with it on its bottom side. -/
theorem entryQ_strEq (D : JointData) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (v x u2 : Word)
    (hreg : regsAt v = (some x, some u2)) (hv : ¬ IsBase v) (hgood : GoodBelow D f v.length) (o : PartialOdometer)
    (hR : RespectsPieces o (tileOddPieces D.S (fun u => (below f v u).tOdd) (fun u => (below f v u).tEven)
      (fun u => (below f v u).lEven) v)) (e : ℕ) (he : e = 2 ∨ e = 3) :
    StrEq o (f u2).tEven (hStringAt (hWordOf u2 true) 0) (if e = 2 then p0Off v .q1DPlus else p0Off v .q1DPlus + vQ1 v) 0 := by
  have hl2 : u2.length < v.length := regsAt_lt v u2 (Or.inr (by rw [hreg]))
  have hb2 : below f v u2 = f u2 := by simp only [below, if_pos hl2]
  obtain ⟨hS2, -⟩ := hgood u2 hl2
  have hR2 := (WeakStepAssembly.slice_respects D f u2 hS2).2
  have hin : ∀ y ∈ placedSites (hStringAt (hWordOf u2 true) 0), y ∈ (f u2).tEven.dom :=
    fun y hy => side_mem_dom hR2 .hPlus hy
  -- the entry as a piece: the even register, or an L-correction after a `3`
  have hent : ∃ q : PartialOdometer, (q = (f u2).tEven ∨ (v.getLast? = some Digit.three ∧
      q = (below f v v.dropLast).lEven true false)) ∧
      PlacedEqA o q (if e = 2 then p0Off v .q1DPlus else p0Off v .q1DPlus + vQ1 v) 0 := by
    rcases he with rfl | rfl
    · have e2 := tOP_entry2 D.S (fun u => (below f v u).tOdd) (fun u => (below f v u).tEven)
        (fun u => (below f v u).lEven) v
      rw [hreg, q1DPlusAff_zero] at e2
      simp only [regOdo, hb2] at e2
      refine ⟨_, ?_, by simpa using placedEqA_of_respects hR e2⟩
      split_ifs with hc
      · have h3 : v.getLast? = some Digit.three := by
          by_contra hne
          simp [hne] at hc
        exact Or.inr ⟨h3, rfl⟩
      · exact Or.inl rfl
    · have e3 := tOP_entry3 D.S (fun u => (below f v u).tOdd) (fun u => (below f v u).tEven)
        (fun u => (below f v u).lEven) v
      rw [hreg, q1DPlusAff_zero] at e3
      simp only [regOdo, hb2] at e3
      refine ⟨_, ?_, by simpa using placedEqA_of_respects hR e3⟩
      split_ifs with hc
      · have h3 : v.getLast? = some Digit.three := by
          by_contra hne
          simp [hne] at hc
        exact Or.inr ⟨h3, rfl⟩
      · exact Or.inl rfl
  obtain ⟨q, hq | ⟨h3, hq⟩, hP⟩ := hent
  · subst hq
    exact strEq_of_placed hP hin
  · subst hq
    have hvd : v = v.dropLast ++ [Digit.three] := SameParentAlt.eq_snoc_of_getLast v Digit.three h3
    have hu2 : u2 = v.dropLast := by
      have := ConnectedAltL.regs_pre_snd v.dropLast Digit.three (by decide)
      rw [← hvd, hreg] at this
      exact Option.some.inj this
    subst hu2
    have hdef := JointRot.evenLDefined_dropLast hv h3
    have hLP := ((hgood v.dropLast hl2).1.2.2.2).2 true false hdef
    rw [hlS] at hLP
    obtain ⟨-, c, hc⟩ := hLP.2
    obtain ⟨b, hb⟩ := hP
    rw [hb2] at hb
    refine ⟨c + b, fun y hy => ?_⟩
    have hy' : y ∈ placedSites (sideString (hWordOf v.dropLast true) (vWordOf v.dropLast true) 0 .hPlus) := hy
    obtain ⟨hyL, -, hyv⟩ := hc .hPlus (by simp [paperLSides]) y hy'
    obtain ⟨m1, e1⟩ := hb y hyL
    refine ⟨m1, ?_⟩
    rw [e1, hyv]
    simp only [dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero]
    ring

/-! ### The nested copies on the bottom string -/

theorem posO (pre : Word) (h0 : trailingCount Digit.two pre = 0) (hb : W1Odd pre = true) (k : ℕ) :
    p0Off (wk2 pre k) .p1Plus = 0 ∧ p0Off (wk2 pre k) .q1DPlus = qPos pre (2 * k) ∧
      p0Off (wk2 pre k) .q1DPlus + vQ1 (wk2 pre k) = qPos pre (2 * k + 1) ∧ brPos pre k = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [p1Plus_G pre h0]; simp [hb]
  · rw [q1DPlus_G pre h0]; simp [qPos, hb]
  · rw [q1DPlus_G pre h0, vQ1_G]
    simp only [qPos, hb, if_true]
    ext <;> simp <;> ring
  · simp [brPos, hb]

theorem posE (pre : Word) (h0 : trailingCount Digit.two pre = 0) (hb : W1Odd pre = false) (k : ℕ) :
    p0Off (wk2 pre k) .p1Plus = (2 : ℤ) • vU pre ∧ p0Off (wk2 pre k) .q1DPlus = qPos pre 0 ∧
      p0Off (wk2 pre k) .q1DPlus + vQ1 (wk2 pre k) = qPos pre 1 ∧ brPos pre k = ((2 * k + 2 : ℕ) : ℤ) • vU pre := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [p1Plus_G pre h0]; simp [hb]
  · rw [q1DPlus_G pre h0]; simp [qPos, hb]
  · rw [q1DPlus_G pre h0, vQ1_G]; simp [qPos, hb]
  · simp [brPos, hb]

/-- **The nested copies on the bottom string of the odd child of `pre 2^k`**: an odometer respecting the odd decomposition of
`pre 2^k` contains, on the bottom string of the even register `u2` of `pre`, its even tile odometer at each `qPos pre m`
(`m ≤ 2k+1`), and the odd register `u1` of `pre` at `brPos pre k`, all with affine factor `0`; these copies cover the bottom
string of the child. -/
theorem nestedH (D : JointData) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (pre : Word) (hpre : ¬ IsBase pre)
    (h0 : trailingCount Digit.two pre = 0) (u1 u2 : Word) (hreg : regsAt pre = (some u1, some u2)) :
    ∀ (k : ℕ) (o : PartialOdometer), GoodBelow D f (wk2 pre k).length →
      RespectsPieces o (tileOddPieces D.S (fun u => (below f (wk2 pre k) u).tOdd) (fun u => (below f (wk2 pre k) u).tEven)
        (fun u => (below f (wk2 pre k) u).lEven) (wk2 pre k)) →
      (∀ m ≤ 2 * k + 1, StrEq o (f u2).tEven (hStringAt (hWordOf u2 true) 0) (qPos pre m) 0) ∧
      PlacedEqA o (f u1).tOdd (brPos pre k) 0 ∧
      ∀ z ∈ placedSites (hStringAt (hWordOf (wk2 pre k) false) 0),
        (∃ m ≤ 2 * k + 1, z - qPos pre m ∈ placedSites (hStringAt (hWordOf u2 true) 0)) ∨
          z - brPos pre k ∈ placedSites (hStringAt (hWordOf u1 false) 0) := by
  have hl1 : u1.length < pre.length := regsAt_lt pre u1 (Or.inl (by rw [hreg]))
  intro k
  induction k with
  | zero =>
    intro o hgood hR
    have hr0 : regsAt (wk2 pre 0) = (some u1, some u2) := by simpa [wk2] using hreg
    have hnb : ¬ IsBase (wk2 pre 0) := by simpa [wk2] using hpre
    have hl1' : u1.length < (wk2 pre 0).length := by simpa [wk2] using hl1
    have hb1 : below f (wk2 pre 0) u1 = f u1 := by simp only [below, if_pos hl1']
    have e0 := tOP_entry0 D.S (fun u => (below f (wk2 pre 0) u).tOdd) (fun u => (below f (wk2 pre 0) u).tEven)
      (fun u => (below f (wk2 pre 0) u).lEven) (wk2 pre 0)
    rw [hr0, p1PlusAff_zero] at e0
    simp only [regOdo, hb1] at e0
    have hP := placedEqA_of_respects hR e0
    have q2 := entryQ_strEq D hlS f (wk2 pre 0) u1 u2 hr0 hnb hgood o hR 2 (Or.inl rfl)
    have q3 := entryQ_strEq D hlS f (wk2 pre 0) u1 u2 hr0 hnb hgood o hR 3 (Or.inr rfl)
    simp only [if_true, show ¬ (3 = 2) from by decide, if_false] at q2 q3
    have hsp := hsplit (wk2 pre 0) u1 u2 hr0
    cases hb : W1Odd pre
    · obtain ⟨a0, a1, a2, a3⟩ := posE pre h0 hb 0
      rw [a2] at q3 hsp
      rw [a1] at q2 hsp
      rw [a0] at hP hsp
      refine ⟨fun m hm => ?_, by rw [a3]; simpa using hP, fun z hz => ?_⟩
      · rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
        · exact q2
        · exact q3
      · rcases hsp z hz with h | h | h
        · exact Or.inl ⟨0, by omega, h⟩
        · exact Or.inl ⟨1, by omega, h⟩
        · right; rw [a3]; simpa using h
    · obtain ⟨a0, a1, a2, a3⟩ := posO pre h0 hb 0
      rw [a2] at q3 hsp
      rw [a1] at q2 hsp
      rw [a0] at hP hsp
      refine ⟨fun m hm => ?_, by rw [a3]; exact hP, fun z hz => ?_⟩
      · rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
        · exact q2
        · exact q3
      · rcases hsp z hz with h | h | h
        · exact Or.inl ⟨0, by omega, h⟩
        · exact Or.inl ⟨1, by omega, h⟩
        · right; rw [a3]; exact h
  | succ k ih =>
    intro o hgood hR
    obtain ⟨hnb, -, -⟩ := LSidesOddV.wk2_facts pre hpre (k + 1)
    obtain ⟨hnb', hr2', -⟩ := LSidesOddV.wk2_facts pre hpre k
    have hws := LSidesOddV.wk2_succ pre k
    have hlt : (wk2 pre k).length < (wk2 pre (k + 1)).length := by rw [hws]; simp
    have hrs : regsAt (wk2 pre (k + 1)) = (some (wk2 pre k), some u2) := by
      rw [LSidesOddV.regsAt_wk2_succ, hr2', hreg]
    have hbk : below f (wk2 pre (k + 1)) (wk2 pre k) = f (wk2 pre k) := by simp only [below, if_pos hlt]
    have e0 := tOP_entry0 D.S (fun u => (below f (wk2 pre (k + 1)) u).tOdd)
      (fun u => (below f (wk2 pre (k + 1)) u).tEven) (fun u => (below f (wk2 pre (k + 1)) u).lEven) (wk2 pre (k + 1))
    rw [hrs, p1PlusAff_zero] at e0
    simp only [regOdo, hbk] at e0
    have hP := placedEqA_of_respects hR e0
    have q2 := entryQ_strEq D hlS f (wk2 pre (k + 1)) (wk2 pre k) u2 hrs hnb hgood o hR 2 (Or.inl rfl)
    have q3 := entryQ_strEq D hlS f (wk2 pre (k + 1)) (wk2 pre k) u2 hrs hnb hgood o hR 3 (Or.inr rfl)
    simp only [if_true, show ¬ (3 = 2) from by decide, if_false] at q2 q3
    have hgood' : GoodBelow D f (wk2 pre k).length := fun u hu => hgood u (lt_trans hu hlt)
    have hRk : RespectsPieces (f (wk2 pre k)).tOdd (tileOddPieces D.S (fun u => (below f (wk2 pre k) u).tOdd)
        (fun u => (below f (wk2 pre k) u).tEven) (fun u => (below f (wk2 pre k) u).lEven) (wk2 pre k)) :=
      (((hgood (wk2 pre k) hlt).1.2.2.1).2.1 hnb').1
    obtain ⟨hn, hbr, hcov⟩ := ih (f (wk2 pre k)).tOdd hgood' hRk
    have hsp := hsplit (wk2 pre (k + 1)) (wk2 pre k) u2 hrs
    cases hb : W1Odd pre
    · obtain ⟨a0, a1, a2, a3⟩ := posE pre h0 hb (k + 1)
      have a3' := (posE pre h0 hb k).2.2.2
      rw [a2] at q3 hsp
      rw [a1] at q2 hsp
      rw [a0] at hP hsp
      have qs : ∀ m : ℕ, qPos pre (m + 2) = qPos pre m + (2 : ℤ) • vU pre := by
        intro m; simp only [qPos, hb, Bool.false_eq_true, if_false]; push_cast; rw [add_smul]; abel
      refine ⟨fun m hm => ?_, ?_, fun z hz => ?_⟩
      · rcases m with _ | _ | m
        · exact q2
        · exact q3
        · rw [show m + 1 + 1 = m + 2 from rfl, qs]
          simpa using strEq_trans hP (hn m (by omega))
      · rw [a3, show ((2 * (k + 1) + 2 : ℕ) : ℤ) • vU pre = ((2 * k + 2 : ℕ) : ℤ) • vU pre + (2 : ℤ) • vU pre by
          push_cast; rw [← add_smul]; ring_nf, ← a3']
        simpa using placedEqA_trans hP hbr
      · rcases hsp z hz with h | h | h
        · exact Or.inl ⟨0, by omega, h⟩
        · exact Or.inl ⟨1, by omega, h⟩
        · rcases hcov _ h with ⟨m, hm, hm'⟩ | hbz
          · left
            refine ⟨m + 2, by omega, ?_⟩
            rw [qs]; convert hm' using 1; abel
          · right
            rw [a3, show ((2 * (k + 1) + 2 : ℕ) : ℤ) • vU pre = ((2 * k + 2 : ℕ) : ℤ) • vU pre + (2 : ℤ) • vU pre by
              push_cast; rw [← add_smul]; ring_nf, ← a3']
            convert hbz using 1; abel
    · obtain ⟨a0, a1, a2, a3⟩ := posO pre h0 hb (k + 1)
      have a3' := (posO pre h0 hb k).2.2.2
      rw [a3'] at hbr hcov
      rw [a2] at q3 hsp
      rw [a1] at q2 hsp
      rw [a0] at hP hsp
      refine ⟨fun m hm => ?_, ?_, fun z hz => ?_⟩
      · by_cases hmk : m ≤ 2 * k + 1
        · simpa using strEq_trans hP (hn m hmk)
        · rcases (show m = 2 * (k + 1) ∨ m = 2 * (k + 1) + 1 by omega) with rfl | rfl
          · exact q2
          · exact q3
      · rw [a3]
        simpa using placedEqA_trans hP hbr
      · rcases hsp z hz with h | h | h
        · exact Or.inl ⟨2 * (k + 1), by omega, h⟩
        · exact Or.inl ⟨2 * (k + 1) + 1, by omega, h⟩
        · rw [sub_zero] at h
          rcases hcov _ h with ⟨m, hm, hm'⟩ | hbz
          · exact Or.inl ⟨m, by omega, hm'⟩
          · right; rw [a3]; exact hbz

/-! ### The heads and the bridge of the `-` odd L-correction -/

set_option hygiene false in
/-- Unfolds a position of the `-` odd L-correction of `pre 2^k` into the parents of `pre` and `k`. -/
macro "posh_alg" : tactic => `(tactic| (
  obtain ⟨ht, hs⟩ := wk2_trailing pre h0 k
  have hW := JointRot.W1Odd_append_replicate pre k Digit.two (by decide)
  have hp := JointRot.parents_append_twos pre k
  simp only [oHeadPos, oBridgePos, oAffAt, oHeadC, oBridgeC, oddLInitOff, oddLInitAff, p0Off, p0Aff,
    SurgicalDict.offsetP0, vP1, vP2, vQ1, vQ2, altOff, altAff, ht, hs, hW, hp, vA, vU, vV, aQ, brPos]
  cases hb : W1Odd pre <;> simp only [oddKCoeff, ↓reduceIte, Bool.false_eq_true] <;> ext <;>
    simp [SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, texV1Odd, texV1Even, texV2, offsetA, pairAffine] <;> ring))

theorem headPosM_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k i : ℕ) :
    oHeadPos (wk2 pre k) false i =
      if W1Odd pre then vA pre + (i : ℤ) • vU pre else ((2 * k + 1 : ℕ) : ℤ) • vU pre - (i : ℤ) • vU pre := by
  posh_alg

theorem headAffM_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k i : ℕ) :
    oAffAt (wk2 pre k) false (oHeadC (wk2 pre k) false i) = 0 := by
  posh_alg

theorem bridgePosMG (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    oBridgePos (wk2 pre k) false = brPos pre k := by
  posh_alg

theorem bridgeAffMG (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    oAffAt (wk2 pre k) false (oBridgeC (wk2 pre k) false) = 0 := by
  posh_alg

/-- The head of the `-` odd L-correction on the copy `m` of the bottom string. -/
def hIdx (pre : Word) (k m : ℕ) : ℕ := if W1Odd pre then m else 2 * k + 1 - m

theorem head_at (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k m : ℕ) (hm : m ≤ 2 * k + 1) :
    oHeadPos (wk2 pre k) false (hIdx pre k m) = qPos pre m ∧ hIdx pre k m < 2 * (k + 1) := by
  rw [headPosM_eq pre h0]
  simp only [hIdx, qPos]
  cases hb : W1Odd pre
  · simp only [Bool.false_eq_true, if_false, zero_add]
    refine ⟨?_, by omega⟩
    rw [Nat.cast_sub hm, ← sub_smul]
    congr 1
    push_cast
    ring
  · simp only [if_true, true_and]
    omega

/-! ### One constant on the bottom string -/

/-- **The horizontal side of the elongated `-` odd L-correction after trailing `2`s** (`lemma:l_correc_properties` (2), rotated,
horizontal part): for `w = pre 2^k` with `pre` not a base word and not ending in `2`, and the even register of `pre` not a base
word, the glued elongated `-` L-corrected odometer and the tile odometer of the odd child differ by one constant on the bottom
string of the child. -/
theorem oddL_hor_minus_k (D : JointData) (hS : D.S = paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hAB : PaperAltBdry D) (hAnc : PaperAltAnc D) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (pre : Word)
    (hpre : ¬ IsBase pre) (h0 : trailingCount Digit.two pre = 0) (u1 u2 : Word) (hreg : regsAt pre = (some u1, some u2))
    (hu2 : ¬ IsBase u2) (k : ℕ) (hgood : GoodBelow D f (wk2 pre k).length)
    (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f (wk2 pre k)) (wk2 pre k) wo we wao wae tod tev aod aev) (κ : ℕ → ℤ)
    (hag : PiecesAgree (LStepAssembly.oddPs D f (wk2 pre k) false true) κ) :
    ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 .hPlus),
      x ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) false true) κ).dom ∧ x ∈ tod.dom ∧ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) false true) κ).val x = tod.val x + c := by
  obtain ⟨hnb, -, -⟩ := LSidesOddV.wk2_facts pre hpre k
  obtain ⟨hn, hbr, hcov⟩ := nestedH D hlS f pre hpre h0 u1 u2 hreg k tod hgood (hT.2.1 hnb).1
  have hl1 : u1.length < (wk2 pre k).length :=
    lt_of_lt_of_le (regsAt_lt pre u1 (Or.inl (by rw [hreg]))) (by simp [wk2])
  have hl2 : u2.length < (wk2 pre k).length :=
    lt_of_lt_of_le (regsAt_lt pre u2 (Or.inr (by rw [hreg]))) (by simp [wk2])
  obtain ⟨d, hd⟩ := AltStdBottom.alt_std_bottom D hS hA hAB hAnc f (wk2 pre k).length hgood u2 hl2 hu2
  have hb1 : below f (wk2 pre k) u1 = f u1 := by simp only [below, if_pos hl1]
  have hb2 : below f (wk2 pre k) u2 = f u2 := by simp only [below, if_pos hl2]
  obtain ⟨ht, hs⟩ := wk2_trailing pre h0 k
  have hregB : (!(stripTrailing Digit.two (wk2 pre k)).isEmpty &&
      (stripTrailing Digit.two (wk2 pre k)).all (fun d => decide (d = Digit.three))) = false := by
    rw [hs]
    by_contra hc
    simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
      decide_eq_true_eq] at hc
    exact hpre (Or.inr (Or.inl hc.2))
  have hL := TileHalfTurnL.oLP_eq D.S (fun u => (below f (wk2 pre k) u).tOdd) (fun u => (below f (wk2 pre k) u).tEven)
    (fun u => (below f (wk2 pre k) u).aOdd) (fun u => (below f (wk2 pre k) u).aEven) (wk2 pre k) false true hregB
  rw [hs, ht, hreg] at hL
  simp only [regOdo, hb1, hb2] at hL
  have hlen : ((List.range (k + 1)).map (fun j => stdPiece (f u2).tEven (oStemPos (wk2 pre k) false j)
      (oAffAt (wk2 pre k) false (oStemC (wk2 pre k) false j)))).length = k + 1 := by simp
  have hLb : (LStepAssembly.oddPs D f (wk2 pre k) false true)[k + 1]? =
      some (stdPiece (f u1).tOdd (brPos pre k) 0) := by
    unfold LStepAssembly.oddPs
    rw [hL, TileHalfTurnL.get_mid _ _ _ hlen, bridgePosMG pre h0, bridgeAffMG pre h0]
  have hLh : ∀ m ≤ 2 * k + 1, (LStepAssembly.oddPs D f (wk2 pre k) false true)[k + 1 + 1 + hIdx pre k m]? =
      some (stdPiece (f u2).aEven (qPos pre m) 0) := by
    intro m hm
    obtain ⟨e1, e2⟩ := head_at pre h0 k m hm
    unfold LStepAssembly.oddPs
    rw [hL, TileHalfTurnL.get_right _ _ _ hlen, List.getElem?_map, List.getElem?_range (by simp; omega)]
    simp only [Option.map_some, e1, headAffM_eq pre h0]
  choose! bq hbq using hn
  obtain ⟨bB, hbB⟩ := hbr
  have hpu : (parentsAt pre).even = fracEven u2 := (WeakStepAssembly.regsAt_parents pre).2 u2 (by rw [hreg])
  have hpo : (parentsAt pre).odd = fracOdd u1 := (WeakStepAssembly.regsAt_parents pre).1 u1 (by rw [hreg])
  have gh : ∀ m ≤ 2 * k + 1, ∀ y ∈ placedSites (hStringAt (hWordOf u2 true) 0),
      y + qPos pre m ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) false true) κ).dom ∧ y + qPos pre m ∈ tod.dom ∧
        (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) false true) κ).val (y + qPos pre m) = tod.val (y + qPos pre m) + (κ (k + 1 + 1 + hIdx pre k m) + d - bq m) := by
    intro m hm y hy
    obtain ⟨hya, -, hyv⟩ := hd y hy
    have hp : y + qPos pre m ∈ (stdPiece (f u2).aEven (qPos pre m) 0).placed := Finset.mem_image.2 ⟨y, hya, rfl⟩
    obtain ⟨ht', hv⟩ := hbq m hm y hy
    refine ⟨LSidesEven.mem_pieceUnion_of (hLh m hm) hp, ht', ?_⟩
    rw [LSidesEven.glued_val _ κ hag _ _ (hLh m hm) _ hp (by simp [stdPiece]), hv]
    simp only [pieceVal, stdPiece, add_sub_cancel_right, hyv, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero]
    ring
  have gb : ∀ y ∈ (f u1).tOdd.dom,
      y + brPos pre k ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) false true) κ).dom ∧ y + brPos pre k ∈ tod.dom ∧
        (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) false true) κ).val (y + brPos pre k) = tod.val (y + brPos pre k) + (κ (k + 1) - bB) := by
    intro y hy
    have hp : y + brPos pre k ∈ (stdPiece (f u1).tOdd (brPos pre k) 0).placed := Finset.mem_image.2 ⟨y, hy, rfl⟩
    obtain ⟨ht', hv⟩ := hbB y hy
    refine ⟨LSidesEven.mem_pieceUnion_of hLb hp, ht', ?_⟩
    rw [LSidesEven.glued_val _ κ hag _ _ hLb _ hp (by simp [stdPiece]), hv]
    simp only [pieceVal, stdPiece, add_sub_cancel_right, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero]
    ring
  -- the ends of the bottom strings of the registers
  have hq0 : (0 : GInt) ∈ placedSites (hStringAt (hWordOf u2 true) 0) := (bot_ends_even u2).1
  have hqU : vU pre ∈ placedSites (hStringAt (hWordOf u2 true) 0) := by
    simp only [vU, hpu]; exact (bot_ends_even u2).2
  obtain ⟨hS1, -⟩ := hgood u1 hl1
  have hR1 := (WeakStepAssembly.slice_respects D f u1 hS1).1
  have hp0 : (0 : GInt) ∈ (f u1).tOdd.dom := side_mem_dom hR1 .hPlus (bot_ends_odd u1).1
  have hpA : vA pre ∈ (f u1).tOdd.dom := by
    simp only [vA, hpo]; exact side_mem_dom hR1 .hPlus (bot_ends_odd u1).2
  have step : ∀ m < 2 * k + 1, κ (k + 1 + 1 + hIdx pre k (m + 1)) + d - bq (m + 1) =
      κ (k + 1 + 1 + hIdx pre k m) + d - bq m := by
    intro m hm
    have g1 := gh m (by omega) _ hqU
    have g2 := gh (m + 1) (by omega) _ hq0
    have ex : vU pre + qPos pre m = 0 + qPos pre (m + 1) := by
      simp only [qPos]; push_cast; rw [add_smul, one_smul]; abel
    rw [ex] at g1
    rw [g1.2.2] at g2
    linarith [g2.2.2]
  have hall : ∀ m ≤ 2 * k + 1, κ (k + 1 + 1 + hIdx pre k m) + d - bq m =
      κ (k + 1 + 1 + hIdx pre k 0) + d - bq 0 := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih => rw [step m (by omega), ih (by omega)]
  have hbk : κ (k + 1) - bB = κ (k + 1 + 1 + hIdx pre k 0) + d - bq 0 := by
    cases hb : W1Odd pre
    · have g1 := gh (2 * k + 1) le_rfl _ hqU
      have g2 := gb _ hp0
      have ex : vU pre + qPos pre (2 * k + 1) = 0 + brPos pre k := by
        simp only [qPos, brPos, hb, Bool.false_eq_true, if_false]; push_cast
        ext <;> simp <;> ring
      rw [ex, g2.2.2] at g1
      rw [← hall (2 * k + 1) le_rfl]
      linarith [g1.2.2]
    · have g1 := gb _ hpA
      have g2 := gh 0 (by omega) _ hq0
      have ex : vA pre + brPos pre k = 0 + qPos pre 0 := by
        simp only [qPos, brPos, hb, if_true]; simp
      rw [ex, g2.2.2] at g1
      linarith [g1.2.2]
  refine ⟨κ (k + 1 + 1 + hIdx pre k 0) + d - bq 0, fun x hx => ?_⟩
  rcases hcov x hx with ⟨m, hm, hxm⟩ | hxb
  · have g := gh m hm _ hxm
    rw [sub_add_cancel, hall m hm] at g
    exact g
  · have g := gb _ (side_mem_dom hR1 .hPlus hxb)
    rw [sub_add_cancel, hbk] at g
    exact g

/-! ### The `+` odd L-correction, by the half-turn -/

/-- **The top string of the odd child is the half-turn of its bottom string** about the centre `v_1 + v_2 + 1 - i`. -/
theorem top_iff_bottom_odd (w : Word) (x : GInt) :
    x ∈ placedSites (sideString (hWordOf w false) (vWordOf w false) 0 .hMinus) ↔
      TileHalfTurnStd.cOdd ((parentsAt w).current .odd) - x ∈
        placedSites (sideString (hWordOf w false) (vWordOf w false) 0 .hPlus) := by
  simp only [sideString]
  rw [ReflectedCoverConverse.placed_hRev_iff _ Letter.p (hWordOf_head_last w false).2, StdCornerAnchors.stdAnchorY_odd,
    StdCornerAnchors.stdAnchorX_odd]
  have e : texV2 (fracOdd w) + ((1 : ℤ), (-2 : ℤ)) + (texV1Odd (fracOdd w) - (1, 1)) + ReflectedCover.shR Letter.p =
      TileHalfTurnStd.cOdd ((parentsAt w).current .odd) := by
    simp only [fracOdd, ReflectedCover.shR, TileHalfTurnStd.cOdd]
    ext <;> simp <;> ring
  rw [e]
  exact Iff.rfl

/-- **The horizontal side of the elongated `+` odd L-correction after trailing `2`s**: the top string of the odd child, from the
bottom side of the `-` one by the half-turn of the child. -/
theorem oddL_hor_plus_k (D : JointData) (hS : D.S = paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hAB : PaperAltBdry D) (hAnc : PaperAltAnc D) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (pre : Word)
    (hpre : ¬ IsBase pre) (h0 : trailingCount Digit.two pre = 0) (u1 u2 : Word) (hreg : regsAt pre = (some u1, some u2))
    (hu2 : ¬ IsBase u2) (k : ℕ) (hgood : GoodBelow D f (wk2 pre k).length)
    (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f (wk2 pre k)) (wk2 pre k) wo we wao wae tod tev aod aev)
    (hTP : TileProps (wk2 pre k) tod tev aod aev) (κp κm : ℕ → ℤ)
    (hagp : PiecesAgree (LStepAssembly.oddPs D f (wk2 pre k) true true) κp)
    (hagm : PiecesAgree (LStepAssembly.oddPs D f (wk2 pre k) false true) κm) :
    ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 .hMinus),
      x ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true true) κp).dom ∧ x ∈ tod.dom ∧ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true true) κp).val x = tod.val x + c := by
  obtain ⟨v, d, hd, hvd⟩ := LSidesOddV.pre_split2 pre hpre h0
  obtain ⟨htc, hst⟩ := wk2_trailing pre h0 k
  obtain ⟨hnb, -, -⟩ := LSidesOddV.wk2_facts pre hpre k
  have hpreS : stripTrailing Digit.two (wk2 pre k) = v ++ [d] := by rw [hst, hvd]
  have hregB : (!(stripTrailing Digit.two (wk2 pre k)).isEmpty &&
      (stripTrailing Digit.two (wk2 pre k)).all (fun d => decide (d = Digit.three))) = false := by
    rw [hst]
    by_contra hc
    simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
      decide_eq_true_eq] at hc
    exact hpre (Or.inr (Or.inl hc.2))
  have hdef : OddLDefined (wk2 pre k) := ⟨v, d, k, hd, by rw [wk2, hvd]⟩
  have hRs := JointGlue.respectsPieces_glued _ κm (JointGlue.oddLPieces_covered _ _ _ _ _ _ _ _) hagm
  have hRt := JointGlue.respectsPieces_glued _ κp (JointGlue.oddLPieces_covered _ _ _ _ _ _ _ _) hagp
  have hconn := (ConnectedL.connectedL_of D hS hA f (wk2 pre k) (fun u hu => (hgood u hu).1)
    (fun u hu => (hgood u hu).2.2.1)).1 false true hdef
  have hr2 : (regsAt (stripTrailing Digit.two (wk2 pre k))).2 = some v := by
    rw [hpreS]; exact ConnectedAltL.regs_pre_snd v d hd
  have hr1 : (regsAt (stripTrailing Digit.two (wk2 pre k))).1 = some u1 := by rw [hst, hreg]
  have hvl : v.length < (wk2 pre k).length := by rw [wk2, hvd]; simp
  have hu1l : u1.length < (wk2 pre k).length :=
    lt_of_lt_of_le (regsAt_lt pre u1 (Or.inl (by rw [hreg]))) (by simp [wk2])
  have hSt : TileHalfTurnStd.RawHT (regOdo D.S (fun u => (below f (wk2 pre k) u).tOdd)
      (fun u => (below f (wk2 pre k) u).tEven) (regsAt (stripTrailing Digit.two (wk2 pre k))).2 false)
      (TileHalfTurnStd.cEven (parentsAt (stripTrailing Digit.two (wk2 pre k))).even)
      (TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.two (wk2 pre k))).even) := by
    rw [hr2]
    show TileHalfTurnStd.RawHT (below f (wk2 pre k) v).tEven _ _
    rw [JointRot.below_of_lt f (wk2 pre k) v hvl]
    exact TileHalfTurnInput.raw_reg_even D hS hA f (wk2 pre k).length hgood _ v hr2 hvl
  have hBr : TileHalfTurnStd.RawHT (regOdo D.S (fun u => (below f (wk2 pre k) u).tOdd)
      (fun u => (below f (wk2 pre k) u).tEven) (regsAt (stripTrailing Digit.two (wk2 pre k))).1 true)
      (TileHalfTurnStd.cOdd (parentsAt (stripTrailing Digit.two (wk2 pre k))).odd)
      (TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.two (wk2 pre k))).odd) := by
    rw [hr1]
    show TileHalfTurnStd.RawHT (below f (wk2 pre k) u1).tOdd _ _
    rw [JointRot.below_of_lt f (wk2 pre k) u1 hu1l]
    exact TileHalfTurnInput.raw_reg_odd D hS hA f (wk2 pre k).length hgood _ u1 hr1 hu1l
  have hHd : TileHalfTurnStd.RawHT (regOdo D.S (fun u => (below f (wk2 pre k) u).aOdd)
      (fun u => (below f (wk2 pre k) u).aEven) (regsAt (stripTrailing Digit.two (wk2 pre k))).2 false)
      (altD v false) (altE v) := by
    rw [hr2]
    show TileHalfTurnStd.RawHT (below f (wk2 pre k) v).aEven _ _
    rw [JointRot.below_of_lt f (wk2 pre k) v hvl]
    exact (TileHalfTurnInput.raw_below D hS hA f (wk2 pre k).length hgood v hvl).2.2.2
  have hX := TileHalfTurnL.lHalfTurn_odd D.S _ _ _ _ (wk2 pre k) v d hd hpreS hregB false true _ _ hRs hRt hconn hSt hBr
    hHd
  have hsz := LSidesOddV.tod_slope_zero D hS hA f (wk2 pre k) hnb hgood tod (hT.2.1 hnb).1
  have hHt := TileHalfTurnStd.raw_of_tileHalfTurn tod _ _ _ hTP.2.2.1 hsz
  obtain ⟨c0, hc0⟩ := oddL_hor_minus_k D hS hA hAB hAnc hlS f pre hpre h0 u1 u2 hreg hu2 k hgood wo we wao wae tod tev
    aod aev hT κm hagm
  exact LSidesEvenK.top_of_bottom _ _ tod _ _
    {x | x ∈ placedSites (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 .hMinus)}
    {x | x ∈ placedSites (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 .hPlus)}
    (fun x => top_iff_bottom_odd (wk2 pre k) x) ⟨c0, hc0⟩ hX hHt

end FLatticePaper.Tiles.LSidesOddH
