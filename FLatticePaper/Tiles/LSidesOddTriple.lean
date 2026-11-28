import FLatticePaper.Tiles.LSidesOddV

/-! # The vertical sides of the odd L-corrections in the triple case `pre = 3^j`

For `w = 3^j 2^k` (`j ≥ 1`) the odd register of `3^j` is the initial tile `T_{0/1}`, so the bridge of the odd L-correction is
`T_{0/1}` (shifted by `LCorrections.oddBridgeShift`), and at `k = 0` the word `3^j` is a base word, whose odd tile odometer is the
base odometer. The vertical side of the odd child is covered by the stems and the bridge as for the other prefixes; at the base
word this is the base fact `TripleBaseInput` below (numerically, the odd base odometer of `3^j` contains the whole first stem and
the whole shifted bridge, each up to one constant, for `j ≤ 6` and both signs). -/

namespace FLatticePaper.Tiles.LSidesOddTriple

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.WeakStepPaper (paperS)
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles.Standard (IsBase)
open FLatticePaper.Tiles.JointGlue (PiecesAgree gluedOdo pieceVal)
open FLatticePaper.Tiles.JointInduction (GoodBelow regsAt_lt)
open FLatticePaper.Tiles.SurgicalWeak (regsAt regOdo)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.LSidesOddV (PlacedEqA placedEqA_trans placedEqA_of_respects wk2 side_mem_dom)
open FLatticePaper.Tiles.ConnectedAltL (oStemPos)
open FLatticePaper.Tiles.TileHalfTurnL (oBridgePos oAffAt oStemC oBridgeC)

/-- **The base fact of the triple case `pre = 3^j`** (`j ≥ 1`), for the vertical sides of the odd L-corrections of `3^j`: the odd
base odometer `O` of `3^j` contains the even base odometer `E'` of `3^{j-1}` at the first stem and the initial odometer `o_{0/1}`
at the shifted bridge, each with the affine factor of the L-correction and up to a constant, and these two copies cover the
vertical side of the odd base tile that the L-correction contains (the left side for `+`, the right side for `-`; `W_1` is even
at `3^j`). Stated, not proved here. -/
def TripleBaseInput : Prop :=
  ∀ (j : ℕ), 1 ≤ j → ∀ (O E O' E' : PartialOdometer), SurgicalWeak.PaperBaseCond (List.replicate j Digit.three) O E →
    SurgicalWeak.PaperBaseCond (List.replicate (j - 1) Digit.three) O' E' → ∀ plus : Bool,
      PlacedEqA O E' (oddLInitOff (List.replicate j Digit.three) plus) (oddLInitAff (List.replicate j Digit.three) plus) ∧
      PlacedEqA O paperS.zeroO
        (oBridgePos (List.replicate j Digit.three) plus + LCorrections.oddBridgeShift true false plus)
        (oAffAt (List.replicate j Digit.three) plus (oBridgeC (List.replicate j Digit.three) plus)) ∧
      ∀ x ∈ placedSites (sideString (hWordOf (List.replicate j Digit.three) false)
          (vWordOf (List.replicate j Digit.three) false) 0 (if plus then .vMinus else .vPlus)),
        x - oddLInitOff (List.replicate j Digit.three) plus ∈ E'.dom ∨
          x - (oBridgePos (List.replicate j Digit.three) plus + LCorrections.oddBridgeShift true false plus) ∈
            paperS.zeroO.dom

/-! ### The words `3^{j+1} 2^k` -/

/-- The prefix `3^{j+1}` and its even register `3^j`. -/
abbrev tP (j : ℕ) : Word := List.replicate (j + 1) Digit.three
abbrev tU (j : ℕ) : Word := List.replicate j Digit.three

theorem tP_snoc (j : ℕ) : tP j = tU j ++ [Digit.three] := List.replicate_succ' ..

theorem h0T (j : ℕ) : trailingCount Digit.two (tP j) = 0 := by
  rw [tP_snoc, JointRot.trailingCount_snoc]; simp

theorem W1T (j : ℕ) : W1Odd (tP j) = false := by
  have h := JointRot.W1Odd_append_replicate [] (j + 1) Digit.three (by decide)
  exact h.trans rfl

theorem regsT (j : ℕ) : regsAt (tP j) = (none, some (tU j)) := by
  have h1 := SpecialCells.regs_threes_fst (j + 1)
  have h2 := SpecialCells.regs_threes_snd' j
  ext <;> simp [h1, h2]

theorem notBaseT (j k : ℕ) (hk : 0 < k) : ¬ IsBase (wk2 (tP j) k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rintro (h | h | h)
  · simp at h
  · exact absurd (h Digit.two (by simp [wk2])) (by decide)
  · exact absurd (h Digit.three (by simp [wk2])) (by decide)

theorem isBaseT (j : ℕ) : IsBase (tP j) := Or.inr (Or.inl fun _ hd => (List.eq_of_mem_replicate hd))

theorem regs2_wk2 (pre : Word) (k : ℕ) : (regsAt (wk2 pre k)).2 = (regsAt pre).2 := by
  induction k with
  | zero => simp [wk2]
  | succ k ih => rw [LSidesOddV.wk2_succ, WeakStepPaper.regsAt_snoc]; exact ih

/-! ### The positions of the `-` odd L-correction (`W_1` even) -/

/-- `v_{p,2}` and `a_{p,2}` of the parents of the prefix. -/
abbrev vB (pre : Word) : Site := texV2 (parentsAt pre).odd
abbrev aP (pre : Word) : Site := offsetA (parentsAt pre).odd.num (parentsAt pre).odd.den true

set_option hygiene false in
/-- Unfolds a position of the `-` odd L-correction of `pre 2^k` (`W_1` even) into the parents of `pre` and `k`. -/
macro "posm_alg" : tactic => `(tactic| (
  obtain ⟨ht, hs⟩ := LSidesOddV.wk2_trailing pre h0 k
  have hW := JointRot.W1Odd_append_replicate pre k Digit.two (by decide)
  have hp := JointRot.parents_append_twos pre k
  simp only [oStemPos, oBridgePos, oAffAt, oStemC, oBridgeC, oddLInitOff, oddLInitAff, p0Off, p0Aff,
    SurgicalDict.offsetP0, vP1, vP2, vQ1, vQ2, altOff, altAff, ht, hs, hW, hp, hWp, LSidesOddV.vA, LSidesOddV.vU, LSidesOddV.vV, LSidesOddV.aQ, vB, aP,
    oddKCoeff, ↓reduceIte, Bool.false_eq_true]
  ext <;> simp [SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, texV1Odd, texV1Even, texV2, offsetA, pairAffine] <;> ring))

theorem stemPosM_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (hWp : W1Odd pre = false) (k m : ℕ) :
    oStemPos (wk2 pre k) false m =
      LSidesOddV.vA pre + vB pre + ((2 * k + 1 : ℕ) : ℤ) • LSidesOddV.vU pre + (k : ℤ) • LSidesOddV.vV pre - (m : ℤ) • LSidesOddV.vV pre := by
  posm_alg

theorem bridgePosM_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (hWp : W1Odd pre = false) (k : ℕ) :
    oBridgePos (wk2 pre k) false = ((2 * k + 2 : ℕ) : ℤ) • LSidesOddV.vU pre := by
  posm_alg

theorem stemAffM_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (hWp : W1Odd pre = false) (k m : ℕ) :
    oAffAt (wk2 pre k) false (oStemC (wk2 pre k) false m) = aP pre + (k : ℤ) • LSidesOddV.aQ pre - (m : ℤ) • LSidesOddV.aQ pre := by
  posm_alg

theorem bridgeAffM_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (hWp : W1Odd pre = false) (k : ℕ) :
    oAffAt (wk2 pre k) false (oBridgeC (wk2 pre k) false) = 0 := by
  posm_alg

theorem p1Plus_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (hWp : W1Odd pre = false) (k : ℕ) :
    p0Off (wk2 pre k) .p1Plus = (2 : ℤ) • LSidesOddV.vU pre := by
  posm_alg

theorem p1PlusAff_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (hWp : W1Odd pre = false) (k : ℕ) :
    p0Aff (wk2 pre k) .p1Plus = 0 := by
  posm_alg

/-! ### Both signs at once (`W_1` even) -/

/-- The copy of the odd register on the side of the odd L-correction of sign `b`: `P^-` for `+`, `P^+` for `-`. -/
def pOff (w : Word) (b : Bool) : Site := if b then p0Off w .p1Minus else p0Off w .p1Plus
def pAff (w : Word) (b : Bool) : Site := if b then p0Aff w .p1Minus else p0Aff w .p1Plus
/-- The vertical side of the odd L-correction of sign `b` when `W_1` is even: left for `+`, right for `-`. -/
def sideB (b : Bool) : Side := if b then .vMinus else .vPlus

theorem stem0B (w : Word) (b : Bool) :
    oStemPos w b 0 = oddLInitOff w b ∧ oAffAt w b (oStemC w b 0) = oddLInitAff w b := by
  simp [oStemPos, oAffAt, oStemC, altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine]

theorem stem_succB (pre : Word) (h0 : trailingCount Digit.two pre = 0) (hWp : W1Odd pre = false) (b : Bool) (k m : ℕ) :
    oStemPos (wk2 pre (k + 1)) b (m + 1) = oStemPos (wk2 pre k) b m + pOff (wk2 pre (k + 1)) b ∧
      oAffAt (wk2 pre (k + 1)) b (oStemC (wk2 pre (k + 1)) b (m + 1)) =
        pAff (wk2 pre (k + 1)) b + oAffAt (wk2 pre k) b (oStemC (wk2 pre k) b m) := by
  cases b
  · simp only [pOff, pAff, Bool.false_eq_true, if_false]
    rw [stemPosM_eq pre h0 hWp, stemPosM_eq pre h0 hWp, p1Plus_eq pre h0 hWp, stemAffM_eq pre h0 hWp,
      stemAffM_eq pre h0 hWp, p1PlusAff_eq pre h0 hWp]
    refine ⟨?_, ?_⟩ <;> ext <;> simp <;> ring
  · simp only [pOff, pAff, if_true]
    exact LSidesOddV.stem_succ pre h0 k m

theorem bridge_succB (pre : Word) (h0 : trailingCount Digit.two pre = 0) (hWp : W1Odd pre = false) (b : Bool) (k : ℕ) :
    oBridgePos (wk2 pre (k + 1)) b = oBridgePos (wk2 pre k) b + pOff (wk2 pre (k + 1)) b ∧
      oAffAt (wk2 pre (k + 1)) b (oBridgeC (wk2 pre (k + 1)) b) =
        pAff (wk2 pre (k + 1)) b + oAffAt (wk2 pre k) b (oBridgeC (wk2 pre k) b) := by
  cases b
  · simp only [pOff, pAff, Bool.false_eq_true, if_false]
    rw [bridgePosM_eq pre h0 hWp, bridgePosM_eq pre h0 hWp, p1Plus_eq pre h0 hWp, bridgeAffM_eq pre h0 hWp,
      bridgeAffM_eq pre h0 hWp, p1PlusAff_eq pre h0 hWp]
    refine ⟨?_, ?_⟩ <;> ext <;> simp <;> ring
  · simp only [pOff, pAff, if_true]
    exact LSidesOddV.bridge_succ pre h0 k

theorem tOP_entryPB (S : SurgicalWeak.WeakData) (pO pE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (v : Word) (b : Bool) : (tileOddPieces S pO pE lE v)[if b then 1 else 0]? =
      some (stdPiece (regOdo S pO pE (regsAt v).1 true) (pOff v b) (pAff v b)) := by
  cases b <;> simp [tileOddPieces, pOff, pAff]

theorem tOP_entryQB (S : SurgicalWeak.WeakData) (pO pE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (v : Word) (hW : W1Odd v = false) (b : Bool) : (tileOddPieces S pO pE lE v)[if b then 2 else 5]? =
      some (stdPiece (regOdo S pO pE (regsAt v).2 false) (oddLInitOff v b) (oddLInitAff v b)) := by
  cases b <;> simp [tileOddPieces, hW, oddLInitOff, oddLInitAff]

/-- **The vertical sides of the odd child split into two copies** (`W_1` even): the left side into `Q^{+,1}` and `P^-`, the right
side into `P^+` and `Q^{-,2}`. -/
theorem vsplitB (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2)) (hph : phase w ≠ 1) (b : Bool) (z : GInt)
    (hz : z ∈ placedSites (sideString (hWordOf w false) (vWordOf w false) 0 (sideB b))) :
    z - oddLInitOff w b ∈ placedSites (sideString (hWordOf u2 true) (vWordOf u2 true) 0 (sideB b)) ∨
      z - pOff w b ∈ placedSites (sideString (hWordOf u1 false) (vWordOf u1 false) 0 (sideB b)) := by
  have hW : W1Odd w = false := by simp [W1Odd, hph]
  cases b
  · have hp : (parentsAt w).odd = fracOdd u1 := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])
    have hq : (parentsAt w).even = fracEven u2 := (WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])
    obtain ⟨-, -, h3, -⟩ := GlueStringDecomp.odd_ef w u1 u2 hreg hph
    simp only [sideB, pOff, Bool.false_eq_true, if_false, sideString] at hz ⊢
    rw [h3, placedSites_append, List.mem_append] at hz
    rw [GlueStringDecomp.lp_bot_even u2 0, GlueStringDecomp.lp_bot_odd u1 0, zero_add, zero_add]
    have e1 : oddLInitOff w false = texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2) := by
      simp [oddLInitOff, hW, p0Off, SurgicalDict.offsetP0, vP1, vP2, vQ1, hp, hq]
    have e2 : p0Off w .p1Plus = texV1Even (fracEven u2) + texV1Even (fracEven u2) := by
      simp [p0Off, SurgicalDict.offsetP0, hW, vQ1, hq]
    rw [e1, e2]
    rcases hz with h | h
    · right
      rw [show texV1Even (fracEven u2) + texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)) =
          (texV1Odd (fracOdd u1) - (1, 1)) + (texV1Even (fracEven u2) + texV1Even (fracEven u2)) by abel,
        vStringAt_add, AltItem3.mem_placedSites_map] at h
      exact h
    · left
      rw [show texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1)) =
          (texV1Even (fracEven u2) - (1, 1)) + (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2))
          by abel, vStringAt_add, AltItem3.mem_placedSites_map] at h
      exact h
  · have hv : LSidesOddV.vSide w = sideB true := by simp [LSidesOddV.vSide, sideB, hW]
    have := LSidesOddV.vsplit w u1 u2 hreg z (by rw [hv]; exact hz)
    simpa only [hv, pOff, if_true] using this

/-! ### The nested copies of `3^{j+1} 2^k` -/

/-- **The nested copies of `3^{j+1} 2^k`**: an odometer of the odd child of `3^{j+1} 2^k` (the base odometer at `k = 0`, one
respecting the odd decomposition at `k ≥ 1`) contains the even register `3^j` at each stem of the odd L-correction of sign `b` and
the initial odometer `o_{0/1}` at its shifted bridge, with the same affine factors, and these copies cover the vertical side of
sign `b` of the child. -/
theorem nestedT (D : JointData) (hS : D.S = paperS) (hTB : TripleBaseInput) (f : Word → JSlice) (j : ℕ) (b : Bool) :
    ∀ (k : ℕ) (o : PartialOdometer), GoodBelow D f (wk2 (tP j) k).length →
      (k = 0 → ∃ E, SurgicalWeak.PaperBaseCond (tP j) o E) →
      (0 < k → RespectsPieces o (tileOddPieces D.S (fun u => (below f (wk2 (tP j) k) u).tOdd)
        (fun u => (below f (wk2 (tP j) k) u).tEven) (fun u => (below f (wk2 (tP j) k) u).lEven) (wk2 (tP j) k))) →
      (∀ m ≤ k, PlacedEqA o (f (tU j)).tEven (oStemPos (wk2 (tP j) k) b m)
        (oAffAt (wk2 (tP j) k) b (oStemC (wk2 (tP j) k) b m))) ∧
      PlacedEqA o paperS.zeroO (oBridgePos (wk2 (tP j) k) b + LCorrections.oddBridgeShift true false b)
        (oAffAt (wk2 (tP j) k) b (oBridgeC (wk2 (tP j) k) b)) ∧
      ∀ z ∈ placedSites (sideString (hWordOf (wk2 (tP j) k) false) (vWordOf (wk2 (tP j) k) false) 0 (sideB b)),
        (∃ m ≤ k, z - oStemPos (wk2 (tP j) k) b m ∈ (f (tU j)).tEven.dom) ∨
          z - (oBridgePos (wk2 (tP j) k) b + LCorrections.oddBridgeShift true false b) ∈ paperS.zeroO.dom := by
  have hlU : (tU j).length < (tP j).length := by simp
  intro k
  induction k with
  | zero =>
    rintro o hgood hb0 -
    have hw0 : wk2 (tP j) 0 = tP j := by simp [wk2]
    obtain ⟨E, hO⟩ := hb0 rfl
    have hlU' : (tU j).length < (wk2 (tP j) 0).length := by rw [hw0]; exact hlU
    have hE := LSidesEvenK.base_cond_slice D hS f (tU j) (Or.inr (Or.inl fun _ hd => List.eq_of_mem_replicate hd))
      (hgood _ hlU').1
    obtain ⟨h1, h2, h3⟩ := hTB (j + 1) (by omega) o E (f (tU j)).tOdd (f (tU j)).tEven hO (by simpa using hE) b
    rw [hw0]
    refine ⟨fun m hm => ?_, h2, fun z hz => ?_⟩
    · obtain rfl : m = 0 := by omega
      rw [(stem0B (tP j) b).1, (stem0B (tP j) b).2]
      exact h1
    · rcases h3 z hz with h | h
      · left
        exact ⟨0, le_rfl, by rw [(stem0B (tP j) b).1]; exact h⟩
      · exact Or.inr h
  | succ k ih =>
    rintro o hgood - hR
    have hR := hR (by omega)
    have hnb := notBaseT j (k + 1) (by omega)
    have hws := LSidesOddV.wk2_succ (tP j) k
    have hlt : (wk2 (tP j) k).length < (wk2 (tP j) (k + 1)).length := by rw [hws]; simp
    have hrs : regsAt (wk2 (tP j) (k + 1)) = (some (wk2 (tP j) k), some (tU j)) := by
      rw [LSidesOddV.regsAt_wk2_succ, regs2_wk2, regsT]
    have hW' : W1Odd (wk2 (tP j) (k + 1)) = false := by
      rw [JointRot.W1Odd_append_replicate (tP j) (k + 1) Digit.two (by decide), W1T]
    have hph : phase (wk2 (tP j) (k + 1)) ≠ 1 := by
      intro h; simp [W1Odd, h] at hW'
    have hlU' : (tU j).length < (wk2 (tP j) (k + 1)).length := lt_of_lt_of_le hlU (by simp [wk2])
    have hb2 : below f (wk2 (tP j) (k + 1)) (tU j) = f (tU j) := by simp only [below, if_pos hlU']
    have hbk : below f (wk2 (tP j) (k + 1)) (wk2 (tP j) k) = f (wk2 (tP j) k) := by simp only [below, if_pos hlt]
    have e1 := tOP_entryPB D.S (fun u => (below f (wk2 (tP j) (k + 1)) u).tOdd)
      (fun u => (below f (wk2 (tP j) (k + 1)) u).tEven) (fun u => (below f (wk2 (tP j) (k + 1)) u).lEven)
      (wk2 (tP j) (k + 1)) b
    have eQ := tOP_entryQB D.S (fun u => (below f (wk2 (tP j) (k + 1)) u).tOdd)
      (fun u => (below f (wk2 (tP j) (k + 1)) u).tEven) (fun u => (below f (wk2 (tP j) (k + 1)) u).lEven)
      (wk2 (tP j) (k + 1)) hW' b
    rw [hrs] at e1 eQ
    simp only [regOdo, hbk, hb2] at e1 eQ
    have hP := placedEqA_of_respects hR e1
    have hQ := placedEqA_of_respects hR eQ
    have hgood' : GoodBelow D f (wk2 (tP j) k).length := fun u hu => hgood u (lt_trans hu hlt)
    have hJk := (hgood (wk2 (tP j) k) hlt).1
    have hb0 : k = 0 → ∃ E, SurgicalWeak.PaperBaseCond (tP j) (f (wk2 (tP j) k)).tOdd E := by
      rintro rfl
      have hw0 : wk2 (tP j) 0 = tP j := by simp [wk2]
      refine ⟨(f (wk2 (tP j) 0)).tEven, ?_⟩
      have := LSidesEvenK.base_cond_slice D hS f (wk2 (tP j) 0) (by rw [hw0]; exact isBaseT j) hJk
      rw [hw0] at this ⊢
      exact this
    have hRk : 0 < k → RespectsPieces (f (wk2 (tP j) k)).tOdd (tileOddPieces D.S (fun u => (below f (wk2 (tP j) k) u).tOdd)
        (fun u => (below f (wk2 (tP j) k) u).tEven) (fun u => (below f (wk2 (tP j) k) u).lEven) (wk2 (tP j) k)) :=
      fun hk => ((hJk.2.2.1).2.1 (notBaseT j k hk)).1
    obtain ⟨hn, hbr, hcov⟩ := ih (f (wk2 (tP j) k)).tOdd hgood' hb0 hRk
    obtain ⟨hS2, -⟩ := hgood (tU j) hlU'
    have hR2 := (WeakStepAssembly.slice_respects D f (tU j) hS2).2
    refine ⟨fun m hm => ?_, ?_, fun z hz => ?_⟩
    · rcases m with _ | m
      · rw [(stem0B (wk2 (tP j) (k + 1)) b).1, (stem0B (wk2 (tP j) (k + 1)) b).2]
        exact hQ
      · rw [(stem_succB (tP j) (h0T j) (W1T j) b k m).1, (stem_succB (tP j) (h0T j) (W1T j) b k m).2]
        exact placedEqA_trans hP (hn m (by omega))
    · rw [(bridge_succB (tP j) (h0T j) (W1T j) b k).1, (bridge_succB (tP j) (h0T j) (W1T j) b k).2, add_right_comm]
      exact placedEqA_trans hP hbr
    · rcases vsplitB (wk2 (tP j) (k + 1)) (wk2 (tP j) k) (tU j) hrs hph b z hz with h | h
      · left
        refine ⟨0, by omega, ?_⟩
        rw [(stem0B (wk2 (tP j) (k + 1)) b).1]
        exact side_mem_dom hR2 _ h
      · rcases hcov _ h with ⟨m, hm, hm'⟩ | hb
        · left
          refine ⟨m + 1, by omega, ?_⟩
          rw [(stem_succB (tP j) (h0T j) (W1T j) b k m).1]
          convert hm' using 1
          abel
        · right
          rw [(bridge_succB (tP j) (h0T j) (W1T j) b k).1]
          convert hb using 1
          abel

/-! ### The stems and the bridge of the odd L-correction in the triple case -/

theorem oddL_entriesT (S : SurgicalWeak.WeakData) (pO pE aO aE : Word → PartialOdometer) (u : Word) (b elong : Bool)
    (htr : (!(stripTrailing Digit.two u).isEmpty &&
      (stripTrailing Digit.two u).all (fun d => decide (d = Digit.three))) = true) :
    (∀ m ≤ trailingCount Digit.two u, (oddLPieces S pO pE aO aE u b elong)[m]? =
        some (stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.two u)).2 false) (oStemPos u b m)
          (oAffAt u b (oStemC u b m)))) ∧
      (oddLPieces S pO pE aO aE u b elong)[trailingCount Digit.two u + 1]? =
        some (stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.two u)).1 true)
          (oBridgePos u b + LCorrections.oddBridgeShift true (W1Odd u) b) (oAffAt u b (oBridgeC u b))) := by
  refine ⟨fun m hm => ?_, ?_⟩
  · simp only [oddLPieces]
    rw [TileHalfTurnL.get_left _ _ _ m (by simp; omega), List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  · simp only [oddLPieces, htr]
    rw [TileHalfTurnL.get_mid _ _ _ (by simp)]
    rfl

/-- **The stems and the bridge of the odd L-correction of sign `b` at `3^{j+1} 2^k`** agree with the tile odometer of the odd
child up to one constant. -/
theorem oddL_stems_constT (D : JointData) (hS : D.S = paperS) (hTB : TripleBaseInput) (f : Word → JSlice) (j k : ℕ) (b : Bool)
    (hgood : GoodBelow D f (wk2 (tP j) k).length) (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f (wk2 (tP j) k)) (wk2 (tP j) k) wo we wao wae tod tev aod aev)
    (hb0 : k = 0 → ∃ E, SurgicalWeak.PaperBaseCond (tP j) tod E) (elong : Bool) (κ : ℕ → ℤ)
    (hag : PiecesAgree (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ) :
    ∃ c : ℤ, (∀ m ≤ k, ∀ y ∈ (f (tU j)).tEven.dom,
        y + oStemPos (wk2 (tP j) k) b m ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).dom ∧
          y + oStemPos (wk2 (tP j) k) b m ∈ tod.dom ∧
          (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).val (y + oStemPos (wk2 (tP j) k) b m) =
            tod.val (y + oStemPos (wk2 (tP j) k) b m) + c) ∧
      (∀ y ∈ paperS.zeroO.dom,
        y + (oBridgePos (wk2 (tP j) k) b + LCorrections.oddBridgeShift true false b) ∈
            (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).dom ∧
          y + (oBridgePos (wk2 (tP j) k) b + LCorrections.oddBridgeShift true false b) ∈ tod.dom ∧
          (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).val
              (y + (oBridgePos (wk2 (tP j) k) b + LCorrections.oddBridgeShift true false b)) =
            tod.val (y + (oBridgePos (wk2 (tP j) k) b + LCorrections.oddBridgeShift true false b)) + c) := by
  have hR : 0 < k → RespectsPieces tod (tileOddPieces D.S (fun u => (below f (wk2 (tP j) k) u).tOdd)
      (fun u => (below f (wk2 (tP j) k) u).tEven) (fun u => (below f (wk2 (tP j) k) u).lEven) (wk2 (tP j) k)) :=
    fun hk => (hT.2.1 (notBaseT j k hk)).1
  obtain ⟨hn, hbr, -⟩ := nestedT D hS hTB f j b k tod hgood hb0 hR
  obtain ⟨ht, hs⟩ := LSidesOddV.wk2_trailing (tP j) (h0T j) k
  have hW : W1Odd (wk2 (tP j) k) = false := by
    rw [JointRot.W1Odd_append_replicate (tP j) k Digit.two (by decide), W1T]
  have htr : (!(stripTrailing Digit.two (wk2 (tP j) k)).isEmpty &&
      (stripTrailing Digit.two (wk2 (tP j) k)).all (fun d => decide (d = Digit.three))) = true := by
    rw [hs]; simp
  have hlU : (tU j).length < (wk2 (tP j) k).length := by simp [wk2]; omega
  have hbU : below f (wk2 (tP j) k) (tU j) = f (tU j) := by simp only [below, if_pos hlU]
  obtain ⟨hLm, hLb⟩ := oddL_entriesT D.S (fun u => (below f (wk2 (tP j) k) u).tOdd)
    (fun u => (below f (wk2 (tP j) k) u).tEven) (fun u => (below f (wk2 (tP j) k) u).aOdd)
    (fun u => (below f (wk2 (tP j) k) u).aEven) (wk2 (tP j) k) b elong htr
  rw [hs, ht, regsT] at hLm hLb
  simp only [regOdo, hbU, hW] at hLm hLb
  have hz0 : D.S.zeroO = paperS.zeroO := by rw [hS]
  rw [hz0] at hLb
  choose! bs hbs using hn
  obtain ⟨bB, hbB⟩ := hbr
  have gs : ∀ m ≤ k, ∀ y ∈ (f (tU j)).tEven.dom,
      y + oStemPos (wk2 (tP j) k) b m ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).dom ∧
        y + oStemPos (wk2 (tP j) k) b m ∈ tod.dom ∧
        (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).val (y + oStemPos (wk2 (tP j) k) b m) =
          tod.val (y + oStemPos (wk2 (tP j) k) b m) + (κ m - bs m) := by
    intro m hm y hy
    have hp : y + oStemPos (wk2 (tP j) k) b m ∈ (stdPiece (f (tU j)).tEven (oStemPos (wk2 (tP j) k) b m)
        (oAffAt (wk2 (tP j) k) b (oStemC (wk2 (tP j) k) b m))).placed := Finset.mem_image.2 ⟨y, hy, rfl⟩
    obtain ⟨ht', hv⟩ := hbs m hm y hy
    refine ⟨LSidesEven.mem_pieceUnion_of (hLm m hm) hp, ht', ?_⟩
    rw [LSidesEven.glued_val _ κ hag m _ (hLm m hm) _ hp (by simp [stdPiece]), hv]
    simp only [pieceVal, stdPiece, add_sub_cancel_right]
    ring
  have gb : ∀ y ∈ paperS.zeroO.dom,
      y + (oBridgePos (wk2 (tP j) k) b + LCorrections.oddBridgeShift true false b) ∈
          (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).dom ∧
        y + (oBridgePos (wk2 (tP j) k) b + LCorrections.oddBridgeShift true false b) ∈ tod.dom ∧
        (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).val
            (y + (oBridgePos (wk2 (tP j) k) b + LCorrections.oddBridgeShift true false b)) =
          tod.val (y + (oBridgePos (wk2 (tP j) k) b + LCorrections.oddBridgeShift true false b)) + (κ (k + 1) - bB) := by
    intro y hy
    have hp : y + (oBridgePos (wk2 (tP j) k) b + LCorrections.oddBridgeShift true false b) ∈
        (stdPiece paperS.zeroO (oBridgePos (wk2 (tP j) k) b + LCorrections.oddBridgeShift true false b)
          (oAffAt (wk2 (tP j) k) b (oBridgeC (wk2 (tP j) k) b))).placed := Finset.mem_image.2 ⟨y, hy, rfl⟩
    obtain ⟨ht', hv⟩ := hbB y hy
    refine ⟨LSidesEven.mem_pieceUnion_of hLb hp, ht', ?_⟩
    rw [LSidesEven.glued_val _ κ hag (k + 1) _ hLb _ hp (by simp [stdPiece]), hv]
    simp only [pieceVal, stdPiece, add_sub_cancel_right]
    ring
  -- corner points of the even register `3^j` and of `T_{0/1}`
  have hq : (parentsAt (tU j)).current .even = (parentsAt (tP j)).even :=
    ((WeakStepAssembly.regsAt_parents (tP j)).2 (tU j) (by rw [regsT])).symm
  obtain ⟨hS2, -⟩ := hgood (tU j) hlU
  obtain ⟨αe, βe, -, hVe⟩ := TileTranslationStd.stdCorners_even (tU j) (f (tU j)).tEven
    (WeakStepAssembly.slice_respects D f (tU j) hS2).2
  obtain ⟨-, ⟨d10, -⟩, -, ⟨dX, -⟩, ⟨dY10, -⟩, -, -, -⟩ := hVe
  rw [hq] at dX dY10
  have z11 : ((1 : ℤ), (1 : ℤ)) ∈ paperS.zeroO.dom := by
    show ((1 : ℤ), (1 : ℤ)) ∈ Standard.zeroTile
    simp [Standard.zeroTile]
  have z02 : ((0 : ℤ), (2 : ℤ)) ∈ paperS.zeroO.dom := by
    show ((0 : ℤ), (2 : ℤ)) ∈ Standard.zeroTile
    simp [Standard.zeroTile]
  have hpar := SpecialCells.parents_threes (j + 1)
  have step : ∀ m < k, κ (m + 1) - bs (m + 1) = κ m - bs m := by
    intro m hm
    cases b
    · have e : oStemPos (wk2 (tP j) k) false (m + 1) + texV2 (parentsAt (tP j)).even =
          oStemPos (wk2 (tP j) k) false m := by
        rw [stemPosM_eq (tP j) (h0T j) (W1T j), stemPosM_eq (tP j) (h0T j) (W1T j)]
        ext <;> simp <;> ring
      have g1 := gs m (by omega) _ d10
      have g2 := gs (m + 1) (by omega) _ dY10
      have ex : texV2 (parentsAt (tP j)).even + ((1 : ℤ), (0 : ℤ)) + oStemPos (wk2 (tP j) k) false (m + 1) =
          ((1 : ℤ), (0 : ℤ)) + oStemPos (wk2 (tP j) k) false m := by rw [← e]; abel
      rw [ex] at g2
      rw [g2.2.2] at g1
      linarith [g1.2.2]
    · have e : oStemPos (wk2 (tP j) k) true (m + 1) = oStemPos (wk2 (tP j) k) true m + texV2 (parentsAt (tP j)).even := by
        rw [LSidesOddV.stemPos_eq (tP j) (h0T j), LSidesOddV.stemPos_eq (tP j) (h0T j), W1T]
        ext <;> simp <;> ring
      have g1 := gs m (by omega) _ dY10
      have g2 := gs (m + 1) (by omega) _ d10
      have ex : texV2 (parentsAt (tP j)).even + ((1 : ℤ), (0 : ℤ)) + oStemPos (wk2 (tP j) k) true m =
          ((1 : ℤ), (0 : ℤ)) + oStemPos (wk2 (tP j) k) true (m + 1) := by rw [e]; abel
      rw [ex] at g1
      rw [g1.2.2] at g2
      linarith [g2.2.2]
  have hall : ∀ m ≤ k, κ m - bs m = κ 0 - bs 0 := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih => rw [step m (by omega), ih (by omega)]
  have hbk : κ (k + 1) - bB = κ k - bs k := by
    cases b
    · have e : oBridgePos (wk2 (tP j) k) false + LCorrections.oddBridgeShift true false false =
          oStemPos (wk2 (tP j) k) false k + (texV1Even (parentsAt (tP j)).even - ((0 : ℤ), (2 : ℤ))) := by
        rw [bridgePosM_eq (tP j) (h0T j) (W1T j), stemPosM_eq (tP j) (h0T j) (W1T j)]
        simp only [LCorrections.oddBridgeShift, LSidesOddV.vA, LSidesOddV.vU, LSidesOddV.vV, vB, hpar]
        ext <;> simp [texV1Odd, texV2] <;> ring
      have g1 := gs k le_rfl _ dX
      have g2 := gb _ z02
      have ex : ((0 : ℤ), (2 : ℤ)) + (oBridgePos (wk2 (tP j) k) false + LCorrections.oddBridgeShift true false false) =
          texV1Even (parentsAt (tP j)).even + oStemPos (wk2 (tP j) k) false k := by rw [e]; abel
      rw [ex, g1.2.2] at g2
      linarith [g2.2.2]
    · have e : oBridgePos (wk2 (tP j) k) true + LCorrections.oddBridgeShift true false true =
          oStemPos (wk2 (tP j) k) true k + (texV2 (parentsAt (tP j)).even - ((0 : ℤ), (1 : ℤ))) := by
        rw [LSidesOddV.bridgePos_eq (tP j) (h0T j), LSidesOddV.stemPos_eq (tP j) (h0T j), W1T]
        simp only [LCorrections.oddBridgeShift]
        ext <;> simp <;> ring
      have g1 := gs k le_rfl _ dY10
      have g2 := gb _ z11
      have ex : ((1 : ℤ), (1 : ℤ)) + (oBridgePos (wk2 (tP j) k) true + LCorrections.oddBridgeShift true false true) =
          texV2 (parentsAt (tP j)).even + ((1 : ℤ), (0 : ℤ)) + oStemPos (wk2 (tP j) k) true k := by
        rw [e]; ext <;> simp <;> ring
      rw [ex, g1.2.2] at g2
      linarith [g2.2.2]
  refine ⟨κ 0 - bs 0, fun m hm y hy => ?_, fun y hy => ?_⟩
  · rw [← hall m hm]; exact gs m hm y hy
  · rw [← hall k le_rfl, ← hbk]; exact gb y hy

/-- **The vertical side of the odd L-correction of sign `b` at `3^{j+1} 2^k`** (the left side for `+`, the right side for `-`):
the glued L-corrected odometer and the tile odometer of the odd child differ by one constant there. -/
theorem oddL_vert_T (D : JointData) (hS : D.S = paperS) (hTB : TripleBaseInput) (f : Word → JSlice) (j k : ℕ) (b : Bool)
    (hgood : GoodBelow D f (wk2 (tP j) k).length) (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f (wk2 (tP j) k)) (wk2 (tP j) k) wo we wao wae tod tev aod aev)
    (hb0 : k = 0 → ∃ E, SurgicalWeak.PaperBaseCond (tP j) tod E) (elong : Bool) (κ : ℕ → ℤ)
    (hag : PiecesAgree (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ) :
    ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf (wk2 (tP j) k) false) (vWordOf (wk2 (tP j) k) false) 0 (sideB b)),
      x ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).dom ∧ x ∈ tod.dom ∧
        (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).val x = tod.val x + c := by
  have hR : 0 < k → RespectsPieces tod (tileOddPieces D.S (fun u => (below f (wk2 (tP j) k) u).tOdd)
      (fun u => (below f (wk2 (tP j) k) u).tEven) (fun u => (below f (wk2 (tP j) k) u).lEven) (wk2 (tP j) k)) :=
    fun hk => (hT.2.1 (notBaseT j k hk)).1
  obtain ⟨-, -, hcov⟩ := nestedT D hS hTB f j b k tod hgood hb0 hR
  obtain ⟨c, hs, hb⟩ := oddL_stems_constT D hS hTB f j k b hgood wo we wao wae tod tev aod aev hT hb0 elong κ hag
  refine ⟨c, fun x hx => ?_⟩
  rcases hcov x hx with ⟨m, hm, hxm⟩ | hxb
  · have g := hs m hm _ hxm
    rw [sub_add_cancel] at g
    exact g
  · have g := hb _ hxb
    rw [sub_add_cancel] at g
    exact g

/-- **The vertical side of the odd L-correction of sign `b` at `3^{j+1} 2^k`**, both parts of `LSidesAgree` for that side. -/
theorem oddL_vert_side_T (D : JointData) (hS : D.S = paperS) (hTB : TripleBaseInput) (f : Word → JSlice) (j k : ℕ)
    (b : Bool) (hgood : GoodBelow D f (wk2 (tP j) k).length) (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f (wk2 (tP j) k)) (wk2 (tP j) k) wo we wao wae tod tev aod aev)
    (hb0 : k = 0 → ∃ E, SurgicalWeak.PaperBaseCond (tP j) tod E) (elong : Bool) (κ : ℕ → ℤ)
    (hag : PiecesAgree (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ) :
    RespectsTiles (sideOrient (sideB b)).1 (sideOrient (sideB b)).2
        (sideString (hWordOf (wk2 (tP j) k) false) (vWordOf (wk2 (tP j) k) false) 0 (sideB b))
        (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).val ∧
      ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf (wk2 (tP j) k) false) (vWordOf (wk2 (tP j) k) false) 0 (sideB b)),
        x ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).dom ∧ x ∈ tod.dom ∧
          (gluedOdo (LStepAssembly.oddPs D f (wk2 (tP j) k) b elong) κ).val x = tod.val x + c := by
  obtain ⟨c, hc⟩ := oddL_vert_T D hS hTB f j k b hgood wo we wao wae tod tev aod aev hT hb0 elong κ hag
  obtain ⟨-, -, -, -, hR, -⟩ := hT
  have hRs : RespectsTiles (sideOrient (sideB b)).1 (sideOrient (sideB b)).2
      (sideString (hWordOf (wk2 (tP j) k) false) (vWordOf (wk2 (tP j) k) false) 0 (sideB b)) tod.val := by
    cases b
    · exact hR.2.2.2.2
    · exact hR.2.2.2.1
  exact ⟨LSidesEven.respectsTiles_add_const _ _ _ _ _ c hRs (fun x hx => (hc x hx).2.2), c, hc⟩

end FLatticePaper.Tiles.LSidesOddTriple
