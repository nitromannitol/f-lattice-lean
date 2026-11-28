import FLatticePaper.Tiles.CorrectedWalkZero
import FLatticePaper.Tiles.StdPairCompatPaper
import FLatticePaper.Tiles.AltSixEvenOF
import FLatticePaper.Tiles.AltSevenFamilyC
import FLatticePaper.Tiles.AltLSides
import FLatticePaper.Tiles.TileHalfTurnLRot
import FLatticePaper.Tiles.OddPtVMinus
import FLatticePaper.Tiles.EvenMidVMinus
import FLatticePaper.Tiles.VPlusReflect
import FLatticePaper.Tiles.AltShiftFamily

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.AltParentConstants
open FLatticePaper.Tiles.SurgicalWeak (regsAt)
open FLatticePaper.Tiles.Standard (oddTile evenTile IsBase)
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.TileStepAssembly
open FLatticePaper.Tiles.JointGlue (pieceVal)

/-! # Condition (C) at the corrected even alternate decomposition: the boundary

After a `3` the even alternate decomposition `aEP` has the elongated L-corrections `L^+`, `L^-` of the register `w.dropLast` at
the places `0`, `3` of the copies `Q^{+,1}`, `Q^{-,2}`. Its four full copies `1, 2` (of `T(q_1)`) and `4, 5` (of `T(p_1)`) take the
constants of the six-copy agreement of the uncorrected decomposition (`AltSixEvenOF.sixEven_of`), and each L-correction takes the
constant of the copy it replaces minus its own constant on its kept sides (`LSidesAgree`, `D.lSides = paperLSides`). With these
constants:
* the four mixed pairs of full copies agree at every common point (their common points lie in the marks, item (5));
* each L-correction agrees with its doubled partner and with the mixed copy next to it at one point of its kept sides: corners of
  the standard tile, and for the doubled partners the points of the vertical sides of `T(q_1)` found by w3: `V - B + (1, -1)` for
  `W_1` odd (`OddPtVMinus.pt_vMinus_odd`), the midpoint `m = (B + V + (1, -1)) / 2` of the doubled pair and its half-turn image
  `D - m` for `W_1` even (`EvenMidVMinus.mid_vMinus`, `VPlusReflect.mid_vPlus`);
* the two L-corrections have the constant `κ 3 - κ 0` on their overlap: the cross half-turn of `L^+` and `L^-` about the centre of
  `T(q_1)` (`TileHalfTurnInput.crossEven`), with its two constants read at the corners `0` and `D` of the kept sides, gives the
  overlap constant through `CorrectedWalkZero.off_of_halfTurn` (the text's `c = -c`).
These are the six interfaces along the boundary of the decomposition in Cases 2 and 4 of the text, and the interface of the two
L-corrections; the two interfaces of an L-correction with the copy opposite to it are treated separately. Both orientations:
`aEP_boundary_of` (`W_1` odd) and `aEP_boundary_ef` (`W_1` even). -/

namespace FLatticePaper.Tiles.CorrectedAltEven



/-- The L-entries `0`, `3` of the even alternate decomposition after a `3`. -/
theorem aEP_getL (D : JointData) (f : Word → JSlice) (w : Word) (hl : w.dropLast.length < w.length)
    (h3 : w.getLast? = some Digit.three) :
    (aEP D f w)[0]? = some (stdPiece ((f w.dropLast).lEven true true) (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus))
      (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus))) ∧
    (aEP D f w)[3]? = some (stdPiece ((f w.dropLast).lEven false true) (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) +
      (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2) (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + aP2 w)) := by
  have e : below f w w.dropLast = f w.dropLast := JointRot.below_of_lt f w _ hl
  refine ⟨?_, ?_⟩ <;> simp [aEP, tileAltEvenPieces, e, h3]

/-- The origin lies on the left side string of a standard even tile (the first tile of the string sits at `0`). -/
theorem vMinus_zero (wd : Word) :
    ((0 : ℤ), (0 : ℤ)) ∈ placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 .vMinus) := by
  have hne : (vWordOf wd true).reverse ≠ [] := by
    intro h; rw [List.reverse_eq_nil_iff] at h
    have := (StringCorners.vWord_even_head_last wd).1; rw [h] at this; simp at this
  obtain ⟨a, rest, hr⟩ : ∃ a rest, (vWordOf wd true).reverse = a :: rest := by
    cases h : (vWordOf wd true).reverse with
    | nil => exact absurd h hne
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hm : (letterZTile a, (0 : GInt)) ∈ vRevStringAt (vWordOf wd true).reverse 0 := by
    rw [hr, VerticalStepOne.vRevStringAt_eq]
    cases rest <;> simp [VerticalStepOne.vAux]
  have := JointRot.mem_placedSites_of hm (u := ((0 : ℤ), (0 : ℤ))) (by cases a <;> simp [letterZTile, tileShape])
  simpa [sideString] using this

/-- A pair of entries that both agree with one family `F` of functions on their placed domains, and on which `F` agrees. -/
theorem agreeAll_of {ps : List Piece} {κ : ℕ → ℤ} {i j : ℕ} {p0 q0 : Piece} (hp : ps[i]? = some p0) (hq : ps[j]? = some q0)
    (F : ℕ → ℤ × ℤ → ℤ) (hFi : ∀ x ∈ p0.placed, pieceVal p0 x + κ i = F i x)
    (hFj : ∀ x ∈ q0.placed, pieceVal q0 x + κ j = F j x) (hF : ∀ x ∈ p0.placed, x ∈ q0.placed → F i x = F j x) :
    CorrectedWalkZero.AgreeAll ps κ i j := by
  intro p q hp' hq' x hx hx' _ _
  rw [hp] at hp'; rw [hq] at hq'
  cases hp'; cases hq'
  rw [hFi x hx, hFj x hx', hF x hx hx']

/-- One common point of two entries where both agree with `F` and `F` agrees. -/
theorem witness_of {ps : List Piece} {κ : ℕ → ℤ} {i j : ℕ} {o o' : PartialOdometer} {a a' s s' : ℤ × ℤ}
    (hp : ps[i]? = some (stdPiece o a s)) (hq : ps[j]? = some (stdPiece o' a' s')) (F : ℕ → ℤ × ℤ → ℤ) (x : ℤ × ℤ)
    (hx : x - a ∈ o.dom) (hx' : x - a' ∈ o'.dom) (hFi : pieceVal (stdPiece o a s) x + κ i = F i x)
    (hFj : pieceVal (stdPiece o' a' s') x + κ j = F j x) (hF : F i x = F j x) :
    CorrectedWalkZero.EdgeWitness ps κ i j := by
  intro p q hp' hq'
  rw [hp] at hp'; rw [hq] at hq'
  cases hp'; cases hq'
  exact ⟨x, JointRot.mem_placed.2 hx, JointRot.mem_placed.2 hx', by simp [stdPiece], by simp [stdPiece], by
    rw [hFi, hFj, hF]⟩

/-- A full copy of the even parent as a placed subodometer of the uncorrected decomposition. -/
theorem pv_lt (w : Word) (oP oQ : PartialOdometer) (κ : ℕ → ℤ) (i : ℕ) (hi : i < 4) (x : ℤ × ℤ) :
    pieceVal (stdPiece oQ ((altEvenD w).getD i 0) ((altEvenAff w).getD i 0)) x + κ i =
      placedAltEven w oP.val oQ.val κ i x := by
  rw [AltSixEven.eval_lt w _ _ κ i x _ _ _ hi rfl rfl rfl]
  simp [pieceVal, stdPiece, ClosedPathSum.dot2, dotS]

/-- A full copy of the odd parent as a placed subodometer of the uncorrected decomposition. -/
theorem pv_ge (w : Word) (oP oQ : PartialOdometer) (κ : ℕ → ℤ) (i : ℕ) (hi : ¬ i < 4) (x : ℤ × ℤ) :
    pieceVal (stdPiece oP ((altEvenR w).getD (i - 4) 0) ((altEvenAff w).getD i 0)) x + κ i =
      placedAltEven w oP.val oQ.val κ i x := by
  rw [AltSixEven.eval_ge w _ _ κ i x _ _ _ hi rfl rfl rfl]
  simp [pieceVal, stdPiece, ClosedPathSum.dot2, dotS]

/-- An L-entry at a point of its kept sides, where it is the copy it replaces plus its constant. -/
theorem pv_L (w : Word) (oP oQ L : PartialOdometer) (κ : ℕ → ℤ) (i : ℕ) (hi : i < 4) (c : ℤ) (x : ℤ × ℤ)
    (h : L.val (x - (altEvenD w).getD i 0) = oQ.val (x - (altEvenD w).getD i 0) + c) :
    pieceVal (stdPiece L ((altEvenD w).getD i 0) ((altEvenAff w).getD i 0)) x + (κ i - c) =
      placedAltEven w oP.val oQ.val κ i x := by
  rw [AltSixEven.eval_lt w _ _ κ i x _ _ _ hi rfl rfl rfl]
  simp only [pieceVal, stdPiece, ClosedPathSum.dot2, dotS] at h ⊢
  rw [h]; ring

/-- Common points of a copy of the even parent and a copy of the odd parent lie in both marks (item (5)). -/
theorem marks_mix (w u1 u2 : Word) (hb : ¬ IsBase w) (hT1 : (Standard.stateAt w).tOdd = oddTile u1)
    (hT2 : (Standard.stateAt w).tEven = evenTile u2) (i j : ℕ) (hi : i < 4) (hj4 : 4 ≤ j) (hj6 : j < 6) (x : ℤ × ℤ)
    (hx : x - (altEvenD w).getD i 0 ∈ evenTile u2) (hx' : x - (altEvenR w).getD (j - 4) 0 ∈ oddTile u1) :
    x ∈ mAE w u1 u2 i ∧ x ∈ mAE w u1 u2 j := by
  have hlD : (ClosedPathAlt.altEvenD w).length = 4 := rfl
  have hDQ : ClosedPathAlt.altEvenD w = AltPieces.evenQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := rfl
  have hRP : ClosedPathAlt.altEvenR w = AltPieces.evenPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := rfl
  have hma : (ClosedPathAlt.altEvenD w).getD i 0 ∈ AltPieces.evenQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := by
    rw [← hDQ, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hmb : (ClosedPathAlt.altEvenR w).getD (j - 4) 0 ∈
      AltPieces.evenPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := by
    rw [← hRP, List.getD_eq_getElem _ _ (by rw [hRP]; simp [AltPieces.evenPOffs]; omega)]; exact List.getElem_mem _
  rw [← hT2] at hx
  rw [← hT1] at hx'
  obtain ⟨m1, m2⟩ := AltItem5.item5_marks_even hb u1 u2 hT1 hT2 _ hmb _ hma x
    (StdPairCompatPaper.mem_std_shift hx') (StdPairCompatPaper.mem_std_shift hx)
  exact ⟨by simp only [mAE, pieceSet, hlD, if_pos hi]; exact m2,
    by simp only [mAE, pieceSet, hlD, if_neg (show ¬ j < 4 by omega)]; exact m1⟩

/-- The doubled-shift constant of the even register (the shift `S_q`, affine factor `a_{p,2}`), from the shift compatibility of
the registers at every word that is not a base word (`AltShiftFamily.shift_compat_family`). -/
theorem hk_of (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w u1 u2 : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (hr : regsAt w = (some u1, some u2)) (hdE : (f u2).tEven.dom = evenTile u2) :
    ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ w ∈ tEvenSet u2 →
      (f u2).tEven.val (x + shiftQ w) - (f u2).tEven.val x - ClosedPathSum.dot2 (affS w) x = k := by
  obtain ⟨c, hc⟩ := (AltShiftFamily.shift_compat_family D hS hA f w u1 u2 hG hb hr).2
  refine ⟨c, fun x hx hx' => ?_⟩
  have h := hc x (by rw [hdE]; exact hx) (by rw [hdE]; exact hx')
  simpa [ClosedPathSum.dot2, dotS] using h

set_option maxHeartbeats 400000 in
/-- **The boundary of the corrected even alternate decomposition, and the overlap of its two L-corrections, `W_1` odd.** -/
theorem aEP_boundary_of (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hlS : D.lSides = paperLSides) (f : Word → JSlice) (w : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (h3 : w.getLast? = some Digit.three) (hph : phase w = 1) :
    ∃ κ : ℕ → ℤ, CorrectedWalkZero.AgreeAll (aEP D f w) κ 1 4 ∧ CorrectedWalkZero.AgreeAll (aEP D f w) κ 1 5 ∧
      CorrectedWalkZero.AgreeAll (aEP D f w) κ 2 4 ∧ CorrectedWalkZero.AgreeAll (aEP D f w) κ 2 5 ∧
      CorrectedWalkZero.EdgeWitness (aEP D f w) κ 0 1 ∧ CorrectedWalkZero.EdgeWitness (aEP D f w) κ 0 4 ∧
      CorrectedWalkZero.EdgeWitness (aEP D f w) κ 3 2 ∧ CorrectedWalkZero.EdgeWitness (aEP D f w) κ 3 5 ∧
      ∀ off, CorrectedWalkZero.OffMatch (aEP D f w) off → ∀ (hi : 0 < (aEP D f w).length) (hj : 3 < (aEP D f w).length),
        (∃ x ∈ ((aEP D f w).get ⟨0, hi⟩).placed, x ∈ ((aEP D f w).get ⟨3, hj⟩).placed ∧
          x ∉ ((aEP D f w).get ⟨0, hi⟩).exc ∧ x ∉ ((aEP D f w).get ⟨3, hj⟩).exc) → off ⟨0, hi⟩ ⟨3, hj⟩ = κ 3 - κ 0 := by
  obtain ⟨u1, u2, hr, hl1, hl2, hdO, hdE, hU1, hU2, hT1, hT2⟩ := StdPairCompatPaper.regs_data D hS f w hG hb
  have hw : w = w.dropLast ++ [Digit.three] := by
    have := List.dropLast_append_getLast? (l := w) (a := Digit.three) h3
    exact this.symm
  have hu2 : u2 = w.dropLast := by
    have e := ConnectedAltL.regs_pre_snd w.dropLast Digit.three (by decide)
    rw [← hw, hr] at e
    exact Option.some.inj e
  subst hu2
  obtain ⟨g1, g2, g4, g5, hlen⟩ := StdPairCompatPaper.aEP_get D f w u1 w.dropLast hr hl1 hl2 h3
  obtain ⟨g0, g3⟩ := aEP_getL D f w hl2 h3
  have hp := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents w).2 w.dropLast (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hG u1 hl1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hG w.dropLast hl2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdQ] at hhQ
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f w u1 w.dropLast hG hb hr 0).2
  have hk := hk_of D hS hA f w u1 w.dropLast hG hb hr hdE
  obtain ⟨hmix, hdbl⟩ := AltSixEvenOF.sixEven_of w u1 w.dropLast hph hp hq (f u1).tOdd (f w.dropLast).tEven βP βQ hcP hcQ hhQ hk hcompat
  -- the entries with their offsets in the form of `altEvenD`, `altEvenR`
  have g0' : (aEP D f w)[0]? = some (stdPiece ((f w.dropLast).lEven true true) ((altEvenD w).getD 0 0) ((altEvenAff w).getD 0 0)) := g0
  have g3' : (aEP D f w)[3]? = some (stdPiece ((f w.dropLast).lEven false true) ((altEvenD w).getD 3 0) ((altEvenAff w).getD 3 0)) := by
    rw [g3]; congr 2; exact add_comm _ _
  have g1' : (aEP D f w)[1]? = some (stdPiece (f w.dropLast).tEven ((altEvenD w).getD 1 0) ((altEvenAff w).getD 1 0)) := by
    rw [g1]; congr 2; exact add_comm _ _
  have g2' : (aEP D f w)[2]? = some (stdPiece (f w.dropLast).tEven ((altEvenD w).getD 2 0) ((altEvenAff w).getD 2 0)) := g2
  have g4' : (aEP D f w)[4]? = some (stdPiece (f u1).tOdd ((altEvenR w).getD (4 - 4) 0) ((altEvenAff w).getD 4 0)) := g4
  have g5' : (aEP D f w)[5]? = some (stdPiece (f u1).tOdd ((altEvenR w).getD (5 - 4) 0) ((altEvenAff w).getD 5 0)) := g5
  -- the kept sides of the two L-corrections
  have hdef : EvenLDefined w.dropLast := JointRot.evenLDefined_of_mem _ (by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    exact hb (Or.inr (Or.inl fun d hd => by
      rw [hw] at hd; simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl; exacts [hc d hd, rfl])))
  have hJl := (hG w.dropLast hl2).1.2.2.2
  obtain ⟨-, c0, hc0⟩ := (hJl.2 true true hdef).2
  obtain ⟨-, c3, hc3⟩ := (hJl.2 false true hdef).2
  rw [hlS] at hc0 hc3
  have hWd : W1Odd w.dropLast = true := by
    have h := hph
    rw [hw] at h
    simp only [W1Odd, phase, List.count_append] at h ⊢
    simp at h ⊢
    omega
  have k0h := hc0 .hPlus (by simp [paperLSides, printedEvenSides, hWd])
  have k0v := hc0 .vPlus (by simp [paperLSides, printedEvenSides, hWd])
  have k3h := hc3 .hMinus (by simp [paperLSides, printedEvenSides, hWd])
  have k3v := hc3 .vMinus (by simp [paperLSides, printedEvenSides, hWd])
  -- the point `V - B + (1, -1)` of the left side (`OddPtVMinus.pt_vMinus_odd`), a kept side of `L^-`, hence in `T(q_1)`
  have hy : texV2 (parentsAt w).even - texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) ∈ evenTile w.dropLast := by
    have h := OddPtVMinus.pt_vMinus_odd w.dropLast (by rw [← hw]; exact hb)
      (by rw [← hw]; exact StdPairCompatPaper.w1Odd_of hph)
    rw [← hw] at h
    rw [← hdE]; exact (k3v _ h).2.1
  have esc := ConnectedAltL.even_side_corners w.dropLast
  have esm := AltLSides.even_side_more w.dropLast
  rw [← hw] at esc esm
  -- the offsets, `W_1` odd
  obtain ⟨hD, hR, hAf, hSh⟩ := ClosedPathAlt.altEven_of w hph
  have cmE := ClosedPathContacts.corner_marks_even w.dropLast
  have cmO := ClosedPathContacts.corner_marks_odd u1
  rw [← hq] at cmE
  rw [← hp] at cmO
  have hlD : (altEvenD w).length = 4 := rfl
  have hlR : (altEvenR w).length = 2 := rfl
  set κ6 := AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
    (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ with hκ6
  set F := placedAltEven w (f u1).tOdd.val (f w.dropLast).tEven.val κ6 with hF
  let κ : ℕ → ℤ := fun i => if i = 0 then κ6 0 - c0 else if i = 3 then κ6 3 - c3 else κ6 i
  have κ0 : κ 0 = κ6 0 - c0 := rfl
  have κ1 : κ 1 = κ6 1 := rfl
  have κ2 : κ 2 = κ6 2 := rfl
  have κ3 : κ 3 = κ6 3 - c3 := rfl
  have κ4 : κ 4 = κ6 4 := rfl
  have κ5 : κ 5 = κ6 5 := rfl
  have mix : ∀ i j, i < 4 → 4 ≤ j → j < 6 → ∀ x, x - (altEvenD w).getD i 0 ∈ evenTile w.dropLast →
      x - (altEvenR w).getD (j - 4) 0 ∈ oddTile u1 → F i x = F j x := fun i j hi hj4 hj6 x hx hx' => by
    obtain ⟨m1, m2⟩ := marks_mix w u1 w.dropLast hb hT1 hT2 i j hi hj4 hj6 x hx hx'
    exact hmix i j (by rw [hlD, hlR]; omega) (by rw [hlD, hlR]; omega)
      (by simp only [pieceFlag, hlD]; intro h; simp at h; omega) x m1 m2
  have std_mix : ∀ i j, i < 4 → 4 ≤ j → j < 6 → κ i = κ6 i → κ j = κ6 j →
      (aEP D f w)[i]? = some (stdPiece (f w.dropLast).tEven ((altEvenD w).getD i 0) ((altEvenAff w).getD i 0)) →
      (aEP D f w)[j]? = some (stdPiece (f u1).tOdd ((altEvenR w).getD (j - 4) 0) ((altEvenAff w).getD j 0)) →
      CorrectedWalkZero.AgreeAll (aEP D f w) κ i j := fun i j hi hj4 hj6 ei ej gi gj =>
    agreeAll_of gi gj F (fun x _ => by rw [ei]; exact pv_lt w (f u1).tOdd _ κ6 i hi x)
      (fun x _ => by rw [ej]; exact pv_ge w (f u1).tOdd (f w.dropLast).tEven κ6 j (by omega) x)
      (fun x hx hx' => mix i j hi hj4 hj6 x (by rw [← hdE]; exact JointRot.mem_placed.1 hx)
        (by rw [← hdO]; exact JointRot.mem_placed.1 hx'))
  -- corner memberships
  have dQ0 : (0 : ℤ × ℤ) ∈ evenTile w.dropLast := hdQ ▸ hcQ.1.1
  have dQD : texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) ∈ evenTile w.dropLast :=
    hdQ ▸ hcQ.2.2.2.2.2.2.1.1
  have dPX : texV1Odd (parentsAt w).odd ∈ oddTile u1 := hdP ▸ hcP.2.2.2.1.1
  have dPY : texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) ∈ oddTile u1 := hdP ▸ hcP.2.2.2.2.2.1.1
  have dQS : texV1Even (parentsAt w).even + texV2 (parentsAt w).odd ∈ evenTile w.dropLast := by
    have h := (hhQ _ hy).1
    have e : texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) -
        (texV2 (parentsAt w).even - texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))) =
        texV1Even (parentsAt w).even + texV2 (parentsAt w).odd := by
      ext <;> simp <;> ring
    rw [e] at h
    exact h
  have pt : ∀ (S : Set (ℤ × ℤ)) (a z : ℤ × ℤ), z - a ∈ S → z ∈ SiteInduction.shiftS S a :=
    fun S a z h => (AltPiecesAgree.mem_shiftS_iff S a z).2 h
  refine ⟨κ, std_mix 1 4 (by norm_num) le_rfl (by norm_num) κ1 κ4 g1' g4',
    std_mix 1 5 (by norm_num) (by norm_num) (by norm_num) κ1 κ5 g1' g5',
    std_mix 2 4 (by norm_num) le_rfl (by norm_num) κ2 κ4 g2' g4',
    std_mix 2 5 (by norm_num) (by norm_num) (by norm_num) κ2 κ5 g2' g5', ?_, ?_, ?_, ?_, ?_⟩
  · -- `(0, 1)`: the corner `D` of `L^+` on its right side, inside the doubled partner
    set x := (altEvenD w).getD 0 0 + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) with hx
    have e0 : x - (altEvenD w).getD 0 0 = texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hx]; abel
    have e1 : x - (altEvenD w).getD 1 0 = texV2 (parentsAt w).even - texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hx]; simp only [hD, hSh, List.getD_cons_succ, List.getD_cons_zero]; ext <;> simp <;> ring
    have kD := k0v _ esm.2.2.2.1
    refine witness_of g0' g1' F x (by rw [e0]; exact kD.1) (by rw [e1, hdE]; exact hy) ?_ ?_ ?_
    · rw [κ0]; exact pv_L w (f u1).tOdd _ _ κ6 0 (by norm_num) c0 x (by rw [e0]; exact kD.2.2)
    · rw [κ1]; exact pv_lt w (f u1).tOdd _ κ6 1 (by norm_num) x
    · exact hdbl 0 1 (by rw [hlD, hlR]; omega) (by rw [hlD, hlR]; omega) (by norm_num)
        (by simp [pieceFlag, hlD]) ⟨rfl, Or.inl rfl⟩ x
        (by simp only [pieceSet, hlD, if_pos (show 0 < 4 by norm_num)]; exact pt _ _ _ (by rw [e0]; exact dQD))
        (by simp only [pieceSet, hlD, if_pos (show 1 < 4 by norm_num)]; exact pt _ _ _ (by rw [e1]; exact hy))
  · -- `(0, 4)`: the corner `0` of `L^+` on its bottom side, the corner `X` of the copy of the odd parent
    set x := (altEvenD w).getD 0 0 with hx
    have e0 : x - (altEvenD w).getD 0 0 = 0 := sub_self _
    have e4 : x - (altEvenR w).getD (4 - 4) 0 = texV1Odd (parentsAt w).odd := by
      rw [hx]; simp only [hD, hR, List.getD_cons_zero, Nat.sub_self, sub_zero]
    have k := k0h _ esc.1
    refine witness_of g0' g4' F x (by rw [e0]; exact k.1) (by rw [e4, hdO]; exact dPX) ?_ ?_ ?_
    · rw [κ0]; exact pv_L w (f u1).tOdd _ _ κ6 0 (by norm_num) c0 x (by rw [e0]; exact k.2.2)
    · rw [κ4]; exact pv_ge w (f u1).tOdd _ κ6 4 (by norm_num) x
    · exact mix 0 4 (by norm_num) le_rfl (by norm_num) x (by rw [e0]; exact dQ0) (by rw [e4]; exact dPX)
  · -- `(3, 2)`: the corner `0` of `L^-` on its left side, inside the doubled partner
    set x := (altEvenD w).getD 3 0 with hx
    have e3 : x - (altEvenD w).getD 3 0 = 0 := sub_self _
    have e2 : x - (altEvenD w).getD 2 0 = texV1Even (parentsAt w).even + texV2 (parentsAt w).odd := by
      rw [hx]; simp only [hD, hSh, List.getD_cons_succ, List.getD_cons_zero]; abel
    have k := k3v _ (vMinus_zero w.dropLast)
    refine witness_of g3' g2' F x (by rw [e3]; exact k.1) (by rw [e2, hdE]; exact dQS) ?_ ?_ ?_
    · rw [κ3]; exact pv_L w (f u1).tOdd _ _ κ6 3 (by norm_num) c3 x (by rw [e3]; exact k.2.2)
    · rw [κ2]; exact pv_lt w (f u1).tOdd _ κ6 2 (by norm_num) x
    · exact (hdbl 2 3 (by rw [hlD, hlR]; omega) (by rw [hlD, hlR]; omega) (by norm_num)
        (by simp [pieceFlag, hlD]) ⟨rfl, Or.inr rfl⟩ x
        (by simp only [pieceSet, hlD, if_pos (show 2 < 4 by norm_num)]; exact pt _ _ _ (by rw [e2]; exact dQS))
        (by simp only [pieceSet, hlD, if_pos (show 3 < 4 by norm_num)]; exact pt _ _ _ (by rw [e3]; exact dQ0))).symm
  · -- `(3, 5)`: the corner `D` of `L^-` on its top side, the corner `Y + 1 - i` of the copy of the odd parent
    set x := (altEvenD w).getD 3 0 + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) with hx
    have e3 : x - (altEvenD w).getD 3 0 = texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hx]; abel
    have e5 : x - (altEvenR w).getD (5 - 4) 0 = texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hx]; simp only [hD, hR, hSh, List.getD_cons_succ, List.getD_cons_zero, show 5 - 4 = 1 from rfl]
      ext <;> simp <;> ring
    have kD := k3h _ esm.2.2.2.2.2
    refine witness_of g3' g5' F x (by rw [e3]; exact kD.1) (by rw [e5, hdO]; exact dPY) ?_ ?_ ?_
    · rw [κ3]; exact pv_L w (f u1).tOdd _ _ κ6 3 (by norm_num) c3 x (by rw [e3]; exact kD.2.2)
    · rw [κ5]; exact pv_ge w (f u1).tOdd _ κ6 5 (by norm_num) x
    · exact mix 3 5 (by norm_num) (by norm_num) (by norm_num) x (by rw [e3]; exact dQD) (by rw [e5]; exact dPY)
  · -- `(0, 3)`: the cross half-turn of `L^+` and `L^-` about the centre of `T(q_1)`, pinned at the corners `0` and `D` of their
    -- kept sides
    intro off hoff hi hj hx
    have hwl : w.dropLast.length + 1 = w.length := by
      have : w ≠ [] := by rintro rfl; simp at h3
      rw [List.length_dropLast]; have := List.length_pos_of_ne_nil this; omega
    have hG' : GoodBelow D f (w.dropLast.length + 1) := hwl ▸ hG
    have hspec := FLatticePaper.Tiles.TileHalfTurnLRot.specialLHalfTurn_of_rot D
    obtain ⟨K, hK⟩ := FLatticePaper.Tiles.TileHalfTurnInput.crossEven D hS hA hspec f w.dropLast hG' hdef true true
    obtain ⟨K', hK'⟩ := FLatticePaper.Tiles.TileHalfTurnInput.crossEven D hS hA hspec f w.dropLast hG' hdef false true
    have hC : TileHalfTurnStd.cEven ((parentsAt w.dropLast).current .even) =
        texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hq]; rfl
    have k00 := k0h _ esc.1
    have k0D := k0v _ esm.2.2.2.1
    have k30 := k3v _ (vMinus_zero w.dropLast)
    have k3D := k3h _ esm.2.2.2.2.2
    simp only [vQ1, vQ2] at k0D k3D
    have pK := (hK _ k00.1).2
    have pK' := (hK' _ k30.1).2
    have e00 : ∀ v : ℤ × ℤ, v - ((0 : ℤ), (0 : ℤ)) = v := fun v => by ext <;> simp
    simp only [Bool.not_true, Bool.not_false, e00, hC] at pK pK'
    rw [k3D.2.2, k00.2.2] at pK
    rw [k0D.2.2, k30.2.2] at pK'
    simp only [dotS, mul_zero, add_zero] at pK pK'
    refine CorrectedWalkZero.off_of_halfTurn hoff (i := 0) (j := 3) g0' g3' hK hK' ?_ hi hj hx
    rw [hC, κ0, κ3]
    have hcur : (parentsAt w.dropLast).current .even = (parentsAt w).even := by rw [hq]; rfl
    simp only [hκ6, AltSixEvenOF.kEvenOF, hD, hAf, hSh, List.getD_cons_zero, List.getD_cons_succ,
      TileHalfTurnStd.aF, offsetA, dotS, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hcur]
    linear_combination pK' - pK

set_option maxHeartbeats 400000 in
/-- **The boundary of the corrected even alternate decomposition, and the overlap of its two L-corrections, `W_1` even.** The
doubled partner of `L^-` is read at the half-turn image `D - m` of the midpoint `m` on the right side (`VPlusReflect.mid_vPlus`). -/
theorem aEP_boundary_ef (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hlS : D.lSides = paperLSides) (f : Word → JSlice) (w : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (h3 : w.getLast? = some Digit.three) (hph : phase w ≠ 1) :
    ∃ κ : ℕ → ℤ, CorrectedWalkZero.AgreeAll (aEP D f w) κ 1 4 ∧ CorrectedWalkZero.AgreeAll (aEP D f w) κ 1 5 ∧
      CorrectedWalkZero.AgreeAll (aEP D f w) κ 2 4 ∧ CorrectedWalkZero.AgreeAll (aEP D f w) κ 2 5 ∧
      CorrectedWalkZero.EdgeWitness (aEP D f w) κ 0 1 ∧ CorrectedWalkZero.EdgeWitness (aEP D f w) κ 0 4 ∧
      CorrectedWalkZero.EdgeWitness (aEP D f w) κ 3 2 ∧ CorrectedWalkZero.EdgeWitness (aEP D f w) κ 3 5 ∧
      ∀ off, CorrectedWalkZero.OffMatch (aEP D f w) off → ∀ (hi : 0 < (aEP D f w).length) (hj : 3 < (aEP D f w).length),
        (∃ x ∈ ((aEP D f w).get ⟨0, hi⟩).placed, x ∈ ((aEP D f w).get ⟨3, hj⟩).placed ∧
          x ∉ ((aEP D f w).get ⟨0, hi⟩).exc ∧ x ∉ ((aEP D f w).get ⟨3, hj⟩).exc) → off ⟨0, hi⟩ ⟨3, hj⟩ = κ 3 - κ 0 := by
  obtain ⟨u1, u2, hr, hl1, hl2, hdO, hdE, hU1, hU2, hT1, hT2⟩ := StdPairCompatPaper.regs_data D hS f w hG hb
  have hw : w = w.dropLast ++ [Digit.three] := by
    have := List.dropLast_append_getLast? (l := w) (a := Digit.three) h3
    exact this.symm
  have hu2 : u2 = w.dropLast := by
    have e := ConnectedAltL.regs_pre_snd w.dropLast Digit.three (by decide)
    rw [← hw, hr] at e
    exact Option.some.inj e
  subst hu2
  obtain ⟨g1, g2, g4, g5, hlen⟩ := StdPairCompatPaper.aEP_get D f w u1 w.dropLast hr hl1 hl2 h3
  obtain ⟨g0, g3⟩ := aEP_getL D f w hl2 h3
  have hp := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents w).2 w.dropLast (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hG u1 hl1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hG w.dropLast hl2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdQ] at hhQ
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f w u1 w.dropLast hG hb hr 0).2
  have hk := hk_of D hS hA f w u1 w.dropLast hG hb hr hdE
  obtain ⟨hmix, hdbl⟩ := AltSixEven.sixEven_ef w u1 w.dropLast hph hp hq (f u1).tOdd (f w.dropLast).tEven βP βQ hcP hcQ hhQ hk hcompat
  -- the entries with their offsets in the form of `altEvenD`, `altEvenR`
  have g0' : (aEP D f w)[0]? = some (stdPiece ((f w.dropLast).lEven true true) ((altEvenD w).getD 0 0) ((altEvenAff w).getD 0 0)) := g0
  have g3' : (aEP D f w)[3]? = some (stdPiece ((f w.dropLast).lEven false true) ((altEvenD w).getD 3 0) ((altEvenAff w).getD 3 0)) := by
    rw [g3]; congr 2; exact add_comm _ _
  have g1' : (aEP D f w)[1]? = some (stdPiece (f w.dropLast).tEven ((altEvenD w).getD 1 0) ((altEvenAff w).getD 1 0)) := by
    rw [g1]; congr 2; exact add_comm _ _
  have g2' : (aEP D f w)[2]? = some (stdPiece (f w.dropLast).tEven ((altEvenD w).getD 2 0) ((altEvenAff w).getD 2 0)) := g2
  have g4' : (aEP D f w)[4]? = some (stdPiece (f u1).tOdd ((altEvenR w).getD (4 - 4) 0) ((altEvenAff w).getD 4 0)) := g4
  have g5' : (aEP D f w)[5]? = some (stdPiece (f u1).tOdd ((altEvenR w).getD (5 - 4) 0) ((altEvenAff w).getD 5 0)) := g5
  -- the kept sides of the two L-corrections
  have hdef : EvenLDefined w.dropLast := JointRot.evenLDefined_of_mem _ (by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    exact hb (Or.inr (Or.inl fun d hd => by
      rw [hw] at hd; simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl; exacts [hc d hd, rfl])))
  have hJl := (hG w.dropLast hl2).1.2.2.2
  obtain ⟨-, c0, hc0⟩ := (hJl.2 true true hdef).2
  obtain ⟨-, c3, hc3⟩ := (hJl.2 false true hdef).2
  rw [hlS] at hc0 hc3
  have hWd : W1Odd w.dropLast = false := by
    have h := hph
    rw [hw] at h
    simp only [W1Odd, phase, List.count_append] at h ⊢
    simp at h ⊢
    omega
  have k0h := hc0 .hPlus (by simp [paperLSides, printedEvenSides, hWd])
  have k0v := hc0 .vMinus (by simp [paperLSides, printedEvenSides, hWd])
  have k3h := hc3 .hMinus (by simp [paperLSides, printedEvenSides, hWd])
  have k3v := hc3 .vPlus (by simp [paperLSides, printedEvenSides, hWd])
  have esc := ConnectedAltL.even_side_corners w.dropLast
  have esm := AltLSides.even_side_more w.dropLast
  rw [← hw] at esc esm
  -- the offsets, `W_1` odd
  obtain ⟨hD, hR, hAf, hSh⟩ := ClosedPathAlt.altEven_ef w hph
  have cmE := ClosedPathContacts.corner_marks_even w.dropLast
  have cmO := ClosedPathContacts.corner_marks_odd u1
  rw [← hq] at cmE
  rw [← hp] at cmO
  have hlD : (altEvenD w).length = 4 := rfl
  have hlR : (altEvenR w).length = 2 := rfl
  set κ6 := AltSixEven.kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
    (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ with hκ6
  set F := placedAltEven w (f u1).tOdd.val (f w.dropLast).tEven.val κ6 with hF
  let κ : ℕ → ℤ := fun i => if i = 0 then κ6 0 - c0 else if i = 3 then κ6 3 - c3 else κ6 i
  have κ0 : κ 0 = κ6 0 - c0 := rfl
  have κ1 : κ 1 = κ6 1 := rfl
  have κ2 : κ 2 = κ6 2 := rfl
  have κ3 : κ 3 = κ6 3 - c3 := rfl
  have κ4 : κ 4 = κ6 4 := rfl
  have κ5 : κ 5 = κ6 5 := rfl
  have mix : ∀ i j, i < 4 → 4 ≤ j → j < 6 → ∀ x, x - (altEvenD w).getD i 0 ∈ evenTile w.dropLast →
      x - (altEvenR w).getD (j - 4) 0 ∈ oddTile u1 → F i x = F j x := fun i j hi hj4 hj6 x hx hx' => by
    obtain ⟨m1, m2⟩ := marks_mix w u1 w.dropLast hb hT1 hT2 i j hi hj4 hj6 x hx hx'
    exact hmix i j (by rw [hlD, hlR]; omega) (by rw [hlD, hlR]; omega)
      (by simp only [pieceFlag, hlD]; intro h; simp at h; omega) x m1 m2
  have std_mix : ∀ i j, i < 4 → 4 ≤ j → j < 6 → κ i = κ6 i → κ j = κ6 j →
      (aEP D f w)[i]? = some (stdPiece (f w.dropLast).tEven ((altEvenD w).getD i 0) ((altEvenAff w).getD i 0)) →
      (aEP D f w)[j]? = some (stdPiece (f u1).tOdd ((altEvenR w).getD (j - 4) 0) ((altEvenAff w).getD j 0)) →
      CorrectedWalkZero.AgreeAll (aEP D f w) κ i j := fun i j hi hj4 hj6 ei ej gi gj =>
    agreeAll_of gi gj F (fun x _ => by rw [ei]; exact pv_lt w (f u1).tOdd _ κ6 i hi x)
      (fun x _ => by rw [ej]; exact pv_ge w (f u1).tOdd (f w.dropLast).tEven κ6 j (by omega) x)
      (fun x hx hx' => mix i j hi hj4 hj6 x (by rw [← hdE]; exact JointRot.mem_placed.1 hx)
        (by rw [← hdO]; exact JointRot.mem_placed.1 hx'))
  -- corner memberships
  have dQ0 : (0 : ℤ × ℤ) ∈ evenTile w.dropLast := hdQ ▸ hcQ.1.1
  have dQD : texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) ∈ evenTile w.dropLast :=
    hdQ ▸ hcQ.2.2.2.2.2.2.1.1
  have dQX : texV1Even (parentsAt w).even ∈ evenTile w.dropLast := hdQ ▸ hcQ.2.2.2.1.1
  have dQY : texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) ∈ evenTile w.dropLast := hdQ ▸ hcQ.2.2.2.2.2.1.1
  have dP0 : (0 : ℤ × ℤ) ∈ oddTile u1 := hdP ▸ hcP.1.1
  have dPD : texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) ∈ oddTile u1 :=
    hdP ▸ hcP.2.2.2.2.2.2.1.1
  have pt : ∀ (S : Set (ℤ × ℤ)) (a z : ℤ × ℤ), z - a ∈ S → z ∈ SiteInduction.shiftS S a :=
    fun S a z h => (AltPiecesAgree.mem_shiftS_iff S a z).2 h
  -- the midpoint `m` of the doubled pair, on the left side
  have hpar := (parentsAt_valid w).odd_parity
  have hpe := (parentsAt_valid w).even_parity
  unfold Fraction.Odd at hpar
  unfold Fraction.Even at hpe
  set m : ℤ × ℤ := (((parentsAt w).odd.num - (parentsAt w).odd.den + ((parentsAt w).even.num - (parentsAt w).even.den) + 1) / 2,
    ((parentsAt w).odd.num + (parentsAt w).odd.den + ((parentsAt w).even.num + (parentsAt w).even.den) - 1) / 2) with hmdef
  have hm2 : (2 : ℤ) • m = texV2 (parentsAt w).odd + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by
    rw [hmdef]; ext <;> simp [texV2] <;> omega
  have hmL : m ∈ placedSites (sideString (hWordOf w.dropLast true) (vWordOf w.dropLast true) 0 .vMinus) := by
    have h := EvenMidVMinus.mid_vMinus w.dropLast (by rw [← hw]; exact hb)
      (by rw [← hw]; exact StdPairCompatPaper.w1Odd_ef hph) m (by rw [← hw]; exact hm2)
    exact h
  have hmR : texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - m ∈
      placedSites (sideString (hWordOf w.dropLast true) (vWordOf w.dropLast true) 0 .vPlus) := by
    have h := VPlusReflect.mid_vPlus w.dropLast (by rw [← hw]; exact hb)
      (by rw [← hw]; exact StdPairCompatPaper.w1Odd_ef hph) m (by rw [← hw]; exact hm2)
    rw [← hw] at h
    exact h
  have dQm : m ∈ evenTile w.dropLast := by rw [← hdE]; exact (k0v _ hmL).2.1
  have hDm : texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - m =
      m - shiftQ w := by
    rw [hSh]
    have h2 := hm2
    ext
    · have := congrArg Prod.fst h2; simp [texV2, texV1Even] at this ⊢; linarith
    · have := congrArg Prod.snd h2; simp [texV2, texV1Even] at this ⊢; linarith
  have dQm' : m - shiftQ w ∈ evenTile w.dropLast := by
    rw [← hDm]; have h := (hhQ _ dQm).1; exact h
  refine ⟨κ, std_mix 1 4 (by norm_num) le_rfl (by norm_num) κ1 κ4 g1' g4',
    std_mix 1 5 (by norm_num) (by norm_num) (by norm_num) κ1 κ5 g1' g5',
    std_mix 2 4 (by norm_num) le_rfl (by norm_num) κ2 κ4 g2' g4',
    std_mix 2 5 (by norm_num) (by norm_num) (by norm_num) κ2 κ5 g2' g5', ?_, ?_, ?_, ?_, ?_⟩
  · -- `(0, 1)`: the midpoint `m` on the left side of `L^+`, inside the doubled partner
    set x := (altEvenD w).getD 0 0 + m with hx
    have e0 : x - (altEvenD w).getD 0 0 = m := by rw [hx]; abel
    have e1 : x - (altEvenD w).getD 1 0 = m - shiftQ w := by
      rw [hx]; simp only [hD, List.getD_cons_succ, List.getD_cons_zero]; abel
    have km := k0v _ hmL
    refine witness_of g0' g1' F x (by rw [e0]; exact km.1) (by rw [e1, hdE]; exact dQm') ?_ ?_ ?_
    · rw [κ0]; exact pv_L w (f u1).tOdd _ _ κ6 0 (by norm_num) c0 x (by rw [e0]; exact km.2.2)
    · rw [κ1]; exact pv_lt w (f u1).tOdd _ κ6 1 (by norm_num) x
    · exact hdbl 0 1 (by rw [hlD, hlR]; omega) (by rw [hlD, hlR]; omega) (by norm_num)
        (by simp [pieceFlag, hlD]) ⟨rfl, Or.inl rfl⟩ x
        (by simp only [pieceSet, hlD, if_pos (show 0 < 4 by norm_num)]; exact pt _ _ _ (by rw [e0]; exact dQm))
        (by simp only [pieceSet, hlD, if_pos (show 1 < 4 by norm_num)]; exact pt _ _ _ (by rw [e1]; exact dQm'))
  · -- `(0, 4)`: the corner `X` of `L^+` on its bottom side, the corner `0` of the copy of the odd parent
    set x := (altEvenD w).getD 0 0 + texV1Even (parentsAt w).even with hx
    have e0 : x - (altEvenD w).getD 0 0 = texV1Even (parentsAt w).even := by rw [hx]; abel
    have e4 : x - (altEvenR w).getD (4 - 4) 0 = 0 := by
      rw [hx]; simp only [hD, hR, List.getD_cons_zero, Nat.sub_self]; abel
    have k := k0h _ esc.2.1
    refine witness_of g0' g4' F x (by rw [e0]; exact k.1) (by rw [e4, hdO]; exact dP0) ?_ ?_ ?_
    · rw [κ0]; exact pv_L w (f u1).tOdd _ _ κ6 0 (by norm_num) c0 x (by rw [e0]; exact k.2.2)
    · rw [κ4]; exact pv_ge w (f u1).tOdd _ κ6 4 (by norm_num) x
    · exact mix 0 4 (by norm_num) le_rfl (by norm_num) x (by rw [e0]; exact dQX) (by rw [e4]; exact dP0)
  · -- `(3, 2)`: the point `D - m` on the right side of `L^-`, inside the doubled partner
    set x := (altEvenD w).getD 3 0 + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - m) with hx
    have e3 : x - (altEvenD w).getD 3 0 = texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - m := by
      rw [hx]; abel
    have e2 : x - (altEvenD w).getD 2 0 = m := by
      rw [hx, hDm]; simp only [hD, List.getD_cons_succ, List.getD_cons_zero]; abel
    have k := k3v _ hmR
    refine witness_of g3' g2' F x (by rw [e3]; exact k.1) (by rw [e2, hdE]; exact dQm) ?_ ?_ ?_
    · rw [κ3]; exact pv_L w (f u1).tOdd _ _ κ6 3 (by norm_num) c3 x (by rw [e3]; exact k.2.2)
    · rw [κ2]; exact pv_lt w (f u1).tOdd _ κ6 2 (by norm_num) x
    · exact (hdbl 2 3 (by rw [hlD, hlR]; omega) (by rw [hlD, hlR]; omega) (by norm_num)
        (by simp [pieceFlag, hlD]) ⟨rfl, Or.inr rfl⟩ x
        (by simp only [pieceSet, hlD, if_pos (show 2 < 4 by norm_num)]; exact pt _ _ _ (by rw [e2]; exact dQm))
        (by simp only [pieceSet, hlD, if_pos (show 3 < 4 by norm_num)]; exact pt _ _ _ (by rw [e3, hDm]; exact dQm'))).symm
  · -- `(3, 5)`: the corner `Y + 1 - i` of `L^-` on its top side, the corner `D` of the copy of the odd parent
    set x := (altEvenD w).getD 3 0 + (texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) with hx
    have e3 : x - (altEvenD w).getD 3 0 = texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by rw [hx]; abel
    have e5 : x - (altEvenR w).getD (5 - 4) 0 = texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hx]; simp only [hD, hR, hSh, List.getD_cons_succ, List.getD_cons_zero, show 5 - 4 = 1 from rfl]
      ext <;> simp <;> ring
    have kD := k3h _ esc.2.2
    refine witness_of g3' g5' F x (by rw [e3]; exact kD.1) (by rw [e5, hdO]; exact dPD) ?_ ?_ ?_
    · rw [κ3]; exact pv_L w (f u1).tOdd _ _ κ6 3 (by norm_num) c3 x (by rw [e3]; exact kD.2.2)
    · rw [κ5]; exact pv_ge w (f u1).tOdd _ κ6 5 (by norm_num) x
    · exact mix 3 5 (by norm_num) (by norm_num) (by norm_num) x (by rw [e3]; exact dQY) (by rw [e5]; exact dPD)
  · -- `(0, 3)`: the cross half-turn of `L^+` and `L^-` about the centre of `T(q_1)`, pinned at the corners `0` and `D` of their
    -- kept sides
    intro off hoff hi hj hx
    have hwl : w.dropLast.length + 1 = w.length := by
      have : w ≠ [] := by rintro rfl; simp at h3
      rw [List.length_dropLast]; have := List.length_pos_of_ne_nil this; omega
    have hG' : GoodBelow D f (w.dropLast.length + 1) := hwl ▸ hG
    have hspec := FLatticePaper.Tiles.TileHalfTurnLRot.specialLHalfTurn_of_rot D
    obtain ⟨K, hK⟩ := FLatticePaper.Tiles.TileHalfTurnInput.crossEven D hS hA hspec f w.dropLast hG' hdef true true
    obtain ⟨K', hK'⟩ := FLatticePaper.Tiles.TileHalfTurnInput.crossEven D hS hA hspec f w.dropLast hG' hdef false true
    have hC : TileHalfTurnStd.cEven ((parentsAt w.dropLast).current .even) =
        texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hq]; rfl
    have k00 := k0h _ esc.1
    have k3D := k3h _ esm.2.2.2.2.2
    simp only [vQ1, vQ2] at k3D
    have pK := (hK _ k00.1).2
    have pK' := (hK' _ k3D.1).2
    have e00 : ∀ v : ℤ × ℤ, v - ((0 : ℤ), (0 : ℤ)) = v := fun v => by ext <;> simp
    have eDD : ∀ v : ℤ × ℤ, v - v = ((0 : ℤ), (0 : ℤ)) := fun v => by ext <;> simp
    simp only [Bool.not_true, Bool.not_false, e00, hC, eDD] at pK pK'
    rw [k3D.2.2, k00.2.2] at pK
    rw [k00.2.2, k3D.2.2] at pK'
    have hT0 := (hhQ _ (show (0 : ℤ × ℤ) ∈ tEvenSet w.dropLast from dQ0)).2
    simp only [sub_zero] at hT0
    simp only [dotS, mul_zero, add_zero] at pK pK' hT0
    refine CorrectedWalkZero.off_of_halfTurn hoff (i := 0) (j := 3) g0' g3' hK hK' ?_ hi hj hx
    rw [hC, κ0, κ3]
    have hcur : (parentsAt w.dropLast).current .even = (parentsAt w).even := by rw [hq]; rfl
    simp only [hκ6, AltSixEven.kEvenEF, hD, hAf, hSh, List.getD_cons_zero, List.getD_cons_succ,
      TileHalfTurnStd.aF, offsetA, dotS, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_mk, smul_eq_mul,
      Prod.mk_zero_zero, hcur] at pK pK' hT0 ⊢
    linear_combination pK' - pK + 2 * hT0

end FLatticePaper.Tiles.CorrectedAltEven
