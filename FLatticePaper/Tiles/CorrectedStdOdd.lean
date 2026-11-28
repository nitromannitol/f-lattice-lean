import FLatticePaper.Tiles.CorrectedAltEven
import FLatticePaper.Tiles.WeakStepAssembly
import FLatticePaper.Tiles.TileSlopeZeroPaper

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.SurgicalWeak (regsAt)
open FLatticePaper.Tiles.Standard (oddTile evenTile IsBase)
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.TileStepAssembly
open FLatticePaper.Tiles.JointGlue (pieceVal)

/-! # Condition (C) at the corrected odd standard decomposition: the boundary

After a `3` the odd standard decomposition `tOP` has the short L-corrections `L^+`, `L^-` of the register `w.dropLast` at the places
of two copies of `T(q_1)` (`2, 5` for `W_1` odd, `3, 4` for `W_1` even). Its four full copies take the constants of condition (C) of
the uncorrected odd child (`closedPathOdd_final`, as in the weak step, `odd_constants`), and each L-correction takes the constant of
the copy it replaces minus its own constant on its kept side (`LSidesAgree`, `D.lSides = paperLSides`). With these constants:
* the four mixed pairs of full copies agree at every common point (their common points lie in the marks, item (d));
* each L-correction agrees with its doubled partner and with the mixed copy next to it at a corner of its kept side;
* the two L-corrections have the constant `κ j - κ i` on their overlap, by their cross half-turn about the centre of `T(q_1)`
  (`TileHalfTurnInput.crossEven`), pinned at the corners `0` and `D`; the constants of the full copies enter through the chain
  of corner witnesses `Q^{+,1} → P^+ → Q^{-,1} → Q^{-,2}`.
These are the six interfaces along the boundary of the decomposition in Case 2 of the text, and the interface of the two
L-corrections. Both orientations: `tOP_boundary_of` (`W_1` odd, L-corrections at `2, 5`) and `tOP_boundary_ef` (`W_1` even, at
`3, 4`, chain `Q^{+,2} → P^+ → Q^{-,2} → Q^{-,1}`). -/

namespace FLatticePaper.Tiles.CorrectedStdOdd



/-- The L-entries of the odd standard decomposition after a `3`. -/
theorem tOP_getL (D : JointData) (f : Word → JSlice) (w : Word) (hl : w.dropLast.length < w.length)
    (h3 : w.getLast? = some Digit.three) :
    (W1Odd w = true →
      (tOP D f w)[2]? = some (stdPiece ((f w.dropLast).lEven true false) (p0Off w .q1DPlus) (p0Aff w .q1DPlus)) ∧
      (tOP D f w)[5]? = some (stdPiece ((f w.dropLast).lEven false false) (p0Off w .q1DMinus + vQ1 w) (p0Aff w .q1DMinus))) ∧
    (W1Odd w = false →
      (tOP D f w)[3]? = some (stdPiece ((f w.dropLast).lEven true false) (p0Off w .q1DPlus + vQ1 w) (p0Aff w .q1DPlus)) ∧
      (tOP D f w)[4]? = some (stdPiece ((f w.dropLast).lEven false false) (p0Off w .q1DMinus) (p0Aff w .q1DMinus))) := by
  have e : below f w w.dropLast = f w.dropLast := JointRot.below_of_lt f w _ hl
  refine ⟨fun ho => ⟨?_, ?_⟩, fun ho => ⟨?_, ?_⟩⟩ <;> simp [tOP, tileOddPieces, e, h3, ho]

/-- The constants of condition (C) for the six full copies of the odd standard child (`closedPathOdd_final`), at every word that
is not a base word. -/
theorem odd_constants (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w u1 u2 : Word) (hgood : GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hreg : regsAt w = (some u1, some u2)) :
    ∃ κo : ℕ → ℤ, MarksAgreeOdd w u1 u2 (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κo i) ∧
      DoubledAgreeOdd w u1 u2 (dblOdd w) (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κo i) := by
  have hl1 : u1.length < w.length := JointInduction.regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hl2 : u2.length < w.length := JointInduction.regsAt_lt w u2 (Or.inr (by rw [hreg]))
  have hp : (parentsAt w).odd = fracOdd u1 := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])
  have hq : (parentsAt w).even = fracEven u2 := (WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])
  obtain ⟨hS1, hJ1⟩ := hgood u1 hl1
  obtain ⟨hS2, hJ2⟩ := hgood u2 hl2
  have hdE : (f u2).tEven.dom = evenTile u2 := by rw [(WeakStepAssembly.slice_domains D f u2 hS2).2, hS]; rfl
  have hRP := (WeakStepAssembly.slice_respects D f u1 hS1).1
  have hRQ := (WeakStepAssembly.slice_respects D f u2 hS2).2
  obtain ⟨-, ⟨-, hTE, -⟩, -⟩ := hJ2
  have hsl := TileSlopeZeroPaper.tileSlopeZero_paper D hS hA
  obtain ⟨⟨βo, hzo⟩, -⟩ := hsl f w.length hgood u1 hl1
  obtain ⟨-, ⟨βe, hze⟩⟩ := hsl f w.length hgood u2 hl2
  obtain ⟨αo, β1, hNo, hVo⟩ := TileTranslationStd.stdCorners_odd u1 (f u1).tOdd hRP
  obtain ⟨αe, β2, hNe, hVe⟩ := TileTranslationStd.stdCorners_even u2 (f u2).tEven hRQ
  have hsP : ClosedPathTriOdd.SigmaZero (f u1).tOdd.val (texV1Odd (parentsAt w).odd) := by
    rw [hp]; exact WeakStepAssembly.sigma_of_corners _ _ _ _ _ _ _ hzo hNo hVo
  have hsQ : ClosedPathTriOdd.SigmaZero (f u2).tEven.val (texV1Even (parentsAt w).even) := by
    rw [hq]; exact WeakStepAssembly.sigma_of_corners _ _ _ _ _ _ _ hze hNe hVe
  have hdblO : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + texV1Even (parentsAt w).even ∈ tEvenSet u2 →
      (f u2).tEven.val (x + texV1Even (parentsAt w).even) - (f u2).tEven.val x = k := by
    obtain ⟨k, hk⟩ := WeakStepAssembly.translation_v1 _ _ _ _ hTE
    refine ⟨k, fun x hx hxv => ?_⟩
    rw [hq] at hxv ⊢
    exact hk x (by rw [hdE]; exact hx) (by rw [hdE]; exact hxv)
  obtain ⟨hmO, -⟩ := MixedCompatGeneral.mixedCompatInput D hS hA f w u1 u2 hgood hw hreg
  exact ClosedPathTriOdd.closedPathOdd_final w u1 u2 hp hq (f u1).tOdd.val (f u2).tEven.val
    (f u1).tOdd.dom (f u2).tEven.dom 0 hRP hRQ hsP hsQ hdblO hmO

/-- A full copy of the odd parent as a placed subodometer of the uncorrected odd child. -/
theorem pvO_lt (w : Word) (oP oQ : PartialOdometer) (κ : ℕ → ℤ) (i : ℕ) (hi : i < 2) (x : ℤ × ℤ) :
    pieceVal (stdPiece oP ((oddP w).getD i 0) (affOdd (parentsAt w).odd (parentsAt w).even i)) x + κ i =
      placedOdd w oP.val oQ.val 0 i x + κ i := by
  simp only [pieceVal, stdPiece, placedOdd, if_pos hi, ClosedPathSum.dot2, dotS, Pi.zero_apply, add_zero]

/-- A full copy of the even parent as a placed subodometer of the uncorrected odd child. -/
theorem pvO_ge (w : Word) (oP oQ : PartialOdometer) (κ : ℕ → ℤ) (i : ℕ) (hi : ¬ i < 2) (x : ℤ × ℤ) :
    pieceVal (stdPiece oQ ((oddQ w).getD (i - 2) 0) (affOdd (parentsAt w).odd (parentsAt w).even i)) x + κ i =
      placedOdd w oP.val oQ.val 0 i x + κ i := by
  simp only [pieceVal, stdPiece, placedOdd, if_neg hi, ClosedPathSum.dot2, dotS, Pi.zero_apply, add_zero]

/-- An L-entry at a point of its kept side, where it is the copy it replaces plus its constant. -/
theorem pvO_L (w : Word) (oP oQ L : PartialOdometer) (κ : ℕ → ℤ) (i : ℕ) (hi : ¬ i < 2) (c : ℤ) (x : ℤ × ℤ)
    (h : L.val (x - (oddQ w).getD (i - 2) 0) = oQ.val (x - (oddQ w).getD (i - 2) 0) + c) :
    pieceVal (stdPiece L ((oddQ w).getD (i - 2) 0) (affOdd (parentsAt w).odd (parentsAt w).even i)) x + (κ i - c) =
      placedOdd w oP.val oQ.val 0 i x + κ i := by
  simp only [pieceVal, stdPiece, placedOdd, if_neg hi, ClosedPathSum.dot2, dotS, Pi.zero_apply, add_zero] at h ⊢
  rw [h]; ring


/-- Common points of a copy of the odd parent and a copy of the even parent lie in both marks (item (d)). -/
theorem marksO_mix (w u1 u2 : Word) (hb : ¬ IsBase w) (hT1 : (Standard.stateAt w).tOdd = oddTile u1)
    (hT2 : (Standard.stateAt w).tEven = evenTile u2) (i j : ℕ) (hi : i < 2) (hj2 : 2 ≤ j) (hj6 : j < 6) (x : ℤ × ℤ)
    (hx : x - (oddP w).getD i 0 ∈ oddTile u1) (hx' : x - (oddQ w).getD (j - 2) 0 ∈ evenTile u2) :
    x ∈ mOdd w u1 u2 i ∧ x ∈ mOdd w u1 u2 j := by
  have hlP : (oddP w).length = 2 := by unfold oddP MixedPieces.pOffsetsOdd; split_ifs <;> rfl
  have hlQ : (oddQ w).length = 4 := by unfold oddQ MixedPieces.qOffsetsOdd; split_ifs <;> rfl
  have hma : (oddP w).getD i 0 ∈ oddP w := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hmb : (oddQ w).getD (j - 2) 0 ∈ oddQ w := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  obtain ⟨m1, m2⟩ := MixedFromCells.mixedOdd_all w hb u1 u2 hT1 hT2 _ hma _ hmb x
    (StdPairCompatPaper.mem_shift_tile hx) (StdPairCompatPaper.mem_shift_tile hx')
  exact ⟨by simp only [mOdd, pieceSet, hlP, if_pos hi]; exact m1,
    by simp only [mOdd, pieceSet, hlP, if_neg (show ¬ j < 2 by omega)]; exact m2⟩

set_option maxHeartbeats 400000 in
/-- **The boundary of the corrected odd standard decomposition, and the overlap of its two L-corrections, `W_1` odd.** -/
theorem tOP_boundary_of (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hlS : D.lSides = paperLSides) (f : Word → JSlice) (w : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (h3 : w.getLast? = some Digit.three) (hph : phase w = 1) :
    ∃ κ : ℕ → ℤ, CorrectedWalkZero.AgreeAll (tOP D f w) κ 0 3 ∧ CorrectedWalkZero.AgreeAll (tOP D f w) κ 0 4 ∧
      CorrectedWalkZero.AgreeAll (tOP D f w) κ 1 3 ∧ CorrectedWalkZero.AgreeAll (tOP D f w) κ 1 4 ∧
      CorrectedWalkZero.EdgeWitness (tOP D f w) κ 2 0 ∧ CorrectedWalkZero.EdgeWitness (tOP D f w) κ 2 3 ∧
      CorrectedWalkZero.EdgeWitness (tOP D f w) κ 5 1 ∧ CorrectedWalkZero.EdgeWitness (tOP D f w) κ 5 4 ∧
      ∀ off, CorrectedWalkZero.OffMatch (tOP D f w) off → ∀ (hi : 2 < (tOP D f w).length) (hj : 5 < (tOP D f w).length),
        (∃ x ∈ ((tOP D f w).get ⟨2, hi⟩).placed, x ∈ ((tOP D f w).get ⟨5, hj⟩).placed ∧
          x ∉ ((tOP D f w).get ⟨2, hi⟩).exc ∧ x ∉ ((tOP D f w).get ⟨5, hj⟩).exc) → off ⟨2, hi⟩ ⟨5, hj⟩ = κ 5 - κ 2 := by
  obtain ⟨u1, u2, hr, hl1, hl2, hdO, hdE, hU1, hU2, hT1, hT2⟩ := StdPairCompatPaper.regs_data D hS f w hG hb
  have hw : w = w.dropLast ++ [Digit.three] := (List.dropLast_append_getLast? (l := w) (a := Digit.three) h3).symm
  have hu2 : u2 = w.dropLast := by
    have e := ConnectedAltL.regs_pre_snd w.dropLast Digit.three (by decide)
    rw [← hw, hr] at e
    exact Option.some.inj e
  subst hu2
  have hWo : W1Odd w = true := StdPairCompatPaper.w1Odd_of hph
  obtain ⟨g0, g1, hgo, -⟩ := StdPairCompatPaper.tOP_get D f w u1 w.dropLast hr hl1 hl2 h3
  obtain ⟨g3, g4⟩ := hgo hWo
  obtain ⟨hLo, -⟩ := tOP_getL D f w hl2 h3
  obtain ⟨g2, g5⟩ := hLo hWo
  obtain ⟨o0, o1, o2, o3, o4, o5⟩ := StdPairCompatPaper.odd_offs w
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := StdPairCompatPaper.odd_affs w
  rw [← o0, ← f0] at g0; rw [← o1, ← f1] at g1; rw [← o2, ← f2] at g2; rw [← o3, ← f3] at g3
  rw [← o4, ← f4] at g4; rw [← o5, ← f5] at g5
  have hp := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents w).2 w.dropLast (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hG u1 hl1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hG w.dropLast hl2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdQ] at hhQ
  obtain ⟨κo, hMa, hDa⟩ := odd_constants D hS hA f w u1 w.dropLast hG hb hr
  -- the kept sides of the two short L-corrections
  have hdef : EvenLDefined w.dropLast := JointRot.evenLDefined_of_mem _ (by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    exact hb (Or.inr (Or.inl fun d hd => by
      rw [hw] at hd; simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl; exacts [hc d hd, rfl])))
  have hJl := (hG w.dropLast hl2).1.2.2.2
  obtain ⟨-, c2, hc2⟩ := (hJl.2 true false hdef).2
  obtain ⟨-, c5, hc5⟩ := (hJl.2 false false hdef).2
  rw [hlS] at hc2 hc5
  have k2 := hc2 .hPlus (by simp [paperLSides])
  have k5 := hc5 .hMinus (by simp [paperLSides])
  have esc := ConnectedAltL.even_side_corners w.dropLast
  have esm := AltLSides.even_side_more w.dropLast
  rw [← hw] at esc esm
  simp only [vQ1, vQ2] at esc esm
  -- the offsets, `W_1` odd
  have hP := oddP_of w hph
  have hQ := oddQ_of w hph
  have cmE := ClosedPathContacts.corner_marks_even w.dropLast
  have cmO := ClosedPathContacts.corner_marks_odd u1
  rw [← hq] at cmE
  rw [← hp] at cmO
  have hlP : (oddP w).length = 2 := by rw [hP]; rfl
  have hlQ : (oddQ w).length = 4 := by rw [hQ]; rfl
  set F := fun i z => placedOdd w (f u1).tOdd.val (f w.dropLast).tEven.val 0 i z + κo i with hF
  let κ : ℕ → ℤ := fun i => if i = 2 then κo 2 - c2 else if i = 5 then κo 5 - c5 else κo i
  have κ0 : κ 0 = κo 0 := rfl
  have κ1 : κ 1 = κo 1 := rfl
  have κ2 : κ 2 = κo 2 - c2 := rfl
  have κ3 : κ 3 = κo 3 := rfl
  have κ4 : κ 4 = κo 4 := rfl
  have κ5 : κ 5 = κo 5 - c5 := rfl
  have pt : ∀ (S : Set (ℤ × ℤ)) (a z : ℤ × ℤ), z - a ∈ S → z ∈ SiteInduction.shiftS S a :=
    fun S a z h => (AltPiecesAgree.mem_shiftS_iff S a z).2 h
  have mixF : ∀ i j, i < 2 → 2 ≤ j → j < 6 → ∀ x, x - (oddP w).getD i 0 ∈ oddTile u1 →
      x - (oddQ w).getD (j - 2) 0 ∈ evenTile w.dropLast → F i x = F j x := fun i j hi hj2 hj6 x hx hx' => by
    obtain ⟨m1, m2⟩ := marksO_mix w u1 w.dropLast hb hT1 hT2 i j hi hj2 hj6 x hx hx'
    exact hMa i j (by rw [hlP, hlQ]; omega) (by rw [hlP, hlQ]; omega)
      (by simp only [pieceFlag, hlP]; intro h; simp at h; omega) x m1 m2
  have std_mix : ∀ i j, i < 2 → 2 ≤ j → j < 6 → κ i = κo i → κ j = κo j →
      (tOP D f w)[i]? = some (stdPiece (f u1).tOdd ((oddP w).getD i 0) (affOdd (parentsAt w).odd (parentsAt w).even i)) →
      (tOP D f w)[j]? = some (stdPiece (f w.dropLast).tEven ((oddQ w).getD (j - 2) 0)
        (affOdd (parentsAt w).odd (parentsAt w).even j)) →
      CorrectedWalkZero.AgreeAll (tOP D f w) κ i j := fun i j hi hj2 hj6 ei ej gi gj =>
    CorrectedAltEven.agreeAll_of gi gj F (fun x _ => by rw [ei]; exact pvO_lt w _ (f w.dropLast).tEven κo i hi x)
      (fun x _ => by rw [ej]; exact pvO_ge w (f u1).tOdd _ κo j (by omega) x)
      (fun x hx hx' => mixF i j hi hj2 hj6 x (by rw [← hdO]; exact JointRot.mem_placed.1 hx)
        (by rw [← hdE]; exact JointRot.mem_placed.1 hx'))
  -- corner memberships
  have dQ0 : (0 : ℤ × ℤ) ∈ evenTile w.dropLast := hdQ ▸ hcQ.1.1
  have dQ1 : ((1 : ℤ), (0 : ℤ)) ∈ evenTile w.dropLast := hdQ ▸ hcQ.2.1.1
  have dQX : texV1Even (parentsAt w).even ∈ evenTile w.dropLast := hdQ ▸ hcQ.2.2.2.1.1
  have dQD : texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) ∈ evenTile w.dropLast :=
    hdQ ▸ hcQ.2.2.2.2.2.2.1.1
  have dPX : texV1Odd (parentsAt w).odd ∈ oddTile u1 := hdP ▸ hcP.2.2.2.1.1
  have dPY1 : texV2 (parentsAt w).odd + ((1 : ℤ), (0 : ℤ)) ∈ oddTile u1 := hdP ▸ hcP.2.2.2.2.1.1
  have dPY : texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) ∈ oddTile u1 := hdP ▸ hcP.2.2.2.2.2.1.1
  refine ⟨κ, std_mix 0 3 (by norm_num) (by norm_num) (by norm_num) κ0 κ3 g0 g3,
    std_mix 0 4 (by norm_num) (by norm_num) (by norm_num) κ0 κ4 g0 g4,
    std_mix 1 3 (by norm_num) (by norm_num) (by norm_num) κ1 κ3 g1 g3,
    std_mix 1 4 (by norm_num) (by norm_num) (by norm_num) κ1 κ4 g1 g4, ?_, ?_, ?_, ?_, ?_⟩
  · -- `(2, 0)`: the corner `0` of `L^+`, the corner `X` of `P^+`
    set x := (oddQ w).getD (2 - 2) 0 with hx
    have e2 : x - (oddQ w).getD (2 - 2) 0 = 0 := sub_self _
    have e0 : x - (oddP w).getD 0 0 = texV1Odd (parentsAt w).odd := by
      rw [hx]; simp only [hP, hQ, List.getD_cons_zero, Nat.sub_self, sub_zero]
    have k := k2 _ esc.1
    refine CorrectedAltEven.witness_of g2 g0 F x (by rw [e2]; exact k.1) (by rw [e0, hdO]; exact dPX) ?_ ?_ ?_
    · rw [κ2]; exact pvO_L w (f u1).tOdd _ _ κo 2 (by norm_num) c2 x (by rw [e2]; exact k.2.2)
    · rw [κ0]; exact pvO_lt w _ (f w.dropLast).tEven κo 0 (by norm_num) x
    · exact (mixF 0 2 (by norm_num) le_rfl (by norm_num) x (by rw [e0]; exact dPX) (by rw [e2]; exact dQ0)).symm
  · -- `(2, 3)`: the corner `X` of `L^+`, the corner `0` of its doubled partner
    set x := (oddQ w).getD (2 - 2) 0 + texV1Even (parentsAt w).even with hx
    have e2 : x - (oddQ w).getD (2 - 2) 0 = texV1Even (parentsAt w).even := by rw [hx]; abel
    have e3 : x - (oddQ w).getD (3 - 2) 0 = 0 := by
      rw [hx]; simp only [hQ, List.getD_cons_zero, List.getD_cons_succ, Nat.sub_self, show 3 - 2 = 1 from rfl]; abel
    have k := k2 _ esc.2.1
    refine CorrectedAltEven.witness_of g2 g3 F x (by rw [e2]; exact k.1) (by rw [e3, hdE]; exact dQ0) ?_ ?_ ?_
    · rw [κ2]; exact pvO_L w (f u1).tOdd _ _ κo 2 (by norm_num) c2 x (by rw [e2]; exact k.2.2)
    · rw [κ3]; exact pvO_ge w (f u1).tOdd _ κo 3 (by norm_num) x
    · exact hDa 2 3 (by rw [hlP, hlQ]; omega) (by rw [hlP, hlQ]; omega) (by norm_num) (by simp [pieceFlag, hlP])
        ⟨rfl, Or.inl hlP.symm⟩ x
        (by simp only [pieceSet, hlP, if_neg (show ¬ 2 < 2 by norm_num)]; exact pt _ _ _ (by rw [e2]; exact dQX))
        (by simp only [pieceSet, hlP, if_neg (show ¬ 3 < 2 by norm_num)]; exact pt _ _ _ (by rw [e3]; exact dQ0))
  · -- `(5, 1)`: the corner `D` of `L^-`, the corner `Y + 1 - i` of `P^-`
    set x := (oddQ w).getD (5 - 2) 0 + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) with hx
    have e5 : x - (oddQ w).getD (5 - 2) 0 = texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hx]; abel
    have e1 : x - (oddP w).getD 1 0 = texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hx]; simp only [hP, hQ, List.getD_cons_zero, List.getD_cons_succ, show 5 - 2 = 3 from rfl]; abel
    have k := k5 _ esm.2.2.2.2.2
    refine CorrectedAltEven.witness_of g5 g1 F x (by rw [e5]; exact k.1) (by rw [e1, hdO]; exact dPY) ?_ ?_ ?_
    · rw [κ5]; exact pvO_L w (f u1).tOdd _ _ κo 5 (by norm_num) c5 x (by rw [e5]; exact k.2.2)
    · rw [κ1]; exact pvO_lt w _ (f w.dropLast).tEven κo 1 (by norm_num) x
    · exact (mixF 1 5 (by norm_num) (by norm_num) (by norm_num) x (by rw [e1]; exact dPY) (by rw [e5]; exact dQD)).symm
  · -- `(5, 4)`: the corner `Y + 1 - i` of `L^-`, the corner `D` of its doubled partner
    set x := (oddQ w).getD (5 - 2) 0 + (texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) with hx
    have e5 : x - (oddQ w).getD (5 - 2) 0 = texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by rw [hx]; abel
    have e4 : x - (oddQ w).getD (4 - 2) 0 = texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hx]; simp only [hQ, List.getD_cons_zero, List.getD_cons_succ, show 5 - 2 = 3 from rfl, show 4 - 2 = 2 from rfl]; abel
    have dQY : texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) ∈ evenTile w.dropLast := hdQ ▸ hcQ.2.2.2.2.2.1.1
    have k := k5 _ esc.2.2
    refine CorrectedAltEven.witness_of g5 g4 F x (by rw [e5]; exact k.1) (by rw [e4, hdE]; exact dQD) ?_ ?_ ?_
    · rw [κ5]; exact pvO_L w (f u1).tOdd _ _ κo 5 (by norm_num) c5 x (by rw [e5]; exact k.2.2)
    · rw [κ4]; exact pvO_ge w (f u1).tOdd _ κo 4 (by norm_num) x
    · exact (hDa 4 5 (by rw [hlP, hlQ]; omega) (by rw [hlP, hlQ]; omega) (by norm_num) (by simp [pieceFlag, hlP])
        ⟨rfl, Or.inr (by rw [hlP])⟩ x
        (by simp only [pieceSet, hlP, if_neg (show ¬ 4 < 2 by norm_num)]; exact pt _ _ _ (by rw [e4]; exact dQD))
        (by simp only [pieceSet, hlP, if_neg (show ¬ 5 < 2 by norm_num)]; exact pt _ _ _ (by rw [e5]; exact dQY))).symm
  · -- `(2, 5)`: the cross half-turn of `L^+` and `L^-`, pinned at the corners `0` and `D` of their kept sides; the
    -- constants of `P^+`, `Q^{-,1}`, `Q^{-,2}` relative to `Q^{+,1}` from the corners `X`, `Y + 1`, `X` of the full copies
    intro off hoff hi hj hx
    have hwl : w.dropLast.length + 1 = w.length := by
      have : w ≠ [] := by rintro rfl; simp at h3
      rw [List.length_dropLast]; have := List.length_pos_of_ne_nil this; omega
    have hG' : GoodBelow D f (w.dropLast.length + 1) := hwl ▸ hG
    have hspec := FLatticePaper.Tiles.TileHalfTurnLRot.specialLHalfTurn_of_rot D
    obtain ⟨K, hK⟩ := FLatticePaper.Tiles.TileHalfTurnInput.crossEven D hS hA hspec f w.dropLast hG' hdef true false
    obtain ⟨K', hK'⟩ := FLatticePaper.Tiles.TileHalfTurnInput.crossEven D hS hA hspec f w.dropLast hG' hdef false false
    have hC : TileHalfTurnStd.cEven ((parentsAt w.dropLast).current .even) =
        texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hq]; rfl
    have hcur : (parentsAt w.dropLast).current .even = (parentsAt w).even := by rw [hq]; rfl
    have k00 := k2 _ esc.1
    have k5D := k5 _ esm.2.2.2.2.2
    have pK := (hK _ k00.1).2
    have pK' := (hK' _ k5D.1).2
    have e00 : ∀ v : ℤ × ℤ, v - ((0 : ℤ), (0 : ℤ)) = v := fun v => by ext <;> simp
    have eDD : ∀ v : ℤ × ℤ, v - v = ((0 : ℤ), (0 : ℤ)) := fun v => by ext <;> simp
    simp only [Bool.not_true, Bool.not_false, e00, hC, eDD] at pK pK'
    rw [k5D.2.2, k00.2.2] at pK
    rw [k00.2.2, k5D.2.2] at pK'
    have hT0 := (hhQ _ (show (0 : ℤ × ℤ) ∈ tEvenSet w.dropLast from dQ0)).2
    simp only [sub_zero] at hT0
    -- the chain `Q^{+,1} → P^+ → Q^{-,1} → Q^{-,2}` of the full copies
    have r20 := mixF 0 2 (by norm_num) le_rfl (by norm_num) ((oddQ w).getD 0 0)
      (by simp only [hP, hQ, List.getD_cons_zero, sub_zero]; exact dPX) (by rw [sub_self]; exact dQ0)
    have r04 := mixF 0 4 (by norm_num) (by norm_num) (by norm_num) (texV2 (parentsAt w).odd + ((1 : ℤ), (0 : ℤ)))
      (by simp only [hP, List.getD_cons_zero, sub_zero]; exact dPY1)
      (by simp only [hQ, List.getD_cons_zero, List.getD_cons_succ, show 4 - 2 = 2 from rfl, add_sub_cancel_left]; exact dQ1)
    have r45 := hDa 4 5 (by rw [hlP, hlQ]; omega) (by rw [hlP, hlQ]; omega) (by norm_num) (by simp [pieceFlag, hlP])
      ⟨rfl, Or.inr (by rw [hlP])⟩ ((oddQ w).getD 2 0 + texV1Even (parentsAt w).even)
      (by simp only [pieceSet, hlP, if_neg (show ¬ 4 < 2 by norm_num)]
          exact pt _ _ _ (by simp only [show 4 - 2 = 2 from rfl, add_sub_cancel_left]; exact dQX))
      (by simp only [pieceSet, hlP, if_neg (show ¬ 5 < 2 by norm_num)]
          exact pt _ _ _ (by simp only [hQ, List.getD_cons_zero, List.getD_cons_succ, show 5 - 2 = 3 from rfl]
                             rw [show texV2 (parentsAt w).odd + texV1Even (parentsAt w).even - (texV2 (parentsAt w).odd +
                               texV1Even (parentsAt w).even) = 0 from sub_self _]; exact dQ0))
    obtain ⟨-, -, -, vPX, vPY1, -, -, -⟩ := AltParentConstants.corner_raw (f u1).tOdd βP _ _ _ hcP
    obtain ⟨vQ0, vQ1', -, vQX, -, -, vQD, -⟩ := AltParentConstants.corner_raw (f w.dropLast).tEven βQ _ _ _ hcQ
    have hB4 := AltSixEven.h0_even (texV2 (parentsAt w).odd) (by
      have hpar := (parentsAt_valid w).odd_parity
      simp only [texV2]; omega)
    have a0 : affOdd (parentsAt w).odd (parentsAt w).even 0 = 0 := by simp [affOdd]
    have a2 : affOdd (parentsAt w).odd (parentsAt w).even 2 = 0 := by simp [affOdd]
    have a4 : affOdd (parentsAt w).odd (parentsAt w).even 4 = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
      simp [affOdd]
    have a5 : affOdd (parentsAt w).odd (parentsAt w).even 5 = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
      simp [affOdd]
    refine CorrectedWalkZero.off_of_halfTurn hoff (i := 2) (j := 5) g2 g5 hK hK' ?_ hi hj hx
    rw [hC, κ2, κ5, a2, a5]
    simp only [hF, placedOdd, if_pos (show (0 : ℕ) < 2 by norm_num), if_neg (show ¬ (2 : ℕ) < 2 by norm_num),
      if_neg (show ¬ (4 : ℕ) < 2 by norm_num), if_neg (show ¬ (5 : ℕ) < 2 by norm_num), Pi.zero_apply, add_zero,
      show (2 : ℕ) - 2 = 0 from rfl, show (4 : ℕ) - 2 = 2 from rfl, show (5 : ℕ) - 2 = 3 from rfl] at r20 r04 r45
    simp only [hP, hQ, List.getD_cons_zero, List.getD_cons_succ, sub_zero, sub_self, add_sub_cancel_left] at r20 r04 r45 ⊢
    rw [vPX, vQ0, a0, a2] at r20
    rw [vPY1, vQ1', a0, a4] at r04
    rw [vQX, vQ0, a4, a5] at r45
    simp only [ClosedPathSum.dot2, TileHalfTurnStd.aF, offsetA, dotS, texV1Odd, texV1Even, texV2, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.smul_mk,
      smul_eq_mul, Prod.mk_zero_zero, hcur] at r20 r04 r45 pK pK' hT0 hB4 ⊢
    linear_combination (-4 : ℤ) * r45 + (-4 : ℤ) * r04 + 4 * r20 - pK + pK' + 2 * hT0 - hB4

set_option maxHeartbeats 400000 in
/-- **The boundary of the corrected odd standard decomposition, and the overlap of its two L-corrections, `W_1` even.** -/
theorem tOP_boundary_ef (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hlS : D.lSides = paperLSides) (f : Word → JSlice) (w : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (h3 : w.getLast? = some Digit.three) (hph : phase w ≠ 1) :
    ∃ κ : ℕ → ℤ, CorrectedWalkZero.AgreeAll (tOP D f w) κ 0 2 ∧ CorrectedWalkZero.AgreeAll (tOP D f w) κ 0 5 ∧
      CorrectedWalkZero.AgreeAll (tOP D f w) κ 1 2 ∧ CorrectedWalkZero.AgreeAll (tOP D f w) κ 1 5 ∧
      CorrectedWalkZero.EdgeWitness (tOP D f w) κ 3 0 ∧ CorrectedWalkZero.EdgeWitness (tOP D f w) κ 3 2 ∧
      CorrectedWalkZero.EdgeWitness (tOP D f w) κ 4 1 ∧ CorrectedWalkZero.EdgeWitness (tOP D f w) κ 4 5 ∧
      ∀ off, CorrectedWalkZero.OffMatch (tOP D f w) off → ∀ (hi : 3 < (tOP D f w).length) (hj : 4 < (tOP D f w).length),
        (∃ x ∈ ((tOP D f w).get ⟨3, hi⟩).placed, x ∈ ((tOP D f w).get ⟨4, hj⟩).placed ∧
          x ∉ ((tOP D f w).get ⟨3, hi⟩).exc ∧ x ∉ ((tOP D f w).get ⟨4, hj⟩).exc) → off ⟨3, hi⟩ ⟨4, hj⟩ = κ 4 - κ 3 := by
  obtain ⟨u1, u2, hr, hl1, hl2, hdO, hdE, hU1, hU2, hT1, hT2⟩ := StdPairCompatPaper.regs_data D hS f w hG hb
  have hw : w = w.dropLast ++ [Digit.three] := (List.dropLast_append_getLast? (l := w) (a := Digit.three) h3).symm
  have hu2 : u2 = w.dropLast := by
    have e := ConnectedAltL.regs_pre_snd w.dropLast Digit.three (by decide)
    rw [← hw, hr] at e
    exact Option.some.inj e
  subst hu2
  have hWo : W1Odd w = false := StdPairCompatPaper.w1Odd_ef hph
  obtain ⟨g0, g1, -, hge⟩ := StdPairCompatPaper.tOP_get D f w u1 w.dropLast hr hl1 hl2 h3
  obtain ⟨g2, g5⟩ := hge hWo
  obtain ⟨-, hLe⟩ := tOP_getL D f w hl2 h3
  obtain ⟨g3, g4⟩ := hLe hWo
  obtain ⟨o0, o1, o2, o3, o4, o5⟩ := StdPairCompatPaper.odd_offs w
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := StdPairCompatPaper.odd_affs w
  rw [← o0, ← f0] at g0; rw [← o1, ← f1] at g1; rw [← o2, ← f2] at g2; rw [← o3, ← f3] at g3
  rw [← o4, ← f4] at g4; rw [← o5, ← f5] at g5
  have hp := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents w).2 w.dropLast (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hG u1 hl1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hG w.dropLast hl2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdQ] at hhQ
  obtain ⟨κo, hMa, hDa⟩ := odd_constants D hS hA f w u1 w.dropLast hG hb hr
  -- the kept sides of the two short L-corrections
  have hdef : EvenLDefined w.dropLast := JointRot.evenLDefined_of_mem _ (by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    exact hb (Or.inr (Or.inl fun d hd => by
      rw [hw] at hd; simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl; exacts [hc d hd, rfl])))
  have hJl := (hG w.dropLast hl2).1.2.2.2
  obtain ⟨-, c3, hc3⟩ := (hJl.2 true false hdef).2
  obtain ⟨-, c4, hc4⟩ := (hJl.2 false false hdef).2
  rw [hlS] at hc3 hc4
  have k3 := hc3 .hPlus (by simp [paperLSides])
  have k4 := hc4 .hMinus (by simp [paperLSides])
  have esc := ConnectedAltL.even_side_corners w.dropLast
  have esm := AltLSides.even_side_more w.dropLast
  rw [← hw] at esc esm
  simp only [vQ1, vQ2] at esc esm
  -- the offsets, `W_1` odd
  have hP := oddP_ef w hph
  have hQ := oddQ_ef w hph
  have cmE := ClosedPathContacts.corner_marks_even w.dropLast
  have cmO := ClosedPathContacts.corner_marks_odd u1
  rw [← hq] at cmE
  rw [← hp] at cmO
  have hlP : (oddP w).length = 2 := by rw [hP]; rfl
  have hlQ : (oddQ w).length = 4 := by rw [hQ]; rfl
  set F := fun i z => placedOdd w (f u1).tOdd.val (f w.dropLast).tEven.val 0 i z + κo i with hF
  let κ : ℕ → ℤ := fun i => if i = 3 then κo 3 - c3 else if i = 4 then κo 4 - c4 else κo i
  have κ0 : κ 0 = κo 0 := rfl
  have κ1 : κ 1 = κo 1 := rfl
  have κ2 : κ 2 = κo 2 := rfl
  have κ3 : κ 3 = κo 3 - c3 := rfl
  have κ4 : κ 4 = κo 4 - c4 := rfl
  have κ5 : κ 5 = κo 5 := rfl
  have pt : ∀ (S : Set (ℤ × ℤ)) (a z : ℤ × ℤ), z - a ∈ S → z ∈ SiteInduction.shiftS S a :=
    fun S a z h => (AltPiecesAgree.mem_shiftS_iff S a z).2 h
  have mixF : ∀ i j, i < 2 → 2 ≤ j → j < 6 → ∀ x, x - (oddP w).getD i 0 ∈ oddTile u1 →
      x - (oddQ w).getD (j - 2) 0 ∈ evenTile w.dropLast → F i x = F j x := fun i j hi hj2 hj6 x hx hx' => by
    obtain ⟨m1, m2⟩ := marksO_mix w u1 w.dropLast hb hT1 hT2 i j hi hj2 hj6 x hx hx'
    exact hMa i j (by rw [hlP, hlQ]; omega) (by rw [hlP, hlQ]; omega)
      (by simp only [pieceFlag, hlP]; intro h; simp at h; omega) x m1 m2
  have std_mix : ∀ i j, i < 2 → 2 ≤ j → j < 6 → κ i = κo i → κ j = κo j →
      (tOP D f w)[i]? = some (stdPiece (f u1).tOdd ((oddP w).getD i 0) (affOdd (parentsAt w).odd (parentsAt w).even i)) →
      (tOP D f w)[j]? = some (stdPiece (f w.dropLast).tEven ((oddQ w).getD (j - 2) 0)
        (affOdd (parentsAt w).odd (parentsAt w).even j)) →
      CorrectedWalkZero.AgreeAll (tOP D f w) κ i j := fun i j hi hj2 hj6 ei ej gi gj =>
    CorrectedAltEven.agreeAll_of gi gj F (fun x _ => by rw [ei]; exact pvO_lt w _ (f w.dropLast).tEven κo i hi x)
      (fun x _ => by rw [ej]; exact pvO_ge w (f u1).tOdd _ κo j (by omega) x)
      (fun x hx hx' => mixF i j hi hj2 hj6 x (by rw [← hdO]; exact JointRot.mem_placed.1 hx)
        (by rw [← hdE]; exact JointRot.mem_placed.1 hx'))
  -- corner memberships
  have dQ0 : (0 : ℤ × ℤ) ∈ evenTile w.dropLast := hdQ ▸ hcQ.1.1
  have dQ1 : ((1 : ℤ), (0 : ℤ)) ∈ evenTile w.dropLast := hdQ ▸ hcQ.2.1.1
  have dQX : texV1Even (parentsAt w).even ∈ evenTile w.dropLast := hdQ ▸ hcQ.2.2.2.1.1
  have dQD : texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) ∈ evenTile w.dropLast :=
    hdQ ▸ hcQ.2.2.2.2.2.2.1.1
  have dPX : texV1Odd (parentsAt w).odd ∈ oddTile u1 := hdP ▸ hcP.2.2.2.1.1
  have dPY1 : texV2 (parentsAt w).odd + ((1 : ℤ), (0 : ℤ)) ∈ oddTile u1 := hdP ▸ hcP.2.2.2.2.1.1
  have dPY : texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) ∈ oddTile u1 := hdP ▸ hcP.2.2.2.2.2.1.1
  have dPD : texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) ∈ oddTile u1 :=
    hdP ▸ hcP.2.2.2.2.2.2.1.1
  have dPD1 : texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈ oddTile u1 :=
    hdP ▸ hcP.2.2.2.2.2.2.2.1
  have dP0 : (0 : ℤ × ℤ) ∈ oddTile u1 := hdP ▸ hcP.1.1
  have dQXi : texV1Even (parentsAt w).even - ((0 : ℤ), (1 : ℤ)) ∈ evenTile w.dropLast := hdQ ▸ hcQ.2.2.1.1
  have dQY : texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) ∈ evenTile w.dropLast := hdQ ▸ hcQ.2.2.2.2.2.1.1
  refine ⟨κ, std_mix 0 2 (by norm_num) le_rfl (by norm_num) κ0 κ2 g0 g2,
    std_mix 0 5 (by norm_num) (by norm_num) (by norm_num) κ0 κ5 g0 g5,
    std_mix 1 2 (by norm_num) le_rfl (by norm_num) κ1 κ2 g1 g2,
    std_mix 1 5 (by norm_num) (by norm_num) (by norm_num) κ1 κ5 g1 g5, ?_, ?_, ?_, ?_, ?_⟩
  · -- `(3, 0)`: the corner `X` of `L^+`, the corner `0` of `P^+`
    set x := (oddQ w).getD (3 - 2) 0 + texV1Even (parentsAt w).even with hx
    have e3 : x - (oddQ w).getD (3 - 2) 0 = texV1Even (parentsAt w).even := by rw [hx]; abel
    have e0 : x - (oddP w).getD 0 0 = 0 := by
      rw [hx]; simp only [hP, hQ, List.getD_cons_zero, List.getD_cons_succ, show 3 - 2 = 1 from rfl]; abel
    have k := k3 _ esc.2.1
    refine CorrectedAltEven.witness_of g3 g0 F x (by rw [e3]; exact k.1) (by rw [e0, hdO]; exact dP0) ?_ ?_ ?_
    · rw [κ3]; exact pvO_L w (f u1).tOdd _ _ κo 3 (by norm_num) c3 x (by rw [e3]; exact k.2.2)
    · rw [κ0]; exact pvO_lt w _ (f w.dropLast).tEven κo 0 (by norm_num) x
    · exact (mixF 0 3 (by norm_num) (by norm_num) (by norm_num) x (by rw [e0]; exact dP0) (by rw [e3]; exact dQX)).symm
  · -- `(3, 2)`: the corner `0` of `L^+`, the corner `X` of its doubled partner
    set x := (oddQ w).getD (3 - 2) 0 with hx
    have e3 : x - (oddQ w).getD (3 - 2) 0 = 0 := sub_self _
    have e2 : x - (oddQ w).getD (2 - 2) 0 = texV1Even (parentsAt w).even := by
      rw [hx]; simp only [hQ, List.getD_cons_zero, List.getD_cons_succ, show 3 - 2 = 1 from rfl, Nat.sub_self, sub_zero]
    have k := k3 _ esc.1
    refine CorrectedAltEven.witness_of g3 g2 F x (by rw [e3]; exact k.1) (by rw [e2, hdE]; exact dQX) ?_ ?_ ?_
    · rw [κ3]; exact pvO_L w (f u1).tOdd _ _ κo 3 (by norm_num) c3 x (by rw [e3]; exact k.2.2)
    · rw [κ2]; exact pvO_ge w (f u1).tOdd _ κo 2 (by norm_num) x
    · exact (hDa 2 3 (by rw [hlP, hlQ]; omega) (by rw [hlP, hlQ]; omega) (by norm_num) (by simp [pieceFlag, hlP])
        ⟨rfl, Or.inl hlP.symm⟩ x
        (by simp only [pieceSet, hlP, if_neg (show ¬ 2 < 2 by norm_num)]; exact pt _ _ _ (by rw [e2]; exact dQX))
        (by simp only [pieceSet, hlP, if_neg (show ¬ 3 < 2 by norm_num)]; exact pt _ _ _ (by rw [e3]; exact dQ0))).symm
  · -- `(4, 1)`: the corner `Y + 1 - i` of `L^-`, the corner `D` of `P^-`
    set x := (oddQ w).getD (4 - 2) 0 + (texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) with hx
    have e4 : x - (oddQ w).getD (4 - 2) 0 = texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by rw [hx]; abel
    have e1 : x - (oddP w).getD 1 0 = texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hx]; simp only [hP, hQ, List.getD_cons_zero, List.getD_cons_succ, show 4 - 2 = 2 from rfl]; abel
    have k := k4 _ esc.2.2
    refine CorrectedAltEven.witness_of g4 g1 F x (by rw [e4]; exact k.1) (by rw [e1, hdO]; exact dPD) ?_ ?_ ?_
    · rw [κ4]; exact pvO_L w (f u1).tOdd _ _ κo 4 (by norm_num) c4 x (by rw [e4]; exact k.2.2)
    · rw [κ1]; exact pvO_lt w _ (f w.dropLast).tEven κo 1 (by norm_num) x
    · exact (mixF 1 4 (by norm_num) (by norm_num) (by norm_num) x (by rw [e1]; exact dPD) (by rw [e4]; exact dQY)).symm
  · -- `(4, 5)`: the corner `D` of `L^-`, the corner `Y + 1 - i` of its doubled partner
    set x := (oddQ w).getD (4 - 2) 0 + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) with hx
    have e4 : x - (oddQ w).getD (4 - 2) 0 = texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hx]; abel
    have e5 : x - (oddQ w).getD (5 - 2) 0 = texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hx]; simp only [hQ, List.getD_cons_zero, List.getD_cons_succ, show 4 - 2 = 2 from rfl, show 5 - 2 = 3 from rfl]; abel
    have k := k4 _ esm.2.2.2.2.2
    refine CorrectedAltEven.witness_of g4 g5 F x (by rw [e4]; exact k.1) (by rw [e5, hdE]; exact dQY) ?_ ?_ ?_
    · rw [κ4]; exact pvO_L w (f u1).tOdd _ _ κo 4 (by norm_num) c4 x (by rw [e4]; exact k.2.2)
    · rw [κ5]; exact pvO_ge w (f u1).tOdd _ κo 5 (by norm_num) x
    · exact hDa 4 5 (by rw [hlP, hlQ]; omega) (by rw [hlP, hlQ]; omega) (by norm_num) (by simp [pieceFlag, hlP])
        ⟨rfl, Or.inr (by rw [hlP])⟩ x
        (by simp only [pieceSet, hlP, if_neg (show ¬ 4 < 2 by norm_num)]; exact pt _ _ _ (by rw [e4]; exact dQD))
        (by simp only [pieceSet, hlP, if_neg (show ¬ 5 < 2 by norm_num)]; exact pt _ _ _ (by rw [e5]; exact dQY))
  · -- `(3, 4)`: the cross half-turn of `L^+` and `L^-`, pinned at the corners `0` and `D`; the constants of the full copies
    -- through the chain `Q^{+,2} → P^+ → Q^{-,2} → Q^{-,1}`
    intro off hoff hi hj hx
    have hwl : w.dropLast.length + 1 = w.length := by
      have : w ≠ [] := by rintro rfl; simp at h3
      rw [List.length_dropLast]; have := List.length_pos_of_ne_nil this; omega
    have hG' : GoodBelow D f (w.dropLast.length + 1) := hwl ▸ hG
    have hspec := FLatticePaper.Tiles.TileHalfTurnLRot.specialLHalfTurn_of_rot D
    obtain ⟨K, hK⟩ := FLatticePaper.Tiles.TileHalfTurnInput.crossEven D hS hA hspec f w.dropLast hG' hdef true false
    obtain ⟨K', hK'⟩ := FLatticePaper.Tiles.TileHalfTurnInput.crossEven D hS hA hspec f w.dropLast hG' hdef false false
    have hC : TileHalfTurnStd.cEven ((parentsAt w.dropLast).current .even) =
        texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) := by
      rw [hq]; rfl
    have hcur : (parentsAt w.dropLast).current .even = (parentsAt w).even := by rw [hq]; rfl
    have k00 := k3 _ esc.1
    have k4D := k4 _ esm.2.2.2.2.2
    have pK := (hK _ k00.1).2
    have pK' := (hK' _ k4D.1).2
    have e00 : ∀ v : ℤ × ℤ, v - ((0 : ℤ), (0 : ℤ)) = v := fun v => by ext <;> simp
    have eDD : ∀ v : ℤ × ℤ, v - v = ((0 : ℤ), (0 : ℤ)) := fun v => by ext <;> simp
    simp only [Bool.not_true, Bool.not_false, e00, hC, eDD] at pK pK'
    rw [k4D.2.2, k00.2.2] at pK
    rw [k00.2.2, k4D.2.2] at pK'
    have hT0 := (hhQ _ (show (0 : ℤ × ℤ) ∈ tEvenSet w.dropLast from dQ0)).2
    simp only [sub_zero] at hT0
    have r30 := mixF 0 3 (by norm_num) (by norm_num) (by norm_num) ((oddQ w).getD 1 0 + texV1Even (parentsAt w).even)
      (by simp only [hP, hQ, List.getD_cons_zero, List.getD_cons_succ]; rw [show texV1Even (parentsAt w).even +
          texV1Even (parentsAt w).even - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even) = 0 from sub_self _]
          exact dP0)
      (by simp only [show 3 - 2 = 1 from rfl, add_sub_cancel_left]; exact dQX)
    have r05 := mixF 0 5 (by norm_num) (by norm_num) (by norm_num)
      ((oddP w).getD 0 0 + (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))))
      (by simp only [add_sub_cancel_left]; exact dPD1)
      (by simp only [hP, hQ, List.getD_cons_zero, List.getD_cons_succ, show 5 - 2 = 3 from rfl]
          rw [show texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + (texV1Odd (parentsAt w).odd +
            texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd +
            texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = texV1Even (parentsAt w).even - ((0 : ℤ), (1 : ℤ)) by
              ext <;> simp <;> ring]
          exact dQXi)
    have r45 := hDa 4 5 (by rw [hlP, hlQ]; omega) (by rw [hlP, hlQ]; omega) (by norm_num) (by simp [pieceFlag, hlP])
      ⟨rfl, Or.inr (by rw [hlP])⟩ ((oddQ w).getD 2 0 + texV1Even (parentsAt w).even)
      (by simp only [pieceSet, hlP, if_neg (show ¬ 4 < 2 by norm_num)]
          exact pt _ _ _ (by simp only [show 4 - 2 = 2 from rfl, add_sub_cancel_left]; exact dQX))
      (by simp only [pieceSet, hlP, if_neg (show ¬ 5 < 2 by norm_num)]
          exact pt _ _ _ (by simp only [hQ, List.getD_cons_zero, List.getD_cons_succ, show 5 - 2 = 3 from rfl]
                             rw [show texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV1Even (parentsAt w).even -
                               (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = 0
                               from sub_self _]; exact dQ0))
    obtain ⟨vP0, -, -, -, -, -, -, vPD1⟩ := AltParentConstants.corner_raw (f u1).tOdd βP _ _ _ hcP
    obtain ⟨vQ0, -, vQXi, vQX, -, -, -, -⟩ := AltParentConstants.corner_raw (f w.dropLast).tEven βQ _ _ _ hcQ
    have hB4 := AltSixEven.h0_even (texV2 (parentsAt w).odd) (by
      have hpar := (parentsAt_valid w).odd_parity
      simp only [texV2]; omega)
    have a0 : affOdd (parentsAt w).odd (parentsAt w).even 0 = 0 := by simp [affOdd]
    have a3 : affOdd (parentsAt w).odd (parentsAt w).even 3 = 0 := by simp [affOdd]
    have a4 : affOdd (parentsAt w).odd (parentsAt w).even 4 = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
      simp [affOdd]
    have a5 : affOdd (parentsAt w).odd (parentsAt w).even 5 = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
      simp [affOdd]
    refine CorrectedWalkZero.off_of_halfTurn hoff (i := 3) (j := 4) g3 g4 hK hK' ?_ hi hj hx
    rw [hC, κ3, κ4, a3, a4]
    simp only [hF, placedOdd, if_pos (show (0 : ℕ) < 2 by norm_num), if_neg (show ¬ (3 : ℕ) < 2 by norm_num),
      if_neg (show ¬ (4 : ℕ) < 2 by norm_num), if_neg (show ¬ (5 : ℕ) < 2 by norm_num), Pi.zero_apply, add_zero,
      show (3 : ℕ) - 2 = 1 from rfl, show (4 : ℕ) - 2 = 2 from rfl, show (5 : ℕ) - 2 = 3 from rfl] at r30 r05 r45
    simp only [hP, hQ, List.getD_cons_zero, List.getD_cons_succ, sub_self, add_sub_cancel_left] at r30 r05 r45 ⊢
    have eXi : texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + (texV1Odd (parentsAt w).odd +
        texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd +
        texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = texV1Even (parentsAt w).even - ((0 : ℤ), (1 : ℤ)) := by
      ext <;> simp <;> ring
    rw [eXi] at r05
    rw [vP0, vQX, a0, a3] at r30
    rw [vPD1, vQXi, a0, a5] at r05
    rw [vQX, vQ0, a4, a5] at r45
    simp only [ClosedPathSum.dot2, TileHalfTurnStd.aF, offsetA, dotS, texV1Odd, texV1Even, texV2, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.smul_mk,
      smul_eq_mul, Prod.mk_zero_zero, hcur] at r30 r05 r45 pK pK' hT0 hB4 ⊢
    linear_combination (4 : ℤ) * r45 + (-4 : ℤ) * r05 + 4 * r30 - pK + pK' + 2 * hT0 - hB4
open FLatticePaper.Tiles.ClosedPathExcluded in
/-- **The optional interfaces of the odd standard child do not occur after a `3`.** The full copies `(1, 2)`, `(0, 5)` for `W_1`
odd and `(1, 3)`, `(0, 4)` for `W_1` even do not meet: if they did, the boxes of `ClosedPathExcluded` would give
`n_q + 1 ≤ 2 n_p`, resp. `d_q + 1 ≤ 2 d_p` (as in `ClosedPathTriOdd`), while after a `3` the even parent is `2 p + q'`. -/

theorem opt_disjoint_three (w u1 u2 : Word) (h3 : w.getLast? = some Digit.three)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) :
    (phase w = 1 → (∀ z, z ∈ dOdd w u1 u2 1 → z ∈ dOdd w u1 u2 2 → False) ∧
      (∀ z, z ∈ dOdd w u1 u2 0 → z ∈ dOdd w u1 u2 5 → False)) ∧
    (phase w ≠ 1 → (∀ z, z ∈ dOdd w u1 u2 1 → z ∈ dOdd w u1 u2 3 → False) ∧
      (∀ z, z ∈ dOdd w u1 u2 0 → z ∈ dOdd w u1 u2 4 → False)) := by
  have hs := SameParentCopies.parents_last w _ h3
  have ho : (parentsAt w).odd = (parentsAt w.dropLast).odd := by rw [hs]; simp [Parents.step]
  have he : (parentsAt w).even = ⟨2 * (parentsAt w.dropLast).odd.num + (parentsAt w.dropLast).even.num,
      2 * (parentsAt w.dropLast).odd.den + (parentsAt w.dropLast).even.den⟩ := by
    rw [hs]; simp [Parents.step, Parents.current, Parents.combine]
  obtain ⟨hd0, hn0, -⟩ := (parentsAt_valid w.dropLast).even_bounds
  have hnum : (parentsAt w).even.num = 2 * (parentsAt w).odd.num + (parentsAt w.dropLast).even.num := by
    rw [he, ho]
  have hden : (parentsAt w).even.den = 2 * (parentsAt w).odd.den + (parentsAt w.dropLast).even.den := by
    rw [he, ho]
  refine ⟨fun hph => ⟨fun z0 hd1 hd2 => ?_, fun z0 hd0' hd5 => ?_⟩, fun hph => ⟨fun z0 hd1 hd3 => ?_, fun z0 hd0' hd4 => ?_⟩⟩
  · have hP := oddP_of w hph
    have hQ := oddQ_of w hph
    simp only [dOdd, pieceSet, hP, hQ] at hd1 hd2
    simp at hd1 hd2
    have b1 := box_shift_odd u1 _ z0 hd1
    have b2 := box_shift_even u2 _ z0 hd2
    rw [← hp] at b1
    rw [← hq] at b2
    simp only [texV2, texV1Even, texV1Odd, Prod.fst_add, Prod.snd_add] at b1 b2
    have hov : (parentsAt w).even.num + 1 ≤ 2 * (parentsAt w).odd.num := by omega
    omega
  · have hP := oddP_of w hph
    have hQ := oddQ_of w hph
    simp only [dOdd, pieceSet, hP, hQ] at hd0' hd5
    simp at hd0' hd5
    have b0 := box_shift_odd u1 _ z0 hd0'
    have b5 := box_shift_even u2 _ z0 hd5
    rw [← hp] at b0
    rw [← hq] at b5
    simp only [texV2, texV1Even, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at b0 b5
    have hov : (parentsAt w).even.num + 1 ≤ 2 * (parentsAt w).odd.num := by omega
    omega
  · have hP := oddP_ef w hph
    have hQ := oddQ_ef w hph
    simp only [dOdd, pieceSet, hP, hQ] at hd1 hd3
    simp at hd1 hd3
    have b1 := box_shift_odd u1 _ z0 hd1
    have b3 := box_shift_even u2 _ z0 hd3
    rw [← hp] at b1
    rw [← hq] at b3
    simp only [texV2, texV1Even] at b1 b3
    have hov : (parentsAt w).even.den + 1 ≤ 2 * (parentsAt w).odd.den := by omega
    omega
  · have hP := oddP_ef w hph
    have hQ := oddQ_ef w hph
    simp only [dOdd, pieceSet, hP, hQ] at hd0' hd4
    simp at hd0' hd4
    have b0 := box_shift_odd u1 _ z0 hd0'
    have b4 := box_shift_even u2 _ z0 hd4
    rw [← hp] at b0
    rw [← hq] at b4
    simp only [texV2, texV1Even, texV1Odd, Prod.fst_add, Prod.snd_add] at b0 b4
    have hov : (parentsAt w).even.den + 1 ≤ 2 * (parentsAt w).odd.den := by omega
    omega

end FLatticePaper.Tiles.CorrectedStdOdd
