import FLatticePaper.Tiles.WeakAltStepAssembly
import FLatticePaper.Tiles.WeakAltNode
import FLatticePaper.Tiles.TileStepAssembly
import FLatticePaper.Tiles.AltSevenFamilyB
import FLatticePaper.Tiles.AltSevenFamilyC
import FLatticePaper.Tiles.AltLatticeEvenVWrap

/-! # The weak alternate step of the joint induction for the paper data

`weakAltStep_paper : WeakAltStepInput D`. At a base word the weak alternates are the base ones (`BaseWeakAltInput`). At a word
that is not a base word, each alternate child is treated on its own. At a corrected alternate child the weak alternate is given
by `AltCorrectedWeakInput`. At an uncorrected one it is the glue of the full alternate decomposition, with the constants of
Case 3 of `lemma:tile-odometer-existence` (`AltSevenFamily`, `AltSevenFamilyB`, `AltSevenFamilyC`; their inputs are the
compatibility of the alternate parent piece, `TileCompatInputs.AltParentCompatInput`, and of the shifted doublings,
`AltShiftCompatInput`). Its domain is the alternate tile (`WeakAltNode.altOdd_union`), its node follows from the decomposition
(`WeakAltNode.altOddNode_of_respects`), its half string is `AltGlueRespectsInput`, and (b) along the second lattice vector is
`AltLatticeOddWWrap.odd_W_family` and `AltLatticeEvenVWrap.even_V_family`. -/

namespace FLatticePaper.Tiles.WeakAltStepPaper

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow WeakAltStepInput)
open FLatticePaper.Tiles.WeakStepPaper (paperS)
open FLatticePaper.Tiles.SurgicalWeak (regsAt WeakData)
open FLatticePaper.Tiles.Standard (IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAlt (altRevVAnchor altFwdHAnchor RespectsHalfV RespectsHalfH AltOddNodeP AltEvenNodeP)
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.WeakAltStepAssembly
open FLatticePaper.Tiles.ChildGlue (tOddSet tEvenSet)
open FLatticePaper.Tiles.TileStepAssembly (aOP aEP)

/-! ### Small facts -/

theorem tileAltOdd_noexc (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (l : Word → Bool → Bool → PartialOdometer)
    (w : Word) : ∀ p ∈ tileAltOddPieces S pO pE aO aE l w, p.exc = ∅ := by
  intro p hp
  simp only [tileAltOddPieces] at hp
  rcases List.mem_append.1 hp with hp | hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · revert hp
    split
    · intro h; simp at h
    · intro h; simp only [List.mem_singleton] at h; subst h; rfl

theorem tileAltEven_noexc (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (l : Word → Bool → Bool → PartialOdometer)
    (w : Word) : ∀ p ∈ tileAltEvenPieces S pO pE aO aE l w, p.exc = ∅ := by
  intro p hp
  simp only [tileAltEvenPieces] at hp
  rcases List.mem_append.1 hp with hp | hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · revert hp
    split
    · intro h; simp at h
    · intro h; simp only [List.mem_singleton] at h; subst h; rfl

/-- The lattice self-compatibility of a register along the alternate shift, in the form of the shift constant of Case 3. -/
theorem hk_of_compat (o : PartialOdometer) (T : Finset Site) (hd : o.dom = T) (v a : Site)
    (h : LatticeSelfCompatible o v a) :
    ∃ k : ℤ, ∀ x, x ∈ (↑T : Set Site) → x + v ∈ (↑T : Set Site) →
      o.val (x + v) - o.val x - ClosedPathSum.dot2 a x = k := by
  obtain ⟨c, hc⟩ := h
  subst hd
  exact ⟨c, fun x hx hxv => hc x hx hxv⟩

theorem eq_snoc (w : Word) (hw : w ≠ []) : ∃ v d, w = v ++ [d] :=
  ⟨w.dropLast, w.getLast hw, (List.dropLast_append_getLast hw).symm⟩

theorem len_pos_of_ne (v : Word) (hv : v ≠ []) : 1 ≤ v.length :=
  Nat.pos_of_ne_zero (fun h => hv (List.eq_nil_of_length_eq_zero h))

/-! ### The constants of Case 3 at the uncorrected alternate children -/

/-- **The odd alternate decomposition agrees** at a word that is not a base word and does not end in `2`. -/
theorem oddAlt_agree (D : JointData) (hS : D.S = paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hlS : D.lSides = paperLSides) (hpc : TileCompatInputs.AltParentCompatInput D) (hsc : AltShiftCompatInput D)
    (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hc : w.getLast? ≠ some Digit.two) : ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (aOP D f w) κ := by
  obtain ⟨u1, u2, hreg⟩ := WeakStepAssembly.regsAt_nonbase w hw
  have hl1 : u1.length < w.length := JointInduction.regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hdO : (f u1).tOdd.dom = oddTile u1 := by
    rw [(WeakStepAssembly.slice_domains D f u1 (hg u1 hl1).1).1, hS]; rfl
  have hpcw := fun j (hj : j < 6) => (hpc f w hg hw j hj).1
  have hk : ∀ u, (regsAt w).1 = some u → ∃ k : ℤ, ∀ x, x ∈ tOddSet u → x + ClosedPathAlt.shiftP w ∈ tOddSet u →
      (f u).tOdd.val (x + ClosedPathAlt.shiftP w) - (f u).tOdd.val x - ClosedPathSum.dot2 (ClosedPathAlt.affS w) x = k := by
    intro u hu
    rw [hreg] at hu
    cases hu
    exact hk_of_compat _ _ hdO _ _ (hsc hS hA f w u1 u2 hg hw hreg).1
  have hov := AltSixOverlaps.sixOverlaps_odd_all w hw hc
  obtain ⟨v, d, rfl⟩ := eq_snoc w (fun h => hw (Or.inl h))
  cases d with
  | one =>
    by_cases hv0 : v = []
    · subst hv0
      exact AltSevenFamilyB.familyB_ao31 D hS hA f 0 (Nat.zero_le _) hg hpcw hk
    by_cases hv : IsBase v
    · rcases hv with hv | hv3 | hv2
      · exact absurd hv hv0
      · obtain ⟨k, rfl⟩ : ∃ k, v = List.replicate k Digit.three := ⟨v.length, List.eq_replicate_iff.2 ⟨rfl, hv3⟩⟩
        exact AltSevenFamilyB.familyB_ao31 D hS hA f k (Nat.zero_le _) hg hpcw hk
      · have h1 := len_pos_of_ne v hv0
        obtain ⟨k, rfl⟩ : ∃ k, v = List.replicate k Digit.two := ⟨v.length, List.eq_replicate_iff.2 ⟨rfl, hv2⟩⟩
        exact AltSevenFamilyB.familyB_ao21 D hS hA f k (by simpa using h1) hg hpcw hk
    · by_cases hph : phase (v ++ [Digit.one]) = 1
      · exact AltSevenFamily.family_oo1 D hS hA f v hg hv hph hpcw hk hov
      · exact AltSevenFamily.family_oe1 D hS hA f v hg hv hph hpcw hk hov
  | two => exact (hc (by simp)).elim
  | three =>
    by_cases hv0 : v = []
    · subst hv0
      exact (hw (Or.inr (Or.inl (by simp)))).elim
    by_cases hv : IsBase v
    · rcases hv with hv | hv3 | hv2
      · exact absurd hv hv0
      · refine (hw (Or.inr (Or.inl fun x hx => ?_))).elim
        rcases List.mem_append.1 hx with hx | hx
        · exact hv3 x hx
        · simpa using hx
      · have h1 := len_pos_of_ne v hv0
        obtain ⟨k, rfl⟩ : ∃ k, v = List.replicate k Digit.two := ⟨v.length, List.eq_replicate_iff.2 ⟨rfl, hv2⟩⟩
        exact AltSevenFamilyB.familyB_ao23 D hS hA f k (by simpa using h1) hg hpcw hk
    · by_cases hvc : v.getLast? = some Digit.three
      · by_cases hph : phase (v ++ [Digit.three]) = 1
        · exact AltSevenFamilyC.familyC_oo3 D hS hA f v hg hv hph hvc hlS hpcw hk hov
        · exact AltSevenFamilyC.familyC_oe3 D hS hA f v hg hv hph hvc hlS hpcw hk hov
      · by_cases hph : phase (v ++ [Digit.three]) = 1
        · exact AltSevenFamily.family_oo3 D hS hA f v hg hv hph hvc hpcw hk hov
        · exact AltSevenFamily.family_oe3 D hS hA f v hg hv hph hvc hpcw hk hov

/-- **The even alternate decomposition agrees** at a word that is not a base word and does not end in `3`. -/
theorem evenAlt_agree (D : JointData) (hS : D.S = paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hlS : D.lSides = paperLSides) (hpc : TileCompatInputs.AltParentCompatInput D) (hsc : AltShiftCompatInput D)
    (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hc : w.getLast? ≠ some Digit.three) : ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (aEP D f w) κ := by
  obtain ⟨u1, u2, hreg⟩ := WeakStepAssembly.regsAt_nonbase w hw
  have hl2 : u2.length < w.length := JointInduction.regsAt_lt w u2 (Or.inr (by rw [hreg]))
  have hdE : (f u2).tEven.dom = evenTile u2 := by
    rw [(WeakStepAssembly.slice_domains D f u2 (hg u2 hl2).1).2, hS]; rfl
  have hpcw := fun j (hj : j < 6) => (hpc f w hg hw j hj).2
  have hk : ∀ u, (regsAt w).2 = some u → ∃ k : ℤ, ∀ x, x ∈ tEvenSet u → x + ClosedPathAlt.shiftQ w ∈ tEvenSet u →
      (f u).tEven.val (x + ClosedPathAlt.shiftQ w) - (f u).tEven.val x - ClosedPathSum.dot2 (ClosedPathAlt.affS w) x = k := by
    intro u hu
    rw [hreg] at hu
    cases hu
    exact hk_of_compat _ _ hdE _ _ (hsc hS hA f w u1 u2 hg hw hreg).2
  have hov := AltSixOverlaps.sixOverlaps_even_all w hw hc
  obtain ⟨v, d, rfl⟩ := eq_snoc w (fun h => hw (Or.inl h))
  cases d with
  | one =>
    by_cases hv0 : v = []
    · subst hv0
      exact AltSevenFamilyB.familyB_ae21 D hS hA f 0 (Nat.zero_le _) hg hpcw hk
    by_cases hv : IsBase v
    · rcases hv with hv | hv3 | hv2
      · exact absurd hv hv0
      · have h1 := len_pos_of_ne v hv0
        obtain ⟨k, rfl⟩ : ∃ k, v = List.replicate k Digit.three := ⟨v.length, List.eq_replicate_iff.2 ⟨rfl, hv3⟩⟩
        exact AltSevenFamilyB.familyB_ae31 D hS hA f k (by simpa using h1) hg hpcw hk
      · obtain ⟨k, rfl⟩ : ∃ k, v = List.replicate k Digit.two := ⟨v.length, List.eq_replicate_iff.2 ⟨rfl, hv2⟩⟩
        exact AltSevenFamilyB.familyB_ae21 D hS hA f k (Nat.zero_le _) hg hpcw hk
    · by_cases hph : phase (v ++ [Digit.one]) = 1
      · exact AltSevenFamily.family_of1 D hS hA f v hg hv hph hpcw hk hov
      · exact AltSevenFamily.family_ef1 D hS hA f v hg hv hph hpcw hk hov
  | two =>
    by_cases hv0 : v = []
    · subst hv0
      exact (hw (Or.inr (Or.inr (by simp)))).elim
    by_cases hv : IsBase v
    · rcases hv with hv | hv3 | hv2
      · exact absurd hv hv0
      · have h1 := len_pos_of_ne v hv0
        obtain ⟨k, rfl⟩ : ∃ k, v = List.replicate k Digit.three := ⟨v.length, List.eq_replicate_iff.2 ⟨rfl, hv3⟩⟩
        exact AltSevenFamilyB.familyB_ae32 D hS hA f k (by simpa using h1) hg hpcw hk
      · refine (hw (Or.inr (Or.inr fun x hx => ?_))).elim
        rcases List.mem_append.1 hx with hx | hx
        · exact hv2 x hx
        · simpa using hx
    · by_cases hvc : v.getLast? = some Digit.two
      · by_cases hph : phase (v ++ [Digit.two]) = 1
        · exact AltSevenFamilyC.familyC_of2 D hS hA f v hg hv hph hvc hlS hpcw hk hov
        · exact AltSevenFamilyC.familyC_ef2 D hS hA f v hg hv hph hvc hlS hpcw hk hov
      · by_cases hph : phase (v ++ [Digit.two]) = 1
        · exact AltSevenFamily.family_of2 D hS hA f v hg hv hph hvc hpcw hk hov
        · exact AltSevenFamily.family_ef2 D hS hA f v hg hv hph hvc hpcw hk hov
  | three => exact (hc (by simp)).elim

/-! ### The weak alternates at a word that is not a base word -/

/-- **The odd weak alternate** at a word that is not a base word: the glue of the full decomposition at an uncorrected child,
`AltCorrectedWeakInput` at a corrected one. -/
theorem oddWeak (D : JointData) (hS : D.S = paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hAB : PaperAltBdry D) (hAnc : PaperAltAnc D) (hlS : D.lSides = paperLSides)
    (hpc : TileCompatInputs.AltParentCompatInput D) (hsc : AltShiftCompatInput D) (hgr : AltGlueRespectsInput D)
    (hcw : AltCorrectedWeakInput D) (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (hw : ¬ IsBase w) :
    ∃ wao : PartialOdometer, wao.dom = D.altBdry (some w) true ∧
      AltOddNodeP D.S wao (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
        (fun u => (below f w u).aEven) w ∧
      RespectsHalfV (altRevVAnchor D.anc w) (vWordOf w false) wao.val ∧
      (¬ CorrectedAfterTwo w → RespectsPieces wao (aOP D f w)) ∧ (¬ CorrectedAfterTwo w → AltLatticeOddV2 w wao) := by
  by_cases hc2 : CorrectedAfterTwo w
  · obtain ⟨wao, hd, hn, hr⟩ := (hcw hS hA hAB hAnc hlS f w hg).1 hc2
    exact ⟨wao, hd.trans (hAB w).1.symm, hn, hr, fun h => absurd hc2 h, fun h => absurd hc2 h⟩
  have hc : w.getLast? ≠ some Digit.two := fun h => hc2 ⟨hw, h⟩
  obtain ⟨u1, u2, hreg⟩ := WeakStepAssembly.regsAt_nonbase w hw
  have hl1 : u1.length < w.length := JointInduction.regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hl2 : u2.length < w.length := JointInduction.regsAt_lt w u2 (Or.inr (by rw [hreg]))
  have hb1 := JointRot.below_of_lt f w u1 hl1
  have hb2 := JointRot.below_of_lt f w u2 hl2
  obtain ⟨hS1, -⟩ := hg u1 hl1
  obtain ⟨hS2, -⟩ := hg u2 hl2
  have hdO : (f u1).tOdd.dom = oddTile u1 := by rw [(WeakStepAssembly.slice_domains D f u1 hS1).1, hS]; rfl
  have hdE : (f u2).tEven.dom = evenTile u2 := by rw [(WeakStepAssembly.slice_domains D f u2 hS2).2, hS]; rfl
  have hdAE : (f u2).aEven.dom = altEvenTile PaperAltBase.paperAltBaseTiles u2 :=
    (hS2.2.2.1).2.2.2.2.2.2.2.2.2.2.2.trans (hAB u2).2
  obtain ⟨κ, hag⟩ := oddAlt_agree D hS hA hlS hpc hsc f w hg hw hc
  have hR := JointGlue.respectsPieces_glued (aOP D f w) κ
    (JointGlue.covered_of_no_exc _ (tileAltOdd_noexc D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
      (fun u => (below f w u).aEven) (fun u => (below f w u).lOdd) w)) hag
  have hdomU : pieceUnion (aOP D f w) = altOddTile PaperAltBase.paperAltBaseTiles w :=
    WeakAltNode.altOdd_union D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
      (fun u => (below f w u).aEven) (fun u => (below f w u).lOdd) w u1 u2 hw hreg hc (by simp only [hb1]; exact hdO)
      (by simp only [hb2]; exact hdE) (by simp only [hb2]; exact hdAE)
  have hdom : (JointGlue.gluedOdo (aOP D f w) κ).dom = altOddTile PaperAltBase.paperAltBaseTiles w := hdomU
  refine ⟨JointGlue.gluedOdo (aOP D f w) κ, hdom.trans (hAB w).1.symm, ?_, ?_, fun _ => hR, fun _ => ?_⟩
  · refine WeakAltNode.altOddNode_of_respects D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
      (fun u => (below f w u).aEven) (fun u => (below f w u).lOdd) w u1 u2 hreg hc _ hR ?_ ?_
    · simp only [hb1]; rw [(WeakStepAssembly.slice_domains D f u1 hS1).1]
    · simp only [hb1]; exact (WeakStepAssembly.slice_respects D f u1 hS1).1
  · exact (hgr hS hA hAB hAnc hlS f w _ hg hw).1 hc2 hdom hR
  · obtain ⟨v, d, rfl⟩ := eq_snoc w (fun h => hw (Or.inl h))
    exact AltLatticeOddWWrap.odd_W_family D hS hA hAB hAnc f v d (fun h => hc (by rw [h]; simp)) hw hg _ hR hdom

/-- **The even weak alternate** at a word that is not a base word. -/
theorem evenWeak (D : JointData) (hS : D.S = paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hAB : PaperAltBdry D) (hAnc : PaperAltAnc D) (hlS : D.lSides = paperLSides)
    (hpc : TileCompatInputs.AltParentCompatInput D) (hsc : AltShiftCompatInput D) (hgr : AltGlueRespectsInput D)
    (hcw : AltCorrectedWeakInput D) (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (hw : ¬ IsBase w) :
    ∃ wae : PartialOdometer, wae.dom = D.altBdry (some w) false ∧
      AltEvenNodeP D.S wae (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
        (fun u => (below f w u).aEven) w ∧
      RespectsHalfH (altFwdHAnchor D.anc w) (hWordOf w true) wae.val ∧
      (¬ CorrectedAfterThree w → RespectsPieces wae (aEP D f w)) ∧ (¬ CorrectedAfterThree w → AltLatticeEvenV2 w wae) := by
  by_cases hc3 : CorrectedAfterThree w
  · obtain ⟨wae, hd, hn, hr⟩ := (hcw hS hA hAB hAnc hlS f w hg).2 hc3
    exact ⟨wae, hd.trans (hAB w).2.symm, hn, hr, fun h => absurd hc3 h, fun h => absurd hc3 h⟩
  have hc : w.getLast? ≠ some Digit.three := fun h => hc3 ⟨hw, h⟩
  obtain ⟨u1, u2, hreg⟩ := WeakStepAssembly.regsAt_nonbase w hw
  have hl1 : u1.length < w.length := JointInduction.regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hl2 : u2.length < w.length := JointInduction.regsAt_lt w u2 (Or.inr (by rw [hreg]))
  have hb1 := JointRot.below_of_lt f w u1 hl1
  have hb2 := JointRot.below_of_lt f w u2 hl2
  obtain ⟨hS1, -⟩ := hg u1 hl1
  obtain ⟨hS2, -⟩ := hg u2 hl2
  have hdO : (f u1).tOdd.dom = oddTile u1 := by rw [(WeakStepAssembly.slice_domains D f u1 hS1).1, hS]; rfl
  have hdE : (f u2).tEven.dom = evenTile u2 := by rw [(WeakStepAssembly.slice_domains D f u2 hS2).2, hS]; rfl
  have hdAO : (f u1).aOdd.dom = altOddTile PaperAltBase.paperAltBaseTiles u1 :=
    (hS1.2.2.1).2.2.2.2.2.2.2.2.2.2.1.trans (hAB u1).1
  obtain ⟨κ, hag⟩ := evenAlt_agree D hS hA hlS hpc hsc f w hg hw hc
  have hR := JointGlue.respectsPieces_glued (aEP D f w) κ
    (JointGlue.covered_of_no_exc _ (tileAltEven_noexc D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
      (fun u => (below f w u).aEven) (fun u => (below f w u).lEven) w)) hag
  have hdomU : pieceUnion (aEP D f w) = altEvenTile PaperAltBase.paperAltBaseTiles w :=
    WeakAltNode.altEven_union D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
      (fun u => (below f w u).aEven) (fun u => (below f w u).lEven) w u1 u2 hw hreg hc (by simp only [hb1]; exact hdO)
      (by simp only [hb2]; exact hdE) (by simp only [hb1]; exact hdAO)
  have hdom : (JointGlue.gluedOdo (aEP D f w) κ).dom = altEvenTile PaperAltBase.paperAltBaseTiles w := hdomU
  refine ⟨JointGlue.gluedOdo (aEP D f w) κ, hdom.trans (hAB w).2.symm, ?_, ?_, fun _ => hR, fun _ => ?_⟩
  · refine WeakAltNode.altEvenNode_of_respects D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
      (fun u => (below f w u).aEven) (fun u => (below f w u).lEven) w u1 u2 hreg hc _ hR ?_ ?_
    · simp only [hb2]; rw [(WeakStepAssembly.slice_domains D f u2 hS2).2]
    · simp only [hb2]; exact (WeakStepAssembly.slice_respects D f u2 hS2).2
  · exact (hgr hS hA hAB hAnc hlS f w _ hg hw).2 hc3 hdom hR
  · obtain ⟨v, d, rfl⟩ := eq_snoc w (fun h => hw (Or.inl h))
    exact AltLatticeEvenVWrap.even_V_family D hS hA hAB f v d (fun h => hc (by rw [h]; simp)) hw hg _ hR hdom

/-! ### The weak alternate step -/

/-- **The weak alternate step of the joint induction for the paper data**: `WeakAltStepInput D`, from the named inputs
`BaseWeakAltInput`, `TileCompatInputs.AltParentCompatInput`, `AltShiftCompatInput`, `AltGlueRespectsInput` and
`AltCorrectedWeakInput`. -/
theorem weakAltStep_paper (D : JointData) (hS : D.S = paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hAB : PaperAltBdry D) (hAnc : PaperAltAnc D) (hlS : D.lSides = paperLSides) (hB : BaseWeakAltInput D)
    (hpc : TileCompatInputs.AltParentCompatInput D) (hsc : AltShiftCompatInput D) (hgr : AltGlueRespectsInput D)
    (hcw : AltCorrectedWeakInput D) : WeakAltStepInput D := by
  intro f w hg
  by_cases hw : IsBase w
  · obtain ⟨wao, wae, hdo, hde, hbc, hro, hre, hu⟩ := hB hA hAnc w hw
    refine ⟨wao, wae, ⟨hdo.trans (hAB w).1.symm, hde.trans (hAB w).2.symm, fun _ => ?_, fun h => absurd hw h, hro, hre,
      fun h => absurd hw h, fun h => absurd hw h⟩, hu⟩
    rw [hA]; exact hbc
  · obtain ⟨wao, hdo, hno, hro, hfo, hlo⟩ := oddWeak D hS hA hAB hAnc hlS hpc hsc hgr hcw f w hg hw
    obtain ⟨wae, hde, hne, hre, hfe, hle⟩ := evenWeak D hS hA hAB hAnc hlS hpc hsc hgr hcw f w hg hw
    exact ⟨wao, wae, ⟨hdo, hde, fun h => absurd h hw, fun _ => ⟨hno, hne⟩, hro, hre, fun _ => hfo, fun _ => hfe⟩,
      hlo, hle⟩

end FLatticePaper.Tiles.WeakAltStepPaper
