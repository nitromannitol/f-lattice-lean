import FLatticePaper.Tiles.AltSevenFamily
import FLatticePaper.Tiles.AltSevenC

/-! # Case 3 from the joint family at a corrected parent

The even alternate child of `w = v 2` with `v` ending in `2`, and the odd one of `w = v 3` with `v` ending in `3`. The parent's
decomposition at `v` has two L-entries, the elongated L-corrections of the shorter word; on their kept sides they equal the
standard tile up to one constant (`LPart`, `LSidesAgree`, with `D.lSides = paperLSides`), and the corners used lie on those sides
(`AltLSides`). The rest is as in `AltSevenFamily`. -/

namespace FLatticePaper.Tiles.AltSevenFamilyC

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.AltParentConstants
open FLatticePaper.Tiles.SurgicalWeak (regsAt)
open FLatticePaper.Tiles.Standard (oddTile evenTile IsBase)
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.AltSevenFamily
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)

/-- The L-entries `1`, `2` of a corrected odd alternate decomposition. -/
theorem aOdd_memL (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lOdd : Word → Bool → Bool → PartialOdometer) (w : Word) (hc : w.getLast? = some Digit.two) :
    stdPiece (lOdd w.dropLast false true) ((altOddD w).getD 1 0) ((altOddAff w).getD 1 0) ∈
        tileAltOddPieces S pOdd pEven aOdd aEven lOdd w ∧
      stdPiece (lOdd w.dropLast true true) ((altOddD w).getD 2 0) ((altOddAff w).getD 2 0) ∈
        tileAltOddPieces S pOdd pEven aOdd aEven lOdd w := by
  unfold tileAltOddPieces
  simp only [hc, decide_true, if_true]
  refine ⟨?_, ?_⟩ <;> simp [altOddD, altOddAff, add_comm, JointFamily.W1Odd, JointFamily.altOff,
    JointFamily.altAff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, JointFamily.aP2]

/-- The L-entries `0`, `3` of a corrected even alternate decomposition. -/
theorem aEven_memL (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lEven : Word → Bool → Bool → PartialOdometer) (w : Word) (hc : w.getLast? = some Digit.three) :
    stdPiece (lEven w.dropLast true true) ((altEvenD w).getD 0 0) ((altEvenAff w).getD 0 0) ∈
        tileAltEvenPieces S pOdd pEven aOdd aEven lEven w ∧
      stdPiece (lEven w.dropLast false true) ((altEvenD w).getD 3 0) ((altEvenAff w).getD 3 0) ∈
        tileAltEvenPieces S pOdd pEven aOdd aEven lEven w := by
  unfold tileAltEvenPieces
  simp only [hc, decide_true, if_true]
  refine ⟨?_, ?_⟩ <;> simp [altEvenD, altEvenAff, add_comm, JointFamily.W1Odd, JointFamily.altOff,
    JointFamily.altAff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, JointFamily.aP2]

/-- `AltLSides.L_identity` with the offset and the affine factor in another form. -/
theorem L_sub (H T L : PartialOdometer) (ps : List JointFamily.Piece) (hR : JointFamily.RespectsPieces H ps)
    (off aff OFF AFF : ℤ × ℤ) (hmem : stdPiece L off aff ∈ ps) (hoff : off = OFF) (haff : aff = AFF)
    (S : Set (ℤ × ℤ)) (c : ℤ) (hS : ∀ y ∈ S, y ∈ L.dom ∧ y ∈ T.dom ∧ L.val y = T.val y + c) :
    (∀ x, x - OFF ∈ S → x ∈ (↑H.dom : Set (ℤ × ℤ))) ∧
      ∃ b : ℤ, ∀ x, x - OFF ∈ S → H.val x = T.val (x - OFF) + dotS AFF x + b := by
  subst hoff haff
  exact AltLSides.L_identity H T L ps hR off aff hmem S c hS

/-- Case 3 from the family, even alternate child, `W_1` even, last digit `2`. -/
theorem familyC_ef2 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (v : Word) (hg : GoodBelow D f (v ++ [Digit.two]).length) (hv : ¬ IsBase v)
    (hph : phase (v ++ [Digit.two]) ≠ 1) (hvc : v.getLast? = some Digit.two) (hlS : D.lSides = paperLSides)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltEvenPieces D.S (fun u => (below f (v ++ [Digit.two]) u).tOdd) (fun u => (below f (v ++ [Digit.two]) u).tEven)
      (fun u => (below f (v ++ [Digit.two]) u).aOdd) (fun u => (below f (v ++ [Digit.two]) u).aEven)
      (fun u => (below f (v ++ [Digit.two]) u).lEven) (v ++ [Digit.two])) 6 j)
    (hk : ∀ u2, (regsAt (v ++ [Digit.two])).2 = some u2 → ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ (v ++ [Digit.two]) ∈ tEvenSet u2 →
      (f u2).tEven.val (x + shiftQ (v ++ [Digit.two])) - (f u2).tEven.val x - ClosedPathSum.dot2 (affS (v ++ [Digit.two])) x = k)
    (hov : ∀ u1 u2, regsAt (v ++ [Digit.two]) = (some u1, some u2) → AltPiecesAgree.SixOverlaps (altEvenD (v ++ [Digit.two])) (altEvenR (v ++ [Digit.two]))
      (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) ChildGlue.dblEven) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltEvenPieces D.S (fun u => (below f (v ++ [Digit.two]) u).tOdd) (fun u => (below f (v ++ [Digit.two]) u).tEven)
      (fun u => (below f (v ++ [Digit.two]) u).aOdd) (fun u => (below f (v ++ [Digit.two]) u).aEven)
      (fun u => (below f (v ++ [Digit.two]) u).lEven) (v ++ [Digit.two])) κ := by
  have hlt : v.length < (v ++ [Digit.two]).length := by simp
  have hgv : GoodBelow D f v.length := fun u hu => hg u (lt_trans hu hlt)
  obtain ⟨⟨v1, hv1⟩, ⟨v2, hv2'⟩⟩ := JointRot.regs_some v hv
  have hrv : regsAt v = (some v1, some v2) := Prod.ext hv1 hv2'
  have l1 : v1.length < v.length := JointInduction.regsAt_lt v v1 (Or.inl hv1)
  have l2 : v2.length < v.length := JointInduction.regsAt_lt v v2 (Or.inr hv2')
  have hr : regsAt (v ++ [Digit.two]) = (some v, some v2) := by
    simp [WeakStepPaper.regsAt_snoc, SurgicalWeak.regStep, hrv]
  have hu1 : v.length < (v ++ [Digit.two]).length := hlt
  have hu2 : v2.length < (v ++ [Digit.two]).length := by simp; omega
  have hb1 : below f (v ++ [Digit.two]) v = f v := JointRot.below_of_lt f _ _ hu1
  have hb2 : below f (v ++ [Digit.two]) v2 = f v2 := JointRot.below_of_lt f _ _ hu2
  have hbv : below f (v ++ [Digit.two]) v = f v := JointRot.below_of_lt f _ _ hlt
  have hp := (WeakStepAssembly.regsAt_parents (v ++ [Digit.two])).1 v (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents (v ++ [Digit.two])).2 v2 (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := regOdd_data D hS hA f _ hg v hu1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := regEven_data D hS hA f _ hg v2 hu2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdP] at hhP
  rw [hdQ] at hhQ
  obtain ⟨βP2, -, hcP2, hhP2⟩ := regOdd_data D hS hA f _ hgv v1 l1
  obtain ⟨βQ2, -, hcQ2, hhQ2⟩ := regEven_data D hS hA f _ hgv v2 l2
  have hp2 := (WeakStepAssembly.regsAt_parents v).1 v1 (by rw [hrv])
  have hq2 := (WeakStepAssembly.regsAt_parents v).2 v2 (by rw [hrv])
  rw [← hp2] at hcP2 hhP2
  rw [← hq2] at hcQ2 hhQ2
  have hphv : phase v ≠ 1 := by
    simp only [phase, List.count_append] at hph ⊢
    simp at hph
    omega
  have hhH := aOdd_halfTurn D hS hA f _ hg v hlt
  have hD : altD v true = (2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + (2 : ℤ) • ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + (2 : ℤ) • ((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den) + ((1 : ℤ), (-1 : ℤ)) := by
    simp [altD, W1Odd, hphv, vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2]
  rw [hD] at hhH
  have hRP := (parent_respects D f _ hg v hlt hv).1
  have hmem := (AltPiecesAgree.aOdd_mem D.S (fun v' => (below f v v').tOdd) (fun v' => (below f v v').tEven)
    (fun v' => (below f v v').aOdd) (fun v' => (below f v v').aEven) (fun v' => (below f v v').lOdd) v v1 v2 hrv)
  simp only [JointRot.below_of_lt f v v1 l1, JointRot.below_of_lt f v v2 l2] at hmem
  obtain ⟨hmA, hmB, hmC, hmD⟩ := hmem
  obtain ⟨hd0, h0p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altOddD v).getD 0 0) ((altOddAff v).getD 0 0) ((parentsAt v).even.den, (parentsAt v).even.num) 0 hmA
    (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  obtain ⟨hd3, h3p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altOddD v).getD 3 0) ((altOddAff v).getD 3 0) (((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den)) (((parentsAt v).odd.num, -(parentsAt v).odd.den) + ((parentsAt v).even.num, -(parentsAt v).even.den)) hmB
    (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA] <;> ring)
  obtain ⟨hd4, h4p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altOddR v).getD 0 0) ((altOddAff v).getD 4 0) 0 0 hmC
    (by ext <;> simp [altOddR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  obtain ⟨hd5, h5p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altOddR v).getD 1 0) ((altOddAff v).getD 5 0) ((2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + (2 : ℤ) • ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((parentsAt v).even.den, (parentsAt v).even.num)) ((2 : ℤ) • ((parentsAt v).odd.num, -(parentsAt v).odd.den)) hmD
    (by ext <;> simp [altOddR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  have hv' : v = v1 ++ [Digit.two] := by
    obtain ⟨u, d, rfl⟩ : ∃ u d, v = u ++ [d] := by
      cases v using List.reverseRecOn with
      | nil => exact (hv (Or.inl rfl)).elim
      | append_singleton u d => exact ⟨u, d, rfl⟩
    simp at hvc
    subst hvc
    have e := ConnectedAltL.regs_pre_fst u Digit.two (by decide)
    rw [hv1] at e
    cases e
    rfl
  have hdl : v.dropLast = v1 := by rw [hv']; simp
  have hJl := (hgv v1 l1).1.2.2.2
  have hdef : OddLDefined v1 := JointRot.oddLDefined_of_mem v1 (by
    by_contra hc; simp only [not_exists, not_and, not_not] at hc; exact hv (Or.inr (Or.inr fun d hd => by rw [hv'] at hd; simp at hd; rcases hd with hd | rfl; exacts [hc d hd, rfl])))
  have hWl : W1Odd v1 = false := by
    have := hphv
    rw [hv'] at this
    simp only [W1Odd, phase, List.count_append] at this ⊢
    simp at this ⊢
    omega
  have hmL := AltSevenFamilyC.aOdd_memL D.S (fun v' => (below f v v').tOdd) (fun v' => (below f v v').tEven)
    (fun v' => (below f v v').aOdd) (fun v' => (below f v v').aEven) (fun v' => (below f v v').lOdd) v hvc
  simp only [hdl, JointRot.below_of_lt f v v1 l1] at hmL
  obtain ⟨hmLa, hmLb⟩ := hmL
  obtain ⟨-, c1, hc1⟩ := ((hJl.1 false true hdef).2)
  rw [hlS] at hc1
  obtain ⟨hd1, h1p⟩ := AltSevenFamilyC.L_sub _ (f v1).tOdd _ _ hRP ((altOddD v).getD 1 0) ((altOddAff v).getD 1 0) ((2 : ℤ) • ((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den)) ((parentsAt v).odd.num, -(parentsAt v).odd.den)
    hmLa (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
    {y | ∃ s ∈ paperLSides true (W1Odd v1) false true, y ∈ placedSites (sideString (hWordOf v1 false) (vWordOf v1 false) 0 s)} c1
    (fun y ⟨s, hs, hy⟩ => hc1 s hs y hy)
  have hm1a : (2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈ {y | ∃ s ∈ paperLSides true (W1Odd v1) false true, y ∈ placedSites (sideString (hWordOf v1 false) (vWordOf v1 false) 0 s)} := by
    refine ⟨.vPlus, by simp [paperLSides, hWl], ?_⟩
    have := AltLSides.odd_side_right v1 |>.2
    rw [← hv'] at this
    exact this
  have hm1b : (2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) ∈ {y | ∃ s ∈ paperLSides true (W1Odd v1) false true, y ∈ placedSites (sideString (hWordOf v1 false) (vWordOf v1 false) 0 s)} := by
    refine ⟨.hPlus, by simp [paperLSides, hWl], ?_⟩
    have := ConnectedAltL.odd_side_corners v1 |>.2.1
    rw [← hv'] at this
    exact this
  obtain ⟨-, c2, hc2⟩ := ((hJl.1 true true hdef).2)
  rw [hlS] at hc2
  obtain ⟨hd2, h2p⟩ := AltSevenFamilyC.L_sub _ (f v1).tOdd _ _ hRP ((altOddD v).getD 2 0) ((altOddAff v).getD 2 0) ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den) ((parentsAt v).even.num, -(parentsAt v).even.den)
    hmLb (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
    {y | ∃ s ∈ paperLSides true (W1Odd v1) true true, y ∈ placedSites (sideString (hWordOf v1 false) (vWordOf v1 false) 0 s)} c2
    (fun y ⟨s, hs, hy⟩ => hc2 s hs y hy)
  have hm2a : ((1 : ℤ), (0 : ℤ)) ∈ {y | ∃ s ∈ paperLSides true (W1Odd v1) true true, y ∈ placedSites (sideString (hWordOf v1 false) (vWordOf v1 false) 0 s)} := by
    refine ⟨.vMinus, by simp [paperLSides, hWl], ?_⟩
    have := ConnectedAltL.odd_side_corners v1 |>.2.2.2.1
    exact this
  have hm2b : ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((1 : ℤ), (-1 : ℤ)) ∈ {y | ∃ s ∈ paperLSides true (W1Odd v1) true true, y ∈ placedSites (sideString (hWordOf v1 false) (vWordOf v1 false) 0 s)} := by
    refine ⟨.hMinus, by simp [paperLSides, hWl], ?_⟩
    have := ConnectedAltL.odd_side_corners v1 |>.2.2.1
    rw [← hv'] at this
    exact this
  have hpar2 := (parentsAt_valid v).odd_parity
  have hqe2 := (parentsAt_valid v).even_parity
  unfold Fraction.Odd at hpar2
  unfold Fraction.Even at hqe2
  have hwb : ¬ IsBase (v ++ [Digit.two]) := by
    rintro (h | h | h)
    · simp at h
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inl fun d hd => h d (by simp [hd])))
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inr fun d hd => h d (by simp [hd])))
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ v v2 hg hwb hr 0).2
  have hW : W1Odd (v ++ [Digit.two]) = false := by simpa [W1Odd] using hph
  have hc : (SurgicalAlt.altTypeOf (v ++ [Digit.two])).bind (fun ty => SurgicalAlt.altP1Coeff (W1Odd (v ++ [Digit.two])) ty) = some (0, 0, 0, 1) := by
    simp [SurgicalAlt.altTypeOf, hW, SurgicalAlt.altP1Coeff]
  have ht : altOff (v ++ [Digit.two]) (0, 0, 0, 1) = (texV2 (parentsAt (v ++ [Digit.two])).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2]
  have hη : altAff (v ++ [Digit.two]) (0, 0, 0, 1) = ((parentsAt (v ++ [Digit.two])).even.num, -(parentsAt (v ++ [Digit.two])).even.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  obtain ⟨k, hk⟩ := hk v2 (by rw [hr])
  have hov := hov v v2 hr
  refine ⟨_, AltSevenC.seven_ef2c D.S (fun u => (below f (v ++ [Digit.two]) u).tOdd) (fun u => (below f (v ++ [Digit.two]) u).tEven)
    (fun u => (below f (v ++ [Digit.two]) u).aOdd) (fun u => (below f (v ++ [Digit.two]) u).aEven) (fun u => (below f (v ++ [Digit.two]) u).lEven) (v ++ [Digit.two]) v v2 hph (by simp) hr hp hq
    (parentsAt v).odd.num (parentsAt v).odd.den (parentsAt v).even.num (parentsAt v).even.den hpar2 hqe2
    ⟨by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine],
      by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]⟩
    (f v1).tOdd (f v2).tEven βP βQ ((f v).aOdd.val 0) βP2 βQ2
    (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb2]; exact hhQ) (by simp only [hb2]; exact ⟨k, hk⟩) (by simp only [hb1, hb2]; exact hcompat) hcP2 hcQ2 hhP2 hhQ2
    (by simp only [hb1]; exact fun x hx => (hhH x hx).2) (by simp only [hb1])
    (by simp only [hb1]; exact hd0) (by simp only [hb1]; exact hd3) (by simp only [hb1]; exact hd4) (by simp only [hb1]; exact hd5)
    (by simp only [hb1]; exact h0p) (by simp only [hb1]; exact h3p) (by simp only [hb1]; exact h4p) (by simp only [hb1]; exact h5p)
    _ hm1a hm1b (by simp only [hb1]; exact hd1) (by simp only [hb1]; exact h1p) _ hm2a hm2b (by simp only [hb1]; exact hd2) (by simp only [hb1]; exact h2p)
    (fun j hj => hpc_even D.S _ _ _ _ _ (v ++ [Digit.two]) v v2 _ _ _ hr (by simp) hc ht hη (by simp only [hb1]; exact hdP)
      (by simp only [hb2]; exact hdQ) j hj (hpc j hj)) hov⟩

/-- Case 3 from the family, even alternate child, `W_1` odd, last digit `2`. -/
theorem familyC_of2 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (v : Word) (hg : GoodBelow D f (v ++ [Digit.two]).length) (hv : ¬ IsBase v)
    (hph : phase (v ++ [Digit.two]) = 1) (hvc : v.getLast? = some Digit.two) (hlS : D.lSides = paperLSides)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltEvenPieces D.S (fun u => (below f (v ++ [Digit.two]) u).tOdd) (fun u => (below f (v ++ [Digit.two]) u).tEven)
      (fun u => (below f (v ++ [Digit.two]) u).aOdd) (fun u => (below f (v ++ [Digit.two]) u).aEven)
      (fun u => (below f (v ++ [Digit.two]) u).lEven) (v ++ [Digit.two])) 6 j)
    (hk : ∀ u2, (regsAt (v ++ [Digit.two])).2 = some u2 → ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ (v ++ [Digit.two]) ∈ tEvenSet u2 →
      (f u2).tEven.val (x + shiftQ (v ++ [Digit.two])) - (f u2).tEven.val x - ClosedPathSum.dot2 (affS (v ++ [Digit.two])) x = k)
    (hov : ∀ u1 u2, regsAt (v ++ [Digit.two]) = (some u1, some u2) → AltPiecesAgree.SixOverlaps (altEvenD (v ++ [Digit.two])) (altEvenR (v ++ [Digit.two]))
      (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) ChildGlue.dblEven) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltEvenPieces D.S (fun u => (below f (v ++ [Digit.two]) u).tOdd) (fun u => (below f (v ++ [Digit.two]) u).tEven)
      (fun u => (below f (v ++ [Digit.two]) u).aOdd) (fun u => (below f (v ++ [Digit.two]) u).aEven)
      (fun u => (below f (v ++ [Digit.two]) u).lEven) (v ++ [Digit.two])) κ := by
  have hlt : v.length < (v ++ [Digit.two]).length := by simp
  have hgv : GoodBelow D f v.length := fun u hu => hg u (lt_trans hu hlt)
  obtain ⟨⟨v1, hv1⟩, ⟨v2, hv2'⟩⟩ := JointRot.regs_some v hv
  have hrv : regsAt v = (some v1, some v2) := Prod.ext hv1 hv2'
  have l1 : v1.length < v.length := JointInduction.regsAt_lt v v1 (Or.inl hv1)
  have l2 : v2.length < v.length := JointInduction.regsAt_lt v v2 (Or.inr hv2')
  have hr : regsAt (v ++ [Digit.two]) = (some v, some v2) := by
    simp [WeakStepPaper.regsAt_snoc, SurgicalWeak.regStep, hrv]
  have hu1 : v.length < (v ++ [Digit.two]).length := hlt
  have hu2 : v2.length < (v ++ [Digit.two]).length := by simp; omega
  have hb1 : below f (v ++ [Digit.two]) v = f v := JointRot.below_of_lt f _ _ hu1
  have hb2 : below f (v ++ [Digit.two]) v2 = f v2 := JointRot.below_of_lt f _ _ hu2
  have hbv : below f (v ++ [Digit.two]) v = f v := JointRot.below_of_lt f _ _ hlt
  have hp := (WeakStepAssembly.regsAt_parents (v ++ [Digit.two])).1 v (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents (v ++ [Digit.two])).2 v2 (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := regOdd_data D hS hA f _ hg v hu1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := regEven_data D hS hA f _ hg v2 hu2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdP] at hhP
  rw [hdQ] at hhQ
  obtain ⟨βP2, -, hcP2, hhP2⟩ := regOdd_data D hS hA f _ hgv v1 l1
  obtain ⟨βQ2, -, hcQ2, hhQ2⟩ := regEven_data D hS hA f _ hgv v2 l2
  have hp2 := (WeakStepAssembly.regsAt_parents v).1 v1 (by rw [hrv])
  have hq2 := (WeakStepAssembly.regsAt_parents v).2 v2 (by rw [hrv])
  rw [← hp2] at hcP2 hhP2
  rw [← hq2] at hcQ2 hhQ2
  have hphv : phase v = 1 := by
    simp only [phase, List.count_append] at hph ⊢
    simp at hph
    omega
  have hhH := aOdd_halfTurn D hS hA f _ hg v hlt
  have hD : altD v true = (2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + (2 : ℤ) • ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den) + ((1 : ℤ), (-1 : ℤ)) := by
    simp [altD, W1Odd, hphv, vP1, vP2, vQ2, texV1Odd, texV2]
  rw [hD] at hhH
  have hRP := (parent_respects D f _ hg v hlt hv).1
  have hmem := (AltPiecesAgree.aOdd_mem D.S (fun v' => (below f v v').tOdd) (fun v' => (below f v v').tEven)
    (fun v' => (below f v v').aOdd) (fun v' => (below f v v').aEven) (fun v' => (below f v v').lOdd) v v1 v2 hrv)
  simp only [JointRot.below_of_lt f v v1 l1, JointRot.below_of_lt f v v2 l2] at hmem
  obtain ⟨hmA, hmB, hmC, hmD⟩ := hmem
  obtain ⟨hd0, h0p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altOddD v).getD 0 0) ((altOddAff v).getD 0 0) 0 0 hmA
    (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  obtain ⟨hd3, h3p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altOddD v).getD 3 0) ((altOddAff v).getD 3 0) (((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den)) (((parentsAt v).odd.num, -(parentsAt v).odd.den) + ((parentsAt v).even.num, -(parentsAt v).even.den)) hmB
    (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA] <;> ring)
  obtain ⟨hd4, h4p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altOddR v).getD 0 0) ((altOddAff v).getD 4 0) (2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) 0 hmC
    (by ext <;> simp [altOddR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  obtain ⟨hd5, h5p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altOddR v).getD 1 0) ((altOddAff v).getD 5 0) ((2 : ℤ) • ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) - ((parentsAt v).even.den, (parentsAt v).even.num)) ((2 : ℤ) • ((parentsAt v).odd.num, -(parentsAt v).odd.den)) hmD
    (by ext <;> simp [altOddR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  have hv' : v = v1 ++ [Digit.two] := by
    obtain ⟨u, d, rfl⟩ : ∃ u d, v = u ++ [d] := by
      cases v using List.reverseRecOn with
      | nil => exact (hv (Or.inl rfl)).elim
      | append_singleton u d => exact ⟨u, d, rfl⟩
    simp at hvc
    subst hvc
    have e := ConnectedAltL.regs_pre_fst u Digit.two (by decide)
    rw [hv1] at e
    cases e
    rfl
  have hdl : v.dropLast = v1 := by rw [hv']; simp
  have hJl := (hgv v1 l1).1.2.2.2
  have hdef : OddLDefined v1 := JointRot.oddLDefined_of_mem v1 (by
    by_contra hc; simp only [not_exists, not_and, not_not] at hc; exact hv (Or.inr (Or.inr fun d hd => by rw [hv'] at hd; simp at hd; rcases hd with hd | rfl; exacts [hc d hd, rfl])))
  have hWl : W1Odd v1 = true := by
    have := hphv
    rw [hv'] at this
    simp only [W1Odd, phase, List.count_append] at this ⊢
    simp at this ⊢
    omega
  have hmL := AltSevenFamilyC.aOdd_memL D.S (fun v' => (below f v v').tOdd) (fun v' => (below f v v').tEven)
    (fun v' => (below f v v').aOdd) (fun v' => (below f v v').aEven) (fun v' => (below f v v').lOdd) v hvc
  simp only [hdl, JointRot.below_of_lt f v v1 l1] at hmL
  obtain ⟨hmLa, hmLb⟩ := hmL
  obtain ⟨-, c1, hc1⟩ := ((hJl.1 false true hdef).2)
  rw [hlS] at hc1
  obtain ⟨hd1, h1p⟩ := AltSevenFamilyC.L_sub _ (f v1).tOdd _ _ hRP ((altOddD v).getD 1 0) ((altOddAff v).getD 1 0) (((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) - ((parentsAt v).even.den, (parentsAt v).even.num)) ((parentsAt v).odd.num, -(parentsAt v).odd.den)
    hmLa (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
    {y | ∃ s ∈ paperLSides true (W1Odd v1) false true, y ∈ placedSites (sideString (hWordOf v1 false) (vWordOf v1 false) 0 s)} c1
    (fun y ⟨s, hs, hy⟩ => hc1 s hs y hy)
  have hm1a : ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((1 : ℤ), (0 : ℤ)) ∈ {y | ∃ s ∈ paperLSides true (W1Odd v1) false true, y ∈ placedSites (sideString (hWordOf v1 false) (vWordOf v1 false) 0 s)} := by
    refine ⟨.vMinus, by simp [paperLSides, hWl], ?_⟩
    have := ConnectedAltL.odd_side_corners v1 |>.2.2.2.2.1
    rw [← hv'] at this
    exact this
  have hm1b : (0 : ℤ × ℤ) ∈ {y | ∃ s ∈ paperLSides true (W1Odd v1) false true, y ∈ placedSites (sideString (hWordOf v1 false) (vWordOf v1 false) 0 s)} := by
    refine ⟨.hPlus, by simp [paperLSides, hWl], ?_⟩
    have := ConnectedAltL.odd_side_corners v1 |>.1
    exact this
  obtain ⟨-, c2, hc2⟩ := ((hJl.1 true true hdef).2)
  rw [hlS] at hc2
  obtain ⟨hd2, h2p⟩ := AltSevenFamilyC.L_sub _ (f v1).tOdd _ _ hRP ((altOddD v).getD 2 0) ((altOddAff v).getD 2 0) (((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den)) ((parentsAt v).even.num, -(parentsAt v).even.den)
    hmLb (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
    {y | ∃ s ∈ paperLSides true (W1Odd v1) true true, y ∈ placedSites (sideString (hWordOf v1 false) (vWordOf v1 false) 0 s)} c2
    (fun y ⟨s, hs, hy⟩ => hc2 s hs y hy)
  have hm2a : (2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) - ((0 : ℤ), (1 : ℤ)) ∈ {y | ∃ s ∈ paperLSides true (W1Odd v1) true true, y ∈ placedSites (sideString (hWordOf v1 false) (vWordOf v1 false) 0 s)} := by
    refine ⟨.vPlus, by simp [paperLSides, hWl], ?_⟩
    have := ConnectedAltL.odd_side_corners v1 |>.2.2.2.2.2
    rw [← hv'] at this
    exact this
  have hm2b : (2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((1 : ℤ), (-1 : ℤ)) ∈ {y | ∃ s ∈ paperLSides true (W1Odd v1) true true, y ∈ placedSites (sideString (hWordOf v1 false) (vWordOf v1 false) 0 s)} := by
    refine ⟨.vPlus, by simp [paperLSides, hWl], ?_⟩
    have := AltLSides.odd_side_right v1 |>.1
    rw [← hv'] at this
    exact this
  have hpar2 := (parentsAt_valid v).odd_parity
  have hqe2 := (parentsAt_valid v).even_parity
  unfold Fraction.Odd at hpar2
  unfold Fraction.Even at hqe2
  have hwb : ¬ IsBase (v ++ [Digit.two]) := by
    rintro (h | h | h)
    · simp at h
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inl fun d hd => h d (by simp [hd])))
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inr fun d hd => h d (by simp [hd])))
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ v v2 hg hwb hr 0).2
  have hW : W1Odd (v ++ [Digit.two]) = true := by simp [W1Odd, hph]
  have hc : (SurgicalAlt.altTypeOf (v ++ [Digit.two])).bind (fun ty => SurgicalAlt.altP1Coeff (W1Odd (v ++ [Digit.two])) ty) = some (0, 0, 2, 1) := by
    simp [SurgicalAlt.altTypeOf, hW, SurgicalAlt.altP1Coeff]
  have ht : altOff (v ++ [Digit.two]) (0, 0, 2, 1) = (texV1Even (parentsAt (v ++ [Digit.two])).even + texV1Even (parentsAt (v ++ [Digit.two])).even + texV2 (parentsAt (v ++ [Digit.two])).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2] <;> ring
  have hη : altAff (v ++ [Digit.two]) (0, 0, 2, 1) = ((parentsAt (v ++ [Digit.two])).even.num, -(parentsAt (v ++ [Digit.two])).even.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  obtain ⟨k, hk⟩ := hk v2 (by rw [hr])
  have hov := hov v v2 hr
  refine ⟨_, AltSevenC.seven_of2c D.S (fun u => (below f (v ++ [Digit.two]) u).tOdd) (fun u => (below f (v ++ [Digit.two]) u).tEven)
    (fun u => (below f (v ++ [Digit.two]) u).aOdd) (fun u => (below f (v ++ [Digit.two]) u).aEven) (fun u => (below f (v ++ [Digit.two]) u).lEven) (v ++ [Digit.two]) v v2 hph (by simp) hr hp hq
    (parentsAt v).odd.num (parentsAt v).odd.den (parentsAt v).even.num (parentsAt v).even.den hpar2 hqe2
    ⟨by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine],
      by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]⟩
    (f v1).tOdd (f v2).tEven βP βQ ((f v).aOdd.val 0) βP2 βQ2
    (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb2]; exact hhQ) (by simp only [hb2]; exact ⟨k, hk⟩) (by simp only [hb1, hb2]; exact hcompat) hcP2 hcQ2 hhP2 hhQ2
    (by simp only [hb1]; exact fun x hx => (hhH x hx).2) (by simp only [hb1])
    (by simp only [hb1]; exact hd0) (by simp only [hb1]; exact hd3) (by simp only [hb1]; exact hd4) (by simp only [hb1]; exact hd5)
    (by simp only [hb1]; exact h0p) (by simp only [hb1]; exact h3p) (by simp only [hb1]; exact h4p) (by simp only [hb1]; exact h5p)
    _ hm1a hm1b (by simp only [hb1]; exact hd1) (by simp only [hb1]; exact h1p) _ hm2a hm2b (by simp only [hb1]; exact hd2) (by simp only [hb1]; exact h2p)
    (fun j hj => hpc_even D.S _ _ _ _ _ (v ++ [Digit.two]) v v2 _ _ _ hr (by simp) hc ht hη (by simp only [hb1]; exact hdP)
      (by simp only [hb2]; exact hdQ) j hj (hpc j hj)) hov⟩

/-- Case 3 from the family, odd alternate child, `W_1` even, last digit `3`. -/
theorem familyC_oe3 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (v : Word) (hg : GoodBelow D f (v ++ [Digit.three]).length) (hv : ¬ IsBase v)
    (hph : phase (v ++ [Digit.three]) ≠ 1) (hvc : v.getLast? = some Digit.three) (hlS : D.lSides = paperLSides)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltOddPieces D.S (fun u => (below f (v ++ [Digit.three]) u).tOdd) (fun u => (below f (v ++ [Digit.three]) u).tEven)
      (fun u => (below f (v ++ [Digit.three]) u).aOdd) (fun u => (below f (v ++ [Digit.three]) u).aEven)
      (fun u => (below f (v ++ [Digit.three]) u).lOdd) (v ++ [Digit.three])) 6 j)
    (hk : ∀ u1, (regsAt (v ++ [Digit.three])).1 = some u1 → ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP (v ++ [Digit.three]) ∈ tOddSet u1 →
      (f u1).tOdd.val (x + shiftP (v ++ [Digit.three])) - (f u1).tOdd.val x - ClosedPathSum.dot2 (affS (v ++ [Digit.three])) x = k)
    (hov : ∀ u1 u2, regsAt (v ++ [Digit.three]) = (some u1, some u2) → AltPiecesAgree.SixOverlaps (altOddD (v ++ [Digit.three])) (altOddR (v ++ [Digit.three]))
      (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) ChildGlue.dblEven) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltOddPieces D.S (fun u => (below f (v ++ [Digit.three]) u).tOdd) (fun u => (below f (v ++ [Digit.three]) u).tEven)
      (fun u => (below f (v ++ [Digit.three]) u).aOdd) (fun u => (below f (v ++ [Digit.three]) u).aEven)
      (fun u => (below f (v ++ [Digit.three]) u).lOdd) (v ++ [Digit.three])) κ := by
  have hlt : v.length < (v ++ [Digit.three]).length := by simp
  have hgv : GoodBelow D f v.length := fun u hu => hg u (lt_trans hu hlt)
  obtain ⟨⟨v1, hv1⟩, ⟨v2, hv2'⟩⟩ := JointRot.regs_some v hv
  have hrv : regsAt v = (some v1, some v2) := Prod.ext hv1 hv2'
  have l1 : v1.length < v.length := JointInduction.regsAt_lt v v1 (Or.inl hv1)
  have l2 : v2.length < v.length := JointInduction.regsAt_lt v v2 (Or.inr hv2')
  have hr : regsAt (v ++ [Digit.three]) = (some v1, some v) := by
    simp [WeakStepPaper.regsAt_snoc, SurgicalWeak.regStep, hrv]
  have hu1 : v1.length < (v ++ [Digit.three]).length := by simp; omega
  have hu2 : v.length < (v ++ [Digit.three]).length := hlt
  have hb1 : below f (v ++ [Digit.three]) v1 = f v1 := JointRot.below_of_lt f _ _ hu1
  have hb2 : below f (v ++ [Digit.three]) v = f v := JointRot.below_of_lt f _ _ hu2
  have hbv : below f (v ++ [Digit.three]) v = f v := JointRot.below_of_lt f _ _ hlt
  have hp := (WeakStepAssembly.regsAt_parents (v ++ [Digit.three])).1 v1 (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents (v ++ [Digit.three])).2 v (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := regOdd_data D hS hA f _ hg v1 hu1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := regEven_data D hS hA f _ hg v hu2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdP] at hhP
  rw [hdQ] at hhQ
  obtain ⟨βP2, -, hcP2, hhP2⟩ := regOdd_data D hS hA f _ hgv v1 l1
  obtain ⟨βQ2, -, hcQ2, hhQ2⟩ := regEven_data D hS hA f _ hgv v2 l2
  have hp2 := (WeakStepAssembly.regsAt_parents v).1 v1 (by rw [hrv])
  have hq2 := (WeakStepAssembly.regsAt_parents v).2 v2 (by rw [hrv])
  rw [← hp2] at hcP2 hhP2
  rw [← hq2] at hcQ2 hhQ2
  have hphv : phase v ≠ 1 := by
    simp only [phase, List.count_append] at hph ⊢
    simp at hph
    omega
  have hhH := aEven_halfTurn D hS hA f _ hg v hlt
  have hD : altD v false = (2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + (2 : ℤ) • ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den) + ((1 : ℤ), (-1 : ℤ)) := by
    simp [altD, W1Odd, hphv, vP1, vP2, vQ2, texV1Odd, texV2]
  rw [hD] at hhH
  have hRP := (parent_respects D f _ hg v hlt hv).2
  have hmem := (AltPiecesAgree.aEven_mem D.S (fun v' => (below f v v').tOdd) (fun v' => (below f v v').tEven)
    (fun v' => (below f v v').aOdd) (fun v' => (below f v v').aEven) (fun v' => (below f v v').lEven) v v1 v2 hrv)
  simp only [JointRot.below_of_lt f v v1 l1, JointRot.below_of_lt f v v2 l2] at hmem
  obtain ⟨hmA, hmB, hmC, hmD⟩ := hmem
  obtain ⟨hd1, h1p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altEvenD v).getD 1 0) ((altEvenAff v).getD 1 0) (((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) - ((parentsAt v).even.den, (parentsAt v).even.num)) ((parentsAt v).odd.num, -(parentsAt v).odd.den) hmA
    (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd2, h2p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altEvenD v).getD 2 0) ((altEvenAff v).getD 2 0) ((2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den)) ((parentsAt v).odd.num, -(parentsAt v).odd.den) hmB
    (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd4, h4p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altEvenR v).getD 0 0) ((altEvenAff v).getD 4 0) ((parentsAt v).even.den, (parentsAt v).even.num) 0 hmC
    (by ext <;> simp [altEvenR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd5, h5p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altEvenR v).getD 1 0) ((altEvenAff v).getD 5 0) (((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) - ((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den)) (((parentsAt v).odd.num, -(parentsAt v).odd.den) + ((parentsAt v).even.num, -(parentsAt v).even.den)) hmD
    (by ext <;> simp [altEvenR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA]; ring)
  have hv' : v = v2 ++ [Digit.three] := by
    obtain ⟨u, d, rfl⟩ : ∃ u d, v = u ++ [d] := by
      cases v using List.reverseRecOn with
      | nil => exact (hv (Or.inl rfl)).elim
      | append_singleton u d => exact ⟨u, d, rfl⟩
    simp at hvc
    subst hvc
    have e := ConnectedAltL.regs_pre_snd u Digit.three (by decide)
    rw [hv2'] at e
    cases e
    rfl
  have hdl : v.dropLast = v2 := by rw [hv']; simp
  have hJl := (hgv v2 l2).1.2.2.2
  have hdef : EvenLDefined v2 := JointRot.evenLDefined_of_mem v2 (by
    by_contra hc; simp only [not_exists, not_and, not_not] at hc; exact hv (Or.inr (Or.inl fun d hd => by rw [hv'] at hd; simp at hd; rcases hd with hd | rfl; exacts [hc d hd, rfl])))
  have hWl : W1Odd v2 = false := by
    have := hphv
    rw [hv'] at this
    simp only [W1Odd, phase, List.count_append] at this ⊢
    simp at this ⊢
    omega
  have hmL := AltSevenFamilyC.aEven_memL D.S (fun v' => (below f v v').tOdd) (fun v' => (below f v v').tEven)
    (fun v' => (below f v v').aOdd) (fun v' => (below f v v').aEven) (fun v' => (below f v v').lEven) v hvc
  simp only [hdl, JointRot.below_of_lt f v v2 l2] at hmL
  obtain ⟨hmLa, hmLb⟩ := hmL
  obtain ⟨-, c0, hc0⟩ := ((hJl.2 true true hdef).2)
  rw [hlS] at hc0
  obtain ⟨hd0, h0p⟩ := AltSevenFamilyC.L_sub _ (f v2).tEven _ _ hRP ((altEvenD v).getD 0 0) ((altEvenAff v).getD 0 0) 0 0
    hmLa (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
    {y | ∃ s ∈ paperLSides false (W1Odd v2) true true, y ∈ placedSites (sideString (hWordOf v2 true) (vWordOf v2 true) 0 s)} c0
    (fun y ⟨s, hs, hy⟩ => hc0 s hs y hy)
  have hm0a : ((parentsAt v).even.den, (parentsAt v).even.num) ∈ {y | ∃ s ∈ paperLSides false (W1Odd v2) true true, y ∈ placedSites (sideString (hWordOf v2 true) (vWordOf v2 true) 0 s)} := by
    refine ⟨.hPlus, by simp [paperLSides, printedEvenSides, hWl], ?_⟩
    have := ConnectedAltL.even_side_corners v2 |>.2.1
    rw [← hv'] at this
    exact this
  have hm0b : ((1 : ℤ), (0 : ℤ)) ∈ {y | ∃ s ∈ paperLSides false (W1Odd v2) true true, y ∈ placedSites (sideString (hWordOf v2 true) (vWordOf v2 true) 0 s)} := by
    refine ⟨.vMinus, by simp [paperLSides, printedEvenSides, hWl], ?_⟩
    have := AltLSides.even_side_more v2 |>.1
    exact this
  obtain ⟨-, c3, hc3⟩ := ((hJl.2 false true hdef).2)
  rw [hlS] at hc3
  obtain ⟨hd3, h3p⟩ := AltSevenFamilyC.L_sub _ (f v2).tEven _ _ hRP ((altEvenD v).getD 3 0) ((altEvenAff v).getD 3 0) ((2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + (2 : ℤ) • ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) - ((parentsAt v).even.den, (parentsAt v).even.num)) ((2 : ℤ) • ((parentsAt v).odd.num, -(parentsAt v).odd.den))
    hmLb (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA] <;> ring)
    {y | ∃ s ∈ paperLSides false (W1Odd v2) false true, y ∈ placedSites (sideString (hWordOf v2 true) (vWordOf v2 true) 0 s)} c3
    (fun y ⟨s, hs, hy⟩ => hc3 s hs y hy)
  have hm3a : ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den) + ((1 : ℤ), (-1 : ℤ)) ∈ {y | ∃ s ∈ paperLSides false (W1Odd v2) false true, y ∈ placedSites (sideString (hWordOf v2 true) (vWordOf v2 true) 0 s)} := by
    refine ⟨.hMinus, by simp [paperLSides, printedEvenSides, hWl], ?_⟩
    have := ConnectedAltL.even_side_corners v2 |>.2.2
    rw [← hv'] at this
    exact this
  have hm3b : ((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈ {y | ∃ s ∈ paperLSides false (W1Odd v2) false true, y ∈ placedSites (sideString (hWordOf v2 true) (vWordOf v2 true) 0 s)} := by
    refine ⟨.vPlus, by simp [paperLSides, printedEvenSides, hWl], ?_⟩
    have := AltLSides.even_side_more v2 |>.2.2.2.2.1
    rw [← hv'] at this
    exact this
  obtain ⟨b4, h4p⟩ := h4p
  have h4p' : ∀ x, x - ((parentsAt v).even.den, (parentsAt v).even.num) ∈ (↑(f v1).tOdd.dom : Set (ℤ × ℤ)) →
      (f v).aEven.val x = (f v1).tOdd.val (x - ((parentsAt v).even.den, (parentsAt v).even.num)) + dotS 0 x + ((b4 + βP2) - βP2) := fun x hx => by
    rw [h4p x hx]; ring
  have hpar2 := (parentsAt_valid v).odd_parity
  have hqe2 := (parentsAt_valid v).even_parity
  unfold Fraction.Odd at hpar2
  unfold Fraction.Even at hqe2
  have hwb : ¬ IsBase (v ++ [Digit.three]) := by
    rintro (h | h | h)
    · simp at h
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inl fun d hd => h d (by simp [hd])))
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inr fun d hd => h d (by simp [hd])))
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ v1 v hg hwb hr 0).1
  have hW : W1Odd (v ++ [Digit.three]) = false := by simpa [W1Odd] using hph
  have hc : (SurgicalAlt.altTypeOf (v ++ [Digit.three])).bind (fun ty => SurgicalAlt.altQ1Coeff (W1Odd (v ++ [Digit.three])) ty) = some (0, 1, 1, 0) := by
    simp [SurgicalAlt.altTypeOf, hW, SurgicalAlt.altQ1Coeff]
  have ht : altOff (v ++ [Digit.three]) (0, 1, 1, 0) = (texV2 (parentsAt (v ++ [Digit.three])).odd + texV1Even (parentsAt (v ++ [Digit.three])).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2]
  have hη : altAff (v ++ [Digit.three]) (0, 1, 1, 0) = ((parentsAt (v ++ [Digit.three])).odd.num, -(parentsAt (v ++ [Digit.three])).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  obtain ⟨k, hk⟩ := hk v1 (by rw [hr])
  have hov := hov v1 v hr
  refine ⟨_, AltSevenC.seven_oe3c D.S (fun u => (below f (v ++ [Digit.three]) u).tOdd) (fun u => (below f (v ++ [Digit.three]) u).tEven)
    (fun u => (below f (v ++ [Digit.three]) u).aOdd) (fun u => (below f (v ++ [Digit.three]) u).aEven) (fun u => (below f (v ++ [Digit.three]) u).lOdd) (v ++ [Digit.three]) v1 v hph (by simp) hr hp hq
    (parentsAt v).odd.num (parentsAt v).odd.den (parentsAt v).even.num (parentsAt v).even.den hpar2 hqe2
    ⟨by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine],
      by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]⟩
    (f v1).tOdd (f v2).tEven βP βQ (b4 + βP2) βP2 βQ2
    (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb1]; exact hhP) (by simp only [hb1]; exact ⟨k, hk⟩) (by simp only [hb1, hb2]; exact hcompat) hcP2 hcQ2 hhP2 hhQ2
    (by simp only [hb2]; exact fun x hx => (hhH x hx).2)
    (by simp only [hb2]; exact hd1) (by simp only [hb2]; exact hd2) (by simp only [hb2]; exact hd4) (by simp only [hb2]; exact hd5)
    (by simp only [hb2]; exact h1p) (by simp only [hb2]; exact h2p) (by simp only [hb2]; exact h4p') (by simp only [hb2]; exact h5p)
    _ hm0a hm0b (by simp only [hb2]; exact hd0) (by simp only [hb2]; exact h0p) _ hm3a hm3b (by simp only [hb2]; exact hd3) (by simp only [hb2]; exact h3p)
    (fun j hj => hpc_odd D.S _ _ _ _ _ (v ++ [Digit.three]) v1 v _ _ _ hr (by simp) hc ht hη (by simp only [hb1]; exact hdP)
      (by simp only [hb2]; exact hdQ) j hj (hpc j hj)) hov⟩

/-- Case 3 from the family, odd alternate child, `W_1` odd, last digit `3`. -/
theorem familyC_oo3 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (v : Word) (hg : GoodBelow D f (v ++ [Digit.three]).length) (hv : ¬ IsBase v)
    (hph : phase (v ++ [Digit.three]) = 1) (hvc : v.getLast? = some Digit.three) (hlS : D.lSides = paperLSides)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltOddPieces D.S (fun u => (below f (v ++ [Digit.three]) u).tOdd) (fun u => (below f (v ++ [Digit.three]) u).tEven)
      (fun u => (below f (v ++ [Digit.three]) u).aOdd) (fun u => (below f (v ++ [Digit.three]) u).aEven)
      (fun u => (below f (v ++ [Digit.three]) u).lOdd) (v ++ [Digit.three])) 6 j)
    (hk : ∀ u1, (regsAt (v ++ [Digit.three])).1 = some u1 → ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP (v ++ [Digit.three]) ∈ tOddSet u1 →
      (f u1).tOdd.val (x + shiftP (v ++ [Digit.three])) - (f u1).tOdd.val x - ClosedPathSum.dot2 (affS (v ++ [Digit.three])) x = k)
    (hov : ∀ u1 u2, regsAt (v ++ [Digit.three]) = (some u1, some u2) → AltPiecesAgree.SixOverlaps (altOddD (v ++ [Digit.three])) (altOddR (v ++ [Digit.three]))
      (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) ChildGlue.dblEven) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltOddPieces D.S (fun u => (below f (v ++ [Digit.three]) u).tOdd) (fun u => (below f (v ++ [Digit.three]) u).tEven)
      (fun u => (below f (v ++ [Digit.three]) u).aOdd) (fun u => (below f (v ++ [Digit.three]) u).aEven)
      (fun u => (below f (v ++ [Digit.three]) u).lOdd) (v ++ [Digit.three])) κ := by
  have hlt : v.length < (v ++ [Digit.three]).length := by simp
  have hgv : GoodBelow D f v.length := fun u hu => hg u (lt_trans hu hlt)
  obtain ⟨⟨v1, hv1⟩, ⟨v2, hv2'⟩⟩ := JointRot.regs_some v hv
  have hrv : regsAt v = (some v1, some v2) := Prod.ext hv1 hv2'
  have l1 : v1.length < v.length := JointInduction.regsAt_lt v v1 (Or.inl hv1)
  have l2 : v2.length < v.length := JointInduction.regsAt_lt v v2 (Or.inr hv2')
  have hr : regsAt (v ++ [Digit.three]) = (some v1, some v) := by
    simp [WeakStepPaper.regsAt_snoc, SurgicalWeak.regStep, hrv]
  have hu1 : v1.length < (v ++ [Digit.three]).length := by simp; omega
  have hu2 : v.length < (v ++ [Digit.three]).length := hlt
  have hb1 : below f (v ++ [Digit.three]) v1 = f v1 := JointRot.below_of_lt f _ _ hu1
  have hb2 : below f (v ++ [Digit.three]) v = f v := JointRot.below_of_lt f _ _ hu2
  have hbv : below f (v ++ [Digit.three]) v = f v := JointRot.below_of_lt f _ _ hlt
  have hp := (WeakStepAssembly.regsAt_parents (v ++ [Digit.three])).1 v1 (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents (v ++ [Digit.three])).2 v (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := regOdd_data D hS hA f _ hg v1 hu1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := regEven_data D hS hA f _ hg v hu2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdP] at hhP
  rw [hdQ] at hhQ
  obtain ⟨βP2, -, hcP2, hhP2⟩ := regOdd_data D hS hA f _ hgv v1 l1
  obtain ⟨βQ2, -, hcQ2, hhQ2⟩ := regEven_data D hS hA f _ hgv v2 l2
  have hp2 := (WeakStepAssembly.regsAt_parents v).1 v1 (by rw [hrv])
  have hq2 := (WeakStepAssembly.regsAt_parents v).2 v2 (by rw [hrv])
  rw [← hp2] at hcP2 hhP2
  rw [← hq2] at hcQ2 hhQ2
  have hphv : phase v = 1 := by
    simp only [phase, List.count_append] at hph ⊢
    simp at hph
    omega
  have hhH := aEven_halfTurn D hS hA f _ hg v hlt
  have hD : altD v false = (2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + (2 : ℤ) • ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + (2 : ℤ) • ((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den) + ((1 : ℤ), (-1 : ℤ)) := by
    simp [altD, W1Odd, hphv, vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2]
  rw [hD] at hhH
  have hRP := (parent_respects D f _ hg v hlt hv).2
  have hmem := (AltPiecesAgree.aEven_mem D.S (fun v' => (below f v v').tOdd) (fun v' => (below f v v').tEven)
    (fun v' => (below f v v').aOdd) (fun v' => (below f v v').aEven) (fun v' => (below f v v').lEven) v v1 v2 hrv)
  simp only [JointRot.below_of_lt f v v1 l1, JointRot.below_of_lt f v v2 l2] at hmem
  obtain ⟨hmA, hmB, hmC, hmD⟩ := hmem
  obtain ⟨hd1, h1p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altEvenD v).getD 1 0) ((altEvenAff v).getD 1 0) ((2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((parentsAt v).even.den, (parentsAt v).even.num)) ((parentsAt v).odd.num, -(parentsAt v).odd.den) hmA
    (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd2, h2p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altEvenD v).getD 2 0) ((altEvenAff v).getD 2 0) ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) ((parentsAt v).odd.num, -(parentsAt v).odd.den) hmB
    (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd4, h4p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altEvenR v).getD 0 0) ((altEvenAff v).getD 4 0) 0 0 hmC
    (by ext <;> simp [altEvenR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd5, h5p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altEvenR v).getD 1 0) ((altEvenAff v).getD 5 0) (((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + (2 : ℤ) • ((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den)) (((parentsAt v).odd.num, -(parentsAt v).odd.den) + ((parentsAt v).even.num, -(parentsAt v).even.den)) hmD
    (by ext <;> simp [altEvenR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA]; ring)
  have hv' : v = v2 ++ [Digit.three] := by
    obtain ⟨u, d, rfl⟩ : ∃ u d, v = u ++ [d] := by
      cases v using List.reverseRecOn with
      | nil => exact (hv (Or.inl rfl)).elim
      | append_singleton u d => exact ⟨u, d, rfl⟩
    simp at hvc
    subst hvc
    have e := ConnectedAltL.regs_pre_snd u Digit.three (by decide)
    rw [hv2'] at e
    cases e
    rfl
  have hdl : v.dropLast = v2 := by rw [hv']; simp
  have hJl := (hgv v2 l2).1.2.2.2
  have hdef : EvenLDefined v2 := JointRot.evenLDefined_of_mem v2 (by
    by_contra hc; simp only [not_exists, not_and, not_not] at hc; exact hv (Or.inr (Or.inl fun d hd => by rw [hv'] at hd; simp at hd; rcases hd with hd | rfl; exacts [hc d hd, rfl])))
  have hWl : W1Odd v2 = true := by
    have := hphv
    rw [hv'] at this
    simp only [W1Odd, phase, List.count_append] at this ⊢
    simp at this ⊢
    omega
  have hmL := AltSevenFamilyC.aEven_memL D.S (fun v' => (below f v v').tOdd) (fun v' => (below f v v').tEven)
    (fun v' => (below f v v').aOdd) (fun v' => (below f v v').aEven) (fun v' => (below f v v').lEven) v hvc
  simp only [hdl, JointRot.below_of_lt f v v2 l2] at hmL
  obtain ⟨hmLa, hmLb⟩ := hmL
  obtain ⟨-, c0, hc0⟩ := ((hJl.2 true true hdef).2)
  rw [hlS] at hc0
  obtain ⟨hd0, h0p⟩ := AltSevenFamilyC.L_sub _ (f v2).tEven _ _ hRP ((altEvenD v).getD 0 0) ((altEvenAff v).getD 0 0) (2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) 0
    hmLa (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
    {y | ∃ s ∈ paperLSides false (W1Odd v2) true true, y ∈ placedSites (sideString (hWordOf v2 true) (vWordOf v2 true) 0 s)} c0
    (fun y ⟨s, hs, hy⟩ => hc0 s hs y hy)
  have hm0a : (0 : ℤ × ℤ) ∈ {y | ∃ s ∈ paperLSides false (W1Odd v2) true true, y ∈ placedSites (sideString (hWordOf v2 true) (vWordOf v2 true) 0 s)} := by
    refine ⟨.hPlus, by simp [paperLSides, printedEvenSides, hWl], ?_⟩
    have := ConnectedAltL.even_side_corners v2 |>.1
    exact this
  have hm0b : ((parentsAt v).even.den, (parentsAt v).even.num) - ((0 : ℤ), (1 : ℤ)) ∈ {y | ∃ s ∈ paperLSides false (W1Odd v2) true true, y ∈ placedSites (sideString (hWordOf v2 true) (vWordOf v2 true) 0 s)} := by
    refine ⟨.vPlus, by simp [paperLSides, printedEvenSides, hWl], ?_⟩
    have := AltLSides.even_side_more v2 |>.2.2.1
    rw [← hv'] at this
    exact this
  obtain ⟨-, c3, hc3⟩ := ((hJl.2 false true hdef).2)
  rw [hlS] at hc3
  obtain ⟨hd3, h3p⟩ := AltSevenFamilyC.L_sub _ (f v2).tEven _ _ hRP ((altEvenD v).getD 3 0) ((altEvenAff v).getD 3 0) ((2 : ℤ) • ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((parentsAt v).even.den, (parentsAt v).even.num)) ((2 : ℤ) • ((parentsAt v).odd.num, -(parentsAt v).odd.den))
    hmLb (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA] <;> ring)
    {y | ∃ s ∈ paperLSides false (W1Odd v2) false true, y ∈ placedSites (sideString (hWordOf v2 true) (vWordOf v2 true) 0 s)} c3
    (fun y ⟨s, hs, hy⟩ => hc3 s hs y hy)
  have hm3a : ((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den) + ((1 : ℤ), (-1 : ℤ)) ∈ {y | ∃ s ∈ paperLSides false (W1Odd v2) false true, y ∈ placedSites (sideString (hWordOf v2 true) (vWordOf v2 true) 0 s)} := by
    refine ⟨.hMinus, by simp [paperLSides, printedEvenSides, hWl], ?_⟩
    have := AltLSides.even_side_more v2 |>.2.2.2.2.2
    rw [← hv'] at this
    exact this
  have hm3b : ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den) + ((1 : ℤ), (0 : ℤ)) ∈ {y | ∃ s ∈ paperLSides false (W1Odd v2) false true, y ∈ placedSites (sideString (hWordOf v2 true) (vWordOf v2 true) 0 s)} := by
    refine ⟨.vMinus, by simp [paperLSides, printedEvenSides, hWl], ?_⟩
    have := AltLSides.even_side_more v2 |>.2.1
    rw [← hv'] at this
    exact this
  obtain ⟨b4, h4p⟩ := h4p
  have h4p' : ∀ x, x - 0 ∈ (↑(f v1).tOdd.dom : Set (ℤ × ℤ)) →
      (f v).aEven.val x = (f v1).tOdd.val (x - 0) + dotS 0 x + ((b4 + βP2) - βP2) := fun x hx => by
    rw [h4p x hx]; ring
  have hpar2 := (parentsAt_valid v).odd_parity
  have hqe2 := (parentsAt_valid v).even_parity
  unfold Fraction.Odd at hpar2
  unfold Fraction.Even at hqe2
  have hwb : ¬ IsBase (v ++ [Digit.three]) := by
    rintro (h | h | h)
    · simp at h
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inl fun d hd => h d (by simp [hd])))
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inr fun d hd => h d (by simp [hd])))
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ v1 v hg hwb hr 0).1
  have hW : W1Odd (v ++ [Digit.three]) = true := by simp [W1Odd, hph]
  have hc : (SurgicalAlt.altTypeOf (v ++ [Digit.three])).bind (fun ty => SurgicalAlt.altQ1Coeff (W1Odd (v ++ [Digit.three])) ty) = some (1, 1, -1, 0) := by
    simp [SurgicalAlt.altTypeOf, hW, SurgicalAlt.altQ1Coeff]
  have ht : altOff (v ++ [Digit.three]) (1, 1, -1, 0) = (texV1Odd (parentsAt (v ++ [Digit.three])).odd + texV2 (parentsAt (v ++ [Digit.three])).odd - texV1Even (parentsAt (v ++ [Digit.three])).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2] <;> ring
  have hη : altAff (v ++ [Digit.three]) (1, 1, -1, 0) = ((parentsAt (v ++ [Digit.three])).odd.num, -(parentsAt (v ++ [Digit.three])).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  obtain ⟨k, hk⟩ := hk v1 (by rw [hr])
  have hov := hov v1 v hr
  refine ⟨_, AltSevenC.seven_oo3c D.S (fun u => (below f (v ++ [Digit.three]) u).tOdd) (fun u => (below f (v ++ [Digit.three]) u).tEven)
    (fun u => (below f (v ++ [Digit.three]) u).aOdd) (fun u => (below f (v ++ [Digit.three]) u).aEven) (fun u => (below f (v ++ [Digit.three]) u).lOdd) (v ++ [Digit.three]) v1 v hph (by simp) hr hp hq
    (parentsAt v).odd.num (parentsAt v).odd.den (parentsAt v).even.num (parentsAt v).even.den hpar2 hqe2
    ⟨by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine],
      by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]⟩
    (f v1).tOdd (f v2).tEven βP βQ (b4 + βP2) βP2 βQ2
    (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb1]; exact hhP) (by simp only [hb1]; exact ⟨k, hk⟩) (by simp only [hb1, hb2]; exact hcompat) hcP2 hcQ2 hhP2 hhQ2
    (by simp only [hb2]; exact fun x hx => (hhH x hx).2)
    (by simp only [hb2]; exact hd1) (by simp only [hb2]; exact hd2) (by simp only [hb2]; exact hd4) (by simp only [hb2]; exact hd5)
    (by simp only [hb2]; exact h1p) (by simp only [hb2]; exact h2p) (by simp only [hb2]; exact h4p') (by simp only [hb2]; exact h5p)
    _ hm0a hm0b (by simp only [hb2]; exact hd0) (by simp only [hb2]; exact h0p) _ hm3a hm3b (by simp only [hb2]; exact hd3) (by simp only [hb2]; exact h3p)
    (fun j hj => hpc_odd D.S _ _ _ _ _ (v ++ [Digit.three]) v1 v _ _ _ hr (by simp) hc ht hη (by simp only [hb1]; exact hdP)
      (by simp only [hb2]; exact hdQ) j hj (hpc j hj)) hov⟩

end FLatticePaper.Tiles.AltSevenFamilyC
