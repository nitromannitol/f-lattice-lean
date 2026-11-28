import FLatticePaper.Tiles.AltSeven
import FLatticePaper.Tiles.TileTranslationStd
import FLatticePaper.Tiles.MixedCompatGeneral
import FLatticePaper.Tiles.TileCompatInputs

/-! # Case 3 from the joint family

At an uncorrected non-base word `w = v d` whose parent piece is present (the even alternate child for `d = 1, 2`, the odd one for
`d = 1, 3`), with the parent's word `v` not a base word and its own alternate decomposition not corrected: the seven pieces of the
alternate decomposition of `w` built from the family agree with explicit constants (`AltSeven`). The data of the registers and
of the parent come from `GoodBelow`: the corner values of the registers (`TileTranslationStd.stdCorners_odd/_even`, slope zero by
`JointRot.family_slopes`), their half-turns and the half-turn of the parent (`TileProps`), the decomposition of the parent
(`TilePart` at `v`), and the mixed compatibility (`MixedCompatGeneral.alt_mixed`). The remaining hypotheses are the local
compatibility of the parent piece with each copy (`hpc`), the shift constant of the doubled register (`hk`) and the overlaps of
the six copies (`hov`). -/

namespace FLatticePaper.Tiles.AltSevenFamily

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.AltParentConstants
open FLatticePaper.Tiles.SurgicalWeak (regsAt)
open FLatticePaper.Tiles.Standard (oddTile evenTile IsBase)
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.SiteInduction

theorem regOdd_data (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (n : ℕ) (hg : GoodBelow D f n) (u : Word) (hu : u.length < n) :
    ∃ β : ℤ, (f u).tOdd.dom = oddTile u ∧
      TileTranslation.StdCornerValues (f u).tOdd 0 β (texV1Odd (fracOdd u)) (texV2 (fracOdd u))
        ((fracOdd u).num, -(fracOdd u).den) ∧
      ∀ y ∈ (↑(f u).tOdd.dom : Set (ℤ × ℤ)), texV1Odd (fracOdd u) + texV2 (fracOdd u) + ((1 : ℤ), (-1 : ℤ)) - y ∈
          (↑(f u).tOdd.dom : Set (ℤ × ℤ)) ∧
        2 * ((f u).tOdd.val (texV1Odd (fracOdd u) + texV2 (fracOdd u) + ((1 : ℤ), (-1 : ℤ)) - y) - (f u).tOdd.val y) =
          dotS ((fracOdd u).num, -(fracOdd u).den) (texV1Odd (fracOdd u) + texV2 (fracOdd u) + ((1 : ℤ), (-1 : ℤ))) -
            2 * dotS ((fracOdd u).num, -(fracOdd u).den) y := by
  have hJ := hg u hu
  have sl := JointRot.family_slopes D f u.length (fun v hv => (hg v (lt_of_le_of_lt hv hu)).1)
    (JointRot.baseSlopes_paper D hS hA) u le_rfl
  obtain ⟨β, hβ⟩ := sl.1
  have hT := hJ.1.2.2.1
  obtain ⟨α, β', hN, hC⟩ := TileTranslationStd.stdCorners_odd u (f u).tOdd hT.2.2.2.2.1
  obtain ⟨rfl, rfl⟩ := JointRot.firstTileNormal_unique _ _ _ _ _ hN hβ
  refine ⟨β', ?_, hC, ?_⟩
  · rw [hT.2.2.2.2.2.2.2.2.1, hS]; rfl
  · exact halfTurn_raw (f u).tOdd _ _ _ hJ.2.2.1.2.2.1 ⟨β', hN⟩

theorem rel_one (v : Word) :
    (parentsAt (v ++ [Digit.one])).odd.num = (parentsAt v).odd.num + (parentsAt v).even.num ∧
      (parentsAt (v ++ [Digit.one])).odd.den = (parentsAt v).odd.den + (parentsAt v).even.den ∧
      (parentsAt (v ++ [Digit.one])).even.num = 2 * (parentsAt v).odd.num + (parentsAt v).even.num ∧
      (parentsAt (v ++ [Digit.one])).even.den = 2 * (parentsAt v).odd.den + (parentsAt v).even.den := by
  simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]

theorem regs_one (v : Word) : regsAt (v ++ [Digit.one]) = (some v, some v) := by
  simp [WeakStepPaper.regsAt_snoc, SurgicalWeak.regStep]

theorem off1 (u : Word) (h : phase u = 1) :
    (altOddD u).getD 1 0 = ((parentsAt u).odd.num - (parentsAt u).odd.den, (parentsAt u).odd.num + (parentsAt u).odd.den) -
      ((parentsAt u).even.den, (parentsAt u).even.num) ∧
    (altOddAff u).getD 3 0 = ((parentsAt u).odd.num, -(parentsAt u).odd.den) + ((parentsAt u).even.num, -(parentsAt u).even.den) := by
  constructor <;> ext <;> simp [altOddD, altOddAff, cofW, cafW, shiftP, affS, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine,
    SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, h, texV1Odd, texV1Even, texV2, offsetA] <;> ring

theorem regEven_data (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (n : ℕ) (hg : GoodBelow D f n) (u : Word) (hu : u.length < n) :
    ∃ β : ℤ, (f u).tEven.dom = evenTile u ∧
      TileTranslation.StdCornerValues (f u).tEven 0 β (texV1Even (fracEven u)) (texV2 (fracEven u))
        ((fracEven u).num, -(fracEven u).den) ∧
      ∀ y ∈ (↑(f u).tEven.dom : Set (ℤ × ℤ)), texV1Even (fracEven u) + texV2 (fracEven u) + ((1 : ℤ), (-1 : ℤ)) - y ∈
          (↑(f u).tEven.dom : Set (ℤ × ℤ)) ∧
        2 * ((f u).tEven.val (texV1Even (fracEven u) + texV2 (fracEven u) + ((1 : ℤ), (-1 : ℤ)) - y) - (f u).tEven.val y) =
          dotS ((fracEven u).num, -(fracEven u).den) (texV1Even (fracEven u) + texV2 (fracEven u) + ((1 : ℤ), (-1 : ℤ))) -
            2 * dotS ((fracEven u).num, -(fracEven u).den) y := by
  have hJ := hg u hu
  have sl := JointRot.family_slopes D f u.length (fun v hv => (hg v (lt_of_le_of_lt hv hu)).1)
    (JointRot.baseSlopes_paper D hS hA) u le_rfl
  obtain ⟨β, hβ⟩ := sl.2.1
  have hT := hJ.1.2.2.1
  obtain ⟨α, β', hN, hC⟩ := TileTranslationStd.stdCorners_even u (f u).tEven hT.2.2.2.2.2.1
  obtain ⟨rfl, rfl⟩ := JointRot.firstTileNormal_unique _ _ _ _ _ hN hβ
  refine ⟨β', ?_, hC, ?_⟩
  · rw [hT.2.2.2.2.2.2.2.2.2.1, hS]; rfl
  · exact halfTurn_raw (f u).tEven _ _ _ hJ.2.2.1.2.2.2.1 ⟨β', hN⟩

theorem aOdd_halfTurn (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (n : ℕ) (hg : GoodBelow D f n) (u : Word) (hu : u.length < n) :
    ∀ x ∈ (↑(f u).aOdd.dom : Set (ℤ × ℤ)), altD u true - x ∈ (↑(f u).aOdd.dom : Set (ℤ × ℤ)) ∧
      2 * ((f u).aOdd.val (altD u true - x) - (f u).aOdd.val x) = dotS (altE u) (altD u true) - 2 * dotS (altE u) x := by
  have sl := JointRot.family_slopes D f u.length (fun v hv => (hg v (lt_of_le_of_lt hv hu)).1)
    (JointRot.baseSlopes_paper D hS hA) u le_rfl
  exact altHalfTurn_raw _ _ _ (hg u hu).2.2.1.2.2.2.2.1 sl.2.2.1

theorem aEven_halfTurn (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (n : ℕ) (hg : GoodBelow D f n) (u : Word) (hu : u.length < n) :
    ∀ x ∈ (↑(f u).aEven.dom : Set (ℤ × ℤ)), altD u false - x ∈ (↑(f u).aEven.dom : Set (ℤ × ℤ)) ∧
      2 * ((f u).aEven.val (altD u false - x) - (f u).aEven.val x) = dotS (altE u) (altD u false) - 2 * dotS (altE u) x := by
  have sl := JointRot.family_slopes D f u.length (fun v hv => (hg v (lt_of_le_of_lt hv hu)).1)
    (JointRot.baseSlopes_paper D hS hA) u le_rfl
  exact altHalfTurn_raw _ _ _ (hg u hu).2.2.1.2.2.2.2.2 sl.2.2.2

theorem sub_of_respects (o : PartialOdometer) (ps : List Piece) (hR : RespectsPieces o ps) (q : PartialOdometer)
    (off aff OFF AFF : ℤ × ℤ) (hmem : stdPiece q off aff ∈ ps) (hoff : off = OFF) (haff : aff = AFF) :
    (∀ x, x - OFF ∈ (↑q.dom : Set (ℤ × ℤ)) → x ∈ (↑o.dom : Set (ℤ × ℤ))) ∧
      ∃ b : ℤ, ∀ x, x - OFF ∈ (↑q.dom : Set (ℤ × ℤ)) → o.val x = q.val (x - OFF) + dotS AFF x + b := by
  subst hoff haff
  refine ⟨fun x hx => ?_, ?_⟩
  · have : x ∈ pieceUnion ps := JointGlue.mem_pieceUnion.mpr ⟨_, hmem, (AltPiecesAgree.mem_placed_std q off aff x).mpr hx⟩
    rw [← hR.1] at this
    exact this
  · obtain ⟨b, hb⟩ := hR.2 _ hmem
    exact ⟨b, fun x hx => hb x ((AltPiecesAgree.mem_placed_std q off aff x).mpr hx) (by simp [stdPiece])⟩

theorem parent_respects (D : JointData) (f : Word → JSlice) (n : ℕ) (hg : GoodBelow D f n) (u : Word) (hu : u.length < n)
    (hub : ¬ IsBase u) :
    RespectsPieces (f u).aOdd (tileAltOddPieces D.S (fun v => (below f u v).tOdd) (fun v => (below f u v).tEven)
        (fun v => (below f u v).aOdd) (fun v => (below f u v).aEven) (fun v => (below f u v).lOdd) u) ∧
      RespectsPieces (f u).aEven (tileAltEvenPieces D.S (fun v => (below f u v).tOdd) (fun v => (below f u v).tEven)
        (fun v => (below f u v).aOdd) (fun v => (below f u v).aEven) (fun v => (below f u v).lEven) u) :=
  ⟨((hg u hu).1.2.2.1.2.1 hub).2.2.1, ((hg u hu).1.2.2.1.2.1 hub).2.2.2⟩


theorem hpc_even (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lEven : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (c : SurgicalAlt.AltCoeff) (T η : ℤ × ℤ)
    (hr : regsAt w = (some u1, some u2)) (h3 : w.getLast? ≠ some Digit.three)
    (hc : (SurgicalAlt.altTypeOf w).bind (fun ty => SurgicalAlt.altP1Coeff (W1Odd w) ty) = some c)
    (ht : altOff w c = T) (hη : altAff w c = η)
    (hdP : (pOdd u1).dom = oddTile u1) (hdQ : (pEven u2).dom = evenTile u2) (j : ℕ) (hj : j < 6)
    (h : TileCompatInputs.PairCompat (tileAltEvenPieces S pOdd pEven aOdd aEven lEven w) 6 j) :
    ∃ C : ℤ, ∀ z, z - T ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)) → z ∈ dAE w u1 u2 j →
      (aOdd u1).val (z - T) + ClosedPathSum.dot2 η z - placedAltEven w (pOdd u1).val (pEven u2).val 0 j z = C := by
  rw [AltPiecesAgree.aEven_list S pOdd pEven aOdd aEven lEven w u1 u2 c hr h3 hc] at h
  have hstd := AltPiecesAgree.aEven_std w u1 u2 (pOdd u1) (pEven u2) (aOdd u1) (altOff w c) (altAff w c) hdP hdQ j hj
  interval_cases j <;>
  · obtain ⟨C, hC⟩ := h _ _ rfl rfl
    refine ⟨C, fun z hz hzj => ?_⟩
    have e := hstd _ rfl z
    have := hC z (by rw [AltPiecesAgree.mem_placed_std, ht]; exact hz) (e.1.mpr hzj) (by simp [stdPiece]) (by simp [stdPiece])
    rw [e.2] at this
    simpa [JointGlue.pieceVal, stdPiece, ht, hη, ClosedPathSum.dot2, dotS] using this

theorem hpc_odd (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lOdd : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (c : SurgicalAlt.AltCoeff) (T η : ℤ × ℤ)
    (hr : regsAt w = (some u1, some u2)) (h2 : w.getLast? ≠ some Digit.two)
    (hc : (SurgicalAlt.altTypeOf w).bind (fun ty => SurgicalAlt.altQ1Coeff (W1Odd w) ty) = some c)
    (ht : altOff w c = T) (hη : altAff w c = η)
    (hdP : (pOdd u1).dom = oddTile u1) (hdQ : (pEven u2).dom = evenTile u2) (j : ℕ) (hj : j < 6)
    (h : TileCompatInputs.PairCompat (tileAltOddPieces S pOdd pEven aOdd aEven lOdd w) 6 j) :
    ∃ C : ℤ, ∀ z, z - T ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)) → z ∈ dAO w u1 u2 j →
      (aEven u2).val (z - T) + ClosedPathSum.dot2 η z - placedAltOdd w (pOdd u1).val (pEven u2).val 0 j z = C := by
  rw [AltPiecesAgree.aOdd_list S pOdd pEven aOdd aEven lOdd w u1 u2 c hr h2 hc] at h
  have hstd := AltPiecesAgree.aOdd_std w u1 u2 (pOdd u1) (pEven u2) (aEven u2) (altOff w c) (altAff w c) hdP hdQ j hj
  interval_cases j <;>
  · obtain ⟨C, hC⟩ := h _ _ rfl rfl
    refine ⟨C, fun z hz hzj => ?_⟩
    have e := hstd _ rfl z
    have := hC z (by rw [AltPiecesAgree.mem_placed_std, ht]; exact hz) (e.1.mpr hzj) (by simp [stdPiece]) (by simp [stdPiece])
    rw [e.2] at this
    simpa [JointGlue.pieceVal, stdPiece, ht, hη, ClosedPathSum.dot2, dotS] using this

/-- Case 3 from the family, even alternate child, `W_1` even, last digit `1`. -/
theorem family_ef1 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (v : Word) (hg : GoodBelow D f (v ++ [Digit.one]).length) (hv : ¬ IsBase v)
    (hph : phase (v ++ [Digit.one]) ≠ 1)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltEvenPieces D.S (fun u => (below f (v ++ [Digit.one]) u).tOdd) (fun u => (below f (v ++ [Digit.one]) u).tEven)
      (fun u => (below f (v ++ [Digit.one]) u).aOdd) (fun u => (below f (v ++ [Digit.one]) u).aEven)
      (fun u => (below f (v ++ [Digit.one]) u).lEven) (v ++ [Digit.one])) 6 j)
    (hk : ∀ u2, (regsAt (v ++ [Digit.one])).2 = some u2 → ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ (v ++ [Digit.one]) ∈ tEvenSet u2 →
      (f u2).tEven.val (x + shiftQ (v ++ [Digit.one])) - (f u2).tEven.val x - ClosedPathSum.dot2 (affS (v ++ [Digit.one])) x = k)
    (hov : ∀ u1 u2, regsAt (v ++ [Digit.one]) = (some u1, some u2) → AltPiecesAgree.SixOverlaps (altEvenD (v ++ [Digit.one])) (altEvenR (v ++ [Digit.one]))
      (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) ChildGlue.dblEven) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltEvenPieces D.S (fun u => (below f (v ++ [Digit.one]) u).tOdd) (fun u => (below f (v ++ [Digit.one]) u).tEven)
      (fun u => (below f (v ++ [Digit.one]) u).aOdd) (fun u => (below f (v ++ [Digit.one]) u).aEven)
      (fun u => (below f (v ++ [Digit.one]) u).lEven) (v ++ [Digit.one])) κ := by
  have hlt : v.length < (v ++ [Digit.one]).length := by simp
  have hgv : GoodBelow D f v.length := fun u hu => hg u (lt_trans hu hlt)
  obtain ⟨⟨v1, hv1⟩, ⟨v2, hv2'⟩⟩ := JointRot.regs_some v hv
  have hrv : regsAt v = (some v1, some v2) := Prod.ext hv1 hv2'
  have l1 : v1.length < v.length := JointInduction.regsAt_lt v v1 (Or.inl hv1)
  have l2 : v2.length < v.length := JointInduction.regsAt_lt v v2 (Or.inr hv2')
  have hr : regsAt (v ++ [Digit.one]) = (some v, some v) := by
    simp [WeakStepPaper.regsAt_snoc, SurgicalWeak.regStep]
  have hu1 : v.length < (v ++ [Digit.one]).length := hlt
  have hu2 : v.length < (v ++ [Digit.one]).length := hlt
  have hb1 : below f (v ++ [Digit.one]) v = f v := JointRot.below_of_lt f _ _ hu1
  have hb2 : below f (v ++ [Digit.one]) v = f v := JointRot.below_of_lt f _ _ hu2
  have hbv : below f (v ++ [Digit.one]) v = f v := JointRot.below_of_lt f _ _ hlt
  have hp := (WeakStepAssembly.regsAt_parents (v ++ [Digit.one])).1 v (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents (v ++ [Digit.one])).2 v (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := regOdd_data D hS hA f _ hg v hu1
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
  have hpar2 := (parentsAt_valid v).odd_parity
  have hqe2 := (parentsAt_valid v).even_parity
  unfold Fraction.Odd at hpar2
  unfold Fraction.Even at hqe2
  have hwb : ¬ IsBase (v ++ [Digit.one]) := by
    rintro (h | h | h)
    · simp at h
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inl fun d hd => h d (by simp [hd])))
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inr fun d hd => h d (by simp [hd])))
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ v v hg hwb hr 0).2
  have hW : W1Odd (v ++ [Digit.one]) = false := by simpa [W1Odd] using hph
  have hc : (SurgicalAlt.altTypeOf (v ++ [Digit.one])).bind (fun ty => SurgicalAlt.altP1Coeff (W1Odd (v ++ [Digit.one])) ty) = some (1, 1, -1, 0) := by
    simp [SurgicalAlt.altTypeOf, hW, SurgicalAlt.altP1Coeff]
  have ht : altOff (v ++ [Digit.one]) (1, 1, -1, 0) = (texV1Odd (parentsAt (v ++ [Digit.one])).odd + texV2 (parentsAt (v ++ [Digit.one])).odd - texV1Even (parentsAt (v ++ [Digit.one])).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2] <;> ring
  have hη : altAff (v ++ [Digit.one]) (1, 1, -1, 0) = ((parentsAt (v ++ [Digit.one])).odd.num, -(parentsAt (v ++ [Digit.one])).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  obtain ⟨k, hk⟩ := hk v (by rw [hr])
  have hov := hov v v hr
  refine ⟨_, AltSeven.seven_ef1 D.S (fun u => (below f (v ++ [Digit.one]) u).tOdd) (fun u => (below f (v ++ [Digit.one]) u).tEven)
    (fun u => (below f (v ++ [Digit.one]) u).aOdd) (fun u => (below f (v ++ [Digit.one]) u).aEven) (fun u => (below f (v ++ [Digit.one]) u).lEven) (v ++ [Digit.one]) v v hph (by simp) hr hp hq
    (parentsAt v).odd.num (parentsAt v).odd.den (parentsAt v).even.num (parentsAt v).even.den hpar2 hqe2
    ⟨by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine],
      by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]⟩
    (f v1).tOdd (f v2).tEven βP βQ ((f v).aOdd.val 0) βP2 βQ2
    (by simp only [hb1]; exact hdP) (by simp only [hb1]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb1]; exact hcQ)
    (by simp only [hb1]; exact hhQ) (by simp only [hb1]; exact ⟨k, hk⟩) (by simp only [hb1]; exact hcompat) hcP2 hcQ2 hhP2 hhQ2
    (by simp only [hb1]; exact fun x hx => (hhH x hx).2) (by simp only [hb1])
    (by simp only [hb1]; exact hd0) (by simp only [hb1]; exact hd3) (by simp only [hb1]; exact hd4) (by simp only [hb1]; exact hd5)
    (by simp only [hb1]; exact h0p) (by simp only [hb1]; exact h3p) (by simp only [hb1]; exact h4p) (by simp only [hb1]; exact h5p)
    (fun j hj => hpc_even D.S _ _ _ _ _ (v ++ [Digit.one]) v v _ _ _ hr (by simp) hc ht hη (by simp only [hb1]; exact hdP)
      (by simp only [hb1]; exact hdQ) j hj (hpc j hj)) hov⟩

/-- Case 3 from the family, even alternate child, `W_1` odd, last digit `1`. -/
theorem family_of1 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (v : Word) (hg : GoodBelow D f (v ++ [Digit.one]).length) (hv : ¬ IsBase v)
    (hph : phase (v ++ [Digit.one]) = 1)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltEvenPieces D.S (fun u => (below f (v ++ [Digit.one]) u).tOdd) (fun u => (below f (v ++ [Digit.one]) u).tEven)
      (fun u => (below f (v ++ [Digit.one]) u).aOdd) (fun u => (below f (v ++ [Digit.one]) u).aEven)
      (fun u => (below f (v ++ [Digit.one]) u).lEven) (v ++ [Digit.one])) 6 j)
    (hk : ∀ u2, (regsAt (v ++ [Digit.one])).2 = some u2 → ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ (v ++ [Digit.one]) ∈ tEvenSet u2 →
      (f u2).tEven.val (x + shiftQ (v ++ [Digit.one])) - (f u2).tEven.val x - ClosedPathSum.dot2 (affS (v ++ [Digit.one])) x = k)
    (hov : ∀ u1 u2, regsAt (v ++ [Digit.one]) = (some u1, some u2) → AltPiecesAgree.SixOverlaps (altEvenD (v ++ [Digit.one])) (altEvenR (v ++ [Digit.one]))
      (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) ChildGlue.dblEven) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltEvenPieces D.S (fun u => (below f (v ++ [Digit.one]) u).tOdd) (fun u => (below f (v ++ [Digit.one]) u).tEven)
      (fun u => (below f (v ++ [Digit.one]) u).aOdd) (fun u => (below f (v ++ [Digit.one]) u).aEven)
      (fun u => (below f (v ++ [Digit.one]) u).lEven) (v ++ [Digit.one])) κ := by
  have hlt : v.length < (v ++ [Digit.one]).length := by simp
  have hgv : GoodBelow D f v.length := fun u hu => hg u (lt_trans hu hlt)
  obtain ⟨⟨v1, hv1⟩, ⟨v2, hv2'⟩⟩ := JointRot.regs_some v hv
  have hrv : regsAt v = (some v1, some v2) := Prod.ext hv1 hv2'
  have l1 : v1.length < v.length := JointInduction.regsAt_lt v v1 (Or.inl hv1)
  have l2 : v2.length < v.length := JointInduction.regsAt_lt v v2 (Or.inr hv2')
  have hr : regsAt (v ++ [Digit.one]) = (some v, some v) := by
    simp [WeakStepPaper.regsAt_snoc, SurgicalWeak.regStep]
  have hu1 : v.length < (v ++ [Digit.one]).length := hlt
  have hu2 : v.length < (v ++ [Digit.one]).length := hlt
  have hb1 : below f (v ++ [Digit.one]) v = f v := JointRot.below_of_lt f _ _ hu1
  have hb2 : below f (v ++ [Digit.one]) v = f v := JointRot.below_of_lt f _ _ hu2
  have hbv : below f (v ++ [Digit.one]) v = f v := JointRot.below_of_lt f _ _ hlt
  have hp := (WeakStepAssembly.regsAt_parents (v ++ [Digit.one])).1 v (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents (v ++ [Digit.one])).2 v (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := regOdd_data D hS hA f _ hg v hu1
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
  have hpar2 := (parentsAt_valid v).odd_parity
  have hqe2 := (parentsAt_valid v).even_parity
  unfold Fraction.Odd at hpar2
  unfold Fraction.Even at hqe2
  have hwb : ¬ IsBase (v ++ [Digit.one]) := by
    rintro (h | h | h)
    · simp at h
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inl fun d hd => h d (by simp [hd])))
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inr fun d hd => h d (by simp [hd])))
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ v v hg hwb hr 0).2
  have hW : W1Odd (v ++ [Digit.one]) = true := by simp [W1Odd, hph]
  have hc : (SurgicalAlt.altTypeOf (v ++ [Digit.one])).bind (fun ty => SurgicalAlt.altP1Coeff (W1Odd (v ++ [Digit.one])) ty) = some (0, 1, 1, 0) := by
    simp [SurgicalAlt.altTypeOf, hW, SurgicalAlt.altP1Coeff]
  have ht : altOff (v ++ [Digit.one]) (0, 1, 1, 0) = (texV2 (parentsAt (v ++ [Digit.one])).odd + texV1Even (parentsAt (v ++ [Digit.one])).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2]
  have hη : altAff (v ++ [Digit.one]) (0, 1, 1, 0) = ((parentsAt (v ++ [Digit.one])).odd.num, -(parentsAt (v ++ [Digit.one])).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  obtain ⟨k, hk⟩ := hk v (by rw [hr])
  have hov := hov v v hr
  refine ⟨_, AltSeven.seven_of1 D.S (fun u => (below f (v ++ [Digit.one]) u).tOdd) (fun u => (below f (v ++ [Digit.one]) u).tEven)
    (fun u => (below f (v ++ [Digit.one]) u).aOdd) (fun u => (below f (v ++ [Digit.one]) u).aEven) (fun u => (below f (v ++ [Digit.one]) u).lEven) (v ++ [Digit.one]) v v hph (by simp) hr hp hq
    (parentsAt v).odd.num (parentsAt v).odd.den (parentsAt v).even.num (parentsAt v).even.den hpar2 hqe2
    ⟨by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine],
      by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]⟩
    (f v1).tOdd (f v2).tEven βP βQ ((f v).aOdd.val 0) βP2 βQ2
    (by simp only [hb1]; exact hdP) (by simp only [hb1]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb1]; exact hcQ)
    (by simp only [hb1]; exact hhQ) (by simp only [hb1]; exact ⟨k, hk⟩) (by simp only [hb1]; exact hcompat) hcP2 hcQ2 hhP2 hhQ2
    (by simp only [hb1]; exact fun x hx => (hhH x hx).2) (by simp only [hb1])
    (by simp only [hb1]; exact hd0) (by simp only [hb1]; exact hd3) (by simp only [hb1]; exact hd4) (by simp only [hb1]; exact hd5)
    (by simp only [hb1]; exact h0p) (by simp only [hb1]; exact h3p) (by simp only [hb1]; exact h4p) (by simp only [hb1]; exact h5p)
    (fun j hj => hpc_even D.S _ _ _ _ _ (v ++ [Digit.one]) v v _ _ _ hr (by simp) hc ht hη (by simp only [hb1]; exact hdP)
      (by simp only [hb1]; exact hdQ) j hj (hpc j hj)) hov⟩

/-- Case 3 from the family, even alternate child, `W_1` even, last digit `2`. -/
theorem family_ef2 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (v : Word) (hg : GoodBelow D f (v ++ [Digit.two]).length) (hv : ¬ IsBase v)
    (hph : phase (v ++ [Digit.two]) ≠ 1) (hvc : v.getLast? ≠ some Digit.two)
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
  obtain ⟨c', hc'⟩ : ∃ c', (SurgicalAlt.altTypeOf v).bind (fun ty => SurgicalAlt.altQ1Coeff (W1Odd v) ty) = some c' := by
    obtain ⟨v', d, rfl⟩ : ∃ v' d, v = v' ++ [d] := by
      cases v using List.reverseRecOn with
      | nil => exact (hv (Or.inl rfl)).elim
      | append_singleton v' d => exact ⟨v', d, rfl⟩
    cases d <;> simp [SurgicalAlt.altTypeOf, SurgicalAlt.altQ1Coeff] at hvc ⊢ <;> split_ifs <;> exact ⟨_, _, _, _, rfl⟩
  rw [AltPiecesAgree.aOdd_list D.S _ _ _ _ _ v v1 v2 c' hrv hvc hc'] at hRP
  simp only [JointRot.below_of_lt f v v1 l1, JointRot.below_of_lt f v v2 l2] at hRP
  obtain ⟨hd0, h0p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altOddD v).getD 0 0) ((altOddAff v).getD 0 0) ((parentsAt v).even.den, (parentsAt v).even.num) 0 (by simp)
    (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  obtain ⟨hd1, h1p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altOddD v).getD 1 0) ((altOddAff v).getD 1 0) ((2 : ℤ) • ((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den)) ((parentsAt v).odd.num, -(parentsAt v).odd.den) (by simp)
    (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  obtain ⟨hd2, h2p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altOddD v).getD 2 0) ((altOddAff v).getD 2 0) ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den) ((parentsAt v).even.num, -(parentsAt v).even.den) (by simp)
    (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  obtain ⟨hd3, h3p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altOddD v).getD 3 0) ((altOddAff v).getD 3 0) (((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den)) (((parentsAt v).odd.num, -(parentsAt v).odd.den) + ((parentsAt v).even.num, -(parentsAt v).even.den)) (by simp)
    (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA] <;> ring)
  obtain ⟨hd4, h4p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altOddR v).getD 0 0) ((altOddAff v).getD 4 0) 0 0 (by simp)
    (by ext <;> simp [altOddR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  obtain ⟨hd5, h5p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altOddR v).getD 1 0) ((altOddAff v).getD 5 0) ((2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + (2 : ℤ) • ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((parentsAt v).even.den, (parentsAt v).even.num)) ((2 : ℤ) • ((parentsAt v).odd.num, -(parentsAt v).odd.den)) (by simp)
    (by ext <;> simp [altOddR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
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
  refine ⟨_, AltSeven.seven_ef2 D.S (fun u => (below f (v ++ [Digit.two]) u).tOdd) (fun u => (below f (v ++ [Digit.two]) u).tEven)
    (fun u => (below f (v ++ [Digit.two]) u).aOdd) (fun u => (below f (v ++ [Digit.two]) u).aEven) (fun u => (below f (v ++ [Digit.two]) u).lEven) (v ++ [Digit.two]) v v2 hph (by simp) hr hp hq
    (parentsAt v).odd.num (parentsAt v).odd.den (parentsAt v).even.num (parentsAt v).even.den hpar2 hqe2
    ⟨by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine],
      by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]⟩
    (f v1).tOdd (f v2).tEven βP βQ ((f v).aOdd.val 0) βP2 βQ2
    (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb2]; exact hhQ) (by simp only [hb2]; exact ⟨k, hk⟩) (by simp only [hb1, hb2]; exact hcompat) hcP2 hcQ2 hhP2 hhQ2
    (by simp only [hb1]; exact fun x hx => (hhH x hx).2) (by simp only [hb1])
    (by simp only [hb1]; exact hd0) (by simp only [hb1]; exact hd1) (by simp only [hb1]; exact hd2) (by simp only [hb1]; exact hd3)
    (by simp only [hb1]; exact hd4) (by simp only [hb1]; exact hd5) (by simp only [hb1]; exact h0p) (by simp only [hb1]; exact h1p)
    (by simp only [hb1]; exact h2p) (by simp only [hb1]; exact h3p) (by simp only [hb1]; exact h4p) (by simp only [hb1]; exact h5p)
    (fun j hj => hpc_even D.S _ _ _ _ _ (v ++ [Digit.two]) v v2 _ _ _ hr (by simp) hc ht hη (by simp only [hb1]; exact hdP)
      (by simp only [hb2]; exact hdQ) j hj (hpc j hj)) hov⟩

/-- Case 3 from the family, even alternate child, `W_1` odd, last digit `2`. -/
theorem family_of2 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (v : Word) (hg : GoodBelow D f (v ++ [Digit.two]).length) (hv : ¬ IsBase v)
    (hph : phase (v ++ [Digit.two]) = 1) (hvc : v.getLast? ≠ some Digit.two)
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
  obtain ⟨c', hc'⟩ : ∃ c', (SurgicalAlt.altTypeOf v).bind (fun ty => SurgicalAlt.altQ1Coeff (W1Odd v) ty) = some c' := by
    obtain ⟨v', d, rfl⟩ : ∃ v' d, v = v' ++ [d] := by
      cases v using List.reverseRecOn with
      | nil => exact (hv (Or.inl rfl)).elim
      | append_singleton v' d => exact ⟨v', d, rfl⟩
    cases d <;> simp [SurgicalAlt.altTypeOf, SurgicalAlt.altQ1Coeff] at hvc ⊢ <;> split_ifs <;> exact ⟨_, _, _, _, rfl⟩
  rw [AltPiecesAgree.aOdd_list D.S _ _ _ _ _ v v1 v2 c' hrv hvc hc'] at hRP
  simp only [JointRot.below_of_lt f v v1 l1, JointRot.below_of_lt f v v2 l2] at hRP
  obtain ⟨hd0, h0p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altOddD v).getD 0 0) ((altOddAff v).getD 0 0) 0 0 (by simp)
    (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  obtain ⟨hd1, h1p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altOddD v).getD 1 0) ((altOddAff v).getD 1 0) (((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) - ((parentsAt v).even.den, (parentsAt v).even.num)) ((parentsAt v).odd.num, -(parentsAt v).odd.den) (by simp)
    (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  obtain ⟨hd2, h2p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altOddD v).getD 2 0) ((altOddAff v).getD 2 0) (((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den)) ((parentsAt v).even.num, -(parentsAt v).even.den) (by simp)
    (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  obtain ⟨hd3, h3p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altOddD v).getD 3 0) ((altOddAff v).getD 3 0) (((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den)) (((parentsAt v).odd.num, -(parentsAt v).odd.den) + ((parentsAt v).even.num, -(parentsAt v).even.den)) (by simp)
    (by ext <;> simp [altOddD, cofW, shiftP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA] <;> ring)
  obtain ⟨hd4, h4p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altOddR v).getD 0 0) ((altOddAff v).getD 4 0) (2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) 0 (by simp)
    (by ext <;> simp [altOddR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
  obtain ⟨hd5, h5p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altOddR v).getD 1 0) ((altOddAff v).getD 5 0) ((2 : ℤ) • ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) - ((parentsAt v).even.den, (parentsAt v).even.num)) ((2 : ℤ) • ((parentsAt v).odd.num, -(parentsAt v).odd.den)) (by simp)
    (by ext <;> simp [altOddR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altOddAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, hphv, offsetA])
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
  refine ⟨_, AltSeven.seven_of2 D.S (fun u => (below f (v ++ [Digit.two]) u).tOdd) (fun u => (below f (v ++ [Digit.two]) u).tEven)
    (fun u => (below f (v ++ [Digit.two]) u).aOdd) (fun u => (below f (v ++ [Digit.two]) u).aEven) (fun u => (below f (v ++ [Digit.two]) u).lEven) (v ++ [Digit.two]) v v2 hph (by simp) hr hp hq
    (parentsAt v).odd.num (parentsAt v).odd.den (parentsAt v).even.num (parentsAt v).even.den hpar2 hqe2
    ⟨by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine],
      by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]⟩
    (f v1).tOdd (f v2).tEven βP βQ ((f v).aOdd.val 0) βP2 βQ2
    (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb2]; exact hhQ) (by simp only [hb2]; exact ⟨k, hk⟩) (by simp only [hb1, hb2]; exact hcompat) hcP2 hcQ2 hhP2 hhQ2
    (by simp only [hb1]; exact fun x hx => (hhH x hx).2) (by simp only [hb1])
    (by simp only [hb1]; exact hd0) (by simp only [hb1]; exact hd1) (by simp only [hb1]; exact hd2) (by simp only [hb1]; exact hd3)
    (by simp only [hb1]; exact hd4) (by simp only [hb1]; exact hd5) (by simp only [hb1]; exact h0p) (by simp only [hb1]; exact h1p)
    (by simp only [hb1]; exact h2p) (by simp only [hb1]; exact h3p) (by simp only [hb1]; exact h4p) (by simp only [hb1]; exact h5p)
    (fun j hj => hpc_even D.S _ _ _ _ _ (v ++ [Digit.two]) v v2 _ _ _ hr (by simp) hc ht hη (by simp only [hb1]; exact hdP)
      (by simp only [hb2]; exact hdQ) j hj (hpc j hj)) hov⟩

/-- Case 3 from the family, odd alternate child, `W_1` even, last digit `1`. -/
theorem family_oe1 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (v : Word) (hg : GoodBelow D f (v ++ [Digit.one]).length) (hv : ¬ IsBase v)
    (hph : phase (v ++ [Digit.one]) ≠ 1)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltOddPieces D.S (fun u => (below f (v ++ [Digit.one]) u).tOdd) (fun u => (below f (v ++ [Digit.one]) u).tEven)
      (fun u => (below f (v ++ [Digit.one]) u).aOdd) (fun u => (below f (v ++ [Digit.one]) u).aEven)
      (fun u => (below f (v ++ [Digit.one]) u).lOdd) (v ++ [Digit.one])) 6 j)
    (hk : ∀ u1, (regsAt (v ++ [Digit.one])).1 = some u1 → ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP (v ++ [Digit.one]) ∈ tOddSet u1 →
      (f u1).tOdd.val (x + shiftP (v ++ [Digit.one])) - (f u1).tOdd.val x - ClosedPathSum.dot2 (affS (v ++ [Digit.one])) x = k)
    (hov : ∀ u1 u2, regsAt (v ++ [Digit.one]) = (some u1, some u2) → AltPiecesAgree.SixOverlaps (altOddD (v ++ [Digit.one])) (altOddR (v ++ [Digit.one]))
      (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) ChildGlue.dblEven) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltOddPieces D.S (fun u => (below f (v ++ [Digit.one]) u).tOdd) (fun u => (below f (v ++ [Digit.one]) u).tEven)
      (fun u => (below f (v ++ [Digit.one]) u).aOdd) (fun u => (below f (v ++ [Digit.one]) u).aEven)
      (fun u => (below f (v ++ [Digit.one]) u).lOdd) (v ++ [Digit.one])) κ := by
  have hlt : v.length < (v ++ [Digit.one]).length := by simp
  have hgv : GoodBelow D f v.length := fun u hu => hg u (lt_trans hu hlt)
  obtain ⟨⟨v1, hv1⟩, ⟨v2, hv2'⟩⟩ := JointRot.regs_some v hv
  have hrv : regsAt v = (some v1, some v2) := Prod.ext hv1 hv2'
  have l1 : v1.length < v.length := JointInduction.regsAt_lt v v1 (Or.inl hv1)
  have l2 : v2.length < v.length := JointInduction.regsAt_lt v v2 (Or.inr hv2')
  have hr : regsAt (v ++ [Digit.one]) = (some v, some v) := by
    simp [WeakStepPaper.regsAt_snoc, SurgicalWeak.regStep]
  have hu1 : v.length < (v ++ [Digit.one]).length := hlt
  have hu2 : v.length < (v ++ [Digit.one]).length := hlt
  have hb1 : below f (v ++ [Digit.one]) v = f v := JointRot.below_of_lt f _ _ hu1
  have hb2 : below f (v ++ [Digit.one]) v = f v := JointRot.below_of_lt f _ _ hu2
  have hbv : below f (v ++ [Digit.one]) v = f v := JointRot.below_of_lt f _ _ hlt
  have hp := (WeakStepAssembly.regsAt_parents (v ++ [Digit.one])).1 v (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents (v ++ [Digit.one])).2 v (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := regOdd_data D hS hA f _ hg v hu1
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
  obtain ⟨b4, h4p⟩ := h4p
  have h4p' : ∀ x, x - 0 ∈ (↑(f v1).tOdd.dom : Set (ℤ × ℤ)) →
      (f v).aEven.val x = (f v1).tOdd.val (x - 0) + dotS 0 x + ((b4 + βP2) - βP2) := fun x hx => by
    rw [h4p x hx]; ring
  have hpar2 := (parentsAt_valid v).odd_parity
  have hqe2 := (parentsAt_valid v).even_parity
  unfold Fraction.Odd at hpar2
  unfold Fraction.Even at hqe2
  have hwb : ¬ IsBase (v ++ [Digit.one]) := by
    rintro (h | h | h)
    · simp at h
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inl fun d hd => h d (by simp [hd])))
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inr fun d hd => h d (by simp [hd])))
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ v v hg hwb hr 0).1
  have hW : W1Odd (v ++ [Digit.one]) = false := by simpa [W1Odd] using hph
  have hc : (SurgicalAlt.altTypeOf (v ++ [Digit.one])).bind (fun ty => SurgicalAlt.altQ1Coeff (W1Odd (v ++ [Digit.one])) ty) = some (0, 1, 1, 0) := by
    simp [SurgicalAlt.altTypeOf, hW, SurgicalAlt.altQ1Coeff]
  have ht : altOff (v ++ [Digit.one]) (0, 1, 1, 0) = (texV2 (parentsAt (v ++ [Digit.one])).odd + texV1Even (parentsAt (v ++ [Digit.one])).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2]
  have hη : altAff (v ++ [Digit.one]) (0, 1, 1, 0) = ((parentsAt (v ++ [Digit.one])).odd.num, -(parentsAt (v ++ [Digit.one])).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  obtain ⟨k, hk⟩ := hk v (by rw [hr])
  have hov := hov v v hr
  refine ⟨_, AltSeven.seven_oe1 D.S (fun u => (below f (v ++ [Digit.one]) u).tOdd) (fun u => (below f (v ++ [Digit.one]) u).tEven)
    (fun u => (below f (v ++ [Digit.one]) u).aOdd) (fun u => (below f (v ++ [Digit.one]) u).aEven) (fun u => (below f (v ++ [Digit.one]) u).lOdd) (v ++ [Digit.one]) v v hph (by simp) hr hp hq
    (parentsAt v).odd.num (parentsAt v).odd.den (parentsAt v).even.num (parentsAt v).even.den hpar2 hqe2
    ⟨by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine],
      by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]⟩
    (f v1).tOdd (f v2).tEven βP βQ (b4 + βP2) βP2 βQ2
    (by simp only [hb1]; exact hdP) (by simp only [hb1]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb1]; exact hcQ)
    (by simp only [hb1]; exact hhP) (by simp only [hb1]; exact ⟨k, hk⟩) (by simp only [hb1]; exact hcompat) hcP2 hcQ2 hhP2 hhQ2
    (by simp only [hb1]; exact fun x hx => (hhH x hx).2)
    (by simp only [hb1]; exact hd1) (by simp only [hb1]; exact hd2) (by simp only [hb1]; exact hd4) (by simp only [hb1]; exact hd5)
    (by simp only [hb1]; exact h1p) (by simp only [hb1]; exact h2p) (by simp only [hb1]; exact h4p') (by simp only [hb1]; exact h5p)
    (fun j hj => hpc_odd D.S _ _ _ _ _ (v ++ [Digit.one]) v v _ _ _ hr (by simp) hc ht hη (by simp only [hb1]; exact hdP)
      (by simp only [hb1]; exact hdQ) j hj (hpc j hj)) hov⟩

/-- Case 3 from the family, odd alternate child, `W_1` odd, last digit `1`. -/
theorem family_oo1 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (v : Word) (hg : GoodBelow D f (v ++ [Digit.one]).length) (hv : ¬ IsBase v)
    (hph : phase (v ++ [Digit.one]) = 1)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltOddPieces D.S (fun u => (below f (v ++ [Digit.one]) u).tOdd) (fun u => (below f (v ++ [Digit.one]) u).tEven)
      (fun u => (below f (v ++ [Digit.one]) u).aOdd) (fun u => (below f (v ++ [Digit.one]) u).aEven)
      (fun u => (below f (v ++ [Digit.one]) u).lOdd) (v ++ [Digit.one])) 6 j)
    (hk : ∀ u1, (regsAt (v ++ [Digit.one])).1 = some u1 → ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP (v ++ [Digit.one]) ∈ tOddSet u1 →
      (f u1).tOdd.val (x + shiftP (v ++ [Digit.one])) - (f u1).tOdd.val x - ClosedPathSum.dot2 (affS (v ++ [Digit.one])) x = k)
    (hov : ∀ u1 u2, regsAt (v ++ [Digit.one]) = (some u1, some u2) → AltPiecesAgree.SixOverlaps (altOddD (v ++ [Digit.one])) (altOddR (v ++ [Digit.one]))
      (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) ChildGlue.dblEven) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltOddPieces D.S (fun u => (below f (v ++ [Digit.one]) u).tOdd) (fun u => (below f (v ++ [Digit.one]) u).tEven)
      (fun u => (below f (v ++ [Digit.one]) u).aOdd) (fun u => (below f (v ++ [Digit.one]) u).aEven)
      (fun u => (below f (v ++ [Digit.one]) u).lOdd) (v ++ [Digit.one])) κ := by
  have hlt : v.length < (v ++ [Digit.one]).length := by simp
  have hgv : GoodBelow D f v.length := fun u hu => hg u (lt_trans hu hlt)
  obtain ⟨⟨v1, hv1⟩, ⟨v2, hv2'⟩⟩ := JointRot.regs_some v hv
  have hrv : regsAt v = (some v1, some v2) := Prod.ext hv1 hv2'
  have l1 : v1.length < v.length := JointInduction.regsAt_lt v v1 (Or.inl hv1)
  have l2 : v2.length < v.length := JointInduction.regsAt_lt v v2 (Or.inr hv2')
  have hr : regsAt (v ++ [Digit.one]) = (some v, some v) := by
    simp [WeakStepPaper.regsAt_snoc, SurgicalWeak.regStep]
  have hu1 : v.length < (v ++ [Digit.one]).length := hlt
  have hu2 : v.length < (v ++ [Digit.one]).length := hlt
  have hb1 : below f (v ++ [Digit.one]) v = f v := JointRot.below_of_lt f _ _ hu1
  have hb2 : below f (v ++ [Digit.one]) v = f v := JointRot.below_of_lt f _ _ hu2
  have hbv : below f (v ++ [Digit.one]) v = f v := JointRot.below_of_lt f _ _ hlt
  have hp := (WeakStepAssembly.regsAt_parents (v ++ [Digit.one])).1 v (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents (v ++ [Digit.one])).2 v (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := regOdd_data D hS hA f _ hg v hu1
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
  obtain ⟨b4, h4p⟩ := h4p
  have h4p' : ∀ x, x - ((parentsAt v).even.den, (parentsAt v).even.num) ∈ (↑(f v1).tOdd.dom : Set (ℤ × ℤ)) →
      (f v).aEven.val x = (f v1).tOdd.val (x - ((parentsAt v).even.den, (parentsAt v).even.num)) + dotS 0 x + ((b4 + βP2) - βP2) := fun x hx => by
    rw [h4p x hx]; ring
  have hpar2 := (parentsAt_valid v).odd_parity
  have hqe2 := (parentsAt_valid v).even_parity
  unfold Fraction.Odd at hpar2
  unfold Fraction.Even at hqe2
  have hwb : ¬ IsBase (v ++ [Digit.one]) := by
    rintro (h | h | h)
    · simp at h
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inl fun d hd => h d (by simp [hd])))
    · first | exact absurd (h _ (by simp)) (by decide) | exact hv (Or.inr (Or.inr fun d hd => h d (by simp [hd])))
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ v v hg hwb hr 0).1
  have hW : W1Odd (v ++ [Digit.one]) = true := by simp [W1Odd, hph]
  have hc : (SurgicalAlt.altTypeOf (v ++ [Digit.one])).bind (fun ty => SurgicalAlt.altQ1Coeff (W1Odd (v ++ [Digit.one])) ty) = some (1, 1, -1, 0) := by
    simp [SurgicalAlt.altTypeOf, hW, SurgicalAlt.altQ1Coeff]
  have ht : altOff (v ++ [Digit.one]) (1, 1, -1, 0) = (texV1Odd (parentsAt (v ++ [Digit.one])).odd + texV2 (parentsAt (v ++ [Digit.one])).odd - texV1Even (parentsAt (v ++ [Digit.one])).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2] <;> ring
  have hη : altAff (v ++ [Digit.one]) (1, 1, -1, 0) = ((parentsAt (v ++ [Digit.one])).odd.num, -(parentsAt (v ++ [Digit.one])).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  obtain ⟨k, hk⟩ := hk v (by rw [hr])
  have hov := hov v v hr
  refine ⟨_, AltSeven.seven_oo1 D.S (fun u => (below f (v ++ [Digit.one]) u).tOdd) (fun u => (below f (v ++ [Digit.one]) u).tEven)
    (fun u => (below f (v ++ [Digit.one]) u).aOdd) (fun u => (below f (v ++ [Digit.one]) u).aEven) (fun u => (below f (v ++ [Digit.one]) u).lOdd) (v ++ [Digit.one]) v v hph (by simp) hr hp hq
    (parentsAt v).odd.num (parentsAt v).odd.den (parentsAt v).even.num (parentsAt v).even.den hpar2 hqe2
    ⟨by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine],
      by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]⟩
    (f v1).tOdd (f v2).tEven βP βQ (b4 + βP2) βP2 βQ2
    (by simp only [hb1]; exact hdP) (by simp only [hb1]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb1]; exact hcQ)
    (by simp only [hb1]; exact hhP) (by simp only [hb1]; exact ⟨k, hk⟩) (by simp only [hb1]; exact hcompat) hcP2 hcQ2 hhP2 hhQ2
    (by simp only [hb1]; exact fun x hx => (hhH x hx).2)
    (by simp only [hb1]; exact hd1) (by simp only [hb1]; exact hd2) (by simp only [hb1]; exact hd4) (by simp only [hb1]; exact hd5)
    (by simp only [hb1]; exact h1p) (by simp only [hb1]; exact h2p) (by simp only [hb1]; exact h4p') (by simp only [hb1]; exact h5p)
    (fun j hj => hpc_odd D.S _ _ _ _ _ (v ++ [Digit.one]) v v _ _ _ hr (by simp) hc ht hη (by simp only [hb1]; exact hdP)
      (by simp only [hb1]; exact hdQ) j hj (hpc j hj)) hov⟩

/-- Case 3 from the family, odd alternate child, `W_1` even, last digit `3`. -/
theorem family_oe3 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (v : Word) (hg : GoodBelow D f (v ++ [Digit.three]).length) (hv : ¬ IsBase v)
    (hph : phase (v ++ [Digit.three]) ≠ 1) (hvc : v.getLast? ≠ some Digit.three)
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
  obtain ⟨c', hc'⟩ : ∃ c', (SurgicalAlt.altTypeOf v).bind (fun ty => SurgicalAlt.altP1Coeff (W1Odd v) ty) = some c' := by
    obtain ⟨v', d, rfl⟩ : ∃ v' d, v = v' ++ [d] := by
      cases v using List.reverseRecOn with
      | nil => exact (hv (Or.inl rfl)).elim
      | append_singleton v' d => exact ⟨v', d, rfl⟩
    cases d <;> simp [SurgicalAlt.altTypeOf, SurgicalAlt.altP1Coeff] at hvc ⊢ <;> split_ifs <;> exact ⟨_, _, _, _, rfl⟩
  rw [AltPiecesAgree.aEven_list D.S _ _ _ _ _ v v1 v2 c' hrv hvc hc'] at hRP
  simp only [JointRot.below_of_lt f v v1 l1, JointRot.below_of_lt f v v2 l2] at hRP
  obtain ⟨hd0, h0p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altEvenD v).getD 0 0) ((altEvenAff v).getD 0 0) 0 0 (by simp)
    (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd1, h1p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altEvenD v).getD 1 0) ((altEvenAff v).getD 1 0) (((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) - ((parentsAt v).even.den, (parentsAt v).even.num)) ((parentsAt v).odd.num, -(parentsAt v).odd.den) (by simp)
    (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd2, h2p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altEvenD v).getD 2 0) ((altEvenAff v).getD 2 0) ((2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den)) ((parentsAt v).odd.num, -(parentsAt v).odd.den) (by simp)
    (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd3, h3p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altEvenD v).getD 3 0) ((altEvenAff v).getD 3 0) ((2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + (2 : ℤ) • ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) - ((parentsAt v).even.den, (parentsAt v).even.num)) ((2 : ℤ) • ((parentsAt v).odd.num, -(parentsAt v).odd.den)) (by simp)
    (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA] <;> ring)
  obtain ⟨hd4, h4p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altEvenR v).getD 0 0) ((altEvenAff v).getD 4 0) ((parentsAt v).even.den, (parentsAt v).even.num) 0 (by simp)
    (by ext <;> simp [altEvenR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd5, h5p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altEvenR v).getD 1 0) ((altEvenAff v).getD 5 0) (((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) - ((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den)) (((parentsAt v).odd.num, -(parentsAt v).odd.den) + ((parentsAt v).even.num, -(parentsAt v).even.den)) (by simp)
    (by ext <;> simp [altEvenR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA]; ring)
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
  refine ⟨_, AltSeven.seven_oe3 D.S (fun u => (below f (v ++ [Digit.three]) u).tOdd) (fun u => (below f (v ++ [Digit.three]) u).tEven)
    (fun u => (below f (v ++ [Digit.three]) u).aOdd) (fun u => (below f (v ++ [Digit.three]) u).aEven) (fun u => (below f (v ++ [Digit.three]) u).lOdd) (v ++ [Digit.three]) v1 v hph (by simp) hr hp hq
    (parentsAt v).odd.num (parentsAt v).odd.den (parentsAt v).even.num (parentsAt v).even.den hpar2 hqe2
    ⟨by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine],
      by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]⟩
    (f v1).tOdd (f v2).tEven βP βQ ((f v).aEven.val 0) βP2 βQ2
    (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb1]; exact hhP) (by simp only [hb1]; exact ⟨k, hk⟩) (by simp only [hb1, hb2]; exact hcompat) hcP2 hcQ2 hhP2 hhQ2
    (by simp only [hb2]; exact fun x hx => (hhH x hx).2) (by simp only [hb2])
    (by simp only [hb2]; exact hd0) (by simp only [hb2]; exact hd1) (by simp only [hb2]; exact hd2) (by simp only [hb2]; exact hd3)
    (by simp only [hb2]; exact hd4) (by simp only [hb2]; exact hd5) (by simp only [hb2]; exact h0p) (by simp only [hb2]; exact h1p)
    (by simp only [hb2]; exact h2p) (by simp only [hb2]; exact h3p) (by simp only [hb2]; exact h4p) (by simp only [hb2]; exact h5p)
    (fun j hj => hpc_odd D.S _ _ _ _ _ (v ++ [Digit.three]) v1 v _ _ _ hr (by simp) hc ht hη (by simp only [hb1]; exact hdP)
      (by simp only [hb2]; exact hdQ) j hj (hpc j hj)) hov⟩

/-- Case 3 from the family, odd alternate child, `W_1` odd, last digit `3`. -/
theorem family_oo3 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (v : Word) (hg : GoodBelow D f (v ++ [Digit.three]).length) (hv : ¬ IsBase v)
    (hph : phase (v ++ [Digit.three]) = 1) (hvc : v.getLast? ≠ some Digit.three)
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
  obtain ⟨c', hc'⟩ : ∃ c', (SurgicalAlt.altTypeOf v).bind (fun ty => SurgicalAlt.altP1Coeff (W1Odd v) ty) = some c' := by
    obtain ⟨v', d, rfl⟩ : ∃ v' d, v = v' ++ [d] := by
      cases v using List.reverseRecOn with
      | nil => exact (hv (Or.inl rfl)).elim
      | append_singleton v' d => exact ⟨v', d, rfl⟩
    cases d <;> simp [SurgicalAlt.altTypeOf, SurgicalAlt.altP1Coeff] at hvc ⊢ <;> split_ifs <;> exact ⟨_, _, _, _, rfl⟩
  rw [AltPiecesAgree.aEven_list D.S _ _ _ _ _ v v1 v2 c' hrv hvc hc'] at hRP
  simp only [JointRot.below_of_lt f v v1 l1, JointRot.below_of_lt f v v2 l2] at hRP
  obtain ⟨hd0, h0p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altEvenD v).getD 0 0) ((altEvenAff v).getD 0 0) (2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) 0 (by simp)
    (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd1, h1p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altEvenD v).getD 1 0) ((altEvenAff v).getD 1 0) ((2 * (parentsAt v).odd.den, 2 * (parentsAt v).odd.num) + ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((parentsAt v).even.den, (parentsAt v).even.num)) ((parentsAt v).odd.num, -(parentsAt v).odd.den) (by simp)
    (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd2, h2p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altEvenD v).getD 2 0) ((altEvenAff v).getD 2 0) ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) ((parentsAt v).odd.num, -(parentsAt v).odd.den) (by simp)
    (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd3, h3p⟩ := sub_of_respects _ _ hRP (f v2).tEven ((altEvenD v).getD 3 0) ((altEvenAff v).getD 3 0) ((2 : ℤ) • ((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + ((parentsAt v).even.den, (parentsAt v).even.num)) ((2 : ℤ) • ((parentsAt v).odd.num, -(parentsAt v).odd.den)) (by simp)
    (by ext <;> simp [altEvenD, cofW, shiftQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, hphv, texV1Odd, texV1Even, texV2] <;> ring) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA] <;> ring)
  obtain ⟨hd4, h4p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altEvenR v).getD 0 0) ((altEvenAff v).getD 4 0) 0 0 (by simp)
    (by ext <;> simp [altEvenR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA])
  obtain ⟨hd5, h5p⟩ := sub_of_respects _ _ hRP (f v1).tOdd ((altEvenR v).getD 1 0) ((altEvenAff v).getD 5 0) (((parentsAt v).odd.num - (parentsAt v).odd.den, (parentsAt v).odd.num + (parentsAt v).odd.den) + (2 : ℤ) • ((parentsAt v).even.den, (parentsAt v).even.num) + ((parentsAt v).even.num - (parentsAt v).even.den, (parentsAt v).even.num + (parentsAt v).even.den)) (((parentsAt v).odd.num, -(parentsAt v).odd.den) + ((parentsAt v).even.num, -(parentsAt v).even.den)) (by simp)
    (by ext <;> simp [altEvenR, cofW, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, hphv, texV1Odd, texV1Even, texV2]) (by ext <;> simp [altEvenAff, cafW, affS, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, hphv, offsetA]; ring)
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
  refine ⟨_, AltSeven.seven_oo3 D.S (fun u => (below f (v ++ [Digit.three]) u).tOdd) (fun u => (below f (v ++ [Digit.three]) u).tEven)
    (fun u => (below f (v ++ [Digit.three]) u).aOdd) (fun u => (below f (v ++ [Digit.three]) u).aEven) (fun u => (below f (v ++ [Digit.three]) u).lOdd) (v ++ [Digit.three]) v1 v hph (by simp) hr hp hq
    (parentsAt v).odd.num (parentsAt v).odd.den (parentsAt v).even.num (parentsAt v).even.den hpar2 hqe2
    ⟨by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine],
      by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine], by simp [parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]⟩
    (f v1).tOdd (f v2).tEven βP βQ ((f v).aEven.val 0) βP2 βQ2
    (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb1]; exact hhP) (by simp only [hb1]; exact ⟨k, hk⟩) (by simp only [hb1, hb2]; exact hcompat) hcP2 hcQ2 hhP2 hhQ2
    (by simp only [hb2]; exact fun x hx => (hhH x hx).2) (by simp only [hb2])
    (by simp only [hb2]; exact hd0) (by simp only [hb2]; exact hd1) (by simp only [hb2]; exact hd2) (by simp only [hb2]; exact hd3)
    (by simp only [hb2]; exact hd4) (by simp only [hb2]; exact hd5) (by simp only [hb2]; exact h0p) (by simp only [hb2]; exact h1p)
    (by simp only [hb2]; exact h2p) (by simp only [hb2]; exact h3p) (by simp only [hb2]; exact h4p) (by simp only [hb2]; exact h5p)
    (fun j hj => hpc_odd D.S _ _ _ _ _ (v ++ [Digit.three]) v1 v _ _ _ hr (by simp) hc ht hη (by simp only [hb1]; exact hdP)
      (by simp only [hb2]; exact hdQ) j hj (hpc j hj)) hov⟩

end FLatticePaper.Tiles.AltSevenFamily
