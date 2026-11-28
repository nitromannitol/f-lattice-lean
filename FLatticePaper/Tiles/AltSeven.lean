import FLatticePaper.Tiles.AltPiecesAgree
import FLatticePaper.Tiles.AltParentEF1
import FLatticePaper.Tiles.AltParentOF1
import FLatticePaper.Tiles.AltParentEF2
import FLatticePaper.Tiles.AltParentOF2
import FLatticePaper.Tiles.AltParentOE1
import FLatticePaper.Tiles.AltParentOO1
import FLatticePaper.Tiles.AltParentOE3
import FLatticePaper.Tiles.AltParentOO3

/-! # Case 3: the seven pieces of an alternate decomposition agree, uncorrected words with the parent piece

For each orientation and each type that keeps the parent piece (types `1, 2` for the even alternate child, `1, 3` for the odd
one), at a word that is not corrected: the six standard copies (`AltSixEven`, `AltSixEvenOF`, `AltSixOdd`), the constants of the
subtiles of the parent piece one level up (`AltParentEven`, `AltEvenTilePieces`) and the six parent contacts (`AltParentEF1` and
the others) give `PiecesAgree` for `tileAltEvenPieces`, `tileAltOddPieces` with explicit constants (`AltPiecesAgree.sevenAgree_of`).
The parent contacts take the local compatibility of the parent piece with each copy (`hpc`, `TileCompatInputs.PairCompat` of the
entries `6, j`); the overlaps of the six copies are as in `SixOverlaps`. -/

namespace FLatticePaper.Tiles.AltSeven

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.ClosedPathSum
open FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.AltSixEven FLatticePaper.Tiles.AltParentEven FLatticePaper.Tiles.AltPiecesAgree
open FLatticePaper.Tiles.AltSixOdd (kOddEF kOddOF)
open FLatticePaper.Tiles.JointFamily (h0 stdPiece tileAltEvenPieces tileAltOddPieces altOff altAff W1Odd)
open FLatticePaper.Tiles.JointGlue (pieceVal PiecesAgree)
open FLatticePaper.Tiles.SurgicalWeak (regsAt)
open FLatticePaper.Tiles.SurgicalAlt (altTypeOf altP1Coeff altQ1Coeff)
open FLatticePaper.Tiles.Standard (oddTile evenTile)

/-- Case 3, even alternate child, `W_1` even, type 1. -/
theorem seven_ef1 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hl : w.getLast? = some Digit.one) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 + nq2 ∧ (parentsAt w).odd.den = dp2 + dq2 ∧
      (parentsAt w).even.num = 2 * np2 + nq2 ∧ (parentsAt w).even.den = 2 * dp2 + dq2)
    (oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : (pOdd u1).dom = oddTile u1) (hdQ : (pEven u2).dom = evenTile u2)
    (hcP : TileTranslation.StdCornerValues (pOdd u1) 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues (pEven u2) 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhR : ∀ y ∈ tEvenSet u2,
      texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y ∈ tEvenSet u2 ∧
      2 * ((pEven u2).val (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y) - (pEven u2).val y) =
        dotS ((parentsAt w).even.num, -(parentsAt w).even.den) (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((parentsAt w).even.num, -(parentsAt w).even.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ w ∈ tEvenSet u2 →
      (pEven u2).val (x + shiftQ w) - (pEven u2).val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatEven w u1 u2 (placedAltEven w (pOdd u1).val (pEven u2).val 0))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hhP2 : ∀ y ∈ (↑oP2.dom : Set (ℤ × ℤ)),
      (2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP2.dom : Set _) ∧
      2 * (oP2.val ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y) - oP2.val y) =
        dotS (np2, -dp2) ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np2, -dp2) y)
    (hhQ2 : ∀ y ∈ (↑oQ2.dom : Set (ℤ × ℤ)),
      (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ2.dom : Set _) ∧
      2 * (oQ2.val ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ2.val y) =
        dotS (nq2, -dq2) ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq2, -dq2) y)
    (hhH : ∀ x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)),
      2 * ((aOdd u1).val ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - x) - (aOdd u1).val x) =
      dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) x)
    (hN : (aOdd u1).val 0 = βH)
    (hd0 : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd3 : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd5 : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (h0p : ∃ b : ℤ, ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oP2.val (x - 0) + dotS 0 x + b)
    (h3p : ∃ b : ℤ, ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oP2.val (x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + b)
    (h4p : ∃ b : ℤ, ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oQ2.val (x - (2 * dp2, 2 * np2)) + dotS 0 x + b)
    (h5p : ∃ b : ℤ, ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oQ2.val (x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + b)
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)) → z ∈ dAE w u1 u2 j →
      (aOdd u1).val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven) :
    PiecesAgree (tileAltEvenPieces S pOdd pEven aOdd aEven lX w) (kappa7 (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH)) := by
  obtain ⟨b0, h0p⟩ := h0p
  obtain ⟨b3, h3p⟩ := h3p
  obtain ⟨b4, h4p⟩ := h4p
  obtain ⟨b5, h5p⟩ := h5p
  obtain ⟨e0, e4, e3, e5⟩ := oddPieces_of np2 dp2 nq2 dq2 hpar2 hqe2 (aOdd u1) oP2 oQ2 βH βP2 βQ2 b0 b3 b4 b5 hcP2 hcQ2
    hhP2 hhQ2 hhH hN (fun x hx => hd0 x (by simpa using hx)) hd4 h0p h3p h4p h5p
  subst e0 e3 e4 e5
  have hsix := sixEven_ef w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = false := by simpa [W1Odd] using hph
  have hc : (altTypeOf w).bind (fun ty => altP1Coeff (W1Odd w) ty) = some (1, 1, -1, 0) := by
    simp [altTypeOf, hl, hW, altP1Coeff]
  have ht : altOff w (1, 1, -1, 0) = (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2] <;> ring
  have hη : altAff w (1, 1, -1, 0) = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aEven_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven
    (placedAltEven w (pOdd u1).val (pEven u2).val 0) (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH) rfl (by simp [altEvenD, altEvenR])
    (aEven_std w u1 u2 (pOdd u1) (pEven u2) (aOdd u1) _ _ hdP hdQ) ?_ ?_ hov
  · have e : (fun i z => placedAltEven w (pOdd u1).val (pEven u2).val 0 i z + (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) i) =
        placedAltEven w (pOdd u1).val (pEven u2).val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) := by
      funext i z
      exact AltSixEven.placedAltEven_add w _ _ _ i z
    rw [e]
    exact hsix
  · intro p hp6 j hj z hz hzj
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp6
    subst hp6
    rw [mem_placed_std, ht] at hz
    have hv : pieceVal (stdPiece (aOdd u1) (altOff w (1, 1, -1, 0)) (altAff w (1, 1, -1, 0))) z =
        (aOdd u1).val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z := by
      simp only [pieceVal, stdPiece, ht, hη, dot2, dotS]
    rw [hv, AltSixEven.placedAltEven_add]
    interval_cases j
    · exact AltParentEF1.parent_ef1_0 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 hd3 hd4 hd5 h0p h3p h4p h5p (hpc 0 (by norm_num)) z hz hzj
    · exact AltParentEF1.parent_ef1_1 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 hd3 hd4 hd5 h0p h3p h4p h5p (hpc 1 (by norm_num)) z hz hzj
    · exact AltParentEF1.parent_ef1_2 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 hd3 hd4 hd5 h0p h3p h4p h5p (hpc 2 (by norm_num)) z hz hzj
    · exact AltParentEF1.parent_ef1_3 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 hd3 hd4 hd5 h0p h3p h4p h5p (hpc 3 (by norm_num)) z hz hzj
    · exact AltParentEF1.parent_ef1_4 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 hd3 hd4 hd5 h0p h3p h4p h5p (hpc 4 (by norm_num)) z hz hzj
    · exact AltParentEF1.parent_ef1_5 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 hd3 hd4 hd5 h0p h3p h4p h5p (hpc 5 (by norm_num)) z hz hzj

/-- Case 3, even alternate child, `W_1` odd, type 1. -/
theorem seven_of1 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hph : phase w = 1)
    (hl : w.getLast? = some Digit.one) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 + nq2 ∧ (parentsAt w).odd.den = dp2 + dq2 ∧
      (parentsAt w).even.num = 2 * np2 + nq2 ∧ (parentsAt w).even.den = 2 * dp2 + dq2)
    (oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : (pOdd u1).dom = oddTile u1) (hdQ : (pEven u2).dom = evenTile u2)
    (hcP : TileTranslation.StdCornerValues (pOdd u1) 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues (pEven u2) 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhR : ∀ y ∈ tEvenSet u2,
      texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y ∈ tEvenSet u2 ∧
      2 * ((pEven u2).val (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y) - (pEven u2).val y) =
        dotS ((parentsAt w).even.num, -(parentsAt w).even.den) (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((parentsAt w).even.num, -(parentsAt w).even.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ w ∈ tEvenSet u2 →
      (pEven u2).val (x + shiftQ w) - (pEven u2).val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatEven w u1 u2 (placedAltEven w (pOdd u1).val (pEven u2).val 0))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hhP2 : ∀ y ∈ (↑oP2.dom : Set (ℤ × ℤ)),
      (2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP2.dom : Set _) ∧
      2 * (oP2.val ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y) - oP2.val y) =
        dotS (np2, -dp2) ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np2, -dp2) y)
    (hhQ2 : ∀ y ∈ (↑oQ2.dom : Set (ℤ × ℤ)),
      (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ2.dom : Set _) ∧
      2 * (oQ2.val ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ2.val y) =
        dotS (nq2, -dq2) ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq2, -dq2) y)
    (hhH : ∀ x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)),
      2 * ((aOdd u1).val ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - x) - (aOdd u1).val x) =
      dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) x)
    (hN : (aOdd u1).val 0 = βH)
    (hd0 : ∀ x, x - (dq2, nq2) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd3 : ∀ x, x - ((np2 - dp2, np2 + dp2) + (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - 0 ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd5 : ∀ x, x - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (h0p : ∃ b : ℤ, ∀ x, x - (dq2, nq2) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oP2.val (x - (dq2, nq2)) + dotS 0 x + b)
    (h3p : ∃ b : ℤ, ∀ x, x - ((np2 - dp2, np2 + dp2) + (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oP2.val (x - ((np2 - dp2, np2 + dp2) + (dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + b)
    (h4p : ∃ b : ℤ, ∀ x, x - 0 ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oQ2.val (x - 0) + dotS 0 x + b)
    (h5p : ∃ b : ℤ, ∀ x, x - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oQ2.val (x - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + b)
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)) → z ∈ dAE w u1 u2 j →
      (aOdd u1).val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven) :
    PiecesAgree (tileAltEvenPieces S pOdd pEven aOdd aEven lX w) (kappa7 (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH)) := by
  obtain ⟨b0, h0p⟩ := h0p
  obtain ⟨b3, h3p⟩ := h3p
  obtain ⟨b4, h4p⟩ := h4p
  obtain ⟨b5, h5p⟩ := h5p
  obtain ⟨e4, e0, e3, e5⟩ := oddPiecesEF_of np2 dp2 nq2 dq2 hpar2 hqe2 (aOdd u1) oP2 oQ2 βH βP2 βQ2 b0 b3 b4 b5 hcP2 hcQ2
    hhP2 hhQ2 hhH hN hd0 hd4 h0p h3p h4p h5p
  subst e0 e3 e4 e5
  have hsix := AltSixEvenOF.sixEven_of w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = true := by simp [W1Odd, hph]
  have hc : (altTypeOf w).bind (fun ty => altP1Coeff (W1Odd w) ty) = some (0, 1, 1, 0) := by
    simp [altTypeOf, hl, hW, altP1Coeff]
  have ht : altOff w (0, 1, 1, 0) = (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2]
  have hη : altAff w (0, 1, 1, 0) = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aEven_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven
    (placedAltEven w (pOdd u1).val (pEven u2).val 0) (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH) rfl (by simp [altEvenD, altEvenR])
    (aEven_std w u1 u2 (pOdd u1) (pEven u2) (aOdd u1) _ _ hdP hdQ) ?_ ?_ hov
  · have e : (fun i z => placedAltEven w (pOdd u1).val (pEven u2).val 0 i z + (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) i) =
        placedAltEven w (pOdd u1).val (pEven u2).val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) := by
      funext i z
      exact AltSixEven.placedAltEven_add w _ _ _ i z
    rw [e]
    exact hsix
  · intro p hp6 j hj z hz hzj
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp6
    subst hp6
    rw [mem_placed_std, ht] at hz
    have hv : pieceVal (stdPiece (aOdd u1) (altOff w (0, 1, 1, 0)) (altAff w (0, 1, 1, 0))) z =
        (aOdd u1).val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z := by
      simp only [pieceVal, stdPiece, ht, hη, dot2, dotS]
    rw [hv, AltSixEven.placedAltEven_add]
    interval_cases j
    · exact AltParentOF1.parent_of1_0 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 hd3 hd4 hd5 h0p h3p h4p h5p (hpc 0 (by norm_num)) z hz hzj
    · exact AltParentOF1.parent_of1_1 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 hd3 hd4 hd5 h0p h3p h4p h5p (hpc 1 (by norm_num)) z hz hzj
    · exact AltParentOF1.parent_of1_2 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 hd3 hd4 hd5 h0p h3p h4p h5p (hpc 2 (by norm_num)) z hz hzj
    · exact AltParentOF1.parent_of1_3 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 hd3 hd4 hd5 h0p h3p h4p h5p (hpc 3 (by norm_num)) z hz hzj
    · exact AltParentOF1.parent_of1_4 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 hd3 hd4 hd5 h0p h3p h4p h5p (hpc 4 (by norm_num)) z hz hzj
    · exact AltParentOF1.parent_of1_5 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 hd3 hd4 hd5 h0p h3p h4p h5p (hpc 5 (by norm_num)) z hz hzj

/-- Case 3, even alternate child, `W_1` even, type 2. -/
theorem seven_ef2 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hl : w.getLast? = some Digit.two) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 + nq2 ∧ (parentsAt w).odd.den = dp2 + dq2 ∧
      (parentsAt w).even.num = nq2 ∧ (parentsAt w).even.den = dq2)
    (oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : (pOdd u1).dom = oddTile u1) (hdQ : (pEven u2).dom = evenTile u2)
    (hcP : TileTranslation.StdCornerValues (pOdd u1) 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues (pEven u2) 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhR : ∀ y ∈ tEvenSet u2,
      texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y ∈ tEvenSet u2 ∧
      2 * ((pEven u2).val (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y) - (pEven u2).val y) =
        dotS ((parentsAt w).even.num, -(parentsAt w).even.den) (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((parentsAt w).even.num, -(parentsAt w).even.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ w ∈ tEvenSet u2 →
      (pEven u2).val (x + shiftQ w) - (pEven u2).val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatEven w u1 u2 (placedAltEven w (pOdd u1).val (pEven u2).val 0))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hhP2 : ∀ y ∈ (↑oP2.dom : Set (ℤ × ℤ)),
      (2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP2.dom : Set _) ∧
      2 * (oP2.val ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y) - oP2.val y) =
        dotS (np2, -dp2) ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np2, -dp2) y)
    (hhQ2 : ∀ y ∈ (↑oQ2.dom : Set (ℤ × ℤ)),
      (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ2.dom : Set _) ∧
      2 * (oQ2.val ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ2.val y) =
        dotS (nq2, -dq2) ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq2, -dq2) y)
    (hhH : ∀ x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)),
      2 * ((aOdd u1).val ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - x) - (aOdd u1).val x) =
      dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) x)
    (hN : (aOdd u1).val 0 = βH)
    (hd0 : ∀ x, x - (dq2, nq2) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd1 : ∀ x, x - ((2 : ℤ) • (dq2, nq2) + (np2 - dp2, np2 + dp2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd2 : ∀ x, x - (nq2 - dq2, nq2 + dq2) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd3 : ∀ x, x - ((np2 - dp2, np2 + dp2) + (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - 0 ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd5 : ∀ x, x - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (h0p : ∃ b : ℤ, ∀ x, x - (dq2, nq2) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oP2.val (x - (dq2, nq2)) + dotS 0 x + b)
    (h1p : ∃ b : ℤ, ∀ x, x - ((2 : ℤ) • (dq2, nq2) + (np2 - dp2, np2 + dp2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oP2.val (x - ((2 : ℤ) • (dq2, nq2) + (np2 - dp2, np2 + dp2))) + dotS (np2, -dp2) x + b)
    (h2p : ∃ b : ℤ, ∀ x, x - (nq2 - dq2, nq2 + dq2) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oP2.val (x - (nq2 - dq2, nq2 + dq2)) + dotS (nq2, -dq2) x + b)
    (h3p : ∃ b : ℤ, ∀ x, x - ((np2 - dp2, np2 + dp2) + (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oP2.val (x - ((np2 - dp2, np2 + dp2) + (dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + b)
    (h4p : ∃ b : ℤ, ∀ x, x - 0 ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oQ2.val (x - 0) + dotS 0 x + b)
    (h5p : ∃ b : ℤ, ∀ x, x - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oQ2.val (x - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + b)
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)) → z ∈ dAE w u1 u2 j →
      (aOdd u1).val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven) :
    PiecesAgree (tileAltEvenPieces S pOdd pEven aOdd aEven lX w) (kappa7 (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2) - βH)) := by
  obtain ⟨b0, h0p⟩ := h0p
  obtain ⟨b1, h1p⟩ := h1p
  obtain ⟨b2, h2p⟩ := h2p
  obtain ⟨b3, h3p⟩ := h3p
  obtain ⟨b4, h4p⟩ := h4p
  obtain ⟨b5, h5p⟩ := h5p
  obtain ⟨e4, e0, e3, e5⟩ := oddPiecesEF_of np2 dp2 nq2 dq2 hpar2 hqe2 (aOdd u1) oP2 oQ2 βH βP2 βQ2 b0 b3 b4 b5 hcP2 hcQ2
    hhP2 hhQ2 hhH hN hd0 hd4 h0p h3p h4p h5p
  subst e0 e3 e4 e5
  obtain ⟨e1, e2⟩ := oddPieces12EF_of np2 dp2 nq2 dq2 hpar2 hqe2 _ rfl (aOdd u1) oP2 oQ2 βH βP2 βQ2 b1 b2 _ hcP2 hcQ2 hhP2 hhH
    hd1 h1p h2p h5p rfl
  subst e1 e2
  have hsix := sixEven_ef w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = false := by simpa [W1Odd] using hph
  have hc : (altTypeOf w).bind (fun ty => altP1Coeff (W1Odd w) ty) = some (0, 0, 0, 1) := by
    simp [altTypeOf, hl, hW, altP1Coeff]
  have ht : altOff w (0, 0, 0, 1) = (texV2 (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2]
  have hη : altAff w (0, 0, 0, 1) = ((parentsAt w).even.num, -(parentsAt w).even.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aEven_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven
    (placedAltEven w (pOdd u1).val (pEven u2).val 0) (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2) - βH) rfl (by simp [altEvenD, altEvenR])
    (aEven_std w u1 u2 (pOdd u1) (pEven u2) (aOdd u1) _ _ hdP hdQ) ?_ ?_ hov
  · have e : (fun i z => placedAltEven w (pOdd u1).val (pEven u2).val 0 i z + (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) i) =
        placedAltEven w (pOdd u1).val (pEven u2).val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) := by
      funext i z
      exact AltSixEven.placedAltEven_add w _ _ _ i z
    rw [e]
    exact hsix
  · intro p hp6 j hj z hz hzj
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp6
    subst hp6
    rw [mem_placed_std, ht] at hz
    have hv : pieceVal (stdPiece (aOdd u1) (altOff w (0, 0, 0, 1)) (altAff w (0, 0, 0, 1))) z =
        (aOdd u1).val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z := by
      simp only [pieceVal, stdPiece, ht, hη, dot2, dotS]
    rw [hv, AltSixEven.placedAltEven_add]
    interval_cases j
    · exact AltParentEF2.parent_ef2_0 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 0 (by norm_num)) z hz hzj
    · exact AltParentEF2.parent_ef2_1 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 1 (by norm_num)) z hz hzj
    · exact AltParentEF2.parent_ef2_2 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 2 (by norm_num)) z hz hzj
    · exact AltParentEF2.parent_ef2_3 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 3 (by norm_num)) z hz hzj
    · exact AltParentEF2.parent_ef2_4 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 4 (by norm_num)) z hz hzj
    · exact AltParentEF2.parent_ef2_5 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 5 (by norm_num)) z hz hzj

/-- Case 3, even alternate child, `W_1` odd, type 2. -/
theorem seven_of2 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hph : phase w = 1)
    (hl : w.getLast? = some Digit.two) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 + nq2 ∧ (parentsAt w).odd.den = dp2 + dq2 ∧
      (parentsAt w).even.num = nq2 ∧ (parentsAt w).even.den = dq2)
    (oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : (pOdd u1).dom = oddTile u1) (hdQ : (pEven u2).dom = evenTile u2)
    (hcP : TileTranslation.StdCornerValues (pOdd u1) 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues (pEven u2) 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhR : ∀ y ∈ tEvenSet u2,
      texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y ∈ tEvenSet u2 ∧
      2 * ((pEven u2).val (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y) - (pEven u2).val y) =
        dotS ((parentsAt w).even.num, -(parentsAt w).even.den) (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((parentsAt w).even.num, -(parentsAt w).even.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ w ∈ tEvenSet u2 →
      (pEven u2).val (x + shiftQ w) - (pEven u2).val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatEven w u1 u2 (placedAltEven w (pOdd u1).val (pEven u2).val 0))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hhP2 : ∀ y ∈ (↑oP2.dom : Set (ℤ × ℤ)),
      (2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP2.dom : Set _) ∧
      2 * (oP2.val ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y) - oP2.val y) =
        dotS (np2, -dp2) ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np2, -dp2) y)
    (hhQ2 : ∀ y ∈ (↑oQ2.dom : Set (ℤ × ℤ)),
      (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ2.dom : Set _) ∧
      2 * (oQ2.val ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ2.val y) =
        dotS (nq2, -dq2) ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq2, -dq2) y)
    (hhH : ∀ x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)),
      2 * ((aOdd u1).val ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - x) - (aOdd u1).val x) =
      dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) x)
    (hN : (aOdd u1).val 0 = βH)
    (hd0 : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd1 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd2 : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd3 : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (hd5 : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)))
    (h0p : ∃ b : ℤ, ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oP2.val (x - 0) + dotS 0 x + b)
    (h1p : ∃ b : ℤ, ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oP2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS (np2, -dp2) x + b)
    (h2p : ∃ b : ℤ, ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oP2.val (x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS (nq2, -dq2) x + b)
    (h3p : ∃ b : ℤ, ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oP2.val (x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + b)
    (h4p : ∃ b : ℤ, ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oQ2.val (x - (2 * dp2, 2 * np2)) + dotS 0 x + b)
    (h5p : ∃ b : ℤ, ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aOdd u1).val x = oQ2.val (x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + b)
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)) → z ∈ dAE w u1 u2 j →
      (aOdd u1).val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven) :
    PiecesAgree (tileAltEvenPieces S pOdd pEven aOdd aEven lX w) (kappa7 (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).odd.num - 2 * (parentsAt w).odd.den * (parentsAt w).even.num) - βH)) := by
  obtain ⟨b0, h0p⟩ := h0p
  obtain ⟨b1, h1p⟩ := h1p
  obtain ⟨b2, h2p⟩ := h2p
  obtain ⟨b3, h3p⟩ := h3p
  obtain ⟨b4, h4p⟩ := h4p
  obtain ⟨b5, h5p⟩ := h5p
  obtain ⟨e0, e4, e3, e5⟩ := oddPieces_of np2 dp2 nq2 dq2 hpar2 hqe2 (aOdd u1) oP2 oQ2 βH βP2 βQ2 b0 b3 b4 b5 hcP2 hcQ2
    hhP2 hhQ2 hhH hN (fun x hx => hd0 x (by simpa using hx)) hd4 h0p h3p h4p h5p
  subst e0 e3 e4 e5
  obtain ⟨e1, e2⟩ := oddPieces12_of np2 dp2 nq2 dq2 hpar2 hqe2 _ rfl (aOdd u1) oP2 oQ2 βH βP2 βQ2 b1 b2 _ hcP2 hcQ2 hhP2 hhH
    hd1 h1p h2p h5p rfl
  subst e1 e2
  have hsix := AltSixEvenOF.sixEven_of w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = true := by simp [W1Odd, hph]
  have hc : (altTypeOf w).bind (fun ty => altP1Coeff (W1Odd w) ty) = some (0, 0, 2, 1) := by
    simp [altTypeOf, hl, hW, altP1Coeff]
  have ht : altOff w (0, 0, 2, 1) = (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2] <;> ring
  have hη : altAff w (0, 0, 2, 1) = ((parentsAt w).even.num, -(parentsAt w).even.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aEven_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven
    (placedAltEven w (pOdd u1).val (pEven u2).val 0) (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).odd.num - 2 * (parentsAt w).odd.den * (parentsAt w).even.num) - βH) rfl (by simp [altEvenD, altEvenR])
    (aEven_std w u1 u2 (pOdd u1) (pEven u2) (aOdd u1) _ _ hdP hdQ) ?_ ?_ hov
  · have e : (fun i z => placedAltEven w (pOdd u1).val (pEven u2).val 0 i z + (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) i) =
        placedAltEven w (pOdd u1).val (pEven u2).val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) := by
      funext i z
      exact AltSixEven.placedAltEven_add w _ _ _ i z
    rw [e]
    exact hsix
  · intro p hp6 j hj z hz hzj
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp6
    subst hp6
    rw [mem_placed_std, ht] at hz
    have hv : pieceVal (stdPiece (aOdd u1) (altOff w (0, 0, 2, 1)) (altAff w (0, 0, 2, 1))) z =
        (aOdd u1).val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z := by
      simp only [pieceVal, stdPiece, ht, hη, dot2, dotS]
    rw [hv, AltSixEven.placedAltEven_add]
    interval_cases j
    · exact AltParentOF2.parent_of2_0 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 0 (by norm_num)) z hz hzj
    · exact AltParentOF2.parent_of2_1 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 1 (by norm_num)) z hz hzj
    · exact AltParentOF2.parent_of2_2 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 2 (by norm_num)) z hz hzj
    · exact AltParentOF2.parent_of2_3 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 3 (by norm_num)) z hz hzj
    · exact AltParentOF2.parent_of2_4 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 4 (by norm_num)) z hz hzj
    · exact AltParentOF2.parent_of2_5 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aOdd u1) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 5 (by norm_num)) z hz hzj

/-- Case 3, odd alternate child, `W_1` even, type 1. -/
theorem seven_oe1 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hl : w.getLast? = some Digit.one) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 + nq2 ∧ (parentsAt w).odd.den = dp2 + dq2 ∧
      (parentsAt w).even.num = 2 * np2 + nq2 ∧ (parentsAt w).even.den = 2 * dp2 + dq2)
    (oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : (pOdd u1).dom = oddTile u1) (hdQ : (pEven u2).dom = evenTile u2)
    (hcP : TileTranslation.StdCornerValues (pOdd u1) 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues (pEven u2) 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhR : ∀ y ∈ tOddSet u1,
      texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y ∈ tOddSet u1 ∧
      2 * ((pOdd u1).val (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y) - (pOdd u1).val y) =
        dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      (pOdd u1).val (x + shiftP w) - (pOdd u1).val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w (pOdd u1).val (pEven u2).val 0))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hhP2 : ∀ y ∈ (↑oP2.dom : Set (ℤ × ℤ)),
      (2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP2.dom : Set _) ∧
      2 * (oP2.val ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y) - oP2.val y) =
        dotS (np2, -dp2) ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np2, -dp2) y)
    (hhQ2 : ∀ y ∈ (↑oQ2.dom : Set (ℤ × ℤ)),
      (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ2.dom : Set _) ∧
      2 * (oQ2.val ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ2.val y) =
        dotS (nq2, -dq2) ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq2, -dq2) y)
    (hhH : ∀ x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)),
      2 * ((aEven u2).val ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - x) - (aEven u2).val x) =
      dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) x)
    (hd1 : ∀ x, x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd2 : ∀ x, x - (np2 - dp2, np2 + dp2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd5 : ∀ x, x - ((np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (h1p : ∃ b : ℤ, ∀ x, x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oQ2.val (x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + (dq2, nq2))) + dotS (np2, -dp2) x + b)
    (h2p : ∃ b : ℤ, ∀ x, x - (np2 - dp2, np2 + dp2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oQ2.val (x - (np2 - dp2, np2 + dp2)) + dotS (np2, -dp2) x + b)
    (h4p : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oP2.val (x - 0) + dotS 0 x + (βH - βP2))
    (h5p : ∃ b : ℤ, ∀ x, x - ((np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oP2.val (x - ((np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + b)
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)) → z ∈ dAO w u1 u2 j →
      (aEven u2).val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven) :
    PiecesAgree (tileAltOddPieces S pOdd pEven aOdd aEven lX w) (kappa7 (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH)) := by
  obtain ⟨b1, h1p⟩ := h1p
  obtain ⟨b2, h2p⟩ := h2p
  obtain ⟨b5, h5p⟩ := h5p
  obtain ⟨e1, e2, e5⟩ := AltEvenTilePieces.evenPieces1245_of np2 dp2 nq2 dq2 hpar2 hqe2 (aEven u2) oP2 oQ2 βH βP2 βQ2
    b1 b2 _ b5 hcP2 hcQ2 hhP2 hhQ2 hhH hd2 hd4 h1p h2p h4p h5p rfl
  subst e1 e2 e5
  have hsix := AltSixOdd.sixOdd_ef w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = false := by simpa [W1Odd] using hph
  have hc : (altTypeOf w).bind (fun ty => altQ1Coeff (W1Odd w) ty) = some (0, 1, 1, 0) := by
    simp [altTypeOf, hl, hW, altQ1Coeff]
  have ht : altOff w (0, 1, 1, 0) = (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2]
  have hη : altAff w (0, 1, 1, 0) = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aOdd_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven
    (placedAltOdd w (pOdd u1).val (pEven u2).val 0) (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH) rfl (by simp [altOddD, altOddR])
    (aOdd_std w u1 u2 (pOdd u1) (pEven u2) (aEven u2) _ _ hdP hdQ) ?_ ?_ hov
  · have e : (fun i z => placedAltOdd w (pOdd u1).val (pEven u2).val 0 i z + (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) i) =
        placedAltOdd w (pOdd u1).val (pEven u2).val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) := by
      funext i z
      exact AltSixOdd.placedAltOdd_add w _ _ _ i z
    rw [e]
    exact hsix
  · intro p hp6 j hj z hz hzj
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp6
    subst hp6
    rw [mem_placed_std, ht] at hz
    have hv : pieceVal (stdPiece (aEven u2) (altOff w (0, 1, 1, 0)) (altAff w (0, 1, 1, 0))) z =
        (aEven u2).val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z := by
      simp only [pieceVal, stdPiece, ht, hη, dot2, dotS]
    rw [hv, AltSixOdd.placedAltOdd_add]
    interval_cases j
    · exact AltParentOE1.parent_oe1_0 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd1 h1p hd2 h2p hd4 h4p hd5 h5p (hpc 0 (by norm_num)) z hz hzj
    · exact AltParentOE1.parent_oe1_1 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd1 h1p hd2 h2p hd4 h4p hd5 h5p (hpc 1 (by norm_num)) z hz hzj
    · exact AltParentOE1.parent_oe1_2 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd1 h1p hd2 h2p hd4 h4p hd5 h5p (hpc 2 (by norm_num)) z hz hzj
    · exact AltParentOE1.parent_oe1_3 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd1 h1p hd2 h2p hd4 h4p hd5 h5p (hpc 3 (by norm_num)) z hz hzj
    · exact AltParentOE1.parent_oe1_4 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd1 h1p hd2 h2p hd4 h4p hd5 h5p (hpc 4 (by norm_num)) z hz hzj
    · exact AltParentOE1.parent_oe1_5 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd1 h1p hd2 h2p hd4 h4p hd5 h5p (hpc 5 (by norm_num)) z hz hzj

/-- Case 3, odd alternate child, `W_1` odd, type 1. -/
theorem seven_oo1 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hph : phase w = 1)
    (hl : w.getLast? = some Digit.one) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 + nq2 ∧ (parentsAt w).odd.den = dp2 + dq2 ∧
      (parentsAt w).even.num = 2 * np2 + nq2 ∧ (parentsAt w).even.den = 2 * dp2 + dq2)
    (oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : (pOdd u1).dom = oddTile u1) (hdQ : (pEven u2).dom = evenTile u2)
    (hcP : TileTranslation.StdCornerValues (pOdd u1) 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues (pEven u2) 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhR : ∀ y ∈ tOddSet u1,
      texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y ∈ tOddSet u1 ∧
      2 * ((pOdd u1).val (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y) - (pOdd u1).val y) =
        dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      (pOdd u1).val (x + shiftP w) - (pOdd u1).val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w (pOdd u1).val (pEven u2).val 0))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hhP2 : ∀ y ∈ (↑oP2.dom : Set (ℤ × ℤ)),
      (2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP2.dom : Set _) ∧
      2 * (oP2.val ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y) - oP2.val y) =
        dotS (np2, -dp2) ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np2, -dp2) y)
    (hhQ2 : ∀ y ∈ (↑oQ2.dom : Set (ℤ × ℤ)),
      (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ2.dom : Set _) ∧
      2 * (oQ2.val ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ2.val y) =
        dotS (nq2, -dq2) ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq2, -dq2) y)
    (hhH : ∀ x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)),
      2 * ((aEven u2).val ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - x) - (aEven u2).val x) =
      dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) x)
    (hd1 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd2 : ∀ x, x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - (dq2, nq2) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd5 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (h1p : ∃ b : ℤ, ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oQ2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS (np2, -dp2) x + b)
    (h2p : ∃ b : ℤ, ∀ x, x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oQ2.val (x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2))) + dotS (np2, -dp2) x + b)
    (h4p : ∀ x, x - (dq2, nq2) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oP2.val (x - (dq2, nq2)) + dotS 0 x + (βH - βP2))
    (h5p : ∃ b : ℤ, ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oP2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + b)
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)) → z ∈ dAO w u1 u2 j →
      (aEven u2).val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven) :
    PiecesAgree (tileAltOddPieces S pOdd pEven aOdd aEven lX w) (kappa7 (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH)) := by
  obtain ⟨b1, h1p⟩ := h1p
  obtain ⟨b2, h2p⟩ := h2p
  obtain ⟨b5, h5p⟩ := h5p
  obtain ⟨e1, e2, e5⟩ := AltEvenTilePieces.evenPieces1245EF_of np2 dp2 nq2 dq2 hpar2 hqe2 (aEven u2) oP2 oQ2 βH βP2 βQ2
    b1 b2 _ b5 hcP2 hcQ2 hhP2 hhQ2 hhH hd2 hd4 h1p h2p h4p h5p rfl
  subst e1 e2 e5
  have hsix := AltSixOdd.sixOdd_of w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = true := by simp [W1Odd, hph]
  have hc : (altTypeOf w).bind (fun ty => altQ1Coeff (W1Odd w) ty) = some (1, 1, -1, 0) := by
    simp [altTypeOf, hl, hW, altQ1Coeff]
  have ht : altOff w (1, 1, -1, 0) = (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2] <;> ring
  have hη : altAff w (1, 1, -1, 0) = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aOdd_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven
    (placedAltOdd w (pOdd u1).val (pEven u2).val 0) (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH) rfl (by simp [altOddD, altOddR])
    (aOdd_std w u1 u2 (pOdd u1) (pEven u2) (aEven u2) _ _ hdP hdQ) ?_ ?_ hov
  · have e : (fun i z => placedAltOdd w (pOdd u1).val (pEven u2).val 0 i z + (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) i) =
        placedAltOdd w (pOdd u1).val (pEven u2).val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) := by
      funext i z
      exact AltSixOdd.placedAltOdd_add w _ _ _ i z
    rw [e]
    exact hsix
  · intro p hp6 j hj z hz hzj
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp6
    subst hp6
    rw [mem_placed_std, ht] at hz
    have hv : pieceVal (stdPiece (aEven u2) (altOff w (1, 1, -1, 0)) (altAff w (1, 1, -1, 0))) z =
        (aEven u2).val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z := by
      simp only [pieceVal, stdPiece, ht, hη, dot2, dotS]
    rw [hv, AltSixOdd.placedAltOdd_add]
    interval_cases j
    · exact AltParentOO1.parent_oo1_0 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd1 h1p hd2 h2p hd4 h4p hd5 h5p (hpc 0 (by norm_num)) z hz hzj
    · exact AltParentOO1.parent_oo1_1 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd1 h1p hd2 h2p hd4 h4p hd5 h5p (hpc 1 (by norm_num)) z hz hzj
    · exact AltParentOO1.parent_oo1_2 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd1 h1p hd2 h2p hd4 h4p hd5 h5p (hpc 2 (by norm_num)) z hz hzj
    · exact AltParentOO1.parent_oo1_3 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd1 h1p hd2 h2p hd4 h4p hd5 h5p (hpc 3 (by norm_num)) z hz hzj
    · exact AltParentOO1.parent_oo1_4 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd1 h1p hd2 h2p hd4 h4p hd5 h5p (hpc 4 (by norm_num)) z hz hzj
    · exact AltParentOO1.parent_oo1_5 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd1 h1p hd2 h2p hd4 h4p hd5 h5p (hpc 5 (by norm_num)) z hz hzj

/-- Case 3, odd alternate child, `W_1` even, type 3. -/
theorem seven_oe3 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hl : w.getLast? = some Digit.three) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 ∧ (parentsAt w).odd.den = dp2 ∧
      (parentsAt w).even.num = 2 * np2 + nq2 ∧ (parentsAt w).even.den = 2 * dp2 + dq2)
    (oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : (pOdd u1).dom = oddTile u1) (hdQ : (pEven u2).dom = evenTile u2)
    (hcP : TileTranslation.StdCornerValues (pOdd u1) 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues (pEven u2) 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhR : ∀ y ∈ tOddSet u1,
      texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y ∈ tOddSet u1 ∧
      2 * ((pOdd u1).val (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y) - (pOdd u1).val y) =
        dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      (pOdd u1).val (x + shiftP w) - (pOdd u1).val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w (pOdd u1).val (pEven u2).val 0))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hhP2 : ∀ y ∈ (↑oP2.dom : Set (ℤ × ℤ)),
      (2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP2.dom : Set _) ∧
      2 * (oP2.val ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y) - oP2.val y) =
        dotS (np2, -dp2) ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np2, -dp2) y)
    (hhQ2 : ∀ y ∈ (↑oQ2.dom : Set (ℤ × ℤ)),
      (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ2.dom : Set _) ∧
      2 * (oQ2.val ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ2.val y) =
        dotS (nq2, -dq2) ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq2, -dq2) y)
    (hhH : ∀ x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)),
      2 * ((aEven u2).val ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - x) - (aEven u2).val x) =
      dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) x)
    (hN : (aEven u2).val 0 = βH)
    (hd0 : ∀ x, x - 0 ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd1 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd2 : ∀ x, x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd3 : ∀ x, x - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - (dq2, nq2) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd5 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (h0p : ∃ b : ℤ, ∀ x, x - 0 ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oQ2.val (x - 0) + dotS 0 x + b)
    (h1p : ∃ b : ℤ, ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oQ2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS (np2, -dp2) x + b)
    (h2p : ∃ b : ℤ, ∀ x, x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oQ2.val (x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2))) + dotS (np2, -dp2) x + b)
    (h3p : ∃ b : ℤ, ∀ x, x - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oQ2.val (x - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + b)
    (h4p : ∃ b : ℤ, ∀ x, x - (dq2, nq2) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oP2.val (x - (dq2, nq2)) + dotS 0 x + b)
    (h5p : ∃ b : ℤ, ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oP2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + b)
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)) → z ∈ dAO w u1 u2 j →
      (aEven u2).val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven) :
    PiecesAgree (tileAltOddPieces S pOdd pEven aOdd aEven lX w) (kappa7 (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH)) := by
  obtain ⟨b0, h0p⟩ := h0p
  obtain ⟨b1, h1p⟩ := h1p
  obtain ⟨b2, h2p⟩ := h2p
  obtain ⟨b3, h3p⟩ := h3p
  obtain ⟨b4, h4p⟩ := h4p
  obtain ⟨b5, h5p⟩ := h5p
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := AltEvenTilePieces.evenPiecesEF_of np2 dp2 nq2 dq2 hpar2 hqe2 (aEven u2) oP2 oQ2 βH βP2 βQ2
    b0 b1 b2 b3 b4 b5 hcP2 hcQ2 hhP2 hhQ2 hhH hN hd0 hd2 hd4 h0p h1p h2p h3p h4p h5p
  subst e0 e1 e2 e3 e4 e5
  have hsix := AltSixOdd.sixOdd_ef w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = false := by simpa [W1Odd] using hph
  have hc : (altTypeOf w).bind (fun ty => altQ1Coeff (W1Odd w) ty) = some (0, 1, 1, 0) := by
    simp [altTypeOf, hl, hW, altQ1Coeff]
  have ht : altOff w (0, 1, 1, 0) = (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2]
  have hη : altAff w (0, 1, 1, 0) = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aOdd_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven
    (placedAltOdd w (pOdd u1).val (pEven u2).val 0) (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH) rfl (by simp [altOddD, altOddR])
    (aOdd_std w u1 u2 (pOdd u1) (pEven u2) (aEven u2) _ _ hdP hdQ) ?_ ?_ hov
  · have e : (fun i z => placedAltOdd w (pOdd u1).val (pEven u2).val 0 i z + (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) i) =
        placedAltOdd w (pOdd u1).val (pEven u2).val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) := by
      funext i z
      exact AltSixOdd.placedAltOdd_add w _ _ _ i z
    rw [e]
    exact hsix
  · intro p hp6 j hj z hz hzj
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp6
    subst hp6
    rw [mem_placed_std, ht] at hz
    have hv : pieceVal (stdPiece (aEven u2) (altOff w (0, 1, 1, 0)) (altAff w (0, 1, 1, 0))) z =
        (aEven u2).val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z := by
      simp only [pieceVal, stdPiece, ht, hη, dot2, dotS]
    rw [hv, AltSixOdd.placedAltOdd_add]
    interval_cases j
    · exact AltParentOE3.parent_oe3_0 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 0 (by norm_num)) z hz hzj
    · exact AltParentOE3.parent_oe3_1 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 1 (by norm_num)) z hz hzj
    · exact AltParentOE3.parent_oe3_2 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 2 (by norm_num)) z hz hzj
    · exact AltParentOE3.parent_oe3_3 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 3 (by norm_num)) z hz hzj
    · exact AltParentOE3.parent_oe3_4 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 4 (by norm_num)) z hz hzj
    · exact AltParentOE3.parent_oe3_5 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 5 (by norm_num)) z hz hzj

/-- Case 3, odd alternate child, `W_1` odd, type 3. -/
theorem seven_oo3 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hph : phase w = 1)
    (hl : w.getLast? = some Digit.three) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 ∧ (parentsAt w).odd.den = dp2 ∧
      (parentsAt w).even.num = 2 * np2 + nq2 ∧ (parentsAt w).even.den = 2 * dp2 + dq2)
    (oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : (pOdd u1).dom = oddTile u1) (hdQ : (pEven u2).dom = evenTile u2)
    (hcP : TileTranslation.StdCornerValues (pOdd u1) 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues (pEven u2) 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhR : ∀ y ∈ tOddSet u1,
      texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y ∈ tOddSet u1 ∧
      2 * ((pOdd u1).val (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y) - (pOdd u1).val y) =
        dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      (pOdd u1).val (x + shiftP w) - (pOdd u1).val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w (pOdd u1).val (pEven u2).val 0))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hhP2 : ∀ y ∈ (↑oP2.dom : Set (ℤ × ℤ)),
      (2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP2.dom : Set _) ∧
      2 * (oP2.val ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) - y) - oP2.val y) =
        dotS (np2, -dp2) ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np2, -dp2) y)
    (hhQ2 : ∀ y ∈ (↑oQ2.dom : Set (ℤ × ℤ)),
      (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ2.dom : Set _) ∧
      2 * (oQ2.val ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ2.val y) =
        dotS (nq2, -dq2) ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq2, -dq2) y)
    (hhH : ∀ x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)),
      2 * ((aEven u2).val ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - x) - (aEven u2).val x) =
      dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((2 : ℤ) • (np2, -dp2) + (nq2, -dq2)) x)
    (hN : (aEven u2).val 0 = βH)
    (hd0 : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd1 : ∀ x, x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd2 : ∀ x, x - (np2 - dp2, np2 + dp2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd3 : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) + (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (hd5 : ∀ x, x - ((np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)))
    (h0p : ∃ b : ℤ, ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oQ2.val (x - (2 * dp2, 2 * np2)) + dotS 0 x + b)
    (h1p : ∃ b : ℤ, ∀ x, x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oQ2.val (x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + (dq2, nq2))) + dotS (np2, -dp2) x + b)
    (h2p : ∃ b : ℤ, ∀ x, x - (np2 - dp2, np2 + dp2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oQ2.val (x - (np2 - dp2, np2 + dp2)) + dotS (np2, -dp2) x + b)
    (h3p : ∃ b : ℤ, ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) + (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oQ2.val (x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) + (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + b)
    (h4p : ∃ b : ℤ, ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oP2.val (x - 0) + dotS 0 x + b)
    (h5p : ∃ b : ℤ, ∀ x, x - ((np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      (aEven u2).val x = oP2.val (x - ((np2 - dp2, np2 + dp2) + (2 : ℤ) • (dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + b)
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)) → z ∈ dAO w u1 u2 j →
      (aEven u2).val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven) :
    PiecesAgree (tileAltOddPieces S pOdd pEven aOdd aEven lX w) (kappa7 (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH)) := by
  obtain ⟨b0, h0p⟩ := h0p
  obtain ⟨b1, h1p⟩ := h1p
  obtain ⟨b2, h2p⟩ := h2p
  obtain ⟨b3, h3p⟩ := h3p
  obtain ⟨b4, h4p⟩ := h4p
  obtain ⟨b5, h5p⟩ := h5p
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := AltEvenTilePieces.evenPieces_of np2 dp2 nq2 dq2 hpar2 hqe2 (aEven u2) oP2 oQ2 βH βP2 βQ2
    b0 b1 b2 b3 b4 b5 hcP2 hcQ2 hhP2 hhQ2 hhH hN hd0 hd2 hd4 h0p h1p h2p h3p h4p h5p
  subst e0 e1 e2 e3 e4 e5
  have hsix := AltSixOdd.sixOdd_of w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = true := by simp [W1Odd, hph]
  have hc : (altTypeOf w).bind (fun ty => altQ1Coeff (W1Odd w) ty) = some (1, 1, -1, 0) := by
    simp [altTypeOf, hl, hW, altQ1Coeff]
  have ht : altOff w (1, 1, -1, 0) = (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2] <;> ring
  have hη : altAff w (1, 1, -1, 0) = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aOdd_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven
    (placedAltOdd w (pOdd u1).val (pEven u2).val 0) (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH) rfl (by simp [altOddD, altOddR])
    (aOdd_std w u1 u2 (pOdd u1) (pEven u2) (aEven u2) _ _ hdP hdQ) ?_ ?_ hov
  · have e : (fun i z => placedAltOdd w (pOdd u1).val (pEven u2).val 0 i z + (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) i) =
        placedAltOdd w (pOdd u1).val (pEven u2).val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) := by
      funext i z
      exact AltSixOdd.placedAltOdd_add w _ _ _ i z
    rw [e]
    exact hsix
  · intro p hp6 j hj z hz hzj
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp6
    subst hp6
    rw [mem_placed_std, ht] at hz
    have hv : pieceVal (stdPiece (aEven u2) (altOff w (1, 1, -1, 0)) (altAff w (1, 1, -1, 0))) z =
        (aEven u2).val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z := by
      simp only [pieceVal, stdPiece, ht, hη, dot2, dotS]
    rw [hv, AltSixOdd.placedAltOdd_add]
    interval_cases j
    · exact AltParentOO3.parent_oo3_0 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 0 (by norm_num)) z hz hzj
    · exact AltParentOO3.parent_oo3_1 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 1 (by norm_num)) z hz hzj
    · exact AltParentOO3.parent_oo3_2 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 2 (by norm_num)) z hz hzj
    · exact AltParentOO3.parent_oo3_3 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 3 (by norm_num)) z hz hzj
    · exact AltParentOO3.parent_oo3_4 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 4 (by norm_num)) z hz hzj
    · exact AltParentOO3.parent_oo3_5 w u1 u2 hph np2 dp2 nq2 dq2 hpar2 hqe2 hrel (pOdd u1) (pEven u2) (aEven u2) oP2 oQ2
        βP βQ βH βP2 βQ2 hdP hdQ hcP hcQ hcP2 hcQ2 hd0 h0p hd1 h1p hd2 h2p hd3 h3p hd4 h4p hd5 h5p (hpc 5 (by norm_num)) z hz hzj

end FLatticePaper.Tiles.AltSeven
