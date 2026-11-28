import FLatticePaper.Tiles.AltPiecesAgree
import FLatticePaper.Tiles.AltBaseContacts
import FLatticePaper.Tiles.AltParentEF1
import FLatticePaper.Tiles.AltParentOF1
import FLatticePaper.Tiles.AltParentEF2
import FLatticePaper.Tiles.AltParentOF2
import FLatticePaper.Tiles.AltParentOE1
import FLatticePaper.Tiles.AltParentOO1
import FLatticePaper.Tiles.AltParentOE3
import FLatticePaper.Tiles.AltParentOO3

/-! # Case 3 at a base parent word: the seven pieces agree

At `w = v d` with `v = 3^k`, `2^k` or empty, the parent piece is an explicit base alternate tile; its contacts with the six copies
are `AltBaseContacts`, and the seven pieces agree with the same explicit constants as at the other words. -/

namespace FLatticePaper.Tiles.AltSevenBase

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

/-- Case 3 at a base parent word, even alternate child, `W_1` odd, the parent word `3^k`, last digit `1`. -/
theorem seven_base_ae31 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (k : ℕ) (hkk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hl : w.getLast? = some Digit.one) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (βP βQ : ℤ)
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
    (hdH : ∀ x : ℤ × ℤ, x ∈ (aOdd u1).dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ (aOdd u1).dom, (aOdd u1).val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)) → z ∈ dAE w u1 u2 j →
      (aOdd u1).val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven) :
    PiecesAgree (tileAltEvenPieces S pOdd pEven aOdd aEven lX w) (kappa7 (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2))) := by
  have hsix := AltSixEvenOF.sixEven_of w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = true := by simp [W1Odd, hph]
  have hc : (SurgicalAlt.altTypeOf w).bind (fun ty => SurgicalAlt.altP1Coeff (W1Odd w) ty) = some (0, 1, 1, 0) := by
    simp [SurgicalAlt.altTypeOf, hl, hW, SurgicalAlt.altP1Coeff]
  have ht : altOff w (0, 1, 1, 0) = (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2]
  have hη : altAff w (0, 1, 1, 0) = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aEven_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven
    (placedAltEven w (pOdd u1).val (pEven u2).val 0) (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) rfl (by simp [altEvenD, altEvenR])
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
    · exact AltBaseContacts.base_ae31_0 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 0 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae31_1 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 1 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae31_2 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 2 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae31_3 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 3 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae31_4 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 4 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae31_5 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 5 (by norm_num)) z hz hzj

/-- Case 3 at a base parent word, even alternate child, `W_1` even, the parent word `3^k`, last digit `2`. -/
theorem seven_base_ae32 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (k : ℕ) (hkk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hl : w.getLast? = some Digit.two) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 1))
    (βP βQ : ℤ)
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
    (hdH : ∀ x : ℤ × ℤ, x ∈ (aOdd u1).dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ (aOdd u1).dom, (aOdd u1).val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)) → z ∈ dAE w u1 u2 j →
      (aOdd u1).val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven) :
    PiecesAgree (tileAltEvenPieces S pOdd pEven aOdd aEven lX w) (kappa7 (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2))) := by
  have hsix := sixEven_ef w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = false := by simpa [W1Odd] using hph
  have hc : (SurgicalAlt.altTypeOf w).bind (fun ty => SurgicalAlt.altP1Coeff (W1Odd w) ty) = some (0, 0, 0, 1) := by
    simp [SurgicalAlt.altTypeOf, hl, hW, SurgicalAlt.altP1Coeff]
  have ht : altOff w (0, 0, 0, 1) = (texV2 (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2]
  have hη : altAff w (0, 0, 0, 1) = ((parentsAt w).even.num, -(parentsAt w).even.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aEven_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven
    (placedAltEven w (pOdd u1).val (pEven u2).val 0) (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2)) rfl (by simp [altEvenD, altEvenR])
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
    · exact AltBaseContacts.base_ae32_0 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 0 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae32_1 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 1 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae32_2 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 2 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae32_3 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 3 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae32_4 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 4 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae32_5 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 5 (by norm_num)) z hz hzj

/-- Case 3 at a base parent word, even alternate child, `W_1` odd, the parent word `2^k`, last digit `1`. -/
theorem seven_base_ae21 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (k : ℕ) (hkk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hl : w.getLast? = some Digit.one) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (βP βQ : ℤ)
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
    (hdH : ∀ x : ℤ × ℤ, x ∈ (aOdd u1).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ (aOdd u1).dom, (aOdd u1).val x = paperNearStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑(aOdd u1).dom : Set (ℤ × ℤ)) → z ∈ dAE w u1 u2 j →
      (aOdd u1).val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven) :
    PiecesAgree (tileAltEvenPieces S pOdd pEven aOdd aEven lX w) (kappa7 (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2))) := by
  have hsix := AltSixEvenOF.sixEven_of w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = true := by simp [W1Odd, hph]
  have hc : (SurgicalAlt.altTypeOf w).bind (fun ty => SurgicalAlt.altP1Coeff (W1Odd w) ty) = some (0, 1, 1, 0) := by
    simp [SurgicalAlt.altTypeOf, hl, hW, SurgicalAlt.altP1Coeff]
  have ht : altOff w (0, 1, 1, 0) = (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2]
  have hη : altAff w (0, 1, 1, 0) = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aEven_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven
    (placedAltEven w (pOdd u1).val (pEven u2).val 0) (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) rfl (by simp [altEvenD, altEvenR])
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
    · exact AltBaseContacts.base_ae21_0 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 0 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae21_1 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 1 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae21_2 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 2 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae21_3 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 3 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae21_4 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 4 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ae21_5 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aOdd u1) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 5 (by norm_num)) z hz hzj

/-- Case 3 at a base parent word, odd alternate child, `W_1` odd, the parent word `3^k`, last digit `1`. -/
theorem seven_base_ao31 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (k : ℕ) (hkk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hl : w.getLast? = some Digit.one) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (βP βQ : ℤ)
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
    (hdH : ∀ x : ℤ × ℤ, x ∈ (aEven u2).dom ↔ x + ((0 : ℤ), (0 : ℤ)) ∈ paperStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ (aEven u2).dom, (aEven u2).val x = paperStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (0 : ℤ))))
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)) → z ∈ dAO w u1 u2 j →
      (aEven u2).val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven) :
    PiecesAgree (tileAltOddPieces S pOdd pEven aOdd aEven lX w) (kappa7 (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2))) := by
  have hsix := AltSixOdd.sixOdd_of w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = true := by simp [W1Odd, hph]
  have hc : (SurgicalAlt.altTypeOf w).bind (fun ty => SurgicalAlt.altQ1Coeff (W1Odd w) ty) = some (1, 1, -1, 0) := by
    simp [SurgicalAlt.altTypeOf, hl, hW, SurgicalAlt.altQ1Coeff]
  have ht : altOff w (1, 1, -1, 0) = (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2] <;> ring
  have hη : altAff w (1, 1, -1, 0) = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aOdd_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven
    (placedAltOdd w (pOdd u1).val (pEven u2).val 0) (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) rfl (by simp [altOddD, altOddR])
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
    · exact AltBaseContacts.base_ao31_0 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 0 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao31_1 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 1 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao31_2 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 2 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao31_3 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 3 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao31_4 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 4 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao31_5 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 5 (by norm_num)) z hz hzj

/-- Case 3 at a base parent word, odd alternate child, `W_1` odd, the parent word `2^k`, last digit `1`. -/
theorem seven_base_ao21 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (k : ℕ) (hkk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hl : w.getLast? = some Digit.one) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (βP βQ : ℤ)
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
    (hdH : ∀ x : ℤ × ℤ, x ∈ (aEven u2).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ (aEven u2).dom, (aEven u2).val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)) → z ∈ dAO w u1 u2 j →
      (aEven u2).val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven) :
    PiecesAgree (tileAltOddPieces S pOdd pEven aOdd aEven lX w) (kappa7 (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2))) := by
  have hsix := AltSixOdd.sixOdd_of w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = true := by simp [W1Odd, hph]
  have hc : (SurgicalAlt.altTypeOf w).bind (fun ty => SurgicalAlt.altQ1Coeff (W1Odd w) ty) = some (1, 1, -1, 0) := by
    simp [SurgicalAlt.altTypeOf, hl, hW, SurgicalAlt.altQ1Coeff]
  have ht : altOff w (1, 1, -1, 0) = (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2] <;> ring
  have hη : altAff w (1, 1, -1, 0) = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aOdd_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven
    (placedAltOdd w (pOdd u1).val (pEven u2).val 0) (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) rfl (by simp [altOddD, altOddR])
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
    · exact AltBaseContacts.base_ao21_0 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 0 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao21_1 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 1 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao21_2 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 2 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao21_3 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 3 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao21_4 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 4 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao21_5 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 5 (by norm_num)) z hz hzj

/-- Case 3 at a base parent word, odd alternate child, `W_1` even, the parent word `2^k`, last digit `3`. -/
theorem seven_base_ao23 (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lX : Word → Bool → Bool → PartialOdometer) (k : ℕ) (hkk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hl : w.getLast? = some Digit.three) (hr : regsAt w = (some u1, some u2))
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (hrel : (parentsAt w).odd.num = ((k : ℤ)) ∧ (parentsAt w).odd.den = ((k : ℤ) + 1) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (βP βQ : ℤ)
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
    (hdH : ∀ x : ℤ × ℤ, x ∈ (aEven u2).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ (aEven u2).dom, (aEven u2).val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∀ j < 6, ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑(aEven u2).dom : Set (ℤ × ℤ)) → z ∈ dAO w u1 u2 j →
      (aEven u2).val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w (pOdd u1).val (pEven u2).val 0 j z = C)
    (hov : SixOverlaps (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven) :
    PiecesAgree (tileAltOddPieces S pOdd pEven aOdd aEven lX w) (kappa7 (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2))) := by
  have hsix := AltSixOdd.sixOdd_ef w u1 u2 hph hp hq (pOdd u1) (pEven u2) βP βQ hcP hcQ hhR hk hcompat
  have hW : W1Odd w = false := by simpa [W1Odd] using hph
  have hc : (SurgicalAlt.altTypeOf w).bind (fun ty => SurgicalAlt.altQ1Coeff (W1Odd w) ty) = some (0, 1, 1, 0) := by
    simp [SurgicalAlt.altTypeOf, hl, hW, SurgicalAlt.altQ1Coeff]
  have ht : altOff w (0, 1, 1, 0) = (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) := by
    ext <;> simp [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2]
  have hη : altAff w (0, 1, 1, 0) = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
    ext <;> simp [altAff, SurgicalAlt.coeffAffine]
  rw [aOdd_list S pOdd pEven aOdd aEven lX w u1 u2 _ hr (by rw [hl]; decide) hc]
  refine sevenAgree_of _ (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven
    (placedAltOdd w (pOdd u1).val (pEven u2).val 0) (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) rfl (by simp [altOddD, altOddR])
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
    · exact AltBaseContacts.base_ao23_0 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 0 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao23_1 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 1 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao23_2 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 2 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao23_3 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 3 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao23_4 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 4 (by norm_num)) z hz hzj
    · exact AltBaseContacts.base_ao23_5 k hkk w u1 u2 hph hrel (pOdd u1) (pEven u2) (aEven u2) βP βQ hdP hdQ hcP hcQ hdH hvH
        (hpc 5 (by norm_num)) z hz hzj

end FLatticePaper.Tiles.AltSevenBase

