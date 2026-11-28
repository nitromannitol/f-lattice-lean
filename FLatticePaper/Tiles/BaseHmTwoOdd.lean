import FLatticePaper.Tiles.HorizontalEnlarged
import FLatticePaper.Tiles.RevStringList
import FLatticePaper.Tiles.BaseHpNear
import FLatticePaper.Tiles.BaseHmAnchor
import FLatticePaper.Tiles.BaseTwoOdd

/-! # The reversed horizontal base piece of the odd `2^k` word (`k ≥ 1`)

The horizontal word of the odd child of `2^k` is `wD k = q^(2k+2) p`; its reversed word is `p q^(2k+2)`, and the reversed
horizontal string is anchored at `(0, 2k+1)`, the last tile of the reversed vertical piece. The family has the zero tile at
`(0, 2k+1)`, the one tile at `(2, 2k+2)`, and oneD tiles at `(j+1, j+2k+1)` for `2 ≤ j ≤ 2k+2`; its affine factors are
`(k+1, -(k+1))` at `0`, `(k, -(k+1))` from `1` on, and its constants `k(k+1)` at `0`, `k²+k+2` from `1` on. The odometer is
`paperNearStairValue (2k+3) (x + (0,1))`. -/

namespace FLatticePaper.Tiles.BaseHmTwoOdd

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.BaseTwoOdd FLatticePaper.Tiles.BaseHpNear

theorem lettersOf_wD (k j : ℕ) :
    lettersOf (wD k) true j = if j = 0 then Letter.p else if j ≤ 2 * k + 2 then Letter.q else Letter.p := by
  have hr : (wD k).reverse = Letter.p :: List.replicate (2 * k + 2) Letter.q := by
    simp [wD, List.reverse_append]
  unfold lettersOf
  simp only [if_true]
  rw [hr]
  cases j with
  | zero => simp
  | succ i =>
    rw [List.getD_cons_succ, FLatticePaper.Tiles.BaseTwoOdd.getD_rep_q]
    by_cases h1 : i < 2 * k + 2
    · rw [if_pos h1, if_neg (show ¬(i + 1 = 0) by omega), if_pos (show i + 1 ≤ 2 * k + 2 by omega)]
    · rw [if_neg h1, if_neg (show ¬(i + 1 = 0) by omega), if_neg (show ¬(i + 1 ≤ 2 * k + 2) by omega)]

theorem lettersOf_wD0 (k : ℕ) : lettersOf (wD k) true 0 = Letter.p := by
  rw [lettersOf_wD]
  simp

theorem lettersOf_wDq (k j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 2 * k + 2) : lettersOf (wD k) true j = Letter.q := by
  rw [lettersOf_wD, if_neg (show ¬(j = 0) by omega), if_pos h2]

/-- The positions of the reversed tiles of the odd `2^k` piece. -/
def posH2 (k j : ℕ) : GInt :=
  if j = 0 then (0, 2 * (k : ℤ) + 1) else ((j : ℤ) + 1, (j : ℤ) + 2 * (k : ℤ) + 1)

theorem posH2_succ (k j : ℕ) (hj : j + 1 < 2 * k + 3) :
    posH2 k (j + 1) = posH2 k j +
      zeroOneHorizontalReversedStep (lettersOf (wD k) true j) (lettersOf (wD k) true (j + 1)) := by
  by_cases h0 : j = 0
  · subst h0
    rw [lettersOf_wD0, lettersOf_wDq k 1 le_rfl (by omega)]
    show posH2 k 1 = posH2 k 0 + zeroOneHorizontalReversedStep Letter.p Letter.q
    unfold posH2 zeroOneHorizontalReversedStep
    simp only [if_neg (show ¬((0 : ℕ) + 1 = 0) by omega)]
    ext
    all_goals simp
    all_goals ring
  · rw [lettersOf_wDq k j (by omega) (by omega), lettersOf_wDq k (j + 1) (by omega) (by omega)]
    show posH2 k (j + 1) = posH2 k j + zeroOneHorizontalReversedStep Letter.q Letter.q
    unfold posH2 zeroOneHorizontalReversedStep
    simp only [if_neg (show ¬(j + 1 = 0) by omega), if_neg (show ¬(j = 0) by omega)]
    ext
    all_goals simp
    all_goals ring

/-- The affine factor of the reversed odd `2^k` piece: the letter factor plus the shift `(k+1, -(k+2))`. -/
def aH2 (k j : ℕ) : GInt :=
  alphaH (lettersOf (wD k) true j) + (((k : ℤ) + 1), -((k : ℤ) + 2))

theorem aH2_zero (k : ℕ) : aH2 k 0 = (((k : ℤ) + 1), -((k : ℤ) + 1)) := by
  rw [aH2, lettersOf_wD0]
  refine Prod.ext ?_ ?_
  all_goals simp [alphaH]
  all_goals ring

theorem aH2_pos (k j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 2 * k + 2) : aH2 k j = ((k : ℤ), -((k : ℤ) + 1)) := by
  rw [aH2, lettersOf_wDq k j h1 h2]
  refine Prod.ext ?_ ?_
  all_goals simp [alphaH]
  all_goals ring

/-- The centred constant of the reversed odd `2^k` piece. -/
def cH2 (k j : ℕ) : ℤ :=
  if j = 0 then -((k : ℤ) + 1) * ((k : ℤ) + 1) else -((k : ℤ) * (k : ℤ)) - (k : ℤ) - ((j : ℤ) - 1)

theorem cH2_succ (k j : ℕ) (hj : j + 1 < 2 * k + 3) :
    cH2 k (j + 1) = cH2 k j +
      ptDot (aH2 k j) (zeroOneHorizontalReversedStep (lettersOf (wD k) true j) (lettersOf (wD k) true (j + 1))) := by
  by_cases h0 : j = 0
  · subst h0
    rw [lettersOf_wD0, lettersOf_wDq k 1 le_rfl (by omega), aH2_zero]
    show cH2 k 1 = cH2 k 0 + ptDot _ (zeroOneHorizontalReversedStep Letter.p Letter.q)
    unfold cH2 ptDot zeroOneHorizontalReversedStep
    simp
    ring
  · rw [lettersOf_wDq k j (by omega) (by omega), lettersOf_wDq k (j + 1) (by omega) (by omega),
      aH2_pos k j (by omega) (by omega)]
    show cH2 k (j + 1) = cH2 k j + ptDot _ (zeroOneHorizontalReversedStep Letter.q Letter.q)
    unfold cH2 ptDot zeroOneHorizontalReversedStep
    simp only [if_neg (show ¬(j + 1 = 0) by omega), if_neg (show ¬(j = 0) by omega)]
    push_cast
    ring

/-- The horizontal family of the reversed odd `2^k` piece. -/
def HmTwoOddF (k : ℕ) : PTFamily :=
  { ts := (List.range (2 * k + 3)).map (fun j => (hTileAt (lettersOf (wD k) true) j, posH2 k j)),
    a := fun j => aH2 k j,
    b := fun j => cH2 k j - ptDot (aH2 k j) (posH2 k j) }

theorem HmTwoOddF_n (k : ℕ) : (HmTwoOddF k).n = 2 * k + 3 := by
  simp [HmTwoOddF, PTFamily.n]

theorem HmTwoOddF_tile (k j : ℕ) (hj : j < 2 * k + 3) :
    (HmTwoOddF k).tile j = (hTileAt (lettersOf (wD k) true) j, posH2 k j) := by
  unfold PTFamily.tile HmTwoOddF
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem HmTwoOddF_respects (k : ℕ) :
    (HmTwoOddF k).Respects .horizontal true :=
  PTFamily.respects_of_triples (HmTwoOddF k) .horizontal true (lettersOf (wD k) true) (hPrev (lettersOf (wD k) true))
    (fun j => posH2 k j) hTt
    (fun y z => zeroOneHorizontalReversedStep y z) (fun _ y z => alphaH z - alphaH y)
    (fun j => cH2 k j) (fun _ _ _ => (0 : ℤ)) (fun _ _ _ => True)
    (fun j hj => by
      rw [HmTwoOddF_n] at hj
      rw [HmTwoOddF_tile k j hj]
      rfl)
    (fun j _ => hPrev_succ _ j)
    (fun j hj => by
      rw [HmTwoOddF_n] at hj
      exact posH2_succ k j (by omega))
    (fun j hj => by
      rw [HmTwoOddF_n] at hj
      show aH2 k (j + 1) = aH2 k j + (alphaH (lettersOf (wD k) true (j + 1)) - alphaH (lettersOf (wD k) true j))
      unfold aH2
      abel)
    (fun j _ => rfl)
    (fun j hj => by
      rw [HmTwoOddF_n] at hj
      show cH2 k (j + 1) = cH2 k j + (0 : ℤ) +
        ptDot (aH2 k j) (zeroOneHorizontalReversedStep (lettersOf (wD k) true j) (lettersOf (wD k) true (j + 1)))
      rw [cH2_succ k j (by omega)]
      ring)
    (fun _ _ => trivial)
    (fun x y => hTt_letter x y)
    (fun x y z _ => by
      cases y <;> cases z <;> simp [hTt_base_p, hTt_base_q, surgicalSlopeDiff, alphaH, Prod.ext_iff] <;> norm_num)
    (fun _ x y z _ u hu v hv hno hunit => hE_rev x y z u hu v hv hno hunit)
    (fun h => by cases h)

end FLatticePaper.Tiles.BaseHmTwoOdd
