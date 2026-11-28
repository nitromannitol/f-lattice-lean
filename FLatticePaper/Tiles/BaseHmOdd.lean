import FLatticePaper.Tiles.BaseHpLadder
import FLatticePaper.Tiles.HorizontalEnlarged

/-! # The reversed horizontal piece of the odd odometer of `3^k` (`k ≥ 1`): letters and tile types

The reversed word of the odd tile of `3^k` is `u = p^{k+1} q p^k q` (`(wL k).reverse`). Its letters: `q` exactly at the indices
`k+1` and `2k+2`, `p` elsewhere; its enlarged tile types: `one` at those two indices, `zero` elsewhere (for `k ≥ 1`). -/

namespace FLatticePaper.Tiles.BaseHmOdd

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Construction
open FLatticePaper.Tiles.BaseHpLadder (wL getD_rep getD_append_eq)

theorem wL_reverse (k : ℕ) :
    (wL k).reverse = List.replicate (k + 1) Letter.p ++ [Letter.q] ++ List.replicate k Letter.p ++ [Letter.q] := by
  simp [wL, List.reverse_append, List.reverse_replicate, List.append_assoc]

theorem getD_singleton_q (n : ℕ) : [Letter.q].getD n Letter.p = if n = 0 then Letter.q else Letter.p := by
  rcases n with _ | n <;> simp

theorem letter_rev_wL (k j : ℕ) (hj : j < 2 * k + 3) :
    lettersOf (wL k) true j = if j = k + 1 ∨ j = 2 * k + 2 then Letter.q else Letter.p := by
  unfold lettersOf
  simp only [if_true]
  rw [wL_reverse]
  simp only [getD_append_eq, List.length_append, List.length_replicate, List.length_singleton, getD_rep,
    getD_singleton_q]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem tile_type_rev_wL (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 * k + 3) :
    hTileAt (lettersOf (wL k) true) j = if j = k + 1 ∨ j = 2 * k + 2 then ZTile.one else ZTile.zero := by
  unfold hTileAt hPrev
  rw [letter_rev_wL k j hj]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [BaseHpLadder.hTt_xp]
  · rw [if_neg (show j ≠ 0 by omega), letter_rev_wL k (j - 1) (by omega)]
    split_ifs <;> simp_all [BaseHpLadder.hTt_xp, BaseHpLadder.hTt_pq]
    all_goals try omega

/-- The positions of the reversed enlarged tiles of the odd `3^k`: the anchor `(-2k, 2k+1)` at index `0`. -/
def posHm (k j : ℕ) : GInt :=
  if j ≤ k then ((2 * (j : ℤ) - 2 * (k : ℤ)), 2 * (k : ℤ) + 1)
  else if j = k + 1 then (2, 2 * (k : ℤ) + 2)
  else if j ≤ 2 * k + 1 then (2 * (j : ℤ) - 2 * (k : ℤ) - 1, 2 * (k : ℤ) + 2)
  else (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 3)

theorem posHm_succ (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 * k + 2) :
    posHm k (j + 1) = posHm k j +
      zeroOneHorizontalReversedStep (lettersOf (wL k) true j) (lettersOf (wL k) true (j + 1)) := by
  rw [letter_rev_wL k j (by omega), letter_rev_wL k (j + 1) (by omega)]
  unfold posHm zeroOneHorizontalReversedStep
  split_ifs <;> simp [Prod.ext_iff] <;> omega

/-- The affine factor of the reversed odd `3^k` piece: the letter factor `alphaH` plus the shift `σ = (1, -(2k+2))`. -/
def aHm (k j : ℕ) : GInt :=
  alphaH (lettersOf (wL k) true j) + ((1 : ℤ), -(2 * (k : ℤ) + 2))

/-- The constant at the first tile of the reversed odd `3^k` piece. -/
def c0Hm (k : ℕ) : ℤ := -(2 * (k : ℤ) + 1) * ((k : ℤ) + 1)

/-- The index-dependent part of the constant (linear in `k` and `j`). -/
def dHm (k j : ℕ) : ℤ :=
  if j = 0 then 0
  else if j ≤ k then 2 * (j : ℤ)
  else if j ≤ k + 2 then 1
  else if j ≤ 2 * k + 1 then 1 + 2 * ((j : ℤ) - (k : ℤ) - 2)
  else 0

/-- The centred constant of the reversed odd `3^k` piece: `c_j = c_0 + d_j`. -/
def cHm (k j : ℕ) : ℤ := c0Hm k + dHm k j

theorem cHm_succ (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 * k + 2) :
    cHm k (j + 1) = cHm k j +
      ptDot (aHm k j) (zeroOneHorizontalReversedStep (lettersOf (wL k) true j) (lettersOf (wL k) true (j + 1))) := by
  unfold aHm cHm dHm
  rw [letter_rev_wL k j (by omega), letter_rev_wL k (j + 1) (by omega)]
  unfold ptDot zeroOneHorizontalReversedStep alphaH
  simp only [Prod.fst_add, Prod.snd_add]
  split_ifs <;> simp_all <;> omega

end FLatticePaper.Tiles.BaseHmOdd
