import FLatticePaper.Tiles.BaseHmOdd
import FLatticePaper.Tiles.BaseTileProps

/-! # The per-tile identities of the reversed horizontal piece of the odd odometer of `3^k` (`k ≥ 1`), first class

For `j ≤ k` the letter of the reversed word is `p` (tile `zero`), the position is `(2j-2k, 2k+1)`, the affine factor is
`(1, -(2k+1))` and the constant is `c0Hm k + 2j`. The identity `paperLadderValue (2k+2) (u + P_j) = zTileOdo zero u + ptDot a_j u + c_j`
is then a closed form: the triangular term of `plV` is `k(2k+2t+1) + T` with `t = u₂+1`, and it equals `-c0Hm k` at `t = 1`. -/

namespace FLatticePaper.Tiles.BaseHmOddValues

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.BaseHmOdd FLatticePaper.Construction
open FLatticePaper.Tiles.BaseTileProps

/-- The triangular number of `2k + t`, in closed form when `t(t+1) = 2T`. -/
theorem tri_eq (k t T : ℤ) (hT : t * (t + 1) = 2 * T) :
    (2 * k + t) * (2 * k + t + 1) / 2 = k * (2 * k + 2 * t + 1) + T := by
  have h : (2 * k + t) * (2 * k + t + 1) = 2 * (k * (2 * k + 2 * t + 1) + T) := by
    linear_combination hT
  rw [h, Int.mul_ediv_cancel_left _ (by norm_num)]

theorem aHm_mid (k j : ℕ) (hk : 1 ≤ k) (hj : j ≤ k) : aHm k j = ((1 : ℤ), -(2 * (k : ℤ) + 1)) := by
  unfold aHm
  rw [letter_rev_wL k j (by omega), if_neg (show ¬ (j = k + 1 ∨ j = 2 * k + 2) by omega)]
  ext
  · norm_num [alphaH]
  · norm_num [alphaH]
    ring

theorem dHm_mid (k j : ℕ) (hj : j ≤ k) : dHm k j = 2 * (j : ℤ) := by
  unfold dHm
  by_cases h0 : j = 0
  · subst h0; simp
  · rw [if_neg h0, if_pos hj]

theorem cHm_mid (k j : ℕ) (hj : j ≤ k) : cHm k j = c0Hm k + 2 * (j : ℤ) := by
  unfold cHm; rw [dHm_mid k j hj]

end FLatticePaper.Tiles.BaseHmOddValues
