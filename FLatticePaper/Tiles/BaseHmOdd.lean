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

end FLatticePaper.Tiles.BaseHmOdd
