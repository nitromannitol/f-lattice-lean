import FLatticePaper.Tiles.BaseInsideTile
import FLatticePaper.Tiles.BaseThreeEven
import FLatticePaper.Tiles.BaseHmAnchor
import FLatticePaper.Tiles.BaseHpStair
import FLatticePaper.Tiles.BaseCasePseudoSquares

/-! # base_anchored_eq_along and InsideTile for the even 3^k odometer (k ≥ 0, the empty word at k = 0)

The forward word of the even tile is `stairH k = q p^{k+1}` and the vertical word `stairV k = p^{2k+2} q`. The walk points of
`alongStrings` are `(0,0) + Σ gH = (2k+3, 0)` and `(0,0) + Σ gV = (-(2k+1), 2k+4)`; with `anchor_three_even` and
`lastPos_vRev_q_rep` they are the anchors of `anchoredStrings`. `stair_contain` places the walk sites in the paper stair tile. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Farey FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.BaseHmAnchor
open FLatticePaper.Tiles.BaseThreeEven FLatticePaper.Tiles.BaseHpStair
open FLatticePaper.Tiles.Standard FLatticePaper.Construction

theorem base_anchored_eq_along_even (k : ℕ) :
    anchoredStrings (hWordOf (List.replicate k Digit.three) true) (vWordOf (List.replicate k Digit.three) true) (0, 0) =
      alongStrings (hWordOf (List.replicate k Digit.three) true) (vWordOf (List.replicate k Digit.three) true) (0, 0) := by
  have hH : hWordOf (List.replicate k Digit.three) true = stairH k := by
    rw [hWordOf_three_true]
    simp [wE, stairH]
  have hV : vWordOf (List.replicate k Digit.three) true = stairV k := by
    rw [wv_three_even]
    rfl
  rw [hH, hV]
  have hr : (stairV k).reverse = Letter.q :: List.replicate (2 * k + 2) Letter.p := by
    simp [stairV, List.reverse_append]
  have h1 : lastPosOf (vRevStringAt (stairV k).reverse (0, 0)) = (0, 0) + (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 4) + (0, -2) := by
    rw [hr, lastPos_vRev_q_rep (2 * k + 2) (by omega) (0, 0)]
    push_cast
    ext
    · simp
      ring
    · simp
      ring
  have h2 : lastPosOf (hStringAt (stairH k) (0, 0)) = (0, 0) + (2 * (k : ℤ) + 3, 0) + (-1, 0) := by
    rw [← hH, anchor_three_even k]
    ext
    · simp
      ring
    · simp
  have sH : F2Word.sum (gH (stairH k)) = (2 * (k : ℤ) + 3, 0) := sum_gH_stair k
  have sV : F2Word.sum (gV (stairV k)) = (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 4) := sum_gV_stair k
  unfold anchoredStrings alongStrings
  dsimp only [gPseudo]
  rw [walkAt_total, walkAt_gH, sH, sV, h1, h2]

theorem insideTile_even (k : ℕ) :
    InsideTile ((stairF (2 * (k : ℤ) + 3) : Finset GInt) : Set GInt)
      (hStringAt (hWordOf (List.replicate k Digit.three) true) (0, 0) ++
        hRevStringAt (hWordOf (List.replicate k Digit.three) true).reverse
          (lastPosOf (vRevStringAt (vWordOf (List.replicate k Digit.three) true).reverse (0, 0))) ++
        vRevStringAt (vWordOf (List.replicate k Digit.three) true).reverse (0, 0) ++
        vStringAt (vWordOf (List.replicate k Digit.three) true)
          (lastPosOf (hStringAt (hWordOf (List.replicate k Digit.three) true) (0, 0)))) := by
  intro x hx
  rw [Finset.mem_coe, mem_stairF_iff_paper (d := 2 * (k : ℤ) + 3) (by omega)]
  have hA := base_anchored_eq_along_even k
  have hx' : x ∈ placedSites (anchoredStrings (hWordOf (List.replicate k Digit.three) true)
      (vWordOf (List.replicate k Digit.three) true) (0, 0)) := hx
  rw [hA] at hx'
  have hH : hWordOf (List.replicate k Digit.three) true = stairH k := by
    rw [hWordOf_three_true]
    simp [wE, stairH]
  have hV : vWordOf (List.replicate k Digit.three) true = stairV k := by
    rw [wv_three_even]
    rfl
  rw [hH, hV] at hx'
  exact stair_contain k x hx'

end FLatticePaper.Tiles
