import FLatticePaper.Tiles.TexVPositions
import FLatticePaper.Tiles.ReversedTopShift
import FLatticePaper.Tiles.ClosedPathCorners
import FLatticePaper.Tiles.StringCorners
import FLatticePaper.Tiles.PseudoSquareAnchored

/-! # The three anchors of the standard tiles, in the form of `CornerValues.std_corner_values`

For the child fraction `n/d` of a word `w` (`fracOdd w` for the odd child, `fracEven w` for the even one), with
`X = texV1 (n/d)` and `Y = texV2 (n/d) = (n - d, n + d)`:

* `hX`: the last position of the forward horizontal string of `w_h` (from `0`) is `X - (1,1)` (`X - 1 - i`);
* `hY`: the last position of the reversed vertical string of `rev w_v` (from `0`) is `Y + (1,-2)` (`Y + 1 - 2i`);
* `hC`: the last position of the forward vertical string of `w_v` anchored at `X - (1,1)` is `X + Y + (0,-2)` (`X + Y - 2i`).

`hX` is `TexVPositions.lastPos_hWordOf_false_tex` / `_true_tex`. `hY` is `vRev_last_top` with the counts of the vertical word.
`hC` is the sum of the vertical steps of the forward string: the steps of `w_v` after its first letter `p` sum to
`(n - d + 1, n + d - 1)`, because `#p(w_v) = d - n` and `#q(w_v) = n`. -/

namespace FLatticePaper.Tiles.StdCornerAnchors

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.StandardClause

/-- The length of a binary word is the number of its `p` and `q` letters. -/
theorem stdLen_eq_counts (L : BinaryWord) : (L.length : ℤ) = (L.count Letter.p : ℤ) + (L.count Letter.q : ℤ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    cases a <;> simp at ih ⊢ <;> omega

/-- The steps of the vertical string: the sum of `vOffset` over `L` is `(-#p, #p + 2 #q)`. -/
theorem stdSum_vOffset (L : BinaryWord) :
    (L.map vOffset).sum = (-(L.count Letter.p : ℤ), (L.count Letter.p : ℤ) + 2 * (L.count Letter.q : ℤ)) := by
  induction L with
  | nil => ext <;> simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih]
    cases a <;> ext <;> simp [vOffset] <;> ring

/-- The last position of the forward vertical string of a nonempty word `a :: t` is the start plus the sum of the steps of `t`. -/
theorem stdLastPos_vStringAt (a : Letter) (t : BinaryWord) (c : GInt) :
    lastPosOf (vStringAt (a :: t) c) = c + (t.map vOffset).sum := by
  unfold vStringAt
  simp only [List.tail_cons]
  exact ClosedPathCorners.lastPos_zip_scanl _ _ _ (by simp)

/-- `hY` for a vertical word `wv` from `p` to `q` with `#p = d - n` and `#q = n`. -/
theorem stdAnchorY_of (wv : BinaryWord) (n d : ℤ) (hh : wv.head? = some Letter.p) (hl : wv.getLast? = some Letter.q)
    (hcp : (wv.count Letter.p : ℤ) = d - n) (hcq : (wv.count Letter.q : ℤ) = n) :
    lastPosOf (vRevStringAt wv.reverse 0) = (n - d, n + d) + (1, -2) := by
  have hlen : (wv.length : ℤ) = d := by
    rw [stdLen_eq_counts wv, hcp, hcq]
    ring
  rw [vRev_last_top wv hh hl, hcq, hlen]
  ext <;> simp <;> ring

/-- `hC` for a vertical word `wv` from `p` to `q` with `#p = d - n` and `#q = n`, anchored at `c`. -/
theorem stdAnchorC_of (wv : BinaryWord) (n d : ℤ) (hh : wv.head? = some Letter.p)
    (hcp : (wv.count Letter.p : ℤ) = d - n) (hcq : (wv.count Letter.q : ℤ) = n) (c : GInt) :
    lastPosOf (vStringAt wv c) = c + (n - d + 1, n + d - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, wv = Letter.p :: t := by
    cases wv with
    | nil => simp at hh
    | cons a t =>
      simp at hh
      exact ⟨t, by rw [hh]⟩
  have hcp' : ((t.count Letter.p : ℕ) : ℤ) = d - n - 1 := by
    simp at hcp
    linarith
  have hcq' : ((t.count Letter.q : ℕ) : ℤ) = n := by
    simpa [List.count_cons] using hcq
  rw [stdLastPos_vStringAt, stdSum_vOffset, hcp', hcq']
  ext <;> simp <;> ring

/-! ### The standard tiles (odd child `oddTile`, even child `evenTile`) -/

theorem stdAnchorX_odd (w : Word) :
    lastPosOf (hStringAt (hWordOf w false) (0, 0)) = texV1Odd (fracOdd w) - (1, 1) :=
  TexVPositions.lastPos_hWordOf_false_tex w

theorem stdAnchorX_even (w : Word) :
    lastPosOf (hStringAt (hWordOf w true) (0, 0)) = texV1Even (fracEven w) - (1, 1) :=
  TexVPositions.lastPos_hWordOf_true_tex w

theorem stdAnchorY_odd (w : Word) :
    lastPosOf (vRevStringAt (vWordOf w false).reverse 0) = texV2 (fracOdd w) + (1, -2) :=
  stdAnchorY_of (vWordOf w false) (fracOdd w).num (fracOdd w).den (StringCorners.vertWord_head_last w).1
    (StringCorners.vertWord_head_last w).2 (vertWord_counts w).1 (vertWord_counts w).2

theorem stdAnchorY_even (w : Word) :
    lastPosOf (vRevStringAt (vWordOf w true).reverse 0) = texV2 (fracEven w) + (1, -2) :=
  stdAnchorY_of (vWordOf w true) (fracEven w).num (fracEven w).den (StringCorners.vWord_even_head_last w).1
    (StringCorners.vWord_even_head_last w).2 (StringCorners.vWord_even_counts w).1 (StringCorners.vWord_even_counts w).2

theorem stdAnchorC_odd (w : Word) :
    lastPosOf (vStringAt (vWordOf w false) (texV1Odd (fracOdd w) - (1, 1))) =
      texV1Odd (fracOdd w) + texV2 (fracOdd w) + (0, -2) := by
  rw [stdAnchorC_of (vWordOf w false) (fracOdd w).num (fracOdd w).den (StringCorners.vertWord_head_last w).1
    (vertWord_counts w).1 (vertWord_counts w).2]
  ext
  all_goals simp [texV1Odd, texV2]
  all_goals ring

theorem stdAnchorC_even (w : Word) :
    lastPosOf (vStringAt (vWordOf w true) (texV1Even (fracEven w) - (1, 1))) =
      texV1Even (fracEven w) + texV2 (fracEven w) + (0, -2) := by
  rw [stdAnchorC_of (vWordOf w true) (fracEven w).num (fracEven w).den (StringCorners.vWord_even_head_last w).1
    (StringCorners.vWord_even_counts w).1 (StringCorners.vWord_even_counts w).2]
  ext
  all_goals simp [texV1Even, texV2]
  all_goals ring

end FLatticePaper.Tiles.StdCornerAnchors
