import FLatticePaper.Tiles.StringAppend
import FLatticePaper.Tiles.GlueWords

/-! # The boundary strings of a standard child as chains of the strings of its copies

For a word `w` that is not a base word, with registers `u1`, `u2`, each of the four boundary strings of each standard child of
`w` (in the placement of `RespectsAnchored`) is the concatenation of whole strings of the same kind of the copies of the
registers, each started at the copy's offset plus the register's own start. With `A, B` the vectors of the odd register and
`U, V` those of the even one, and the copies of `oddP`, `oddQ`, `evenP`, `evenQ`:

* odd child, `W_1` even: bottom `Q^{+,1}, Q^{+,2}, P^+`; left `Q^{+,1}, P^-`; right `P^+, Q^{-,2}`; top `P^-, Q^{-,1}, Q^{-,2}`;
* odd child, `W_1` odd: bottom `P^+, Q^{+,1}, Q^{+,2}`; left `P^+, Q^{-,1}`; right `Q^{+,2}, P^-`; top `Q^{-,1}, Q^{-,2}, P^-`;
* even child, `W_1` even: bottom `Q^+, P^{+,1}`; left `Q^+, P^{-,1}, P^{-,2}`; right `P^{+,1}, P^{+,2}, Q^-`; top `P^{-,2}, Q^-`;
* even child, `W_1` odd: bottom `P^{+,1}, Q^+`; left `P^{+,1}, P^{+,2}, Q^-`; right `Q^+, P^{-,1}, P^{-,2}`; top `Q^-, P^{-,2}`.

(Numerically, `tmp-w4/c_glue_concat.py`, these are exact for every non-base word of length at most 5.) The words come from
`GlueWords`, the seams from `StringAppend`, and the positions from the corner anchors of the registers (`StdCornerAnchors`). -/

namespace FLatticePaper.Tiles.GlueStringDecomp

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.StringAppend
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.SurgicalWeak (regsAt)

/-! ### The strings of a register word -/

theorem lastPosOf_append (l1 l2 : List (ZTile × GInt)) (h : l2 ≠ []) : lastPosOf (l1 ++ l2) = lastPosOf l2 := by
  unfold lastPosOf
  rw [List.getLast?_append_of_ne_nil _ h]

theorem hWord_ne (u : Word) (b : Bool) : hWordOf u b ≠ [] := by
  intro h
  have := (hWordOf_head_last u b).1
  rw [h] at this
  simp at this

theorem vWord_odd_ne (u : Word) : vWordOf u false ≠ [] := by
  intro h
  have := (StringCorners.vertWord_head_last u).1
  rw [show vWordOf u false = vertWord u from rfl] at h
  rw [h] at this
  simp at this

theorem vWord_even_ne (u : Word) : vWordOf u true ≠ [] := by
  intro h
  have := (StringCorners.vWord_even_head_last u).1
  rw [h] at this
  simp at this

theorem hStringAt_ne (X : BinaryWord) (c : GInt) (h : X ≠ []) : hStringAt X c ≠ [] := by
  obtain ⟨a, X', rfl⟩ := List.exists_cons_of_ne_nil h
  simp [hStringAt, tileSeq, tileSeqAux]

theorem hRevStringAt_ne (X : BinaryWord) (c : GInt) (h : X ≠ []) : hRevStringAt X c ≠ [] := by
  obtain ⟨a, X', rfl⟩ := List.exists_cons_of_ne_nil h
  simp [hRevStringAt, tileSeq, tileSeqAux]

theorem vStringAt_ne (X : BinaryWord) (c : GInt) (h : X ≠ []) : vStringAt X c ≠ [] := by
  obtain ⟨a, X', rfl⟩ := List.exists_cons_of_ne_nil h
  simp [vStringAt]

theorem vRevStringAt_ne (X : BinaryWord) (c : GInt) (h : X ≠ []) : vRevStringAt X c ≠ [] := by
  obtain ⟨a, X', rfl⟩ := List.exists_cons_of_ne_nil h
  simp [vRevStringAt]

/-- The bottom string of the odd register ends at `A - (1, 1)` past its start. -/
theorem lp_bot_odd (u : Word) (c : GInt) :
    lastPosOf (hStringAt (hWordOf u false) c) = c + (texV1Odd (fracOdd u) - (1, 1)) := by
  have h0 : lastPosOf (hStringAt (hWordOf u false) 0) = texV1Odd (fracOdd u) - (1, 1) := TexVPositions.lastPos_hWordOf_false_tex u
  rw [ClosedPathCorners.hFwd_lastPos _ _ (hWord_ne u false)] at h0 ⊢
  rw [← h0, zero_add]

theorem lp_bot_even (u : Word) (c : GInt) :
    lastPosOf (hStringAt (hWordOf u true) c) = c + (texV1Even (fracEven u) - (1, 1)) := by
  have h0 : lastPosOf (hStringAt (hWordOf u true) 0) = texV1Even (fracEven u) - (1, 1) := TexVPositions.lastPos_hWordOf_true_tex u
  rw [ClosedPathCorners.hFwd_lastPos _ _ (hWord_ne u true)] at h0 ⊢
  rw [← h0, zero_add]

/-- The top string of the odd register ends at `A - (1, 0)` past its start. -/
theorem lp_top_odd (u : Word) (c : GInt) :
    lastPosOf (hRevStringAt (hWordOf u false).reverse c) = c + (texV1Odd (fracOdd u) - (1, 1)) + (0, 1) := by
  have h0 : lastPosOf (hStringAt (hWordOf u false) 0) = texV1Odd (fracOdd u) - (1, 1) := TexVPositions.lastPos_hWordOf_false_tex u
  rw [ClosedPathCorners.hRev_lastPos_reverse _ _ (hWordOf_head_last u false).1 (hWordOf_head_last u false).2, h0]

theorem lp_top_even (u : Word) (c : GInt) :
    lastPosOf (hRevStringAt (hWordOf u true).reverse c) = c + (texV1Even (fracEven u) - (1, 1)) + (0, 1) := by
  have h0 : lastPosOf (hStringAt (hWordOf u true) 0) = texV1Even (fracEven u) - (1, 1) := TexVPositions.lastPos_hWordOf_true_tex u
  rw [ClosedPathCorners.hRev_lastPos_reverse _ _ (hWordOf_head_last u true).1 (hWordOf_head_last u true).2, h0]

/-- The left string of the odd register ends at `B + (1, -2)` past its start. -/
theorem lp_left_odd (u : Word) (c : GInt) :
    lastPosOf (vRevStringAt (vWordOf u false).reverse c) = c + (texV2 (fracOdd u) + (1, -2)) := by
  rw [lastPos_vRevStringAt _ _ (by simpa using vWord_odd_ne u), StdCornerAnchors.stdAnchorY_odd]

theorem lp_left_even (u : Word) (c : GInt) :
    lastPosOf (vRevStringAt (vWordOf u true).reverse c) = c + (texV2 (fracEven u) + (1, -2)) := by
  rw [lastPos_vRevStringAt _ _ (by simpa using vWord_even_ne u), StdCornerAnchors.stdAnchorY_even]

/-- The right string of the odd register ends at `B + (1, -1)` past its start. -/
theorem lp_right_odd (u : Word) (c : GInt) :
    lastPosOf (vStringAt (vWordOf u false) c) = c + (texV2 (fracOdd u) + (1, -1)) := by
  rw [StdCornerAnchors.stdAnchorC_of (vWordOf u false) (fracOdd u).num (fracOdd u).den
    (StringCorners.vertWord_head_last u).1 (vertWord_counts u).1 (vertWord_counts u).2]
  congr 1

theorem lp_right_even (u : Word) (c : GInt) :
    lastPosOf (vStringAt (vWordOf u true) c) = c + (texV2 (fracEven u) + (1, -1)) := by
  rw [StdCornerAnchors.stdAnchorC_of (vWordOf u true) (fracEven u).num (fracEven u).den
    (StringCorners.vWord_even_head_last u).1 (StringCorners.vWord_even_counts u).1
    (StringCorners.vWord_even_counts u).2]
  congr 1

/-! ### The heads and the last letters -/

theorem hw_last (u : Word) (b : Bool) : (hWordOf u b).getLast? = some Letter.p := (hWordOf_head_last u b).2
theorem hw_head (u : Word) (b : Bool) : (hWordOf u b).head? = some Letter.q := (hWordOf_head_last u b).1
theorem hw_rev_last (u : Word) (b : Bool) : (hWordOf u b).reverse.getLast? = some Letter.q := by
  rw [List.getLast?_reverse]; exact hw_head u b
theorem hw_rev_head (u : Word) (b : Bool) : (hWordOf u b).reverse.head? = some Letter.p := by
  rw [List.head?_reverse]; exact hw_last u b
theorem vp_head (u : Word) : (vWordOf u false).head? = some Letter.p := (StringCorners.vertWord_head_last u).1
theorem vp_last (u : Word) : (vWordOf u false).getLast? = some Letter.q := (StringCorners.vertWord_head_last u).2
theorem vq_head (u : Word) : (vWordOf u true).head? = some Letter.p := (StringCorners.vWord_even_head_last u).1
theorem vq_last (u : Word) : (vWordOf u true).getLast? = some Letter.q := (StringCorners.vWord_even_head_last u).2

theorem getLast?_app (X Y : BinaryWord) (hY : Y ≠ []) : (X ++ Y).getLast? = Y.getLast? :=
  List.getLast?_append_of_ne_nil _ hY

theorem head?_app (X Y : BinaryWord) (hX : X ≠ []) : (X ++ Y).head? = X.head? := by
  obtain ⟨a, X', rfl⟩ := List.exists_cons_of_ne_nil hX
  rfl


/-! ### The odd child, `W_1` even -/

theorem count_even (w : Word) (h : phase w ≠ 1) : w.count Digit.one % 2 = 0 := by
  unfold phase at h
  omega

theorem count_odd (w : Word) (h : phase w = 1) : ¬ w.count Digit.one % 2 = 0 := by
  unfold phase at h
  omega

/-- **The four boundary strings of the odd child, `W_1` even**, as chains of strings of its copies (`P^+` at `2U`, `P^-` at
`V`, `Q^{+,1}, Q^{+,2}` at `0, U`, `Q^{-,1}, Q^{-,2}` at `A + B, A + B + U`). -/
theorem odd_ef (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2)) (hph : phase w ≠ 1) :
    hStringAt (hWordOf w false) 0 = hStringAt (hWordOf u2 true) 0 ++
        hStringAt (hWordOf u2 true) (texV1Even (fracEven u2)) ++
        hStringAt (hWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2)) ∧
    vRevStringAt (vWordOf w false).reverse 0 = vRevStringAt (vWordOf u2 true).reverse 0 ++
        vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2)) ∧
    vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0)) =
      vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1))) ++
        vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2) +
          (texV1Even (fracEven u2) - (1, 1))) ∧
    hRevStringAt (hWordOf w false).reverse (lastPosOf (vRevStringAt (vWordOf w false).reverse 0)) =
      hRevStringAt (hWordOf u1 false).reverse (texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2))) ++
        hRevStringAt (hWordOf u2 true).reverse (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2))) ++
        hRevStringAt (hWordOf u2 true).reverse (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2) +
          (texV2 (fracEven u2) + (1, -2))) := by
  have hc := count_even w hph
  obtain ⟨hw1, -⟩ := GlueWords.hWordOf_child w u1 u2 hreg
  obtain ⟨hv1, -⟩ := GlueWords.vWordOf_child w u1 u2 hreg
  have hwb : hWordOf w false = hWordOf u2 true ++ hWordOf u2 true ++ hWordOf u1 false := by
    rw [hw1]; unfold childWords; rw [if_pos hc]
  have hwv : vWordOf w false = vWordOf u1 false ++ vWordOf u2 true := by
    rw [hv1]; unfold childWords; rw [if_pos hc]
  -- bottom
  have e1 := hStringAt_app (hWordOf u2 true ++ hWordOf u2 true) (hWordOf u1 false) 0
    (by rw [getLast?_app _ _ (hWord_ne _ _)]; exact hw_last _ _) (hw_head _ _)
  have e2 := hStringAt_app (hWordOf u2 true) (hWordOf u2 true) 0 (hw_last _ _) (hw_head _ _)
  have p1 : lastPosOf (hStringAt (hWordOf u2 true) 0) + (1, 1) = texV1Even (fracEven u2) := by
    rw [lp_bot_even]; ext <;> simp
  have p2 : lastPosOf (hStringAt (hWordOf u2 true ++ hWordOf u2 true) 0) + (1, 1) =
      texV1Even (fracEven u2) + texV1Even (fracEven u2) := by
    rw [e2, p1, lastPosOf_append _ _ (hStringAt_ne _ _ (hWord_ne _ _)), lp_bot_even]; ext <;> simp <;> ring
  have hbot : hStringAt (hWordOf w false) 0 = hStringAt (hWordOf u2 true) 0 ++
      hStringAt (hWordOf u2 true) (texV1Even (fracEven u2)) ++
      hStringAt (hWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2)) := by
    rw [hwb, e1, p2, e2, p1]
  -- left
  have hwl : (vWordOf w false).reverse = (vWordOf u2 true).reverse ++ (vWordOf u1 false).reverse := by
    rw [hwv, List.reverse_append]
  have e3 := vRevStringAt_app (vWordOf u2 true).reverse (vWordOf u1 false).reverse 0
    (by rw [List.getLast?_reverse]; exact vq_head u2) (by rw [List.head?_reverse]; exact vp_last u1)
  have p3 : lastPosOf (vRevStringAt (vWordOf u2 true).reverse 0) + (-1, 2) = texV2 (fracEven u2) := by
    rw [lp_left_even]; ext <;> simp
  have hleft : vRevStringAt (vWordOf w false).reverse 0 = vRevStringAt (vWordOf u2 true).reverse 0 ++
      vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2)) := by
    rw [hwl, e3, p3]
  -- right
  have p4 : lastPosOf (hStringAt (hWordOf w false) 0) =
      texV1Even (fracEven u2) + texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)) := by
    rw [hbot, lastPosOf_append _ _ (hStringAt_ne _ _ (hWord_ne _ _)), lp_bot_odd]
  have e4 := vStringAt_app (vWordOf u1 false) (vWordOf u2 true)
    (texV1Even (fracEven u2) + texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1))) (vWord_odd_ne u1) (vq_head u2)
  have p5 : lastPosOf (vStringAt (vWordOf u1 false)
      (texV1Even (fracEven u2) + texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))) + (-1, 1) =
      texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1)) := by
    rw [lp_right_odd]; ext <;> simp <;> ring
  refine ⟨hbot, hleft, by rw [p4, hwv, e4, p5], ?_⟩
  -- top
  have p6 : lastPosOf (vRevStringAt (vWordOf w false).reverse 0) = texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2)) := by
    rw [hleft, lastPosOf_append _ _ (vRevStringAt_ne _ _ (by simpa using vWord_odd_ne u1)), lp_left_odd]
  have hwt : (hWordOf w false).reverse =
      (hWordOf u1 false).reverse ++ (hWordOf u2 true).reverse ++ (hWordOf u2 true).reverse := by
    rw [hwb]; simp
  have e5 := hRevStringAt_app ((hWordOf u1 false).reverse ++ (hWordOf u2 true).reverse) (hWordOf u2 true).reverse
    (texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2)))
    (by rw [getLast?_app _ _ (by simpa using hWord_ne u2 true)]; exact hw_rev_last u2 true) (hw_rev_head u2 true)
  have e6 := hRevStringAt_app (hWordOf u1 false).reverse (hWordOf u2 true).reverse
    (texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2))) (hw_rev_last u1 false) (hw_rev_head u2 true)
  have p7 : lastPosOf (hRevStringAt (hWordOf u1 false).reverse (texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2)))) +
      (1, 0) = texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)) := by
    rw [lp_top_odd]; ext <;> simp <;> ring
  have p8 : lastPosOf (hRevStringAt ((hWordOf u1 false).reverse ++ (hWordOf u2 true).reverse)
      (texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2)))) + (1, 0) =
      texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV2 (fracEven u2) + (1, -2)) := by
    rw [e6, p7, lastPosOf_append _ _ (hRevStringAt_ne _ _ (by simpa using hWord_ne u2 true)), lp_top_even]
    ext <;> simp <;> ring
  rw [p6, hwt, e5, p8, e6, p7]

/-! ### The odd child, `W_1` odd -/

/-- **The four boundary strings of the odd child, `W_1` odd** (`P^+` at `0`, `P^-` at `2U + V`, `Q^{+,1}, Q^{+,2}` at
`A, A + U`, `Q^{-,1}, Q^{-,2}` at `B, B + U`). -/
theorem odd_of (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2)) (hph : phase w = 1) :
    hStringAt (hWordOf w false) 0 = hStringAt (hWordOf u1 false) 0 ++ hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1)) ++ hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) ∧
    vRevStringAt (vWordOf w false).reverse 0 = vRevStringAt (vWordOf u1 false).reverse 0 ++ vRevStringAt (vWordOf u2 true).reverse (texV2 (fracOdd u1)) ∧
    vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0)) =
      vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1))) ++ vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1))) ∧
    hRevStringAt (hWordOf w false).reverse (lastPosOf (vRevStringAt (vWordOf w false).reverse 0)) =
      hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2))) ++ hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV2 (fracEven u2) + (1, -2))) ++
        hRevStringAt (hWordOf u1 false).reverse (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2))) := by
  have hc := count_odd w hph
  obtain ⟨hw1, -⟩ := GlueWords.hWordOf_child w u1 u2 hreg
  obtain ⟨hv1, -⟩ := GlueWords.vWordOf_child w u1 u2 hreg
  have hwb : hWordOf w false = (hWordOf u1 false) ++ (hWordOf u2 true) ++ (hWordOf u2 true) := by
    rw [hw1]; unfold childWords; rw [if_neg hc]
  have hwv : vWordOf w false = (vWordOf u2 true) ++ (vWordOf u1 false) := by
    rw [hv1]; unfold childWords; rw [if_neg hc]
  have e1 := hStringAt_app ((hWordOf u1 false) ++ (hWordOf u2 true)) (hWordOf u2 true) 0 (by rw [getLast?_app _ _ (hWord_ne _ _)]; exact hw_last _ _) (hw_head _ _)
  have e2 := hStringAt_app (hWordOf u1 false) (hWordOf u2 true) 0 (hw_last _ _) (hw_head _ _)
  have p1 : lastPosOf (hStringAt (hWordOf u1 false) 0) + (1, 1) = texV1Odd (fracOdd u1) := by rw [lp_bot_odd]; ext <;> simp
  have p2 : lastPosOf (hStringAt ((hWordOf u1 false) ++ (hWordOf u2 true)) 0) + (1, 1) = texV1Odd (fracOdd u1) + texV1Even (fracEven u2) := by
    rw [e2, p1, lastPosOf_append _ _ (hStringAt_ne _ _ (hWord_ne _ _)), lp_bot_even]; ext <;> simp <;> ring
  have hbot : hStringAt (hWordOf w false) 0 = hStringAt (hWordOf u1 false) 0 ++ hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1)) ++ hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) := by
    rw [hwb, e1, p2, e2, p1]
  have hwl : (vWordOf w false).reverse = (vWordOf u1 false).reverse ++ (vWordOf u2 true).reverse := by rw [hwv, List.reverse_append]
  have e3 := vRevStringAt_app (vWordOf u1 false).reverse (vWordOf u2 true).reverse 0 (by rw [List.getLast?_reverse]; exact vp_head u1)
    (by rw [List.head?_reverse]; exact vq_last u2)
  have p3 : lastPosOf (vRevStringAt (vWordOf u1 false).reverse 0) + (-1, 2) = texV2 (fracOdd u1) := by rw [lp_left_odd]; ext <;> simp
  have hleft : vRevStringAt (vWordOf w false).reverse 0 = vRevStringAt (vWordOf u1 false).reverse 0 ++ vRevStringAt (vWordOf u2 true).reverse (texV2 (fracOdd u1)) := by
    rw [hwl, e3, p3]
  have p4 : lastPosOf (hStringAt (hWordOf w false) 0) = texV1Odd (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1)) := by
    rw [hbot, lastPosOf_append _ _ (hStringAt_ne _ _ (hWord_ne _ _)), lp_bot_even]
  have e4 := vStringAt_app (vWordOf u2 true) (vWordOf u1 false) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1))) (vWord_even_ne u2) (vp_head u1)
  have p5 : lastPosOf (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1)))) + (-1, 1) = texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)) := by
    rw [lp_right_even]; ext <;> simp <;> ring
  refine ⟨hbot, hleft, by rw [p4, hwv, e4, p5], ?_⟩
  have p6 : lastPosOf (vRevStringAt (vWordOf w false).reverse 0) = texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)) := by
    rw [hleft, lastPosOf_append _ _ (vRevStringAt_ne _ _ (by simpa using vWord_even_ne u2)), lp_left_even]
  have hwt : (hWordOf w false).reverse = (hWordOf u2 true).reverse ++ (hWordOf u2 true).reverse ++ (hWordOf u1 false).reverse := by rw [hwb]; simp
  have e5 := hRevStringAt_app ((hWordOf u2 true).reverse ++ (hWordOf u2 true).reverse) (hWordOf u1 false).reverse (texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))
    (by rw [getLast?_app _ _ (by simpa using hWord_ne u2 true)]; exact hw_rev_last u2 true) (hw_rev_head u1 false)
  have e6 := hRevStringAt_app (hWordOf u2 true).reverse (hWordOf u2 true).reverse (texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2))) (hw_rev_last u2 true) (hw_rev_head u2 true)
  have p7 : lastPosOf (hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))) + (1, 0) = texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV2 (fracEven u2) + (1, -2)) := by
    rw [lp_top_even]; ext <;> simp <;> ring
  have p8 : lastPosOf (hRevStringAt ((hWordOf u2 true).reverse ++ (hWordOf u2 true).reverse) (texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))) + (1, 0) =
      texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2)) := by
    rw [e6, p7, lastPosOf_append _ _ (hRevStringAt_ne _ _ (by simpa using hWord_ne u2 true)), lp_top_even]
    ext <;> simp <;> ring
  rw [p6, hwt, e5, p8, e6, p7]

/-! ### The even child, `W_1` even -/

/-- **The four boundary strings of the even child, `W_1` even** (`P^{+,1}, P^{+,2}` at `U, U + B`, `P^{-,1}, P^{-,2}` at
`V, V + B`, `Q^+` at `0`, `Q^-` at `A + 2B`). -/
theorem even_ef (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2)) (hph : phase w ≠ 1) :
    hStringAt (hWordOf w true) 0 = hStringAt (hWordOf u2 true) 0 ++ hStringAt (hWordOf u1 false) (texV1Even (fracEven u2)) ∧
    vRevStringAt (vWordOf w true).reverse 0 = vRevStringAt (vWordOf u2 true).reverse 0 ++ vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2)) ++
        vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2) + texV2 (fracOdd u1)) ∧
    vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0)) =
      vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1))) ++ vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV2 (fracOdd u1) + (texV1Odd (fracOdd u1) - (1, 1))) ++
        vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1))) ∧
    hRevStringAt (hWordOf w true).reverse (lastPosOf (vRevStringAt (vWordOf w true).reverse 0)) =
      hRevStringAt (hWordOf u1 false).reverse (texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV2 (fracOdd u1) + (1, -2))) ++ hRevStringAt (hWordOf u2 true).reverse (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2))) := by
  have hc := count_even w hph
  obtain ⟨-, hw2⟩ := GlueWords.hWordOf_child w u1 u2 hreg
  obtain ⟨-, hv2⟩ := GlueWords.vWordOf_child w u1 u2 hreg
  have hwb : hWordOf w true = (hWordOf u2 true) ++ (hWordOf u1 false) := by
    rw [hw2]; unfold childWords; rw [if_pos hc]
  have hwv : vWordOf w true = (vWordOf u1 false) ++ (vWordOf u1 false) ++ (vWordOf u2 true) := by
    rw [hv2]; unfold childWords; rw [if_pos hc]
  have e1 := hStringAt_app (hWordOf u2 true) (hWordOf u1 false) 0 (hw_last _ _) (hw_head _ _)
  have p1 : lastPosOf (hStringAt (hWordOf u2 true) 0) + (1, 1) = texV1Even (fracEven u2) := by rw [lp_bot_even]; ext <;> simp
  have hbot : hStringAt (hWordOf w true) 0 = hStringAt (hWordOf u2 true) 0 ++ hStringAt (hWordOf u1 false) (texV1Even (fracEven u2)) := by rw [hwb, e1, p1]
  have hwl : (vWordOf w true).reverse = (vWordOf u2 true).reverse ++ (vWordOf u1 false).reverse ++ (vWordOf u1 false).reverse := by rw [hwv]; simp
  have e3 := vRevStringAt_app ((vWordOf u2 true).reverse ++ (vWordOf u1 false).reverse) (vWordOf u1 false).reverse 0
    (by rw [getLast?_app _ _ (by simpa using vWord_odd_ne u1), List.getLast?_reverse]; exact vp_head u1)
    (by rw [List.head?_reverse]; exact vp_last u1)
  have e3' := vRevStringAt_app (vWordOf u2 true).reverse (vWordOf u1 false).reverse 0 (by rw [List.getLast?_reverse]; exact vq_head u2)
    (by rw [List.head?_reverse]; exact vp_last u1)
  have p3 : lastPosOf (vRevStringAt (vWordOf u2 true).reverse 0) + (-1, 2) = texV2 (fracEven u2) := by rw [lp_left_even]; ext <;> simp
  have p3' : lastPosOf (vRevStringAt ((vWordOf u2 true).reverse ++ (vWordOf u1 false).reverse) 0) + (-1, 2) = texV2 (fracEven u2) + texV2 (fracOdd u1) := by
    rw [e3', p3, lastPosOf_append _ _ (vRevStringAt_ne _ _ (by simpa using vWord_odd_ne u1)), lp_left_odd]
    ext <;> simp <;> ring
  have hleft : vRevStringAt (vWordOf w true).reverse 0 = vRevStringAt (vWordOf u2 true).reverse 0 ++ vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2)) ++
      vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2) + texV2 (fracOdd u1)) := by
    rw [hwl, e3, p3', e3', p3]
  have p4 : lastPosOf (hStringAt (hWordOf w true) 0) = texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)) := by
    rw [hbot, lastPosOf_append _ _ (hStringAt_ne _ _ (hWord_ne _ _)), lp_bot_odd]
  have e4 := vStringAt_app ((vWordOf u1 false) ++ (vWordOf u1 false)) (vWordOf u2 true) (texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1))) (by simpa using vWord_odd_ne u1) (vq_head u2)
  have e4' := vStringAt_app (vWordOf u1 false) (vWordOf u1 false) (texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1))) (vWord_odd_ne u1) (vp_head u1)
  have p5 : lastPosOf (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))) + (-1, 1) = texV1Even (fracEven u2) + texV2 (fracOdd u1) + (texV1Odd (fracOdd u1) - (1, 1)) := by
    rw [lp_right_odd]; ext <;> simp <;> ring
  have p5' : lastPosOf (vStringAt ((vWordOf u1 false) ++ (vWordOf u1 false)) (texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))) + (-1, 1) = texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1)) := by
    rw [e4', p5, lastPosOf_append _ _ (vStringAt_ne _ _ (vWord_odd_ne u1)), lp_right_odd]
    ext <;> simp <;> ring
  refine ⟨hbot, hleft, by rw [p4, hwv, e4, p5', e4', p5], ?_⟩
  have p6 : lastPosOf (vRevStringAt (vWordOf w true).reverse 0) = texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV2 (fracOdd u1) + (1, -2)) := by
    rw [hleft, lastPosOf_append _ _ (vRevStringAt_ne _ _ (by simpa using vWord_odd_ne u1)), lp_left_odd]
  have hwt : (hWordOf w true).reverse = (hWordOf u1 false).reverse ++ (hWordOf u2 true).reverse := by rw [hwb, List.reverse_append]
  have e5 := hRevStringAt_app (hWordOf u1 false).reverse (hWordOf u2 true).reverse (texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV2 (fracOdd u1) + (1, -2))) (hw_rev_last u1 false)
    (hw_rev_head u2 true)
  have p7 : lastPosOf (hRevStringAt (hWordOf u1 false).reverse (texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV2 (fracOdd u1) + (1, -2)))) + (1, 0) = texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)) := by
    rw [lp_top_odd]; ext <;> simp <;> ring
  rw [p6, hwt, e5, p7]

/-! ### The even child, `W_1` odd -/

/-- **The four boundary strings of the even child, `W_1` odd** (`P^{+,1}, P^{+,2}` at `0, B`, `P^{-,1}, P^{-,2}` at
`U + V, U + V + B`, `Q^+` at `A`, `Q^-` at `2B`). -/
theorem even_of (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2)) (hph : phase w = 1) :
    hStringAt (hWordOf w true) 0 = hStringAt (hWordOf u1 false) 0 ++ hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1)) ∧
    vRevStringAt (vWordOf w true).reverse 0 = vRevStringAt (vWordOf u1 false).reverse 0 ++ vRevStringAt (vWordOf u1 false).reverse (texV2 (fracOdd u1)) ++
        vRevStringAt (vWordOf u2 true).reverse (texV2 (fracOdd u1) + texV2 (fracOdd u1)) ∧
    vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0)) =
      vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1))) ++ vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1))) ++
        vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV1Odd (fracOdd u1) - (1, 1))) ∧
    hRevStringAt (hWordOf w true).reverse (lastPosOf (vRevStringAt (vWordOf w true).reverse 0)) =
      hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2))) ++ hRevStringAt (hWordOf u1 false).reverse (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV2 (fracOdd u1) + (1, -2))) := by
  have hc := count_odd w hph
  obtain ⟨-, hw2⟩ := GlueWords.hWordOf_child w u1 u2 hreg
  obtain ⟨-, hv2⟩ := GlueWords.vWordOf_child w u1 u2 hreg
  have hwb : hWordOf w true = (hWordOf u1 false) ++ (hWordOf u2 true) := by
    rw [hw2]; unfold childWords; rw [if_neg hc]
  have hwv : vWordOf w true = (vWordOf u2 true) ++ (vWordOf u1 false) ++ (vWordOf u1 false) := by
    rw [hv2]; unfold childWords; rw [if_neg hc]
  have e1 := hStringAt_app (hWordOf u1 false) (hWordOf u2 true) 0 (hw_last _ _) (hw_head _ _)
  have p1 : lastPosOf (hStringAt (hWordOf u1 false) 0) + (1, 1) = texV1Odd (fracOdd u1) := by rw [lp_bot_odd]; ext <;> simp
  have hbot : hStringAt (hWordOf w true) 0 = hStringAt (hWordOf u1 false) 0 ++ hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1)) := by rw [hwb, e1, p1]
  have hwl : (vWordOf w true).reverse = (vWordOf u1 false).reverse ++ (vWordOf u1 false).reverse ++ (vWordOf u2 true).reverse := by rw [hwv]; simp
  have e3 := vRevStringAt_app ((vWordOf u1 false).reverse ++ (vWordOf u1 false).reverse) (vWordOf u2 true).reverse 0
    (by rw [getLast?_app _ _ (by simpa using vWord_odd_ne u1), List.getLast?_reverse]; exact vp_head u1)
    (by rw [List.head?_reverse]; exact vq_last u2)
  have e3' := vRevStringAt_app (vWordOf u1 false).reverse (vWordOf u1 false).reverse 0 (by rw [List.getLast?_reverse]; exact vp_head u1)
    (by rw [List.head?_reverse]; exact vp_last u1)
  have p3 : lastPosOf (vRevStringAt (vWordOf u1 false).reverse 0) + (-1, 2) = texV2 (fracOdd u1) := by rw [lp_left_odd]; ext <;> simp
  have p3' : lastPosOf (vRevStringAt ((vWordOf u1 false).reverse ++ (vWordOf u1 false).reverse) 0) + (-1, 2) = texV2 (fracOdd u1) + texV2 (fracOdd u1) := by
    rw [e3', p3, lastPosOf_append _ _ (vRevStringAt_ne _ _ (by simpa using vWord_odd_ne u1)), lp_left_odd]
    ext <;> simp <;> ring
  have hleft : vRevStringAt (vWordOf w true).reverse 0 = vRevStringAt (vWordOf u1 false).reverse 0 ++ vRevStringAt (vWordOf u1 false).reverse (texV2 (fracOdd u1)) ++
      vRevStringAt (vWordOf u2 true).reverse (texV2 (fracOdd u1) + texV2 (fracOdd u1)) := by
    rw [hwl, e3, p3', e3', p3]
  have p4 : lastPosOf (hStringAt (hWordOf w true) 0) = texV1Odd (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1)) := by
    rw [hbot, lastPosOf_append _ _ (hStringAt_ne _ _ (hWord_ne _ _)), lp_bot_even]
  have e4 := vStringAt_app ((vWordOf u2 true) ++ (vWordOf u1 false)) (vWordOf u1 false) (texV1Odd (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1)))
    (fun h => vWord_even_ne u2 (List.append_eq_nil_iff.1 h).1) (vp_head u1)
  have e4' := vStringAt_app (vWordOf u2 true) (vWordOf u1 false) (texV1Odd (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1))) (vWord_even_ne u2) (vp_head u1)
  have p5 : lastPosOf (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1)))) + (-1, 1) = texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)) := by
    rw [lp_right_even]; ext <;> simp <;> ring
  have p5' : lastPosOf (vStringAt ((vWordOf u2 true) ++ (vWordOf u1 false)) (texV1Odd (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1)))) + (-1, 1) = texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV1Odd (fracOdd u1) - (1, 1)) := by
    rw [e4', p5, lastPosOf_append _ _ (vStringAt_ne _ _ (vWord_odd_ne u1)), lp_right_odd]
    ext <;> simp <;> ring
  refine ⟨hbot, hleft, by rw [p4, hwv, e4, p5', e4', p5], ?_⟩
  have p6 : lastPosOf (vRevStringAt (vWordOf w true).reverse 0) = texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)) := by
    rw [hleft, lastPosOf_append _ _ (vRevStringAt_ne _ _ (by simpa using vWord_even_ne u2)), lp_left_even]
  have hwt : (hWordOf w true).reverse = (hWordOf u2 true).reverse ++ (hWordOf u1 false).reverse := by rw [hwb, List.reverse_append]
  have e5 := hRevStringAt_app (hWordOf u2 true).reverse (hWordOf u1 false).reverse (texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2))) (hw_rev_last u2 true)
    (hw_rev_head u1 false)
  have p7 : lastPosOf (hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))) + (1, 0) =
      texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV2 (fracOdd u1) + (1, -2)) := by
    rw [lp_top_even]; ext <;> simp <;> ring
  rw [p6, hwt, e5, p7]

end FLatticePaper.Tiles.GlueStringDecomp
