import FLatticePaper.Tiles.PseudoSquareAlong
import FLatticePaper.Tiles.AlmostTiling

/-! # The boundary walk at the two anchor indices of the pseudo-square placement

For the walk placement `walkAt c wh wv k` of `alongStrings`, the point at the index `|gH wh|` is `c + Σ gH wh` and the point at
`|gH wh| + |gV wv| + |gH wh|` is `c + Σ gV wv` (the reversed copy of the first block cancels the first block's sum). These two points
are the anchors `lastPosOf (hStringAt …)` and `lastPosOf (vRevStringAt …)` of `anchoredStrings`, which is what `InsideTile` needs. -/

namespace FLatticePaper.Tiles

theorem F2Word_sum_hat (w : F2Word) : F2Word.sum (F2Word.hat w) = -F2Word.sum w := by
  induction w with
  | nil => simp [F2Word.sum, F2Word.hat]
  | cons x w ih =>
    unfold F2Word.sum at *
    simp only [F2Word.hat, List.reverse_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, List.map_nil, List.sum_nil] at *
    cases x <;> simp [Unit4.neg, Unit4.vec] at * <;> omega

theorem F2Word_sum_append (a b : F2Word) : F2Word.sum (a ++ b) = F2Word.sum a + F2Word.sum b := by
  unfold F2Word.sum
  simp [List.map_append, List.sum_append]

theorem F2Word_sum_rev (w : F2Word) : F2Word.sum (F2Word.rev w) = F2Word.sum w := by
  unfold F2Word.sum F2Word.rev
  rw [List.map_reverse, List.sum_reverse]

theorem F2Word_walk_getD_zero (v : F2Word) (c d : GInt) : (F2Word.walk c v).getD 0 d = c := by
  cases v <;> simp [F2Word.walk, List.scanl_cons]

theorem F2Word_walk_getD_sum (u : F2Word) (c d : GInt) :
    (F2Word.walk c u).getD u.length d = c + F2Word.sum u := by
  induction u generalizing c with
  | nil => simp [F2Word.walk, F2Word.sum]
  | cons x u ih =>
    have h : F2Word.walk c (x :: u) = c :: F2Word.walk (c + x.vec) u := by
      simp [F2Word.walk, List.scanl_cons]
    rw [h, List.length_cons, List.getD_cons_succ, ih]
    unfold F2Word.sum at *
    simp only [List.map_cons, List.sum_cons]
    abel

theorem F2Word_walk_getD_append (u v : F2Word) (c d : GInt) :
    (F2Word.walk c (u ++ v)).getD u.length d = (F2Word.walk c u).getD u.length d := by
  induction u generalizing c with
  | nil => simp only [List.nil_append, List.length_nil]; rw [F2Word_walk_getD_zero, F2Word_walk_getD_zero]
  | cons x u ih =>
    have h1 : F2Word.walk c ((x :: u) ++ v) = c :: F2Word.walk (c + x.vec) (u ++ v) := by
      simp [F2Word.walk, List.scanl_cons]
    have h2 : F2Word.walk c (x :: u) = c :: F2Word.walk (c + x.vec) u := by
      simp [F2Word.walk, List.scanl_cons]
    rw [h1, h2, List.length_cons, List.getD_cons_succ, List.getD_cons_succ, ih]

theorem walkAt_gH (c : GInt) (wh wv : BinaryWord) :
    walkAt c wh wv (gH wh).length = c + F2Word.sum (gH wh) := by
  unfold walkAt boundaryWalk pseudoBoundaryWord gPseudo
  dsimp only
  have hw : gH wh ++ gV wv ++ F2Word.hat (F2Word.rev (gH wh)) ++ F2Word.hat (F2Word.rev (gV wv))
      = gH wh ++ (gV wv ++ F2Word.hat (F2Word.rev (gH wh)) ++ F2Word.hat (F2Word.rev (gV wv))) := by
    simp
  rw [hw, F2Word_walk_getD_append, F2Word_walk_getD_sum]

theorem walkAt_total (c : GInt) (wh wv : BinaryWord) :
    walkAt c wh wv ((gH wh).length + (gV wv).length + (gH wh).length) = c + F2Word.sum (gV wv) := by
  unfold walkAt boundaryWalk pseudoBoundaryWord gPseudo
  dsimp only
  have hlen : (F2Word.hat (F2Word.rev (gH wh))).length = (gH wh).length := by
    simp [F2Word.hat, F2Word.rev]
  have hs : (gH wh).length + (gV wv).length + (gH wh).length
      = (gH wh ++ gV wv ++ F2Word.hat (F2Word.rev (gH wh))).length := by
    simp [hlen]
    omega
  have hw : gH wh ++ gV wv ++ F2Word.hat (F2Word.rev (gH wh)) ++ F2Word.hat (F2Word.rev (gV wv))
      = (gH wh ++ gV wv ++ F2Word.hat (F2Word.rev (gH wh))) ++ F2Word.hat (F2Word.rev (gV wv)) := rfl
  rw [hs, hw, F2Word_walk_getD_append, F2Word_walk_getD_sum]
  have hsum : F2Word.sum (gH wh ++ gV wv ++ F2Word.hat (F2Word.rev (gH wh)))
      = F2Word.sum (gV wv) := by
    rw [F2Word_sum_append, F2Word_sum_append, F2Word_sum_hat, F2Word_sum_rev]
    abel
  rw [hsum]

end FLatticePaper.Tiles
