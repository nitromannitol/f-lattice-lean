import FLatticePaper.Tiles.BaseCasePseudoSquares

/-! The shared walk decomposition of the boundary word `pseudoBoundaryWord w1 w2` (`= boundaryWordOf w1 w2`), from a base point `c`.

The walk has four sides, each a list of points, consecutive sides sharing their end and start point:
* the lower side is the walk of `w1` from `c`;
* the right side is the walk of `w2` from `c + Σw1` (its start is the walk index `|w1|`, `walk_pseudo_right`);
* the top side is the reflection of the walk of `w1` through `c + Σw1 + Σw2` (its start is the walk index `|w1| + |w2|`);
* the left side is the reflection of the walk of `w2` through `c + Σw2` (its start is the walk index `|w1| + |w2| + |w1|`,
  `walk_pseudo_top`).

The top and left sides are reflections because `hat (rev w) = map neg w`: their letters are the negated letters of `w1` and `w2`.
The lemma `walk_decomp` states the four sides as one list. -/

namespace FLatticePaper.Tiles.WalkDecomp

open FLatticePaper.Tiles

theorem walk_cons (c : GInt) (x : Unit4) (w : F2Word) :
    F2Word.walk c (x :: w) = c :: F2Word.walk (c + x.vec) w := by
  simp [F2Word.walk, List.scanl_cons]

theorem walk_nil (c : GInt) : F2Word.walk c [] = [c] := by
  simp [F2Word.walk]

/-- The walk from `c` is the walk from `0` translated by `c`. -/
theorem walk_translate (c : GInt) (w : F2Word) :
    F2Word.walk c w = (F2Word.walk 0 w).map (fun z => c + z) := by
  induction w generalizing c with
  | nil => simp [walk_nil]
  | cons x w ih =>
    have h1 := ih (c + x.vec)
    have h2 := ih (0 + x.vec)
    rw [walk_cons, walk_cons, h1, h2]
    simp [List.map_map, Function.comp_def, add_assoc]

/-- The walk of a concatenation: the walk of the first part, then the walk of the second part started at the end of the first. -/
theorem walk_append (u v : F2Word) (c : GInt) :
    F2Word.walk c (u ++ v) = F2Word.walk c u ++ (F2Word.walk (c + F2Word.sum u) v).tail := by
  induction u generalizing c with
  | nil =>
    cases v with
    | nil => simp [walk_nil]
    | cons x v => simp [walk_cons, walk_nil, F2Word.sum]
  | cons x u ih =>
    rw [List.cons_append, walk_cons, ih (c + x.vec), walk_cons]
    simp [F2Word.sum, add_assoc]

/-- The reversed-and-negated word: `hat (rev w) = map neg w`. -/
theorem hat_rev_eq (w : F2Word) : F2Word.hat (F2Word.rev w) = w.map Unit4.neg := by
  simp [F2Word.hat, F2Word.rev, List.map_reverse, List.reverse_reverse]

/-- The walk of the negated letters is the reflection of the walk through the base point. -/
theorem walk_neg (P : GInt) (w : F2Word) :
    F2Word.walk P (w.map Unit4.neg) = (F2Word.walk 0 w).map (fun z => P - z) := by
  induction w generalizing P with
  | nil => simp [walk_nil]
  | cons x w ih =>
    have hw := walk_translate (0 + x.vec) w
    rw [List.map_cons, walk_cons, ih (P + x.neg.vec), walk_cons, hw]
    have key : ∀ z : GInt, P + x.neg.vec - z = P - (0 + x.vec + z) := fun z => by
      rw [unit4_vec_neg]
      abel
    simp only [List.map_cons, List.map_map, Function.comp_def, sub_zero, key]

/-- **The shared walk decomposition.** The boundary walk from `c` is the lower side, the right side, the top side and the left
side, in order (each side starting at the end of the previous one). -/
theorem walk_decomp (c : GInt) (w1 w2 : F2Word) :
    F2Word.walk c (pseudoBoundaryWord w1 w2) =
      F2Word.walk c w1 ++ (F2Word.walk (c + F2Word.sum w1) w2).tail ++
        ((F2Word.walk 0 w1).map (fun z => (c + F2Word.sum w1 + F2Word.sum w2) - z)).tail ++
        ((F2Word.walk 0 w2).map (fun z => (c + F2Word.sum w2) - z)).tail := by
  unfold pseudoBoundaryWord
  rw [walk_append (w1 ++ w2 ++ F2Word.hat (F2Word.rev w1)) (F2Word.hat (F2Word.rev w2)) c,
    walk_append (w1 ++ w2) (F2Word.hat (F2Word.rev w1)) c, walk_append w1 w2 c]
  simp only [hat_rev_eq, f2sum_append, sum_map_neg, walk_neg]
  have hP : c + (F2Word.sum w1 + F2Word.sum w2) = c + F2Word.sum w1 + F2Word.sum w2 := by abel
  have hL : c + (F2Word.sum w1 + F2Word.sum w2 + -F2Word.sum w1) = c + F2Word.sum w2 := by abel
  rw [hP, hL]

end FLatticePaper.Tiles.WalkDecomp
