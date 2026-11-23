import FLatticePaper.Tiles.BinaryWords

/-! Task 53, item 4 (base words): the quad words of the base family `3^k`.

For `k` threes, the parent `p` is `[p]`, the child `q` is `q p^(k+1)`, and the forward child is `(q p^k)(q p^k) p`.
These are the words of the base tiles `ladderF`/`stairF` of `SiteBase`; the step is the child operator of `childWords` at a
prefix with no `1`s. -/

namespace FLatticePaper.Tiles.BaseWordsQuad

open FLatticePaper.Tiles FLatticePaper.Farey

theorem quad_three (k : ℕ) :
    (quadAt [] (List.replicate k Digit.three)).parentP = [Letter.p] ∧
      (quadAt [] (List.replicate k Digit.three)).childQ = Letter.q :: List.replicate (k + 1) Letter.p ∧
      (quadAt [] (List.replicate k Digit.three)).childP =
        (Letter.q :: List.replicate k Letter.p) ++ (Letter.q :: List.replicate k Letter.p) ++ [Letter.p] := by
  induction k with
  | zero =>
    simp [quadAt_nil, initialQuad, childWords]
  | succ k ih =>
    obtain ⟨h1, h2, -⟩ := ih
    have hc : ((List.replicate k Digit.three) ++ [Digit.three]).count Digit.one = 0 := by
      simp [List.count_replicate]
    rw [List.replicate_succ', quadAt_append_singleton]
    simp only [WordQuad.step, List.nil_append]
    simp only [childWords, hc, Nat.zero_mod, if_true, h1, h2]
    refine ⟨trivial, ?_, ?_⟩
    · simp [List.replicate_succ', List.append_assoc]
    · simp

end FLatticePaper.Tiles.BaseWordsQuad
