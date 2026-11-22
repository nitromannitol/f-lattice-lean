import FLatticePaper.Tiles.TilingCriteria

/-! The boundary word of `lemma:almost_square_tiling` uses `(rev w).hat`, not `w.hat`. Here `hat (rev w)` is letterwise
negation, so the two boundary words agree exactly when `w` is a palindrome. -/

open FLatticePaper.Tiles

theorem hat_rev_eq_map_neg (w : F2Word) : F2Word.hat (F2Word.rev w) = w.map Unit4.neg := by
  simp [F2Word.hat, F2Word.rev, List.map_reverse]

#print axioms hat_rev_eq_map_neg
