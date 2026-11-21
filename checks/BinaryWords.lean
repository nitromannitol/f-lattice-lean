import FLatticePaper.Tiles.BinaryWords

open FLatticePaper.Tiles FLatticePaper.Farey

#print axioms FLatticePaper.Tiles.almost_palindrome_one
#print axioms FLatticePaper.Tiles.almost_palindrome_two
#print axioms FLatticePaper.Tiles.almost_palindrome_three

/-! `eq:words_degenerate_cases` for k = 0, 1, 2. -/

example : quadAt [] (List.replicate 0 Digit.three)
    = ⟨[Letter.q] ++ List.replicate 0 Letter.p ++ [Letter.q] ++ List.replicate 1 Letter.p,
      [Letter.q] ++ List.replicate 1 Letter.p, [Letter.p], [Letter.q] ++ List.replicate 0 Letter.p⟩ := by
  decide

example : quadAt [] (List.replicate 1 Digit.three)
    = ⟨[Letter.q] ++ List.replicate 1 Letter.p ++ [Letter.q] ++ List.replicate 2 Letter.p,
      [Letter.q] ++ List.replicate 2 Letter.p, [Letter.p], [Letter.q] ++ List.replicate 1 Letter.p⟩ := by
  decide

example : quadAt [] (List.replicate 2 Digit.three)
    = ⟨[Letter.q] ++ List.replicate 2 Letter.p ++ [Letter.q] ++ List.replicate 3 Letter.p,
      [Letter.q] ++ List.replicate 3 Letter.p, [Letter.p], [Letter.q] ++ List.replicate 2 Letter.p⟩ := by
  decide

example : quadAt [] (List.replicate 0 Digit.two)
    = ⟨List.replicate (2 * (0 + 1)) Letter.q ++ [Letter.p],
      List.replicate (2 * 0 + 1) Letter.q ++ [Letter.p], List.replicate (2 * 0) Letter.q ++ [Letter.p],
      [Letter.q]⟩ := by
  decide

example : quadAt [] (List.replicate 1 Digit.two)
    = ⟨List.replicate (2 * (1 + 1)) Letter.q ++ [Letter.p],
      List.replicate (2 * 1 + 1) Letter.q ++ [Letter.p], List.replicate (2 * 1) Letter.q ++ [Letter.p],
      [Letter.q]⟩ := by
  decide

example : quadAt [] (List.replicate 2 Digit.two)
    = ⟨List.replicate (2 * (2 + 1)) Letter.q ++ [Letter.p],
      List.replicate (2 * 2 + 1) Letter.q ++ [Letter.p], List.replicate (2 * 2) Letter.q ++ [Letter.p],
      [Letter.q]⟩ := by
  decide
