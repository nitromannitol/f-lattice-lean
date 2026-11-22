import FLatticePaper.Plane.Induction.StandardField
import FLatticePaper.Farey.Numerators

/-! The numerator of the child of a proper word is at least three (task 38, item 1): the child is the current even
register of `parentsAt word`, and `current_even_num_ge_three` gives its numerator `2O + E ≥ 3` for a word with a digit
other than three. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem child_num_ge_three {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    3 ≤ (frameAt word).child.num := by
  have := Farey.current_even_num_ge_three word h
  show 3 ≤ ((parentsAt word).current .even).num
  exact this

end FLatticePaper.Induction
