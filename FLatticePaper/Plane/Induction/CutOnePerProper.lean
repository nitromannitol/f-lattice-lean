import FLatticePaper.Plane.Induction.CutRows
import FLatticePaper.Plane.Induction.ChildNumerator

/-! The named cut hypothesis `CutOnePerOrdinate` holds for the child frame of every proper word: each ordinate `0 ≤ r < L` carries exactly
one free V point (`CutRows.cut_one_per_ordinate`, the existence from `exists_row_point` and the uniqueness from `freeV_row_unique`). The
frame bounds it needs follow from the word: a proper word has child numerator at least three (`child_num_ge_three`), the child
denominator exceeds the numerator by at least two (`child_facts`), and the sum `n + d` is even (`child_even`). -/

namespace FLatticePaper.CutOnePerProper

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeEnum

theorem cutOnePerOrdinate_of_proper {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    CutOnePerOrdinate (frameAt word) := by
  have h3 := child_num_ge_three h
  have hdn := (frameAt word).child_facts.2.2.1
  exact CutRows.cut_one_per_ordinate (frameAt word) (by omega) (by omega) (frameAt word).child_even

end FLatticePaper.CutOnePerProper
