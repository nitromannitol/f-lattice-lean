import FLatticePaper.Plane.Induction.W1Hexc
import FLatticePaper.Plane.Induction.W1OddZeroWord
import FLatticePaper.Plane.Induction.SheetPieces

/-! # Task 75 (SeedFields): both inherited zero seeds of a proper word, from the conjugate's seeds

`SeedFields w` has the even seed (`W1Hexc.even_zero_full`, from the conjugate's `SeedFields` and packet and the open inputs
`openInputs_of_strong`) and the odd seed (`W1OddZeroWord.odd_zero_at_word`, from the conjugate's even seed). Both use only the conjugate's
strong estimates and its `SeedFields`, so this is the induction step of the seeds. The base words (whose conjugate is not proper) need
their own seeds; they are not covered here. -/

namespace FLatticePaper.W1SeedFields

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Seeds

/-- **`SeedFields w` from the conjugate's seeds** (task 75, the induction step). -/
theorem seedFields_of_conj {w : Word} (h : ∃ x ∈ w, x ≠ Digit.three) (hS : StrongEstimates (conjWord w))
    (hpar : SeedFields (conjWord w)) : SeedFields w where
  even_zero := FLatticePaper.W1Hexc.even_zero_full h hpar hS.packet (openInputs_of_strong h hS)
  odd_zero := fun x hx hxl => FLatticePaper.W1OddZeroWord.odd_zero_at_word h hS hpar.even_zero x hx hxl

end FLatticePaper.W1SeedFields
