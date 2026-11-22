import FLatticePaper.Plane.Induction.TwosSheets
import FLatticePaper.Plane.Induction.SheetMinFromConj

/-! Task 29, the premise I3a at the twos words. The chain potential of `2^(k+1)` depends only on the reciprocal field
`G = reciprocalField k` (the standard field of the conjugate `3^k`) and on the signs `eps = -1` of the frames of `2^k` and
`2^(k+1)`, with the odd parent of the conjugate `0/1`. The earlier chain price then reduces to

  Xi(x) = G(s) - G(s + (1,1)) - s_2,     s = Z x = (-x_2, x_1 - 1),

so the unit increments of `Xi` (the first clause of I3 in LocalPremises) are the unit increments of the explicit function
`s |-> G(s) - G(s + (1,1)) - s_2` on the reciprocal side. Checked numerically on the words `2^1..2^5`
(scripts/twos_chain_reduction.py). -/

namespace FLatticePaper.Induction
open Farey Construction FLatticePaper

theorem parentsAt_three_odd (k : ℕ) :
    (frameAt (List.replicate k Digit.three)).parents.odd = ⟨0, 1⟩ := by
  show (parentsAt (List.replicate k Digit.three)).odd = ⟨0, 1⟩
  rw [parentsAt_replicate_three]

/-- The earlier chain shift of the odd parent `0/1` at the two signs `-1`, `-1` is `(1,1)`. -/
theorem earlierChainShift_zero_one_neg :
    earlierChainShift ⟨0, 1⟩ (-1) (-1) = (1, 1) := by
  unfold earlierChainShift
  norm_num

/-- The chain potential of the twos word `2^(k+1)` in terms of the reciprocal field `reciprocalField k`. -/
theorem sheetChainPotential_twos_succ (k : ℕ) (x : Site) :
    sheetChainPotential (List.replicate (k + 1) Digit.two)
        (standardField (conjWord (List.replicate (k + 1) Digit.two))) x =
      reciprocalField k (-x.2, x.1 - 1) - reciprocalField k ((-x.2, x.1 - 1) + (1, 1)) -
        (-x.2, x.1 - 1).2 := by
  rw [show conjWord (List.replicate (k + 1) Digit.two) = List.replicate k Digit.three from
    conjWord_replicate_two k, standardField_threes]
  unfold sheetChainPotential
  rw [show conjWord (List.replicate (k + 1) Digit.two) = List.replicate k Digit.three from
    conjWord_replicate_two k, parentsAt_three_odd, oddBirthPrefix_replicate_two, twos_frame_eps,
    twos_frame_eps]
  unfold earlierChainPrice
  rw [earlierChainShift_zero_one_neg]
  unfold Fraction.transverseGrade
  simp only [Int.neg_mul, one_mul]
  ring

end FLatticePaper.Induction
