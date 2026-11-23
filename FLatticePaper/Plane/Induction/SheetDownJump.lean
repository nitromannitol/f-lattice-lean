import FLatticePaper.Plane.Induction.TieCentre
import FLatticePaper.Plane.Induction.Q3Strong

/-! Task 72 (hResP, step 1: the positive-chart jump identity).

The sheet `A = sheetA Fp` with `Fp = quarterTurnField G` (`G` the conjugate's standard field) satisfies the paragraph-5 identity
at the shifted site `z − uq` (`uq = εU_q`):

`A (z − uq) − A z = cutPrice − price G (Z (z − l_v))`, `Z x = (−x₂, x₁ − 1)`.

This is `paragraph5_field_identity_of_strong` at `x = z − l_v`, with `(z − uq) − l_v = x − εU_q`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **The paragraph-5 identity for the sheet A at `z − uq`.** -/
theorem sheetA_sub_uq_eq_cutPrice {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (z : Site) :
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (z - (frameAt word).uq) -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z =
      (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn (z - (frameAt word).sheetShift)) := by
  have key := paragraph5_field_identity_of_strong h hSE (z - (frameAt word).sheetShift)
  have e1 : z - (frameAt word).uq - (frameAt word).sheetShift =
      z - (frameAt word).sheetShift + (-(frameAt word).eps * (frameAt word).parents.even.den,
        -(frameAt word).eps * (frameAt word).parents.even.num) := by
    unfold ChildFrame.uq
    ext <;> simp <;> ring
  unfold ChildFrame.sheetA
  rw [e1, key]
  rfl

end FLatticePaper.Induction
