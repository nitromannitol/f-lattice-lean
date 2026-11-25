import FLatticePaper.Plane.Induction.SheetDownJump
import FLatticePaper.Plane.Induction.SheetOffsets

/-! Task 72 / Q31, the earlier-price form of the jump `ψ(x) = Fp(x + ε U_q) − Fp(x)`.

`sheetA_sub_uq_eq_cutPrice` gives, for every `x`, `Fp(x − uq) − Fp(x) = c₀' − P'(Z x)`, with `uq = ε U_q`, `Fp = FqW word`, `Z = zTurn`,
and `P'`, `c₀'` the price and cut price of the conjugate. Substituting `x + uq` gives `ψ(x) = P'(Z(x + uq)) − c₀'`. -/

namespace FLatticePaper.PsiIdentity

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet

/-- **The jump in the earlier price.** -/
theorem psi_eq_price {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (x : Site) :
    FqW word (x + (frameAt word).uq) - FqW word x =
      (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn (x + (frameAt word).uq))
        - (frameAt (conjWord word)).cutPrice := by
  have e := sheetA_sub_uq_eq_cutPrice h hSE (x + (frameAt word).uq + (frameAt word).sheetShift)
  unfold ChildFrame.sheetA at e
  have e1 : x + (frameAt word).uq + (frameAt word).sheetShift - (frameAt word).uq - (frameAt word).sheetShift = x := by
    abel
  have e2 : x + (frameAt word).uq + (frameAt word).sheetShift - (frameAt word).sheetShift = x + (frameAt word).uq := by
    abel
  rw [e1, e2] at e
  linarith

end FLatticePaper.PsiIdentity
