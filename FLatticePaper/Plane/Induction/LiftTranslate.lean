import FLatticePaper.Plane.Induction.PriceReflect

/-! Task 72 / Q31 psi (i): the jump is additive along the parent deck vector.

`psi_tip_shift` gives `ψ(x + V_p) = ψ(x) + 1` for `ψ(x) = Fp(x + uq) − Fp(x)` and `V_p = tipVertex`. By integer induction,
`ψ(x + k V_p) = ψ(x) + k` for every `k ∈ ℤ`. This is the translation step of the lift `ψ(z) = ⌈j/r⌉`: a site of the same
parent grade as a reference point `b` is `b + k V_p` (`ParentGradeKernel.same_grade_vp`), so its jump is `ψ(b) + k`. -/

namespace FLatticePaper.LiftTranslate

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet

/-- **Integer translates along `V_p`:** `ψ(x + k V_p) = ψ(x) + k`. -/
theorem psi_tip_int {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (k : ℤ) (x : Site) :
    FqW word (x + k • TipVertex.tipVertex (frameAt word) + (frameAt word).uq) -
        FqW word (x + k • TipVertex.tipVertex (frameAt word)) =
      FqW word (x + (frameAt word).uq) - FqW word x + k := by
  induction k using Int.induction_on generalizing x with
  | zero => simp
  | succ k ih =>
    have e : x + ((k : ℤ) + 1) • TipVertex.tipVertex (frameAt word) =
        (x + (k : ℤ) • TipVertex.tipVertex (frameAt word)) + TipVertex.tipVertex (frameAt word) := by
      rw [add_smul, one_smul, add_assoc]
    rw [e, PriceReflect.psi_tip_shift h hSE, ih x]
    ring
  | pred k ih =>
    have e2 : x + (-(k : ℤ) - 1) • TipVertex.tipVertex (frameAt word) + TipVertex.tipVertex (frameAt word) =
        x + (-(k : ℤ)) • TipVertex.tipVertex (frameAt word) := by
      rw [sub_smul, one_smul]
      abel
    have hstep := PriceReflect.psi_tip_shift h hSE (x + (-(k : ℤ) - 1) • TipVertex.tipVertex (frameAt word))
    rw [e2] at hstep
    rw [ih x] at hstep
    have hg : FqW word (x + (-(k : ℤ) - 1) • TipVertex.tipVertex (frameAt word) + (frameAt word).uq) -
        FqW word (x + (-(k : ℤ) - 1) • TipVertex.tipVertex (frameAt word)) =
        FqW word (x + (frameAt word).uq) - FqW word x + (-(k : ℤ) - 1) := by
      linarith
    exact hg

end FLatticePaper.LiftTranslate
