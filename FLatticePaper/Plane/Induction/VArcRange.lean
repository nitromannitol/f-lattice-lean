import FLatticePaper.Plane.Induction.BaseInputsProof

/-! Task 56 (Q2, the V-arc range of `VArcInputs`), named input and target.

Q2 (fixes/Q2.md) proves `leftRange` of `VArcInputs`, that `D_+ = F − F(· + σ) ∈ {0,1,2}` on the V arcs of `E`, from the
inequality (2) of the sheet comparison (fixes/Q4-strips.md) and the sewn data of the current word. The inequality (2) is
proved by the strictly earlier strong estimates, which w2 discharges. It enters here as the named input `ParentStepSign`,
stated exactly as the fix states it:

  with `t_p(x) = N x₁ − D x₂` (the odd parent `N/D`), the one-step difference `d_f(k, χ) = f_χ(k) − f_χ(k − 1)` of the parent
  field `f` satisfies `d_f ≥ 0` for `k < N` and `d_f ≤ 0` for `k ≥ N`.

Here `f_χ(k)` is the value of the parent field `f` at a site of parity `χ` with transverse coordinate `k`; the fix states that
it depends only on `(k, χ)`, and the representation below uses representatives `x` (transverse coordinate `k`) and `x'`
(transverse coordinate `k − 1`) of the same parity. The field `f` is `Fp` in `Q4-strips.md` (its `f = h₀ + g(r − s_p)`), and
`Fp` is an argument here so that the instance is the quarter-turned earlier field of the current word. -/

namespace FLatticePaper.Induction

open Farey

/-- Q4-strips inequality (2): the one-step sign of the parent field along the transverse coordinate `t_p = N x₁ − D x₂`. -/
def ParentStepSign (frame : ChildFrame) (Fp : Field) : Prop :=
  ∀ x x' : Site, (x.1 + x.2) % 2 = (x'.1 + x'.2) % 2 →
    frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 =
      frame.parents.odd.num * x'.1 - frame.parents.odd.den * x'.2 + 1 →
    (frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 < frame.parents.odd.num → Fp x' ≤ Fp x) ∧
      (frame.parents.odd.num ≤ frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 → Fp x ≤ Fp x')

end FLatticePaper.Induction
