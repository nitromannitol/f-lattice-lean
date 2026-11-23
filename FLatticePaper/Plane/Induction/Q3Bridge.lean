import FLatticePaper.Plane.Induction.ParentStepDischarge

/-! Task 59, paragraph 5: the field identity with the paper's shift `ε U_q` (PROVISIONAL reading of Q4-strips.md line 14).

With `U_q = (d_q, n_q)` the even parent's kernel of the frame, `U_p = 2(D, N)`, and `f = quarterTurnField G` (the field of
`sheetA`), the paragraph-5 identity reads
  `f(x − ε U_q) − f(x) = c₀ − P(Z x)`,   `P = conj.price G`, `c₀ = conj.cutPrice`, `Z x = (−x₂, x₁ − 1)`.

Proof: the codebase identity `quarterTurnField_sub_shift` gives it with the shift `δ₀` of the conjugate; the bridge
`−ε U_q = δ₀ + j U_p` (hypothesis `hlat`, an integer `j`) and the `U_p`-periodicity `quarterTurnField_add_mul_up` identify the
two shifts. `hlat` is checked numerically on the words of length ≤ 4 (`scripts/q3_shift_identity.py`: 108 words, the
multiplier `j` ranges over −3..3); its Farey proof is not yet in the codebase. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem paragraph5_field_identity {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hG : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    (j : ℤ)
    (hlat : (-frame.eps * frame.parents.even.den, -frame.eps * frame.parents.even.num) =
      (-conj.eps * (conj.parents.odd.num + conj.parents.odd.den),
          conj.eps * (conj.parents.odd.num - conj.parents.odd.den)) +
        (j * (2 * frame.parents.odd.den), j * (2 * frame.parents.odd.num)))
    (x : Site) :
    quarterTurnField G (x + (-frame.eps * frame.parents.even.den, -frame.eps * frame.parents.even.num)) -
        quarterTurnField G x =
      conj.cutPrice - conj.price G (-x.2, x.1 - 1) := by
  have h1 := quarterTurnField_sub_shift (conj := conj) (G := G) x
  have e : x + (-frame.eps * frame.parents.even.den, -frame.eps * frame.parents.even.num) =
      (x + (-conj.eps * (conj.parents.odd.num + conj.parents.odd.den),
          conj.eps * (conj.parents.odd.num - conj.parents.odd.den))) +
        (j * (2 * frame.parents.odd.den), j * (2 * frame.parents.odd.num)) := by
    rw [hlat]
    abel
  have h3 : quarterTurnField G (x + (-frame.eps * frame.parents.even.den, -frame.eps * frame.parents.even.num)) =
      quarterTurnField G (x + (-conj.eps * (conj.parents.odd.num + conj.parents.odd.den),
          conj.eps * (conj.parents.odd.num - conj.parents.odd.den))) := by
    rw [e]
    exact quarterTurnField_add_mul_up (frame := frame) (conj := conj) (G := G) hconj hG j _
  linarith [h1, h3]

end FLatticePaper.Induction
