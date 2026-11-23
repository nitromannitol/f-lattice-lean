import FLatticePaper.Plane.Induction.NoBlackPair

/-! Task 72 (fixer's queue, Q16, the algebraic core of the retention at one input of a tied black minimum).

`M = min(A, C)` and `Ψ = C − A`. At a black centre `c` of `M` (`laplacian M c = −1`) with `M c = A c` and an input `i` with
`M i = A i`: if `A` is white at `c` (`laplacian A c = 0`), the other input `j` has `A j − M j = 1`, hence `Ψ j = −1` (`C j = A j − 1`).
This is the pure identity `ΔA − ΔM = 1` on the star; the policy consequences (retention, monotonicity) are not here. -/

namespace FLatticePaper

open Farey

/-- **The other input of a tied black minimum.** -/
theorem other_input_of_tie (A C : Field) {c i j : Site}
    (hi : i = FLatticePaper.incomingNeg c ∨ i = FLatticePaper.incomingPos c)
    (hj : j = FLatticePaper.incomingNeg c ∨ j = FLatticePaper.incomingPos c) (hij : i ≠ j)
    (hM : laplacian (fun z => min (A z) (C z)) c = -1)
    (hA : laplacian A c = 0)
    (hMc : min (A c) (C c) = A c) (hMi : min (A i) (C i) = A i) :
    C j = A j - 1 := by
  unfold laplacian at hM hA
  simp only at hM hA
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact absurd rfl hij
  · omega
  · omega
  · exact absurd rfl hij

end FLatticePaper
