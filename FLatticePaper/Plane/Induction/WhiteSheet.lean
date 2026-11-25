import FLatticePaper.Graph

/-! # W0 of the white case of Q34: an active sheet at a forced white agrees with the field at both inputs

At a white point `z` of `F` (`laplacian F z = 0`) where a sheet `A` with `F ≤ A` at the inputs is active (`F z = A z`), the deficit
sum `Σ_{i ∈ In z} (A i − F i) = lap A z − lap F z = lap A z ≤ 0` and each term is `≥ 0`. Hence both inputs agree with `F`, and `A` is
white at `z`. This is the elementary part of "each active sheet is white and agrees with `F` at both inputs" (Q34, the deficit sum).
-/

namespace FLatticePaper.WhiteSheet

open FLatticePaper

/-- **Active sheets agree at a white point.** -/
theorem agree_at_white {F A : Field} {z : Site} (hbinA : laplacian A z = -1 ∨ laplacian A z = 0)
    (hzF : laplacian F z = 0) (hz : F z = A z)
    (hle : ∀ i : Site, (i = incomingNeg z ∨ i = incomingPos z) → F i ≤ A i) :
    F (incomingNeg z) = A (incomingNeg z) ∧ F (incomingPos z) = A (incomingPos z) ∧ laplacian A z = 0 := by
  have h1 := hle _ (Or.inl rfl)
  have h2 := hle _ (Or.inr rfl)
  unfold laplacian at hzF hbinA ⊢
  omega

end FLatticePaper.WhiteSheet
