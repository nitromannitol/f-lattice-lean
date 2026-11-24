import FLatticePaper.Plane.Induction.TwosSlipMinusMono

/-! Task 72 / twos base: the chain potential of sign `−1`, `Φ₋₁ = D₋₁ + P(· − σ)`, in the translate coordinates of `(1,1)`.

Since `σ = (1,1) − U`, the slip of sign `−1` is `−D(z − (1,1))` (`twos_slip_minus_eq`) and the price drops by one under the
kernel (`twosP_U`), so `Φ₋₁(z) = Ψ(z − (1,1)) − 1` with `Ψ = P − D` (`chainM_eq`). The claim `Φ₋₁(i) ≤ Φ₋₁(c)` along the sign
`−1` selected edges is therefore `Ψ(i − (1,1)) ≤ Ψ(c − (1,1))`, a band comparison of the price and the slip. -/

namespace FLatticePaper.TwosEPolicy
open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey

/-- The shifted chain quantity `Ψ = P − D` at the site `(x, y)`. -/
noncomputable def twosPsi (k : ℕ) (x y : ℤ) : ℤ := twosP k (x, y) - FLatticePaper.Induction.twosSlip k (x, y)

/-- **The chain potential of sign `−1` in the translate coordinates:** `Φ₋₁(z) = Ψ(z − (1,1)) − 1`. -/
theorem chainM_eq (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) z =
      twosPsi k (z.1 - 1) (z.2 - 1) - 1 := by
  unfold ChildFrame.chainPotential
  rw [twos_slip_minus_eq]
  have e : z + (-1 : ℤ) • (frameAt (List.replicate (k + 1) Digit.two)).shortShift =
      (z.1 - 1 + (2 * (k : ℤ) + 5), z.2 - 1 + (2 * (k : ℤ) + 3)) := by
    rw [neg_one_smul, twos_shortShift_explicit]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_neg]
      ring
    · simp only [Prod.snd_add, Prod.snd_neg]
      ring
  rw [e]
  have hP := twosP_U k (z.1 - 1) (z.2 - 1)
  unfold twosPsi
  unfold twosP at hP ⊢
  linarith

end FLatticePaper.TwosEPolicy
