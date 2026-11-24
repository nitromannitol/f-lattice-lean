import FLatticePaper.Plane.Induction.TwosBaseSlip

/-! Task 118, the sign `η = −1` of the twos slip at `2^(k+1)`.

Since `σ = (1,1) − U` and the slip is kernel-invariant, the sign `−1` slip is the `+1` slip at the translate `z − (1,1)`,
with the opposite sign: `slip (−1) z = −twosSlip k (z − (1,1))` (`twos_slip_minus_eq`). Its band on the polygon is the band of
`twos_slip_value` at `z − (1,1)` (`twos_slip_minus_value`). -/

namespace FLatticePaper.Induction
open Farey Construction

/-- **The sign `−1` slip is the `+1` slip at `z − (1,1)`, with the opposite sign.** -/
theorem twos_slip_minus_eq (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) (-1) z =
      -twosSlip k (z.1 - 1, z.2 - 1) := by
  rw [twos_slip_neg k z]
  congr 1
  have h := twosSlip_add_U k (z.1 - 1, z.2 - 1)
  rw [← h]
  congr 1
  rw [neg_one_smul, twos_shortShift_explicit]
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.fst_neg]
    ring
  · simp only [Prod.snd_add, Prod.snd_neg]
    ring

/-- **The band of the sign `−1` slip on the polygon:** the `+1` band at `z − (1,1)`, negated. -/
theorem twos_slip_minus_value (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) (z1 - 1) (z2 - 1)) :
    (-twosSlip k (z1 - 1, z2 - 1) = 0 ∧ TwosSlipZ0 (2 * (k : ℤ) + 4) (z1 - 1) (z2 - 1)) ∨
      (-twosSlip k (z1 - 1, z2 - 1) = -1 ∧ ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) (z1 - 1) (z2 - 1) ∧
        ¬ TwosSlipZ2 (2 * (k : ℤ) + 4) (z1 - 1) (z2 - 1)) ∨
      (-twosSlip k (z1 - 1, z2 - 1) = -2 ∧ TwosSlipZ2 (2 * (k : ℤ) + 4) (z1 - 1) (z2 - 1)) := by
  rcases twos_slip_value k hk with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by omega, h2⟩
  · exact Or.inr (Or.inl ⟨by omega, h2, h3⟩)
  · exact Or.inr (Or.inr ⟨by omega, h2⟩)

end FLatticePaper.Induction
