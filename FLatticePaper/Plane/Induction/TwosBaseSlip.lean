import FLatticePaper.Plane.Induction.BaseFields
import FLatticePaper.Plane.Induction.TwosSlipSaddle

/-! Task 118, base slip at `2^(k+1)`: the named base input `BaseSlip` (`F1_unitSlip`, `F1_noSlipSaddle`, `slipRange`).

The slip `slip 1 z = F z − F (z + σ)` on the closed polygon is `twosSlip k z`, which takes the values `0, 1, 2` by
`twos_slip_value`; the unit slip and the no-even-saddle fields are `twos_slipUnit` and `twos_noSlipSaddle`. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- **The slip range at `2^(k+1)`:** the slip on the closed polygon is in `[0, 2]`. -/
theorem twos_slipRange (k : ℕ) :
    ∀ z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon,
      0 ≤ (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) 1 z ∧
        (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) 1 z ≤ 2 := by
  intro z hz
  have hk := twos_E_key k z hz
  have hv := twos_slip_value k hk
  have e : (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) 1 z =
      twosSlip k (z.1, z.2) := by
    unfold ChildFrame.slip
    rw [one_smul]
    rfl
  rw [e]
  rcases hv with ⟨h1, -⟩ | ⟨h1, -, -⟩ | ⟨h1, -⟩ <;> omega

/-- **The base slip of `2^(k+1)`:** the three slip fields. -/
theorem twos_baseSlip (k : ℕ) : BaseSlip (List.replicate (k + 1) Digit.two) where
  F1_unitSlip := twos_slipUnit k
  F1_noSlipSaddle := twos_noSlipSaddle k
  slipRange := twos_slipRange k

end FLatticePaper.Induction
