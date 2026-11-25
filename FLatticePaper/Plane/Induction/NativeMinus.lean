import FLatticePaper.Plane.Induction.NativeQ34

/-! # The native chart at sign `−1` (Q34, the A-edge statement of the sign `−1` permit)

With `z` and `z − σ` in the closed polygon, `F = sheetMin` at both points, `A(z − σ) = A z`, `C(z − σ) = C z + 2` give

  `D₋(z) = F z − F(z − σ) = min(0, Ψ z) − min(0, Ψ z + 2)`,

which is at most `0` and equals `0` when `Ψ z ≥ 0`. So the sign `−1` claim `D₋(u) ≤ D₋(z)` holds at every edge with `Ψ z ≥ 0`
(native chart, both phases), with no monotonicity input. -/

namespace FLatticePaper.NativeMinus

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet FLatticePaper.W1Step

/-- **The native identity at sign `−1`.** -/
theorem slip_native_identity_minus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {z : Site}
    (hz : z ∈ (frameAt word).closedPolygon) (hzs : z - (frameAt word).shortShift ∈ (frameAt word).closedPolygon) :
    (frameAt word).slip (standardField word) (-1) z =
      min 0 (sheetPsi word z) - min 0 (sheetPsi word z + 2) := by
  unfold ChildFrame.slip
  rw [neg_one_smul, ← sub_eq_add_neg, standardField_eq_sheetMin_of_strong h hSE hz,
    standardField_eq_sheetMin_of_strong h hSE hzs]
  unfold ChildFrame.sheetMin sheetPsi
  have hA := sheetA_sub_shortShift h hSE z
  have hC := sheetC_sub_shortShift h hSE z
  simp only [FqW] at *
  rw [hA, hC]
  omega

/-- **The native sign `−1` claim at an edge with `Ψ z ≥ 0`.** -/
theorem native_sign_minus_of_nonneg {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {z u : Site}
    (hz : z ∈ (frameAt word).closedPolygon) (hzs : z - (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hu : u ∈ (frameAt word).closedPolygon) (hus : u - (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hΨ : 0 ≤ sheetPsi word z) :
    (frameAt word).slip (standardField word) (-1) u ≤ (frameAt word).slip (standardField word) (-1) z := by
  rw [slip_native_identity_minus h hSE hu hus, slip_native_identity_minus h hSE hz hzs]
  omega

end FLatticePaper.NativeMinus
