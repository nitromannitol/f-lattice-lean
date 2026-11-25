import FLatticePaper.Plane.Induction.ArcPsi
import FLatticePaper.Plane.Induction.PsiCalibration

/-! Task 72 / Q29, item 3 of the raw-cut audit: the zero point of the H arc, per phase.

In phase W0 the zero of `Ψ` on the H arc is `H_0 = (1, 0)` (`PsiCalibration.sheetPsi_H0_W0`). In phase W1 the zero is `refl(H_0)`
with `refl = reflH`, and `reflH (1, 0) = H_last = (den, num − 1)` (`PsiCalibration.sheetPsi_hLast_W1`). These are the two `hΨ0`
hypotheses of `ArcPsi.bottom_W0` and `bottom_W1`, with `h0 = (1, 0)` in phase W0 and `h0 = (1, 0)`, `refl h0 = H_last` in phase W1. -/

namespace FLatticePaper.BottomMatch

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.ArcPsi

/-- The reflection sends `H_0 = (1, 0)` to `H_last = (den, num − 1)`. -/
theorem reflH_one_zero (word : Word) :
    reflH word (1, 0) = ((frameAt word).child.den, (frameAt word).child.num - 1) := by
  unfold reflH
  ext <;> simp

/-- Phase W0: `Ψ(H_0) = 0`. -/
theorem zero_point_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1) : sheetPsi word (1, 0) = 0 :=
  PsiCalibration.sheetPsi_H0_W0 word h hSE hW0

/-- Phase W1: `Ψ(refl H_0) = Ψ(H_last) = 0`. -/
theorem zero_point_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) : sheetPsi word (reflH word (1, 0)) = 0 := by
  rw [reflH_one_zero]
  exact PsiCalibration.sheetPsi_hLast_W1 word h hSE hW1

end FLatticePaper.BottomMatch
