import FLatticePaper.Plane.Induction.W1ZeroStrip
import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.StrongEstimates

/-! # The parent quarter turn equals `h₀` on a σ-window (opposite collar, parent side)

Let `G = standardField (conjWord word)`, with conjugate child `num = D − N`, `den = D + N`. For a parent site `x`, the quarter
turn `Fp(x) = quarterTurnField G x` equals `h₀(x) = harmonicGrid x` once `G (Z x) = 0`, where `Z x = (−x₂, x₁ − 1)`.
The conjugate's `t`-grade at `Z x` is `t(Z x) = (D + N) − σ(x)`, with `σ(x) = (D + N) x₁ + (D − N) x₂`:
* the zero strip `1 − den ≤ t ≤ num + 2 den − 1` (any parity) is the window `1 − 2D ≤ σ(x) ≤ 2D + 2N − 1`;
* the even zero `2 − (den + num) ≤ t ≤ 2 (den + num) − 2` on even `Z x` is the window `N − 3D + 2 ≤ σ(x) ≤ 3D + N − 2`. -/

namespace FLatticePaper.OppParent

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1ZeroStrip FLatticePaper.W1Seeds FLatticePaper.W1Strips

/-- `G (Z x) = 0` gives `Fp(x) = h₀(x)`. -/
theorem quarterTurn_h0_of_zero (F : Field) (x : Site) (hz : F (-x.2, x.1 - 1) = 0) :
    quarterTurnField F x = harmonicGrid x := by
  rw [quarterTurn_eq_sub, hz, zero_sub]
  have hx1 : (-x.2, x.1 - 1).2 + 1 = x.1 := by simp
  have hx2 : -(-x.2, x.1 - 1).1 = x.2 := by simp
  have hq := harmonicGrid_quarter_inv (-x.2, x.1 - 1)
  rw [hx1, hx2] at hq
  rw [← hq]

/-- The zero strip of the conjugate: the odd-`Z x` window `1 − 2D ≤ σ(x) ≤ 2D + 2N − 1`. -/
theorem quarterTurn_h0_of_strip {word : Word} (hSE : StrongEstimates (conjWord word)) (N D : ℤ)
    (hcn : (frameAt (conjWord word)).child.num = D - N) (hcd : (frameAt (conjWord word)).child.den = D + N)
    (x : Site) (h1 : 1 - 2 * D ≤ (D + N) * x.1 + (D - N) * x.2)
    (h2 : (D + N) * x.1 + (D - N) * x.2 ≤ 2 * D + 2 * N - 1) :
    quarterTurnField (standardField (conjWord word)) x = harmonicGrid x := by
  apply quarterTurn_h0_of_zero
  apply hSE.packet.strips.1 (-x.2, x.1 - 1)
  · unfold ChildFrame.tGrade; rw [hcn, hcd]; linarith
  · unfold ChildFrame.tGrade; rw [hcn, hcd]; linarith

/-- The even zero of the conjugate: for even `Z x`, the window `N − 3D + 2 ≤ σ(x) ≤ 3D + N − 2`. -/
theorem quarterTurn_h0_of_even_zero {word : Word} (hSE : StrongEstimates (conjWord word))
    (hpar : SeedFields (conjWord word)) (N D : ℤ)
    (hcn : (frameAt (conjWord word)).child.num = D - N) (hcd : (frameAt (conjWord word)).child.den = D + N)
    (x : Site) (hEv : EvenSite (-x.2, x.1 - 1))
    (h1 : N - 3 * D + 2 ≤ (D + N) * x.1 + (D - N) * x.2)
    (h2 : (D + N) * x.1 + (D - N) * x.2 ≤ 3 * D + N - 2) :
    quarterTurnField (standardField (conjWord word)) x = harmonicGrid x := by
  apply quarterTurn_h0_of_zero
  exact W1Strips.even_zero_full (frameAt (conjWord word)) (hper_of_strong hSE) hSE.packet.strips
    (fun z hz => (hSE.slipRange z hz).1) hpar.even_zero (standardField_iRefl hSE) _ hEv
    (by unfold ChildFrame.tGrade; rw [hcn, hcd]; linarith) (by unfold ChildFrame.tGrade; rw [hcn, hcd]; linarith)

end FLatticePaper.OppParent
