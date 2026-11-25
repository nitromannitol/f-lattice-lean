import FLatticePaper.Graph
import FLatticePaper.Plane.Induction.QuadraticCap

/-! The binary-centre step of the all-slope cap (ALL_SLOPE_STEP, the recursion `A_k ≥ 2A_(k−1) − 1 − B_(k−2)`).

A binary centre has laplacian `−1` or `0`, so `2F(c) ≤ F(incomingNeg c) + F(incomingPos c) + 1`: the centre is the ceiling of the mean of
its two inputs. At an even input `N` of an odd centre `c` (with `S = incomingNeg c` and `N = incomingPos c`), the eastern input `E` of `N`
bounds `F N` from above (`2F N ≤ F W + F E + 1` with the western input `W`, and `F W ≤ F E` by the same-sheet monotonicity). Hence
`F E ≥ F N ≥ 2F c − 1 − F S`. -/

namespace FLatticePaper.CapRecursion

open FLatticePaper

/-- A binary centre is the ceiling of the mean of its two inputs (one side of it). -/
theorem binary_upper (F : Field) {c : Site} (hl : laplacian F c = -1 ∨ laplacian F c = 0) :
    2 * F c ≤ F (incomingNeg c) + F (incomingPos c) + 1 := by
  unfold laplacian at hl
  omega

/-- **The odd-centre step.** `F E ≥ 2 F c − 1 − F S` for an odd centre `c` with south input `S` and even north input `N`, whose
western input `W` has no greater height than the eastern input `E`. -/
theorem odd_centre_step (F : Field) {c S N W E : Site} (hS : S = incomingNeg c) (hN : N = incomingPos c)
    (hW : W = incomingNeg N) (hE : E = incomingPos N)
    (hlc : laplacian F c = -1 ∨ laplacian F c = 0) (hlN : laplacian F N = -1 ∨ laplacian F N = 0)
    (hmono : F W ≤ F E) :
    2 * F c - 1 - F S ≤ F E := by
  have h1 := binary_upper F hlN
  have h2 := binary_upper F hlc
  rw [← hW, ← hE] at h1
  rw [← hS, ← hN] at h2
  have hNE : F N ≤ F E := by omega
  omega

end FLatticePaper.CapRecursion
