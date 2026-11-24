import FLatticePaper.Plane.Induction.TwosPeriods
import FLatticePaper.Plane.Induction.TwosStripFacts
import FLatticePaper.Plane.Induction.W1ZeroStrip

/-! Task 72 / twos base: the zero strip field `zeroStripInterval` of `StrongResidual (2^(k+1))`.

It is not a new computation. The twos packet `twos_packet_standard` (with the twos zero strip `twos_zero_strip` and the harmonic
strip `twos_harm_strip` on the closed polygon) gives the strips of the standard field, and `zeroStripInterval_of_packet` turns the
strips into the zero strip of the quarter-turned field on the strip `1 − D ≤ N x₁ − D x₂ ≤ N + 2D − 1`, with `(N, D)` the parent
pair `(parentN, parentD)` of the word. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- **The zero strip of `2^(k+1)`**: `quarterTurnField (standardField (2^(k+1))) x = 0` on the strip `1 − D ≤ N x₁ − D x₂ ≤ N + 2D − 1`. -/
theorem twos_zeroStripInterval (k : ℕ) : ∀ x : Site,
    1 - parentD (List.replicate (k + 1) Digit.two) ≤
        parentN (List.replicate (k + 1) Digit.two) * x.1 - parentD (List.replicate (k + 1) Digit.two) * x.2 →
      parentN (List.replicate (k + 1) Digit.two) * x.1 - parentD (List.replicate (k + 1) Digit.two) * x.2 ≤
        parentN (List.replicate (k + 1) Digit.two) + 2 * parentD (List.replicate (k + 1) Digit.two) - 1 →
      quarterTurnField (standardField (List.replicate (k + 1) Digit.two)) x = 0 :=
  FLatticePaper.W1ZeroStrip.zeroStripInterval_of_packet _
    (twos_packet_standard k (fun _ hz ht => twos_zero_strip k hz ht) (fun _ hz hs => twos_harm_strip k hz hs))

end FLatticePaper.Induction
