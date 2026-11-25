import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.TwosPieces

/-! # The W1 forcing at the twos children (task 72, W1 base at `2^(k+1)`, lead's (2))

The twos child of `2^(k+1)` is `(2k+3)/(2k+5)`, with `a = 2k+4` (`twos_child_num_den`). Its strict interior is the closed
parallelogram below, in the atoms `u = a x + y` and `t = (a−1) x − (a+1) y`. -/

namespace FLatticePaper.W1Twos

open FLatticePaper FLatticePaper.W1

/-- The strict interior of the twos child `(a−1)/(a+1)`: the band `a ≤ a x + y ≤ a² + 2a − 2`, with the parity-resolved range of
`t = (a−1) x − (a+1) y`. -/
theorem strictInterior_twos_iff {n d a : ℤ} (hn : n = a - 1) (hd : d = a + 1) (x y : ℤ) :
    StrictInterior n d (x, y) ↔
      (a ≤ a * x + y ∧ a * x + y ≤ a * a + 2 * a - 2) ∧
      ((x + y) % 2 = 0 → 2 * a - 1 - (2 * (a * a) + 4 * a - 2) ≤ (a - 1) * x - (a + 1) * y ∧
        (a - 1) * x - (a + 1) * y ≤ 1) ∧
      ((x + y) % 2 ≠ 0 → a + 2 - (2 * (a * a) + 4 * a - 2) ≤ (a - 1) * x - (a + 1) * y ∧
        (a - 1) * x - (a + 1) * y ≤ a - 2) := by
  have es : (d + n) * x + (d - n) * y = 2 * (a * x + y) := by subst hn hd; ring
  have et : n * x - d * y = (a - 1) * x - (a + 1) * y := by subst hn hd; ring
  have eT : d ^ 2 + 2 * d * n - n ^ 2 = 2 * (a * a) + 4 * a - 2 := by subst hn hd; ring
  unfold StrictInterior w1b w1T w1t w1a w1s w1h w1c
  dsimp only
  rw [es, et, eT]
  split_ifs with he
  · have he' : (x + y) % 2 = 0 := he
    omega
  · have he' : ¬ (x + y) % 2 = 0 := he
    omega

end FLatticePaper.W1Twos
