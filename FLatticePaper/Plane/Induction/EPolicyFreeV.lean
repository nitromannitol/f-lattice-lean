import FLatticePaper.Plane.Induction.EPolicyFields
import FLatticePaper.Plane.Induction.W1CollarFrame

/-!
# The free V sites of the reciprocal frame (task 118, W1 base)

For `d = 2k+3` the free V sites of `reciprocalFrame k` (the left arc of the closed rectangle, `freeVn 1 d`) are the origin,
the V line `x + y = 1` with `1 ≤ y < d`, and the corner `(2-d, d)`. With `t = x - d y`, `s = (d+1) x + (d-1) y`, `T = d² + 2d - 1`
the identity `(x+y) T = (d+1) s - 2 t` bounds `x + y` to `{0, 1, 2}` and each value is then decided by the closed rectangle.
-/

namespace FLatticePaper.EPolicy

open FLatticePaper FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.Induction

theorem sum_bounds_of_freeV {d x y : ℤ} (hd : 3 ≤ d)
    (hsL : 3 - d ≤ (d + 1) * x + (d - 1) * y) (hsH : (d + 1) * x + (d - 1) * y ≤ d - 1)
    (htL : 1 - (d * d + 2 * d - 1) ≤ x - d * y) (htH : x - d * y ≤ d) :
    0 ≤ x + y ∧ x + y ≤ 2 := by
  have key : (x + y) * (d * d + 2 * d - 1) = (d + 1) * ((d + 1) * x + (d - 1) * y) - 2 * (x - d * y) := by
    ring
  have hT : 0 < d * d + 2 * d - 1 := by nlinarith
  constructor
  · by_contra hc
    have h1 : x + y ≤ -1 := by omega
    nlinarith [mul_le_mul_of_nonneg_right h1 hT.le, mul_le_mul_of_nonneg_left hsL (by linarith : (0 : ℤ) ≤ d + 1)]
  · by_contra hc
    have h1 : 3 ≤ x + y := by omega
    nlinarith [mul_le_mul_of_nonneg_right h1 hT.le, mul_le_mul_of_nonneg_left hsH (by linarith : (0 : ℤ) ≤ d + 1)]

/-- The free V sites of the one-row frame with denominator `d` (the left arc `freeVn 1 d`). -/
theorem freeV_one {d x y : ℤ} (hd : 3 ≤ d) (_hdodd : d % 2 = 1) (hF : freeVn 1 d (x, y)) :
    (x, y) = (0, 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x, y) = (2 - d, d) := by
  obtain ⟨hC, hNot, hV⟩ := hF
  unfold vSp w1s at hV
  simp only at hV
  obtain ⟨hVp, hVr⟩ := hV
  have hsL' : 3 - d ≤ (d + 1) * x + (d - 1) * y := by
    rcases hVr with h | h <;> linarith [h.1, h.2]
  have hsH : (d + 1) * x + (d - 1) * y ≤ d - 1 := by
    rcases hVr with h | h <;> linarith [h.1, h.2]
  have hC0 := hC
  unfold closedRect at hC0
  unfold w1t w1s w1T at hC0
  have htL : 1 - (d * d + 2 * d - 1) ≤ x - d * y := by
    by_cases hev : EvenSite (x, y)
    · rw [if_pos hev] at hC0
      simp only at hC0
      nlinarith [hC0.1]
    · rw [if_neg hev] at hC0
      simp only at hC0
      nlinarith [hC0.1]
  have htH : x - d * y ≤ d := by
    by_cases hev : EvenSite (x, y)
    · rw [if_pos hev] at hC0
      simp only at hC0
      nlinarith [hC0.2.1]
    · rw [if_neg hev] at hC0
      simp only at hC0
      nlinarith [hC0.2.1]
  obtain ⟨hu0, hu2⟩ := sum_bounds_of_freeV hd hsL' hsH htL htH
  have hcases : x + y = 0 ∨ x + y = 1 ∨ x + y = 2 := by omega
  rcases hcases with hu | hu | hu
  · -- the origin: x + y = 0 is even, so s ≥ 0 and y ≥ 0 force x = y = 0
    have hev : EvenSite (x, y) := by
      unfold EvenSite
      show (x + y) % 2 = 0
      omega
    rw [if_pos hev] at hC0
    simp only at hC0
    obtain ⟨c1, c2, c3, c4⟩ := hC0
    have hT : 0 < d * d + 2 * d - 1 := by nlinarith
    have hy0 : 0 ≤ y := by
      by_contra hc
      have hy1 : y ≤ -1 := by omega
      have keyy : y * (d * d + 2 * d - 1) = ((d + 1) * x + (d - 1) * y) - (d + 1) * (x - d * y) := by ring
      nlinarith [mul_le_mul_of_nonneg_right hy1 hT.le, mul_le_mul_of_nonneg_left c2 (by linarith : (0 : ℤ) ≤ d + 1)]
    have hyx : y = -x := by omega
    subst hyx
    have hx0 : x = 0 := le_antisymm (by nlinarith) (by nlinarith)
    subst hx0
    left
    simp
  · -- the V line: x + y = 1 is odd
    have hodd : ¬ EvenSite (x, y) := by
      unfold EvenSite
      show ¬ (x + y) % 2 = 0
      omega
    have hy : y = 1 - x := by omega
    subst hy
    have hx2 : x ≤ 0 := by nlinarith
    have hx1 : 2 - d ≤ x := by nlinarith
    right
    left
    exact ⟨by ring, by linarith, by linarith⟩
  · -- x + y = 2 is even: the exit condition at (x-1, y) forces s ≤ 2, and the corner
    have hev : EvenSite (x, y) := by
      unfold EvenSite
      show (x + y) % 2 = 0
      omega
    rw [if_pos hev] at hC0
    simp only at hC0
    obtain ⟨c1, c2, c3, c4⟩ := hC0
    have hyy : y = 2 - x := by omega
    have hs4 : (d + 1) * x + (d - 1) * y < 4 := by
      by_contra h4
      simp only [not_lt] at h4
      apply hNot
      show closedRect 1 d (x - 1, y)
      have hodd' : ¬ EvenSite (x - 1, y) := by
        unfold EvenSite
        show ¬ (x - 1 + y) % 2 = 0
        omega
      unfold closedRect
      rw [if_neg hodd']
      unfold w1t w1s w1T
      simp only
      refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
    have hsev : ((d + 1) * x + (d - 1) * y) % 2 = 0 := hVp
    have c3' : 0 ≤ (d + 1) * x + (d - 1) * y := c3
    generalize hs : (d + 1) * x + (d - 1) * y = s at hsev hs4 c3'
    have hs02 : s = 0 ∨ s = 2 := by omega
    have hxs : s = 2 * x + 2 * d - 2 := by
      rw [← hs, hyy]
      ring
    rcases hs02 with h0 | h2
    · exfalso
      have hx : x = 1 - d := by linarith
      rw [hyy, hx] at c1
      nlinarith
    · have hx : x = 2 - d := by linarith
      have hy : y = d := by
        rw [hyy, hx]
        ring
      right
      right
      rw [hx, hy]

/-- The free V sites of the reciprocal frame at `3^k`: the origin, the V line `x + y = 1` (`1 ≤ y < 2k+3`), and the corner
`(2-d, d)` with `d = 2k+3`. -/
theorem freeV_reciprocal (k : ℕ) {z : ℤ × ℤ} (hz : z ∈ (reciprocalFrame k).freeV) :
    z = (0, 0) ∨ (z.1 + z.2 = 1 ∧ 1 ≤ z.2 ∧ z.2 < 2 * (k : ℤ) + 3) ∨
      z = (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) := by
  have hF := (FLatticePaper.W1CollarFrame.freeV_iff (reciprocalFrame k) z).1 hz
  rw [reciprocal_child_num, reciprocal_child_den] at hF
  obtain ⟨x, y⟩ := z
  exact freeV_one (by omega) (by omega) hF

end FLatticePaper.EPolicy
