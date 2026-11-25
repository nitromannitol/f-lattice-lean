import FLatticePaper.Plane.Induction.W1Constructor

/-! # The crossing of a unit square on the grade rectangle

For the child `(n, d)` with `n, d` odd, a unit square with lower-left corner `a` has corners `a`, `a + (1,0)`, `a + (0,1)`, `a + (1,1)`.
If some corner is strict (`StrictInterior`), then either every corner is strict, or some corner is closed (`closedRect`) and not strict.
The statement is pure arithmetic in the grades of `a`, once the parity of `w1t a` is tied to the parity of `a` (`parity_w1t`). -/

namespace FLatticePaper.CrossingLattice

open FLatticePaper FLatticePaper.W1

/-- The grade `t` has the parity of the site (`n`, `d` odd). -/
theorem parity_w1t {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (z : Site) :
    w1t n d z % 2 = (z.1 + z.2) % 2 := by
  unfold w1t
  have hn' : n = 2 * (n / 2) + 1 := by omega
  have hd' : d = 2 * (d / 2) + 1 := by omega
  have key : n * z.1 - d * z.2 = (z.1 + z.2) + 2 * ((n / 2) * z.1 - (d / 2) * z.2 - z.2) := by
    linear_combination z.1 * hn' - z.2 * hd'
  rw [key, Int.add_mul_emod_self_left]

/-- The grade `s` is even (`d + n` and `d - n` are even). -/
theorem parity_w1s {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (z : Site) :
    w1s n d z % 2 = 0 := by
  unfold w1s
  have h1 : d + n = 2 * ((d + n) / 2) := by omega
  have h2 : d - n = 2 * ((d - n) / 2) := by omega
  have key : (d + n) * z.1 + (d - n) * z.2 = 2 * (((d + n) / 2) * z.1 + ((d - n) / 2) * z.2) := by
    linear_combination z.1 * h1 + z.2 * h2
  rw [key]
  generalize (((d + n) / 2) * z.1 + ((d - n) / 2) * z.2) = K
  omega

/-- The period `T = d² + 2dn − n²` is even (`n`, `d` odd). -/
theorem parity_w1T {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) : w1T n d % 2 = 0 := by
  have h1 : d + n = 2 * ((d + n) / 2) := by omega
  have key : w1T n d = 2 * (((d + n) / 2) * (d - n) + d * n) := by
    unfold w1T
    linear_combination (d - n) * h1
  rw [key]
  generalize (((d + n) / 2) * (d - n) + d * n) = K
  omega

theorem w1t_right (n d : ℤ) (a : Site) : w1t n d (a.1 + 1, a.2) = w1t n d a + n := by
  unfold w1t; ring

theorem w1s_right (n d : ℤ) (a : Site) : w1s n d (a.1 + 1, a.2) = w1s n d a + (d + n) := by
  unfold w1s; ring

theorem w1t_up (n d : ℤ) (a : Site) : w1t n d (a.1, a.2 + 1) = w1t n d a - d := by
  unfold w1t; ring

theorem w1s_up (n d : ℤ) (a : Site) : w1s n d (a.1, a.2 + 1) = w1s n d a + (d - n) := by
  unfold w1s; ring

theorem w1t_diag (n d : ℤ) (a : Site) : w1t n d (a.1 + 1, a.2 + 1) = w1t n d a + n - d := by
  unfold w1t; ring

theorem w1s_diag (n d : ℤ) (a : Site) : w1s n d (a.1 + 1, a.2 + 1) = w1s n d a + 2 * d := by
  unfold w1s; ring

/-- Strict interior at an even site. -/
theorem sI_even {n d : ℤ} {z : Site} (h : EvenSite z) :
    StrictInterior n d z ↔ (d + n - 2 - w1T n d < w1t n d z ∧ w1t n d z < 2 ∧
      2 * n < w1s n d z ∧ w1s n d z < w1T n d) := by
  unfold StrictInterior w1a w1b w1c w1h
  rw [if_pos h, if_pos h, if_pos h, if_pos h]
  simp

/-- Strict interior at an odd site. -/
theorem sI_odd {n d : ℤ} {z : Site} (h : ¬ EvenSite z) :
    StrictInterior n d z ↔ (d - w1T n d < w1t n d z ∧ w1t n d z < n ∧
      d + n - 2 < w1s n d z ∧ w1s n d z < w1T n d + (2 - d + n)) := by
  unfold StrictInterior w1a w1b w1c w1h
  rw [if_neg h, if_neg h, if_neg h, if_neg h]

/-- Closed rectangle at an even site. -/
theorem cR_even {n d : ℤ} {z : Site} (h : EvenSite z) :
    closedRect n d z ↔ (2 - w1T n d ≤ w1t n d z ∧ w1t n d z ≤ d + n - 2 ∧
      0 ≤ w1s n d z ∧ w1s n d z ≤ w1T n d + 2 * n) := by
  unfold closedRect
  rw [if_pos h]

/-- Closed rectangle at an odd site. -/
theorem cR_odd {n d : ℤ} {z : Site} (h : ¬ EvenSite z) :
    closedRect n d z ↔ (n - w1T n d ≤ w1t n d z ∧ w1t n d z ≤ d ∧
      2 - d + n ≤ w1s n d z ∧ w1s n d z ≤ w1T n d + d + n - 2) := by
  unfold closedRect
  rw [if_neg h]

set_option maxHeartbeats 4000000 in
/-- **The crossing on a unit square.** If one corner is strict, then all four corners are strict, or some corner is closed and not strict. -/
theorem crossing_square {n d : ℤ} (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d) (hTL : 2 * (d + n) < w1T n d)
    (hn : n % 2 = 1) (hd : d % 2 = 1) (a : Site)
    (hS : StrictInterior n d a ∨ StrictInterior n d (a.1 + 1, a.2) ∨
      StrictInterior n d (a.1, a.2 + 1) ∨ StrictInterior n d (a.1 + 1, a.2 + 1)) :
    (StrictInterior n d a ∧ StrictInterior n d (a.1 + 1, a.2) ∧
        StrictInterior n d (a.1, a.2 + 1) ∧ StrictInterior n d (a.1 + 1, a.2 + 1)) ∨
      (closedRect n d a ∧ ¬ StrictInterior n d a) ∨
      (closedRect n d (a.1 + 1, a.2) ∧ ¬ StrictInterior n d (a.1 + 1, a.2)) ∨
      (closedRect n d (a.1, a.2 + 1) ∧ ¬ StrictInterior n d (a.1, a.2 + 1)) ∨
      (closedRect n d (a.1 + 1, a.2 + 1) ∧ ¬ StrictInterior n d (a.1 + 1, a.2 + 1)) := by
  have hpar := parity_w1t (n := n) (d := d) hn hd a
  have hpS := parity_w1s (n := n) (d := d) hn hd a
  have hT := parity_w1T (n := n) (d := d) hn hd
  have hE1 : EvenSite (a.1 + 1, a.2) ↔ ¬ EvenSite a := by
    simp only [EvenSite]; omega
  have hE2 : EvenSite (a.1, a.2 + 1) ↔ ¬ EvenSite a := by
    simp only [EvenSite]; omega
  have hE3 : EvenSite (a.1 + 1, a.2 + 1) ↔ EvenSite a := by
    simp only [EvenSite]; omega
  by_cases e0 : EvenSite a
  · simp only [sI_even, sI_odd, cR_even, cR_odd, hE1, hE2, hE3, e0, not_true_eq_false,
      not_false_eq_true, not_not, w1t_right, w1s_right, w1t_up, w1s_up, w1t_diag, w1s_diag,
      not_and_or, not_lt, not_le] at hS ⊢
    simp only [EvenSite] at e0
    omega
  · simp only [sI_even, sI_odd, cR_even, cR_odd, hE1, hE2, hE3, e0, not_true_eq_false,
      not_false_eq_true, not_not, w1t_right, w1s_right, w1t_up, w1s_up, w1t_diag, w1s_diag,
      not_and_or, not_lt, not_le] at hS ⊢
    simp only [EvenSite] at e0
    omega

end FLatticePaper.CrossingLattice
