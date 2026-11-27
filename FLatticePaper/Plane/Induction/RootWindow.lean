import FLatticePaper.Plane.Induction.W1Constructor

/-! # The child window of a bottom centre

For a strict interior centre `c` of the child `(n, d)` (both odd, `3 ≤ n < d`) with a free H point `v` within one pixel (the
bottom witness), the child grades of `c` lie in the window: at an even centre `2 − L ≤ t ≤ 0` and `2n < s < T`; at an odd centre
`−d ≤ t ≤ n − 2` and `L − 2 < s < T + 2 − d + n`, where `L = d + n`, `t = n x − d y`, `s = L x + (d − n) y`, `T = w1T n d`.

The upper bounds on `t` and the bounds on `s` come from `StrictInterior`; the lower bounds on `t` come from the H spectrum of `v`
and `|v − c| ≤ 1`, by a case split on the two offsets. -/

namespace FLatticePaper.RootWindow

open FLatticePaper FLatticePaper.W1

/-- The parity of `t` is the parity of `x + y` when `n` and `d` are odd. -/
theorem par_t (n d : ℤ) (hn : n % 2 = 1) (hd : d % 2 = 1) (c : Site) :
    w1t n d c % 2 = (c.1 + c.2) % 2 := by
  obtain ⟨a, ha⟩ : ∃ a, n = 2 * a + 1 := ⟨n / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, d = 2 * b + 1 := ⟨d / 2, by omega⟩
  subst ha hb
  have e : w1t (2 * a + 1) (2 * b + 1) c = (c.1 + c.2) + 2 * (a * c.1 - b * c.2 - c.2) := by
    unfold w1t; ring
  rw [e, Int.add_mul_emod_self_left]

/-- The lower bounds on `t` at the centre, from one pixel of a free H point. -/
theorem lower_t (n d : ℤ) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn3 : 3 ≤ n) (hnd : n < d) (c v : Site)
    (hadj1 : |v.1 - c.1| ≤ 1) (hadj2 : |v.2 - c.2| ≤ 1)
    (hsp : (w1t n d v % 2 = 0 ∧ 2 ≤ w1t n d v) ∨ (w1t n d v % 2 = 1 ∧ n ≤ w1t n d v)) :
    ((c.1 + c.2) % 2 = 0 → 2 - (d + n) ≤ w1t n d c) ∧
      ((c.1 + c.2) % 2 = 1 → -d ≤ w1t n d c) := by
  have hk : w1t n d c = w1t n d v + n * (c.1 - v.1) - d * (c.2 - v.2) := by unfold w1t; ring
  have hp1 := par_t n d hn hd c
  have hp2 := par_t n d hn hd v
  obtain ⟨l1, u1⟩ := abs_le.mp hadj1
  obtain ⟨l2, u2⟩ := abs_le.mp hadj2
  have h1 : c.1 - v.1 = -1 ∨ c.1 - v.1 = 0 ∨ c.1 - v.1 = 1 := by omega
  have h2 : c.2 - v.2 = -1 ∨ c.2 - v.2 = 0 ∨ c.2 - v.2 = 1 := by omega
  constructor
  · intro hc
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> rw [h1, h2] at hk <;> omega
  · intro hc
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> rw [h1, h2] at hk <;> omega

/-- **The child window of a bottom centre.** -/
theorem bottom_window (n d : ℤ) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn3 : 3 ≤ n) (hnd : n < d) (c v : Site)
    (hS : StrictInterior n d c)
    (hadj1 : |v.1 - c.1| ≤ 1) (hadj2 : |v.2 - c.2| ≤ 1)
    (hsp : (w1t n d v % 2 = 0 ∧ 2 ≤ w1t n d v) ∨ (w1t n d v % 2 = 1 ∧ n ≤ w1t n d v)) :
    ((c.1 + c.2) % 2 = 0 → 2 - (d + n) ≤ w1t n d c ∧ w1t n d c ≤ 0 ∧ 2 * n < w1s n d c ∧ w1s n d c < w1T n d) ∧
      ((c.1 + c.2) % 2 = 1 → -d ≤ w1t n d c ∧ w1t n d c ≤ n - 2 ∧
        d + n - 2 < w1s n d c ∧ w1s n d c < w1T n d + 2 - d + n) := by
  obtain ⟨-, ht, hs1, hs2⟩ := hS
  have hp := par_t n d hn hd c
  have hlow := lower_t n d hn hd hn3 hnd c v hadj1 hadj2 hsp
  constructor
  · intro he
    have hE : EvenSite c := he
    simp only [w1a, w1h, w1c, if_pos hE] at ht hs1 hs2
    have hl := hlow.1 he
    refine ⟨hl, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
  · intro ho
    have hO : ¬ EvenSite c := by
      intro h
      unfold EvenSite at h
      omega
    simp only [w1a, w1h, w1c, if_neg hO] at ht hs1 hs2
    have hl := hlow.2 ho
    refine ⟨hl, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega

end FLatticePaper.RootWindow
