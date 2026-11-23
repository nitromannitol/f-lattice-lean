import FLatticePaper.Plane.Induction.W1Exit

/-! Task 58, part 2: the one-pixel collar implies the box (named (1) of task 57).

A strict site `z = (x, y)` of the child `n/d` (`n`, `d` odd) that lies within Chebyshev distance one of a boundary vertex `h`
of the H arc has `t(z) ≥ 2 − L` (even) and `t(z) ≥ −d` (odd); the upper bounds `t < 2` (even), `t < n` (odd) are strictness.
A site within one pixel of a V-arc vertex has `s(z) ≤ 2L` (even) and `s(z) ≤ 3d + n − 2` (odd); the lower bounds of `s` and the
lower bounds of `t` on the V side (`t > b − T`) are strictness. The arithmetic below uses only the arc spectra at the vertex:
H vertices have `t ∈ [2, L−2]` (even) and `t ∈ [n, d]` (odd); V vertices have `s ∈ [0, 2n]` (even) and `s ∈ [2 − d + n, L − 2]`
(odd). -/

namespace FLatticePaper.W1CollarBox

/-- An even integer below `2` is at most `0`. -/
theorem le_zero_of_lt_two_even (t : ℤ) (h : t < 2) (he : t % 2 = 0) : t ≤ 0 := by
  omega

/-- The bottom H collar, even site: `t(z) ≥ 2 − L`. The neighbour `h = z + (p, q)` has `t(h) ≥ 2` when even and `t(h) ≥ n`
when odd (the H spectrum). -/
theorem H_t_lower_even (n d x y p q th : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hp1 : -1 ≤ p) (hp2 : p ≤ 1)
    (hq1 : -1 ≤ q) (hq2 : q ≤ 1) (hz : (x + y) % 2 = 0) (hth : th = n * (x + p) - d * (y + q))
    (hve : (x + p + (y + q)) % 2 = 0 → 2 ≤ th) (hvo : (x + p + (y + q)) % 2 = 1 → n ≤ th) :
    2 - (d + n) ≤ n * x - d * y := by
  have key : th = (n * x - d * y) + n * p - d * q := by rw [hth]; ring
  clear hth
  generalize hT : n * x - d * y = tz at key ⊢
  interval_cases p <;> interval_cases q <;> omega

/-- The bottom H collar, odd site: `t(z) ≥ −d`. -/
theorem H_t_lower_odd (n d x y p q th : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hp1 : -1 ≤ p) (hp2 : p ≤ 1)
    (hq1 : -1 ≤ q) (hq2 : q ≤ 1) (hz : (x + y) % 2 = 1) (hth : th = n * (x + p) - d * (y + q))
    (hve : (x + p + (y + q)) % 2 = 0 → 2 ≤ th) (hvo : (x + p + (y + q)) % 2 = 1 → n ≤ th) :
    -d ≤ n * x - d * y := by
  have key : th = (n * x - d * y) + n * p - d * q := by rw [hth]; ring
  clear hth
  generalize hT : n * x - d * y = tz at key ⊢
  interval_cases p <;> interval_cases q <;> omega

/-- The left V collar, even site: `s(z) ≤ 2L`. The neighbour `v = z + (p, q)` has `s(v) ≤ 2n` when even and `s(v) ≤ L − 2`
when odd (the V spectrum). -/
theorem V_s_upper_even (n d x y p q sv : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hp1 : -1 ≤ p) (hp2 : p ≤ 1)
    (hq1 : -1 ≤ q) (hq2 : q ≤ 1) (hz : (x + y) % 2 = 0) (hsv : sv = (d + n) * (x + p) + (d - n) * (y + q))
    (hve : (x + p + (y + q)) % 2 = 0 → sv ≤ 2 * n) (hvo : (x + p + (y + q)) % 2 = 1 → sv ≤ d + n - 2) :
    (d + n) * x + (d - n) * y ≤ 2 * (d + n) := by
  have key : sv = ((d + n) * x + (d - n) * y) + (d + n) * p + (d - n) * q := by rw [hsv]; ring
  clear hsv
  generalize hS : (d + n) * x + (d - n) * y = sz at key ⊢
  interval_cases p <;> interval_cases q <;> omega

/-- The left V collar, odd site: `s(z) ≤ 3d + n − 2`. -/
theorem V_s_upper_odd (n d x y p q sv : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hp1 : -1 ≤ p) (hp2 : p ≤ 1)
    (hq1 : -1 ≤ q) (hq2 : q ≤ 1) (hz : (x + y) % 2 = 1) (hsv : sv = (d + n) * (x + p) + (d - n) * (y + q))
    (hve : (x + p + (y + q)) % 2 = 0 → sv ≤ 2 * n) (hvo : (x + p + (y + q)) % 2 = 1 → sv ≤ d + n - 2) :
    (d + n) * x + (d - n) * y ≤ 3 * d + n - 2 := by
  have key : sv = ((d + n) * x + (d - n) * y) + (d + n) * p + (d - n) * q := by rw [hsv]; ring
  clear hsv
  generalize hS : (d + n) * x + (d - n) * y = sz at key ⊢
  interval_cases p <;> interval_cases q <;> omega

/-- The box of the bottom collar (even), from strictness (`t < 2`) and the H-collar lower bound. -/
theorem bottom_box_even (n d x y p q th : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (hp1 : -1 ≤ p) (hp2 : p ≤ 1) (hq1 : -1 ≤ q) (hq2 : q ≤ 1) (hz : (x + y) % 2 = 0)
    (hth : th = n * (x + p) - d * (y + q))
    (hve : (x + p + (y + q)) % 2 = 0 → 2 ≤ th) (hvo : (x + p + (y + q)) % 2 = 1 → n ≤ th)
    (hstrict : n * x - d * y < 2) :
    2 - (d + n) ≤ n * x - d * y ∧ n * x - d * y ≤ 0 := by
  have h1 := H_t_lower_even n d x y p q th hn hnd hp1 hp2 hq1 hq2 hz hth hve hvo
  have hpar := FLatticePaper.W1Exit.parity_t n d x y hno hdo
  rw [hz] at hpar
  refine ⟨h1, ?_⟩
  generalize n * x - d * y = tz at hpar hstrict ⊢
  omega

/-- The bottom box (odd site): `−d ≤ t ≤ n − 2`, from the H-collar lower bound and strictness (`t < n`). -/
theorem bottom_box_odd (n d x y p q th : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (hp1 : -1 ≤ p) (hp2 : p ≤ 1) (hq1 : -1 ≤ q) (hq2 : q ≤ 1) (hz : (x + y) % 2 = 1)
    (hth : th = n * (x + p) - d * (y + q))
    (hve : (x + p + (y + q)) % 2 = 0 → 2 ≤ th) (hvo : (x + p + (y + q)) % 2 = 1 → n ≤ th)
    (hstrict : n * x - d * y < n) :
    -d ≤ n * x - d * y ∧ n * x - d * y ≤ n - 2 := by
  have h1 := H_t_lower_odd n d x y p q th hn hnd hp1 hp2 hq1 hq2 hz hth hve hvo
  have hpar := FLatticePaper.W1Exit.parity_t n d x y hno hdo
  rw [hz] at hpar
  refine ⟨h1, ?_⟩
  generalize n * x - d * y = tz at hpar hstrict ⊢
  omega

/-- The left box (even site): `L − T ≤ t ≤ 0` and `2n < s ≤ 2L`, from strictness (`t > b − T`, `t < 2`, `s > h`) and the
V-collar upper bound. -/
theorem left_box_even (n d x y p q sv : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (hp1 : -1 ≤ p) (hp2 : p ≤ 1) (hq1 : -1 ≤ q) (hq2 : q ≤ 1) (hz : (x + y) % 2 = 0)
    (hsv : sv = (d + n) * (x + p) + (d - n) * (y + q))
    (hve : (x + p + (y + q)) % 2 = 0 → sv ≤ 2 * n) (hvo : (x + p + (y + q)) % 2 = 1 → sv ≤ d + n - 2)
    (htlo : (d + n - 2) - (d ^ 2 + 2 * d * n - n ^ 2) < n * x - d * y) (hthi : n * x - d * y < 2)
    (hslo : 2 * n < (d + n) * x + (d - n) * y) :
    (d + n) - (d ^ 2 + 2 * d * n - n ^ 2) ≤ n * x - d * y ∧ n * x - d * y ≤ 0 ∧
      2 * n < (d + n) * x + (d - n) * y ∧ (d + n) * x + (d - n) * y ≤ 2 * (d + n) := by
  have hs := V_s_upper_even n d x y p q sv hn hnd hp1 hp2 hq1 hq2 hz hsv hve hvo
  have hpar := FLatticePaper.W1Exit.parity_t n d x y hno hdo
  rw [hz] at hpar
  refine ⟨?_, ?_, hslo, hs⟩
  · have hT2 := FLatticePaper.W1Exit.parity_T n d hno hdo
    generalize d ^ 2 + 2 * d * n - n ^ 2 = TT at htlo hT2 ⊢
    generalize n * x - d * y = tz at hpar htlo ⊢
    omega
  · exact le_zero_of_lt_two_even _ hthi hpar

/-- The left box (odd site): `d − T < t ≤ n − 2` and `L − 2 < s ≤ 3d + n − 2`. -/
theorem left_box_odd (n d x y p q sv : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (hp1 : -1 ≤ p) (hp2 : p ≤ 1) (hq1 : -1 ≤ q) (hq2 : q ≤ 1) (hz : (x + y) % 2 = 1)
    (hsv : sv = (d + n) * (x + p) + (d - n) * (y + q))
    (hve : (x + p + (y + q)) % 2 = 0 → sv ≤ 2 * n) (hvo : (x + p + (y + q)) % 2 = 1 → sv ≤ d + n - 2)
    (htlo : d - (d ^ 2 + 2 * d * n - n ^ 2) < n * x - d * y) (hthi : n * x - d * y < n)
    (hslo : d + n - 2 < (d + n) * x + (d - n) * y) :
    d - (d ^ 2 + 2 * d * n - n ^ 2) < n * x - d * y ∧ n * x - d * y ≤ n - 2 ∧
      d + n - 2 < (d + n) * x + (d - n) * y ∧ (d + n) * x + (d - n) * y ≤ 3 * d + n - 2 := by
  have hs := V_s_upper_odd n d x y p q sv hn hnd hp1 hp2 hq1 hq2 hz hsv hve hvo
  have hpar := FLatticePaper.W1Exit.parity_t n d x y hno hdo
  rw [hz] at hpar
  refine ⟨htlo, ?_, hslo, hs⟩
  generalize n * x - d * y = tz at hpar hthi ⊢
  omega

end FLatticePaper.W1CollarBox
