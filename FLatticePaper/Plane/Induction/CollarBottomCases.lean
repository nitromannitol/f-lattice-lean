import FLatticePaper.Plane.Induction.CollarUpper
import FLatticePaper.Plane.Induction.W1Constructor

/-! Task 72 (hcollar, band (a), the case analysis of the bottom witnesses).

* `strict_even_iff`, `strict_odd_iff`: `StrictInterior` in grade form.
* `even_H_l1`: the even H point with `k = 2` is `(2, 0)` (floor law).
* `odd_H_cases`: an odd H point is `(1, 0)`, `(3, 0)`, or has `s > 3 L`. -/

namespace FLatticePaper.CollarBottomCases

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem strict_even_iff (n d : ℤ) (z : Site) (he : EvenSite z) :
    StrictInterior n d z ↔
      (d + n - 2) - (d ^ 2 + 2 * d * n - n ^ 2) < n * z.1 - d * z.2 ∧ n * z.1 - d * z.2 < 2 ∧
        2 * n < (d + n) * z.1 + (d - n) * z.2 ∧ (d + n) * z.1 + (d - n) * z.2 < d ^ 2 + 2 * d * n - n ^ 2 := by
  unfold StrictInterior w1b w1T w1t w1a w1h w1s w1c
  simp only [if_pos he]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem strict_odd_iff (n d : ℤ) (z : Site) (ho : ¬ EvenSite z) :
    StrictInterior n d z ↔
      d - (d ^ 2 + 2 * d * n - n ^ 2) < n * z.1 - d * z.2 ∧ n * z.1 - d * z.2 < n ∧
        d + n - 2 < (d + n) * z.1 + (d - n) * z.2 ∧
          (d + n) * z.1 + (d - n) * z.2 < (d ^ 2 + 2 * d * n - n ^ 2) + (2 - d + n) := by
  unfold StrictInterior w1b w1T w1t w1a w1h w1s w1c
  simp only [if_neg ho]

/-- The even H point with diagonal index `2` is `(2, 0)`: the floor law gives `z.2 = 0`. -/
theorem even_H_l1 (frame : ChildFrame) {v : Site} (hv : EvenSite v) (hsp : frame.hSpectrum (frame.tGrade v))
    (hk : v.1 + v.2 = 2) : v = (2, 0) := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hfl := even_spectrum_floor frame hv hsp
  have hm : (v.1 + v.2) / 2 = 1 := by omega
  rw [hm] at hfl
  have hLpos : 0 < frame.child.den + frame.child.num := by omega
  have h0 : v.2 = 0 := by
    rw [hfl]
    apply Int.ediv_eq_zero_of_lt (by omega)
    omega
  have h1 : v.1 = 2 := by omega
  exact Prod.ext h1 h0

/-- The odd H points: `v = (1, 0)`, or `v = (3, 0)` (with `s = 3L`), or `s(v) > 3 L`. -/
theorem odd_H_cases (frame : ChildFrame) {v : Site} (hv : ¬ EvenSite v) (hE : v ∈ frame.closedPolygon)
    (hsp : frame.hSpectrum (frame.tGrade v)) :
    v = (1, 0) ∨ v = (3, 0) ∨ 3 * (frame.child.den + frame.child.num) < frame.sGrade v := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hL : 0 < frame.child.den + frame.child.num := by omega
  unfold ChildFrame.hSpectrum at hsp
  have ht : frame.child.num ≤ frame.tGrade v ∧ frame.tGrade v ≤ frame.child.den := by
    rcases hsp with ⟨h1, -, -⟩ | ⟨-, h2, h3⟩
    · exfalso
      obtain ⟨c, hc⟩ := frame.tGrade_parity v
      unfold EvenSite at hv
      omega
    · exact ⟨h2, h3⟩
  have hsE : 2 - frame.child.den + frame.child.num ≤ frame.sGrade v := by
    rw [frame.mem_closedPolygon_iff] at hE
    rcases hE with h | h
    · exact absurd h.1 hv
    · exact h.2.2.2.1
  obtain ⟨x, y⟩ := v
  unfold ChildFrame.tGrade at ht
  unfold ChildFrame.sGrade at hsE ⊢
  unfold EvenSite at hv
  dsimp only at hv ht hsE ⊢
  generalize frame.child.num = n at *
  generalize frame.child.den = d at *
  obtain ⟨k, hk⟩ : ∃ k : ℤ, x + y = k := ⟨_, rfl⟩
  have hx : x = k - y := by omega
  subst hx
  have key : (d + n) * ((d + n) * (k - y) + (d - n) * y) =
      k * ((d + n) ^ 2 - 2 * n ^ 2) + 2 * n * (n * (k - y) - d * y) := by ring
  have hpos : 0 < (d + n) ^ 2 - 2 * n ^ 2 := by nlinarith
  rcases (show k ≤ -1 ∨ k = 1 ∨ k = 3 ∨ 5 ≤ k by omega) with hk1 | hk1 | hk1 | hk1
  · exfalso
    have h1 : k * ((d + n) ^ 2 - 2 * n ^ 2) ≤ -((d + n) ^ 2 - 2 * n ^ 2) := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ -1 - k by omega) hpos.le]
    have h2 : 2 * n * (n * (k - y) - d * y) ≤ 2 * n * d := by
      nlinarith [mul_le_mul_of_nonneg_left ht.2 (show (0 : ℤ) ≤ 2 * n by omega)]
    have h3 := mul_le_mul_of_nonneg_left hsE hL.le
    nlinarith
  · left
    have hLy : (d + n) * y ≤ 0 := by nlinarith
    have hLy' : -(d + n) < (d + n) * y := by nlinarith
    have hy0 : y ≤ 0 := by
      by_contra h
      have h' : 1 ≤ y := by omega
      nlinarith
    have hy1 : 0 ≤ y := by
      by_contra h
      have h' : y ≤ -1 := by omega
      nlinarith
    have hy : y = 0 := by omega
    have hx : k - y = 1 := by omega
    rw [hx, hy]
  · have hLy : (d + n) * y ≤ 2 * n := by nlinarith
    have hy0 : y ≤ 0 := by
      by_contra h
      have h' : 1 ≤ y := by omega
      nlinarith
    by_cases hy : y = 0
    · right; left
      have hx : k - y = 3 := by omega
      rw [hx, hy]
    · right; right
      have hy' : y ≤ -1 := by omega
      nlinarith
  · right; right
    have hLy : (d + n) * y ≤ n * (k - 1) := by nlinarith
    have h1 : (d + n) * (2 * n * y) < (d + n) * ((d + n) * (k - 3)) := by
      have hA : (d + n) * (2 * n * y) ≤ 2 * n * (n * (k - 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left hLy (show (0 : ℤ) ≤ 2 * n by omega)]
      have hB : 2 * n * (n * (k - 1)) < (d + n) * ((d + n) * (k - 3)) := by
        nlinarith
      linarith
    have h2 : 2 * n * y < (d + n) * (k - 3) := lt_of_mul_lt_mul_left h1 hL.le
    nlinarith

/-- **The even direct bottom corners, arithmetic core.** Variables: child `(n, d)` (both odd), `T = d² + 2dn − n²`, the even
centre `c = (a, b)` strict, the even H witness `v = (p, q)` with `p + q = 2l`, the floor-law facts, and `c − v ∈ {−1, 0, 1}²`.
Conclusions: `2L − 2 < s(c)`, `s(c) ≤ T − 2d + 2n + 1`, `2 − L ≤ t(c)`, `t(c) ≤ 0`. The black corner `(1, 1)` is excluded. -/
theorem even_direct_arith (n d T p q l a b : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d)
    (hnodd : n % 2 = 1) (hdodd : d % 2 = 1) (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (hcE : (a + b) % 2 = 0)
    (hcu : n * a - d * b < 2)
    (hcs2 : (d + n) * a + (d - n) * b < T)
    (hvE : (p + q) % 2 = 0) (hvpl : 2 ≤ n * p - d * q)
    (hvl : p + q = 2 * l) (hl1 : 1 ≤ l) (hvs : 2 * d * l + 2 * n ≤ (d + n) * p + (d - n) * q)
    (hvk : p + q ≤ d + n - 2) (hvk2 : p + q = d + n - 2 → p = d - 1 ∧ q = n - 1)
    (hl1' : l = 1 → p = 2 ∧ q = 0)
    (ha : -1 ≤ a - p ∧ a - p ≤ 1) (hb : -1 ≤ b - q ∧ b - q ≤ 1) (hne : ¬ (a = 1 ∧ b = 1)) :
    2 * (d + n) - 2 < (d + n) * a + (d - n) * b ∧
      (d + n) * a + (d - n) * b ≤ T - 2 * d + 2 * n + 1 ∧
        2 - (d + n) ≤ n * a - d * b ∧ n * a - d * b ≤ 0 := by
  have hT0 : 0 ≤ T := by rw [hT]; nlinarith
  have hTL : (d + n) * (2 * d - 2 * n - 1) ≤ 2 * T := by
    rw [hT]
    nlinarith
  -- the parity of the grade `t(c)`: it is even because `n`, `d` are odd and `a + b` is even
  have htpar : (n * a - d * b) % 2 = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, d = 2 * m + 1 := ⟨d / 2, by omega⟩
    have : n * a - d * b = 2 * (k * a - m * b) + (a - b) := by
      rw [hk, hm]
      ring
    omega
  obtain ⟨e1, rfl⟩ : ∃ e1, a = p + e1 := ⟨a - p, by ring⟩
  obtain ⟨e2, rfl⟩ : ∃ e2, b = q + e2 := ⟨b - q, by ring⟩
  have hid : (d + n) * ((d + n) * (p + e1) + (d - n) * (q + e2)) =
      ((p + e1) + (q + e2)) * T + 2 * n * (n * (p + e1) - d * (q + e2)) := by
    rw [hT]
    ring
  have hpar : (e1 + e2) % 2 = 0 := by omega
  have he1 : e1 = -1 ∨ e1 = 0 ∨ e1 = 1 := by omega
  have he2 : e2 = -1 ∨ e2 = 0 ∨ e2 = 1 := by omega
  -- the grade `t(c)` is `≤ 0`
  have ht_c : n * (p + e1) - d * (q + e2) ≤ 0 := by
    generalize hτ : n * (p + e1) - d * (q + e2) = τ at *
    omega
  -- the lower band
  have hlow : 2 * (d + n) - 2 < (d + n) * (p + e1) + (d - n) * (q + e2) := by
    rcases (show l = 1 ∨ 2 ≤ l by omega) with hl | hl
    · obtain ⟨hp, hq⟩ := hl1' hl
      subst hp hq
      rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
      all_goals first
        | linarith
        | (exfalso; apply hne; norm_num)
    · have h2dl : 2 * d * 2 ≤ 2 * d * l := by
        nlinarith
      rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
      all_goals linarith
  -- the diagonal index `k_c = (p + e1) + (q + e2) ≤ L − 2`
  have hkc : (p + e1) + (q + e2) ≤ d + n - 2 := by
    rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
    all_goals first
      | omega
      | (by_contra hc
         have hEq : p + q = d + n - 2 := by omega
         obtain ⟨hp, hq⟩ := hvk2 hEq
         subst hp hq
         have hsT : (d + n) * (d - 1 + 1) + (d - n) * (n - 1 + 1) = T := by
           rw [hT]
           ring
         linarith)
  have hup : (d + n) * ((d + n) * (p + e1) + (d - n) * (q + e2)) ≤ (d + n - 2) * T := by
    rw [hid]
    have h1 : ((p + e1) + (q + e2)) * T ≤ (d + n - 2) * T :=
      mul_le_mul_of_nonneg_right hkc hT0
    have h2 : 2 * n * (n * (p + e1) - d * (q + e2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by omega) ht_c
    linarith
  have hsup : (d + n) * ((d + n) * (p + e1) + (d - n) * (q + e2)) ≤ (d + n) * (T - 2 * d + 2 * n + 1) := by
    have e : (d + n) * (T - 2 * d + 2 * n + 1) =
        (d + n - 2) * T + (2 * T - (d + n) * (2 * d - 2 * n - 1)) := by ring
    linarith
  refine ⟨hlow, ?_, ?_, ht_c⟩
  · exact le_of_mul_le_mul_left hsup (by omega)
  · have hlo : -(d + n) ≤ n * e1 - d * e2 := by
      rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl <;> linarith
    have e : n * (p + e1) - d * (q + e2) = (n * p - d * q) + (n * e1 - d * e2) := by ring
    linarith

/-- **The odd direct bottom corners, even witness.** The odd centre `c = (a, b)` is strict, the even H witness `v = (p, q)`
with `c − v` odd. Conclusions: `L + 2n < s(c)`, `s(c) ≤ T − d + n − 1`, `−d ≤ t(c)`, `t(c) ≤ n − 2`. -/
theorem odd_direct_even_arith (n d T p q l a b : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d)
    (hnodd : n % 2 = 1) (hdodd : d % 2 = 1) (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (hcO : (a + b) % 2 = 1) (hcl : d - T < n * a - d * b) (hcu : n * a - d * b < n)
    (hcs1 : d + n - 2 < (d + n) * a + (d - n) * b) (hcs2 : (d + n) * a + (d - n) * b < T + 2 - d + n)
    (hvE : (p + q) % 2 = 0) (hvpl : 2 ≤ n * p - d * q)
    (hvl : p + q = 2 * l) (hl1 : 1 ≤ l) (hvs : 2 * d * l + 2 * n ≤ (d + n) * p + (d - n) * q)
    (hvk : p + q ≤ d + n - 2) (hl1' : l = 1 → p = 2 ∧ q = 0)
    (ha : -1 ≤ a - p ∧ a - p ≤ 1) (hb : -1 ≤ b - q ∧ b - q ≤ 1) :
    (d + n) + 2 * n < (d + n) * a + (d - n) * b ∧
      (d + n) * a + (d - n) * b ≤ T - d + n - 1 ∧
        -d ≤ n * a - d * b ∧ n * a - d * b ≤ n - 2 := by
  have hT0 : 0 ≤ T := by rw [hT]; nlinarith
  -- the parity of `t(c)`: odd, since `n`, `d` are odd and `a + b` is odd
  have htpar : (n * a - d * b) % 2 = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, d = 2 * m + 1 := ⟨d / 2, by omega⟩
    have : n * a - d * b = 2 * (k * a - m * b) + (a - b) := by
      rw [hk, hm]
      ring
    omega
  obtain ⟨e1, rfl⟩ : ∃ e1, a = p + e1 := ⟨a - p, by ring⟩
  obtain ⟨e2, rfl⟩ : ∃ e2, b = q + e2 := ⟨b - q, by ring⟩
  have hid : (d + n) * ((d + n) * (p + e1) + (d - n) * (q + e2)) =
      ((p + e1) + (q + e2)) * T + 2 * n * (n * (p + e1) - d * (q + e2)) := by
    rw [hT]
    ring
  have hpar : (e1 + e2) % 2 = 1 := by omega
  have he1 : e1 = -1 ∨ e1 = 0 ∨ e1 = 1 := by omega
  have he2 : e2 = -1 ∨ e2 = 0 ∨ e2 = 1 := by omega
  have ht_c : n * (p + e1) - d * (q + e2) ≤ n - 2 := by
    generalize hτ : n * (p + e1) - d * (q + e2) = τ at *
    omega
  have ht_lo : -d ≤ n * (p + e1) - d * (q + e2) := by
    have hlo : -d ≤ n * e1 - d * e2 := by
      rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl <;> first | linarith | omega
    have e : n * (p + e1) - d * (q + e2) = (n * p - d * q) + (n * e1 - d * e2) := by ring
    linarith
  -- the lower band
  have hlow : (d + n) + 2 * n < (d + n) * (p + e1) + (d - n) * (q + e2) := by
    rcases (show l = 1 ∨ 2 ≤ l by omega) with hl | hl
    · obtain ⟨hp, hq⟩ := hl1' hl
      subst hp hq
      rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
      all_goals first
        | (exfalso; omega)
        | (ring_nf at hcu hcs1 hcs2 hcl ⊢; linarith)
    · have h2dl : 4 * d ≤ 2 * d * l := by
        nlinarith
      rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
      all_goals first
        | linarith
  -- the diagonal index: `k_c ≤ L − 1`
  have hkc : (p + e1) + (q + e2) ≤ d + n - 1 := by
    rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
    all_goals first
      | omega
  have hup : (d + n) * ((d + n) * (p + e1) + (d - n) * (q + e2)) ≤ (d + n) * (T - d + n - 1) := by
    rw [hid]
    have h1 : ((p + e1) + (q + e2)) * T ≤ (d + n - 1) * T :=
      mul_le_mul_of_nonneg_right hkc hT0
    have h2 : 2 * n * (n * (p + e1) - d * (q + e2)) ≤ 2 * n * (n - 2) :=
      mul_le_mul_of_nonneg_left ht_c (by omega)
    have h3 : (d + n) * (T - d + n - 1) = (d + n - 1) * T + ((d + n) * (T - d + n - 1) - (d + n - 1) * T) := by
      ring
    have h4 : (d + n) * (T - d + n - 1) - (d + n - 1) * T = T - (d + n) * (d - n + 1) := by ring
    have h5 : T - (d + n) * (d - n + 1) ≥ 2 * n * (n - 2) := by
      rw [hT]
      nlinarith
    nlinarith
  refine ⟨hlow, ?_, ht_lo, ?_⟩
  · exact le_of_mul_le_mul_left hup (by omega)
  · exact ht_c

/-- Parity of the grade `t`: for odd `n`, `d`, `t(a, b) ≡ a + b (mod 2)`. -/
theorem t_parity (n d a b : ℤ) (hn : n % 2 = 1) (hd : d % 2 = 1) :
    (n * a - d * b) % 2 = (a + b) % 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, d = 2 * m + 1 := ⟨d / 2, by omega⟩
  have e : (2 * k + 1) * a - (2 * m + 1) * b = 2 * (k * a - m * b) + (a - b) := by ring
  rw [e]
  omega

/-- The upper bound on `s` for an even centre from the diagonal index `k ≤ L − 2` and `t ≤ 0`. -/
theorem s_le_even (n d T k t s : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d) (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (hid : (d + n) * s = k * T + 2 * n * t) (hk : k ≤ d + n - 2) (ht : t ≤ 0) :
    s ≤ T - 2 * d + 2 * n + 1 := by
  have hT0 : 0 ≤ T := by rw [hT]; nlinarith
  have h1 : k * T ≤ (d + n - 2) * T := mul_le_mul_of_nonneg_right hk hT0
  have h2 : 2 * n * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) ht
  have h3 : (d + n) * s ≤ (d + n) * (T - 2 * d + 2 * n + 1) := by
    have h4 : (d + n - 2) * T ≤ (d + n) * (T - 2 * d + 2 * n + 1) := by
      rw [hT]
      nlinarith [mul_pos (show (0 : ℤ) < d by omega) (show (0 : ℤ) < n by omega)]
    linarith
  exact le_of_mul_le_mul_left h3 (by omega)

/-- The upper bound on `s` for an odd centre from the diagonal index `k ≤ L − 1` and `t ≤ n − 2`. -/
theorem s_le_odd (n d T k t s : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d) (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (hid : (d + n) * s = k * T + 2 * n * t) (hk : k ≤ d + n - 1) (ht : t ≤ n - 2) :
    s ≤ T - d + n - 1 := by
  have hT0 : 0 ≤ T := by rw [hT]; nlinarith
  have h1 : k * T ≤ (d + n - 1) * T := mul_le_mul_of_nonneg_right hk hT0
  have h2 : 2 * n * t ≤ 2 * n * (n - 2) := mul_le_mul_of_nonneg_left ht (by omega)
  have h3 : (d + n) * s ≤ (d + n) * (T - d + n - 1) := by
    have h4 : (d + n - 1) * T + 2 * n * (n - 2) ≤ (d + n) * (T - d + n - 1) := by
      rw [hT]
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - n - 2 by omega) (show (0 : ℤ) ≤ 2 * n - 1 by omega)]
    linarith
  exact le_of_mul_le_mul_left h3 (by omega)

/-- **The even direct bottom corners with an odd witness.** The even strict centre `c = (a, b)` (not `(1,1)`) with an odd
H witness `v = (p, q)`, `|c − v|∞ ≤ 1`: `v = (1,0)` is impossible, and otherwise `s(v) ≥ 3L`. Conclusions: the even band. -/
theorem even_direct_odd_arith (n d T p q a b : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d)
    (hnodd : n % 2 = 1) (hdodd : d % 2 = 1) (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (hcE : (a + b) % 2 = 0) (hcs1 : 2 * n < (d + n) * a + (d - n) * b)
    (hcu : n * a - d * b < 2) (hcs2 : (d + n) * a + (d - n) * b < T) (hne : ¬ (a = 1 ∧ b = 1))
    (hvO : (p + q) % 2 = 1) (hvt : n ≤ n * p - d * q)
    (hvk : p + q ≤ d + n - 1) (hvk2 : p + q = d + n - 1 → p = d ∧ q = n - 1)
    (hvc : (p = 1 ∧ q = 0) ∨ 3 * (d + n) ≤ (d + n) * p + (d - n) * q)
    (ha : -1 ≤ a - p ∧ a - p ≤ 1) (hb : -1 ≤ b - q ∧ b - q ≤ 1) :
    2 * (d + n) - 2 < (d + n) * a + (d - n) * b ∧
      (d + n) * a + (d - n) * b ≤ T - 2 * d + 2 * n + 1 ∧
        2 - (d + n) ≤ n * a - d * b ∧ n * a - d * b ≤ 0 := by
  obtain ⟨e1, rfl⟩ : ∃ e1, a = p + e1 := ⟨a - p, by ring⟩
  obtain ⟨e2, rfl⟩ : ∃ e2, b = q + e2 := ⟨b - q, by ring⟩
  have he1 : e1 = -1 ∨ e1 = 0 ∨ e1 = 1 := by omega
  have he2 : e2 = -1 ∨ e2 = 0 ∨ e2 = 1 := by omega
  have hid : (d + n) * ((d + n) * (p + e1) + (d - n) * (q + e2)) =
      ((p + e1) + (q + e2)) * T + 2 * n * (n * (p + e1) - d * (q + e2)) := by
    rw [hT]
    ring
  have ht0 : n * (p + e1) - d * (q + e2) ≤ 0 := by
    have hp := t_parity n d (p + e1) (q + e2) hnodd hdodd
    generalize hτ : n * (p + e1) - d * (q + e2) = τ at *
    omega
  -- the lower bound on `t`: from `t(v) ≥ n` and the four odd steps
  have ht_lo : 2 - (d + n) ≤ n * (p + e1) - d * (q + e2) := by
    rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
    all_goals first
      | omega
      | linarith
  -- the lower bound on `s`
  have hs_lo : 2 * (d + n) - 2 < (d + n) * (p + e1) + (d - n) * (q + e2) := by
    rcases hvc with ⟨hp, hq⟩ | hbig
    · subst hp
      subst hq
      rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
      all_goals omega
    · rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
      all_goals first
        | omega
        | linarith
  -- the diagonal index `k_c ≤ L − 2`
  have hkc : (p + e1) + (q + e2) ≤ d + n - 2 := by
    by_contra hc
    have hkv : p + q = d + n - 1 := by omega
    obtain ⟨hp, hq⟩ := hvk2 hkv
    rw [hp, hq] at hcu hcs2
    rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
    all_goals first
      | omega
      | linarith
  refine ⟨hs_lo, ?_, ht_lo, ht0⟩
  exact s_le_even n d T ((p + e1) + (q + e2)) (n * (p + e1) - d * (q + e2))
    ((d + n) * (p + e1) + (d - n) * (q + e2)) hn hnd hT hid hkc ht0

/-- **The odd direct bottom corners with an odd witness.** The odd strict centre `c = (a, b)` with an odd H witness
`v = (p, q)`, `|c − v|∞ ≤ 1`, where `v = (1,0)`, `v = (3,0)`, or `s(v) > 3L`. Conclusions: the odd band. -/
theorem odd_direct_odd_arith (n d T p q a b : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d)
    (hnodd : n % 2 = 1) (hdodd : d % 2 = 1) (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (hcO : (a + b) % 2 = 1) (hcu : n * a - d * b < n)
    (hcs1 : d + n - 2 < (d + n) * a + (d - n) * b)
    (hcs2 : (d + n) * a + (d - n) * b < T + 2 - d + n)
    (hvO : (p + q) % 2 = 1) (hvt : n ≤ n * p - d * q)
    (hvk : p + q ≤ d + n - 1) (hvk2 : p + q = d + n - 1 → p = d ∧ q = n - 1)
    (hvc : (p = 1 ∧ q = 0) ∨ (p = 3 ∧ q = 0) ∨ 3 * (d + n) < (d + n) * p + (d - n) * q)
    (ha : -1 ≤ a - p ∧ a - p ≤ 1) (hb : -1 ≤ b - q ∧ b - q ≤ 1) :
    (d + n) + 2 * n < (d + n) * a + (d - n) * b ∧
      (d + n) * a + (d - n) * b ≤ T - d + n - 1 ∧
        -d ≤ n * a - d * b ∧ n * a - d * b ≤ n - 2 := by
  obtain ⟨e1, rfl⟩ : ∃ e1, a = p + e1 := ⟨a - p, by ring⟩
  obtain ⟨e2, rfl⟩ : ∃ e2, b = q + e2 := ⟨b - q, by ring⟩
  have he1 : e1 = -1 ∨ e1 = 0 ∨ e1 = 1 := by omega
  have he2 : e2 = -1 ∨ e2 = 0 ∨ e2 = 1 := by omega
  have hid : (d + n) * ((d + n) * (p + e1) + (d - n) * (q + e2)) =
      ((p + e1) + (q + e2)) * T + 2 * n * (n * (p + e1) - d * (q + e2)) := by
    rw [hT]
    ring
  have ht_hi : n * (p + e1) - d * (q + e2) ≤ n - 2 := by
    have hp := t_parity n d (p + e1) (q + e2) hnodd hdodd
    generalize hτ : n * (p + e1) - d * (q + e2) = τ at *
    omega
  have ht_lo : -d ≤ n * (p + e1) - d * (q + e2) := by
    rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
    all_goals first
      | omega
      | linarith
  -- the lower bound on `s`
  have hs_lo : (d + n) + 2 * n < (d + n) * (p + e1) + (d - n) * (q + e2) := by
    rcases hvc with ⟨hp, hq⟩ | ⟨hp, hq⟩ | hbig
    · subst hp
      subst hq
      rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
      all_goals first
        | omega
    · subst hp
      subst hq
      rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
      all_goals first
        | omega
    · rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
      all_goals first
        | omega
        | linarith
  -- the diagonal index `k_c ≤ L − 1`
  have hkc : (p + e1) + (q + e2) ≤ d + n - 1 := by
    by_contra hc
    have hkv : p + q = d + n - 1 := by omega
    obtain ⟨hp, hq⟩ := hvk2 hkv
    rw [hp, hq] at hcu hcs2
    rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
    all_goals first
      | omega
      | linarith
  refine ⟨hs_lo, ?_, ht_lo, ht_hi⟩
  exact s_le_odd n d T ((p + e1) + (q + e2)) (n * (p + e1) - d * (q + e2))
    ((d + n) * (p + e1) + (d - n) * (q + e2)) hn hnd hT hid hkc ht_hi

end FLatticePaper.CollarBottomCases
