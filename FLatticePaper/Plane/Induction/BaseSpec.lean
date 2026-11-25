import FLatticePaper.Plane.Induction.RootClassify
import Mathlib.Tactic.LinearCombination

/-! Task 72 / Q31 psi (1), the spectrum part of the base membership, in explicit parameters.

Parent `N/D` (odd, `N + D` odd, `1 ≤ N < D`), child `n/d` with `ε = N d − D n = ±1`, `r = D + N`, `c_p = D − N`, `L = d + n`, `c = d − n`.
A base point `(x, i)` of the native cut has `s = L x + c i`, parent grade `p = r x + c_p i`, and `L p = r s − 2 ε i`.
The conjugate's spectrum grade of `w = (1 + i, −x)` is `t_C(w) = p + c_p`.

* odd base (`x + i` odd): `2 − c_p ≤ p ≤ r − 2` (so `t_C` is even in `[2, 2D − 2]`);
* even base (`x + i` even): `0 ≤ p ≤ 2N` (so `t_C` is odd in `[c_p, r]`). -/

namespace FLatticePaper.BaseSpec

/-- The odd base range: `2 − c_p ≤ p ≤ r − 2`, for `0 ≤ i ≤ r − 1` (and `i ≤ r − 2` when `ε = 1`). -/
theorem odd_base_range (D N n d ε x i : ℤ) (hε : ε = N * d - D * n) (hε1 : ε = 1 ∨ ε = -1)
    (hN : 1 ≤ N) (hND : N < D) (hodd : (D + N) % 2 = 1) (hi0 : 0 ≤ i) (hir : i ≤ D + N - 1)
    (hphase : ε = -1 ∨ i ≤ D + N - 2)
    (hL : 2 * (D + N) ≤ d + n)
    (hs0 : 2 - (d - n) ≤ (d + n) * x + (d - n) * i) (hs1 : (d + n) * x + (d - n) * i ≤ d + n - 2)
    (hpar : (x + i) % 2 = 1) :
    2 - (D - N) ≤ (D + N) * x + (D - N) * i ∧ (D + N) * x + (D - N) * i ≤ D + N - 2 := by
  have hrc : (D + N) * (d - n) = (D - N) * (d + n) + 2 * ε := by
    subst hε
    ring
  have hLd : (d + n) * ((D + N) * x + (D - N) * i) = (D + N) * ((d + n) * x + (d - n) * i) - 2 * ε * i := by
    subst hε
    ring
  have hpodd : ((D + N) * x + (D - N) * i) % 2 = 1 := by
    obtain ⟨a, ha⟩ : ∃ a, D + N = 2 * a + 1 := ⟨(D + N) / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, D - N = 2 * b + 1 := ⟨(D - N) / 2, by omega⟩
    have e : (D + N) * x + (D - N) * i = (x + i) + 2 * (a * x + b * i) := by
      rw [ha, hb]
      ring
    rw [e]
    omega
  have hLpos : (0 : ℤ) < d + n := by omega
  set L := d + n with hLdef
  set c := d - n with hcdef
  set r := D + N with hrdef
  set cp := D - N with hcpdef
  set s := L * x + c * i with hsdef
  set p := r * x + cp * i with hpdef
  have hr0 : 0 < r := by omega
  -- upper bound: p < r
  have hup : p < r := by
    have hLp : L * p < L * r := by
      rcases hε1 with h1 | h1
      · rw [h1] at hLd
        have h2 : r * s ≤ r * (L - 2) := mul_le_mul_of_nonneg_left hs1 hr0.le
        nlinarith
      · rw [h1] at hLd
        have h2 : r * s ≤ r * (L - 2) := mul_le_mul_of_nonneg_left hs1 hr0.le
        nlinarith
    exact lt_of_mul_lt_mul_left hLp hLpos.le
  have hup2 : p ≤ r - 2 := by omega
  -- lower bound: p > −c_p, then parity
  have hlo : -cp < p := by
    have hLp : L * (-cp) < L * p := by
      rcases hε1 with h1 | h1
      · rw [h1] at hLd hrc
        have h2 : r * (2 - c) ≤ r * s := mul_le_mul_of_nonneg_left hs0 hr0.le
        have hi2 : i ≤ r - 2 := by
          rcases hphase with h | h
          · omega
          · exact h
        nlinarith
      · rw [h1] at hLd hrc
        have h2 : r * (2 - c) ≤ r * s := mul_le_mul_of_nonneg_left hs0 hr0.le
        nlinarith
    exact lt_of_mul_lt_mul_left hLp hLpos.le
  have hcpodd : cp % 2 = 1 := by omega
  constructor
  · omega
  · exact hup2

/-- The even base range: `0 ≤ p ≤ 2N`, for `0 ≤ i ≤ r − 1` and the even window `0 ≤ s ≤ 2n`. -/
theorem even_base_range (D N n d ε x i : ℤ) (hε : ε = N * d - D * n) (hε1 : ε = 1 ∨ ε = -1)
    (hN : 1 ≤ N) (hND : N < D) (hodd : (D + N) % 2 = 1) (hi0 : 0 ≤ i) (hir : i ≤ D + N - 1)
    (hL : 2 * (D + N) ≤ d + n)
    (hs0 : 0 ≤ (d + n) * x + (d - n) * i) (hs1 : (d + n) * x + (d - n) * i ≤ 2 * n)
    (hpar : (x + i) % 2 = 0) :
    0 ≤ (D + N) * x + (D - N) * i ∧ (D + N) * x + (D - N) * i ≤ 2 * N := by
  have hrn : (D + N) * n = N * (d + n) - ε := by
    subst hε
    ring
  have hLd : (d + n) * ((D + N) * x + (D - N) * i) = (D + N) * ((d + n) * x + (d - n) * i) - 2 * ε * i := by
    subst hε
    ring
  have hpeven : ((D + N) * x + (D - N) * i) % 2 = 0 := by
    obtain ⟨a, ha⟩ : ∃ a, D + N = 2 * a + 1 := ⟨(D + N) / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, D - N = 2 * b + 1 := ⟨(D - N) / 2, by omega⟩
    have e : (D + N) * x + (D - N) * i = (x + i) + 2 * (a * x + b * i) := by
      rw [ha, hb]
      ring
    rw [e]
    omega
  have hLpos : (0 : ℤ) < d + n := by omega
  set L := d + n with hLdef
  set r := D + N with hrdef
  set p := r * x + (D - N) * i with hpdef
  set s := L * x + (d - n) * i with hsdef
  have hr0 : 0 < r := by omega
  have hrL : 2 * r ≤ L := by omega
  have hi1 : 1 + i < L := by omega
  -- upper bound p < 2N + 2
  have hpU : p < 2 * N + 2 := by
    have hLp : L * p < L * (2 * N + 2) := by
      rcases hε1 with h1 | h1
      · rw [h1] at hLd hrn
        have h2 : r * s ≤ r * (2 * n) := mul_le_mul_of_nonneg_left hs1 hr0.le
        nlinarith
      · rw [h1] at hLd hrn
        have h2 : r * s ≤ r * (2 * n) := mul_le_mul_of_nonneg_left hs1 hr0.le
        nlinarith
    exact lt_of_mul_lt_mul_left hLp hLpos.le
  -- lower bound p > −1
  have hpL : -1 < p := by
    have hLp : L * (-1) < L * p := by
      rcases hε1 with h1 | h1
      · rw [h1] at hLd
        have h2 : 0 ≤ r * s := mul_nonneg hr0.le hs0
        nlinarith
      · rw [h1] at hLd
        have h2 : 0 ≤ r * s := mul_nonneg hr0.le hs0
        nlinarith
    exact lt_of_mul_lt_mul_left hLp hLpos.le
  constructor
  · omega
  · omega

/-- The odd `s`-part, case A (base point of odd parity; the conjugate point is even): `0 ≤ s_C ≤ T_C + 2c_p`,
with `s_C = 2D(1 + i) − 2N x` and `T_C = 2(D² + 2DN − N²)`. -/
theorem sC_odd_bound (D N n d ε x i : ℤ) (hε : ε = N * d - D * n) (hε1 : ε = 1 ∨ ε = -1)
    (hN : 1 ≤ N) (hND : N < D) (hi0 : 0 ≤ i) (hir : i ≤ D + N - 1) (hL : 2 * (D + N) ≤ d + n)
    (hc : 0 < d - n)
    (hs0 : 2 - (d - n) ≤ (d + n) * x + (d - n) * i) (hs1 : (d + n) * x + (d - n) * i ≤ d + n - 2) :
    0 ≤ 2 * D * (1 + i) - 2 * N * x ∧
      2 * D * (1 + i) - 2 * N * x ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * (D - N) := by
  have hrc : (D + N) * (d - n) = (D - N) * (d + n) + 2 * ε := by
    subst hε
    ring
  have hLpos : (0 : ℤ) < d + n := by omega
  -- x ≤ 0 from the upper window
  have hx0 : x ≤ 0 := by
    by_contra hpos
    have hx1 : 1 ≤ x := by omega
    have : (d + n) * 1 ≤ (d + n) * x := mul_le_mul_of_nonneg_left hx1 hLpos.le
    have hci : 0 ≤ (d - n) * i := mul_nonneg hc.le hi0
    nlinarith
  constructor
  · nlinarith
  · -- clear the denominator L, then r
    have hLx : 2 - (d - n) - (d - n) * i ≤ (d + n) * x := by linarith
    have hr0 : (0 : ℤ) < D + N := by omega
    have hT : 0 ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) := by nlinarith
    have hid : (D + N) * ((2 * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * (D - N)) * (d + n)
        - (2 * D * (1 + i) * (d + n) - 4 * N + 2 * N * (d - n) * (1 + i)))
        = (d + n) * (2 * (D ^ 2 + 2 * D * N - N ^ 2)) * (D + N - 1 - i)
          + 2 * (D + N) * (D - N) * (d + n) + 4 * N * ((D + N) - ε * (1 + i)) := by
      linear_combination (-2 * N * (1 + i)) * hrc
    have hpos1 : 0 ≤ (d + n) * (2 * (D ^ 2 + 2 * D * N - N ^ 2)) * (D + N - 1 - i) :=
      mul_nonneg (mul_nonneg hLpos.le hT) (by omega)
    have hpos2 : 0 ≤ 2 * (D + N) * (D - N) * (d + n) :=
      mul_nonneg (mul_nonneg (by omega) (by omega)) hLpos.le
    have hpos3 : 0 ≤ 4 * N * ((D + N) - ε * (1 + i)) := by
      apply mul_nonneg (by omega)
      rcases hε1 with h1 | h1
      · rw [h1]; omega
      · rw [h1]; omega
    have hGA : 0 ≤ (2 * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * (D - N)) * (d + n)
        - (2 * D * (1 + i) * (d + n) - 4 * N + 2 * N * (d - n) * (1 + i)) := by
      have h := hid
      have hnn : 0 ≤ (D + N) * ((2 * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * (D - N)) * (d + n)
        - (2 * D * (1 + i) * (d + n) - 4 * N + 2 * N * (d - n) * (1 + i))) := by
        rw [h]; linarith
      exact (mul_nonneg_iff_of_pos_left hr0).mp hnn
    have hLx' : 2 - (d - n) * (1 + i) ≤ (d + n) * x := by linarith
    have hNn : 0 ≤ 2 * N := by omega
    have hfin : (2 * D * (1 + i) - 2 * N * x) * (d + n)
        ≤ (2 * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * (D - N)) * (d + n) := by
      have h5 : 2 * N * ((d + n) * x) ≥ 2 * N * (2 - (d - n) * (1 + i)) :=
        mul_le_mul_of_nonneg_left hLx' hNn
      nlinarith
    exact le_of_mul_le_mul_right hfin hLpos

/-- The odd `s`-part, case B (base point of even parity; the conjugate point is odd): `2 − 2N ≤ s_C ≤ T_C + 2D − 2`. -/
theorem sC_even_bound (D N n d ε x i : ℤ) (hε : ε = N * d - D * n) (hε1 : ε = 1 ∨ ε = -1)
    (hN : 1 ≤ N) (hND : N < D) (hi0 : 0 ≤ i) (hir : i ≤ D + N - 1) (hL : 2 * (D + N) ≤ d + n)
    (hc : 0 < d - n)
    (hs0 : 0 ≤ (d + n) * x + (d - n) * i) (hs1 : (d + n) * x + (d - n) * i ≤ 2 * n) :
    2 - 2 * N ≤ 2 * D * (1 + i) - 2 * N * x ∧
      2 * D * (1 + i) - 2 * N * x ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * D - 2 := by
  have hrc : (D + N) * (d - n) = (D - N) * (d + n) + 2 * ε := by
    subst hε
    ring
  have hLpos : (0 : ℤ) < d + n := by omega
  have hx0 : x ≤ 0 := by
    by_contra hpos
    have hx1 : 1 ≤ x := by omega
    have : (d + n) * 1 ≤ (d + n) * x := mul_le_mul_of_nonneg_left hx1 hLpos.le
    have hci : 0 ≤ (d - n) * i := mul_nonneg hc.le hi0
    nlinarith
  constructor
  · nlinarith
  · have hLx : -((d - n) * i) ≤ (d + n) * x := by linarith
    have hr0 : (0 : ℤ) < D + N := by omega
    have hT : 2 * (D + N) + 2 * N ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) := by nlinarith
    have hTnn : 0 ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) := by linarith
    have hid : (D + N) * ((2 * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * D - 2) * (d + n)
        - (2 * D * (1 + i) * (d + n) + 2 * N * (d - n) * i))
        = (d + n) * (2 * (D ^ 2 + 2 * D * N - N ^ 2)) * ((D + N) - 1 - i)
          + (d + n) * (2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D + N))
          - 4 * N * ε * i := by
      linear_combination (-2 * N * i) * hrc
    have hpos1 : 0 ≤ (d + n) * (2 * (D ^ 2 + 2 * D * N - N ^ 2)) * ((D + N) - 1 - i) :=
      mul_nonneg (mul_nonneg hLpos.le hTnn) (by omega)
    have hpos2 : 0 ≤ (d + n) * (2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D + N)) := by
      apply mul_nonneg hLpos.le
      omega
    have hpos3 : 0 ≤ (d + n) * (2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D + N)) - 4 * N * ε * i := by
      have hTr : 2 * N ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D + N) := by linarith
      have hA : 2 * (D + N) * (2 * N) ≤ 2 * (D + N) * (2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D + N)) :=
        mul_le_mul_of_nonneg_left hTr (by omega)
      have hB : 2 * (D + N) * (2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D + N))
          ≤ (d + n) * (2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D + N)) :=
        mul_le_mul_of_nonneg_right hL (by linarith)
      have hi_r : i ≤ D + N := by omega
      have hC : 4 * N * i ≤ 4 * N * (D + N) := mul_le_mul_of_nonneg_left hi_r (by omega)
      rcases hε1 with h1 | h1
      · rw [h1]
        nlinarith
      · rw [h1]
        nlinarith
    have hGB : 0 ≤ (2 * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * D - 2) * (d + n)
        - (2 * D * (1 + i) * (d + n) + 2 * N * (d - n) * i) := by
      have hnn : 0 ≤ (D + N) * ((2 * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * D - 2) * (d + n)
        - (2 * D * (1 + i) * (d + n) + 2 * N * (d - n) * i)) := by
        rw [hid]; linarith
      exact (mul_nonneg_iff_of_pos_left hr0).mp hnn
    have hLx' : -((d - n) * i) ≤ (d + n) * x := by linarith
    have hNn : 0 ≤ 2 * N := by omega
    have hfin : (2 * D * (1 + i) - 2 * N * x) * (d + n)
        ≤ (2 * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * D - 2) * (d + n) := by
      have h5 : 2 * N * (-((d - n) * i)) ≤ 2 * N * ((d + n) * x) :=
        mul_le_mul_of_nonneg_left hLx' hNn
      nlinarith
    exact le_of_mul_le_mul_right hfin hLpos

end FLatticePaper.BaseSpec
