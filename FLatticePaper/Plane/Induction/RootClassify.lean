import FLatticePaper.Plane.Induction.ArcTransport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Task 72 / Q31, root classification of the native parent V spectrum (step 1 of the raw-cut chain).

Notation: the child `n/d` with odd parent `N/D` and `r = D + N`, `c_p = D − N`, `L = d + n`, `c = d − n`, `ε = N d − D n`,
`s(x, y) = L x + c y`, `s_p(x, y) = r x + c_p y`. For a native V site `z = (x, j)` of ordinate `j`:
* `L s_p(z) = r s(z) − 2 ε j` (`ordinate_identity`), from `r c = c_p L + 2 ε` (`rc_identity`);
* `s_p(z)` has the parity of `z` (`sp_parity`), since `r` and `c_p` are odd;
* the even window `0 ≤ s(z) ≤ 2n` gives `0 ≤ s_p ≤ 2N` (ε = −1) and `0 ≤ s_p ≤ 2N − 2` (ε = +1) (`even_sp_range`). -/

namespace FLatticePaper.RootClassify

/-- `r c = c_p L + 2 ε`. -/
theorem rc_identity (N D n d ε : ℤ) (hε : ε = N * d - D * n) :
    (D + N) * (d - n) = (D - N) * (d + n) + 2 * ε := by
  subst hε
  ring

/-- `L s_p(x, j) = r s(x, j) − 2 ε j`. -/
theorem ordinate_identity (N D n d ε x j : ℤ) (hε : ε = N * d - D * n) :
    (d + n) * ((D + N) * x + (D - N) * j) =
      (D + N) * ((d + n) * x + (d - n) * j) - 2 * ε * j := by
  subst hε
  ring

/-- The parent grade `s_p = r x + c_p j` has the parity of `x + j` when `r` and `c_p` are odd. -/
theorem sp_parity (r c x j : ℤ) (hr : r % 2 = 1) (hc : c % 2 = 1) :
    (r * x + c * j) % 2 = (x + j) % 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, r = 2 * a + 1 := ⟨r / 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, c = 2 * b + 1 := ⟨c / 2, by omega⟩
  have e : (2 * a + 1) * x + (2 * b + 1) * j = (x + j) + 2 * (a * x + b * j) := by ring
  rw [e, Int.add_mul_emod_self_left]

/-- **The even window of the native V spectrum.** For an even native site `(x, j)` with `0 ≤ s ≤ 2n` and `0 ≤ j ≤ L − 2`:
`0 ≤ s_p ≤ 2N − 2` when `ε = 1`, and `0 ≤ s_p ≤ 2N` when `ε = −1`. -/
theorem even_sp_range (N D n d ε x j : ℤ) (hε : ε = N * d - D * n) (hε1 : ε = 1 ∨ ε = -1)
    (hN : 0 ≤ N) (hD : 0 < D) (hodd : (D + N) % 2 = 1) (hodd' : (D - N) % 2 = 1)
    (hL : 0 < d + n) (hj0 : 0 ≤ j) (hjL : j ≤ d + n - 2)
    (hs0 : 0 ≤ (d + n) * x + (d - n) * j) (hs1 : (d + n) * x + (d - n) * j ≤ 2 * n)
    (hpar : (x + j) % 2 = 0) :
    0 ≤ (D + N) * x + (D - N) * j ∧
      (D + N) * x + (D - N) * j ≤ (if ε = 1 then 2 * N - 2 else 2 * N) := by
  set L := d + n with hLdef
  set s := (d + n) * x + (d - n) * j with hsdef
  set p := (D + N) * x + (D - N) * j with hpdef
  have hr0 : 0 < D + N := by omega
  have hid : L * p = (D + N) * s - 2 * ε * j := by
    rw [hpdef, hsdef, hLdef]
    exact ordinate_identity N D n d ε x j hε
  have hrn : (D + N) * n = N * L - ε := by
    rw [hLdef]
    rw [hε]
    exact FLatticePaper.ArcTransport.r_mul_n N D n d
  have hpar' : p % 2 = 0 := by
    rw [hpdef, sp_parity (D + N) (D - N) x j hodd hodd', hpar]
  have hsup : (D + N) * s ≤ (D + N) * (2 * n) := mul_le_mul_of_nonneg_left hs1 hr0.le
  have hsdown : 0 ≤ (D + N) * s := mul_nonneg hr0.le hs0
  have hLpos : (0 : ℤ) < L := by rw [hLdef]; exact hL
  rcases hε1 with h1 | h1
  · -- ε = 1: L p = r s − 2 j, with 2 r n = 2 N L − 2
    rw [h1] at hid hrn ⊢
    simp only [if_true]
    have hup : L * p < L * (2 * N) := by nlinarith
    have hlo : L * (-2) < L * p := by nlinarith
    have hpN : p < 2 * N := lt_of_mul_lt_mul_left hup hLpos.le
    have hpL : -2 < p := lt_of_mul_lt_mul_left hlo hLpos.le
    constructor
    · omega
    · omega
  · -- ε = −1: L p = r s + 2 j, with 2 r n = 2 N L + 2
    rw [h1] at hid hrn ⊢
    have hnot : ¬ ((-1 : ℤ) = 1) := by norm_num
    simp only [hnot, if_false]
    have hup : L * p < L * (2 * N + 2) := by nlinarith
    have hlo : 0 ≤ L * p := by nlinarith
    have hpN : p < 2 * N + 2 := lt_of_mul_lt_mul_left hup hLpos.le
    have hp0 : 0 ≤ p := le_of_mul_le_mul_left (by rw [mul_zero]; exact hlo) hLpos
    constructor
    · exact hp0
    · omega

/-- **The odd window of the native V spectrum.** For an odd native site `(x, j)` with `0 ≤ j ≤ L − 2` and the odd window
`2 − c ≤ s ≤ L − 2` (`c = d − n`): `N − D ≤ s_p ≤ D + N` (coarse; the table values are `2 − c_p ≤ s_p ≤ r` for ε = −1 and
`−c_p ≤ s_p ≤ r − 2` for ε = 1). -/
theorem odd_sp_range (N D n d ε x j : ℤ) (hε : ε = N * d - D * n) (hε1 : ε = 1 ∨ ε = -1)
    (hN : 0 ≤ N) (hD : 0 < D) (hodd : (D + N) % 2 = 1) (hodd' : (D - N) % 2 = 1)
    (hL : 0 < d + n) (hj0 : 0 ≤ j) (hjL : j ≤ d + n - 2)
    (hs0 : 2 - (d - n) ≤ (d + n) * x + (d - n) * j) (hs1 : (d + n) * x + (d - n) * j ≤ d + n - 2)
    (hpar : (x + j) % 2 = 1) :
    N - D ≤ (D + N) * x + (D - N) * j ∧ (D + N) * x + (D - N) * j ≤ D + N := by
  set L := d + n with hLdef
  set s := (d + n) * x + (d - n) * j with hsdef
  set p := (D + N) * x + (D - N) * j with hpdef
  have hr0 : 0 < D + N := by omega
  have hid : L * p = (D + N) * s - 2 * ε * j := by
    rw [hpdef, hsdef, hLdef]
    exact ordinate_identity N D n d ε x j hε
  have hcdet : (D + N) * (d - n) = (D - N) * (d + n) + 2 * ε := rc_identity N D n d ε hε
  have hpar' : p % 2 = 1 := by
    rw [hpdef, sp_parity (D + N) (D - N) x j hodd hodd', hpar]
  have hLpos : (0 : ℤ) < L := by rw [hLdef]; exact hL
  have hsl : (2 - (d - n)) ≤ s := hs0
  have hsu : s ≤ L - 2 := by rw [hLdef, hsdef] at *; exact hs1
  have hrs_lo : (D + N) * (2 - (d - n)) ≤ (D + N) * s := mul_le_mul_of_nonneg_left hsl hr0.le
  have hrs_hi : (D + N) * s ≤ (D + N) * (L - 2) := mul_le_mul_of_nonneg_left hsu hr0.le
  rcases hε1 with h1 | h1
  · -- ε = 1: L p = r s − 2 j,  r c = c_p L + 2
    rw [h1] at hid hcdet
    constructor
    · have h2 : L * (N - D - 2) < L * p := by nlinarith
      have h3 : N - D - 2 < p := lt_of_mul_lt_mul_left h2 hLpos.le
      omega
    · have h2 : L * p < L * (D + N + 1) := by nlinarith
      have h3 : p < D + N + 1 := lt_of_mul_lt_mul_left h2 hLpos.le
      omega
  · -- ε = −1: L p = r s + 2 j,  r c = c_p L − 2
    rw [h1] at hid hcdet
    constructor
    · have h2 : L * (N - D - 1) < L * p := by nlinarith
      have h3 : N - D - 1 < p := lt_of_mul_lt_mul_left h2 hLpos.le
      omega
    · have h2 : L * p < L * (D + N + 2) := by nlinarith
      have h3 : p < D + N + 2 := lt_of_mul_lt_mul_left h2 hLpos.le
      omega

end FLatticePaper.RootClassify
