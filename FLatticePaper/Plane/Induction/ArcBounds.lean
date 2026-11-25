import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The H-arc bounds (step 2 of the H full star price span), by the integer identities

For a site `(z1, z2)` of a frame with child fraction `n/d` (`c = d − n`, `L = d + n`, `T = d² + 2dn − n²`):

  `t = n z1 − d z2`, `s = L z1 + c z2`,  with  `T z1 = d s + c t`  and  `T z2 = n s − L t`  (ring identities).

Given the closed-polygon `s`-range and `t`-spectrum of a `freeH` point, the two identities and integer rounding give
`1 ≤ z1 ≤ d`, `0 ≤ z2 ≤ n − 1` in the odd case, and `2 ≤ z1 ≤ d − 1`, `0 ≤ z2 ≤ n − 1` in the even case (parity excludes
`z1 ∈ {1, d}`). The vertex bounds on `s` follow: odd `L ≤ s ≤ T − c`, even `2L ≤ s ≤ T − 2d`. -/

namespace FLatticePaper.ArcBounds

/-- **Odd `freeH` points.** -/
theorem arc_odd_bounds (n d z1 z2 : ℤ) (hn : 0 < n) (hnd : n < d) (hd2 : 2 ≤ d - n)
    (ht1 : n ≤ n * z1 - d * z2) (ht2 : n * z1 - d * z2 ≤ d)
    (hs1 : 2 - (d - n) ≤ (d + n) * z1 + (d - n) * z2)
    (hs2 : (d + n) * z1 + (d - n) * z2 ≤ d ^ 2 + 2 * d * n - n ^ 2 + (d + n) - 2) :
    0 ≤ z2 ∧ z2 ≤ n - 1 ∧ 1 ≤ z1 ∧ z1 ≤ d ∧
      (d + n) ≤ (d + n) * z1 + (d - n) * z2 ∧
      (d + n) * z1 + (d - n) * z2 ≤ d ^ 2 + 2 * d * n - n ^ 2 - (d - n) := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hid2 : (d ^ 2 + 2 * d * n - n ^ 2) * z2 =
      n * ((d + n) * z1 + (d - n) * z2) - (d + n) * (n * z1 - d * z2) := by ring
  have hid1 : (d ^ 2 + 2 * d * n - n ^ 2) * z1 =
      d * ((d + n) * z1 + (d - n) * z2) + (d - n) * (n * z1 - d * z2) := by ring
  have hs1' : n * (2 - (d - n)) ≤ n * ((d + n) * z1 + (d - n) * z2) :=
    mul_le_mul_of_nonneg_left hs1 hn.le
  have hs2' : n * ((d + n) * z1 + (d - n) * z2) ≤ n * (d ^ 2 + 2 * d * n - n ^ 2 + (d + n) - 2) :=
    mul_le_mul_of_nonneg_left hs2 hn.le
  have ht2' : (d + n) * (n * z1 - d * z2) ≤ (d + n) * d :=
    mul_le_mul_of_nonneg_left ht2 (by linarith)
  have ht1' : (d + n) * n ≤ (d + n) * (n * z1 - d * z2) :=
    mul_le_mul_of_nonneg_left ht1 (by linarith)
  -- z2 ≥ 0
  have hz2lo : 0 ≤ z2 := by
    by_contra hcon
    have h1 : z2 ≤ -1 := by omega
    nlinarith
  -- z2 ≤ n − 1
  have hz2hi : z2 ≤ n - 1 := by
    by_contra hcon
    have h1 : n ≤ z2 := by omega
    nlinarith
  -- z1 ≥ 1 and z1 ≤ d, from n z1 = t + d z2
  have hn1 : n * z1 = (n * z1 - d * z2) + d * z2 := by ring
  have hz1lo : 1 ≤ z1 := by
    by_contra hcon
    have h1 : z1 ≤ 0 := by omega
    nlinarith
  have hz1hi : z1 ≤ d := by
    by_contra hcon
    have h1 : d + 1 ≤ z1 := by omega
    nlinarith
  refine ⟨hz2lo, hz2hi, hz1lo, hz1hi, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- **Even `freeH` points.** The parity `(z1 + z2)` even, with `d`, `n` odd, excludes `z1 ∈ {1, d}`. -/
theorem arc_even_bounds (n d z1 z2 : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d) (hdodd : d % 2 = 1) (hnodd : n % 2 = 1)
    (hpar : (z1 + z2) % 2 = 0)
    (ht1 : 2 ≤ n * z1 - d * z2) (ht2 : n * z1 - d * z2 ≤ (d + n) - 2)
    (hs1 : 0 ≤ (d + n) * z1 + (d - n) * z2)
    (hs2 : (d + n) * z1 + (d - n) * z2 ≤ d ^ 2 + 2 * d * n - n ^ 2 + 2 * n) :
    2 ≤ z1 ∧ z1 ≤ d - 1 ∧ 0 ≤ z2 ∧ z2 ≤ n - 1 ∧
      2 * (d + n) ≤ (d + n) * z1 + (d - n) * z2 ∧
      (d + n) * z1 + (d - n) * z2 ≤ d ^ 2 + 2 * d * n - n ^ 2 - 2 * d := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hid1 : (d ^ 2 + 2 * d * n - n ^ 2) * z1 =
      d * ((d + n) * z1 + (d - n) * z2) + (d - n) * (n * z1 - d * z2) := by ring
  -- z1 ≥ 1 and z1 ≤ d
  have hz1lo : 1 ≤ z1 := by
    by_contra hcon
    have h1 : z1 ≤ 0 := by omega
    nlinarith
  have hz1hi : z1 ≤ d := by
    by_contra hcon
    have h1 : d + 1 ≤ z1 := by omega
    nlinarith
  -- z1 ≠ 1 (parity: z2 odd; then t = n − d z2 would be out of the even spectrum)
  have hne1 : z1 ≠ 1 := by
    intro h1
    subst h1
    have hz2odd : z2 % 2 = 1 := by omega
    have hz2le : z2 ≤ 0 := by
      by_contra hcon
      have h2 : 1 ≤ z2 := by omega
      nlinarith
    have hz2le' : z2 ≤ -1 := by omega
    nlinarith
  -- z1 ≠ d (parity: z2 = n − 1 would make z1 + z2 = d + n − 1 odd)
  have hned : z1 ≠ d := by
    intro h1
    subst h1
    have hk1 : n - z2 ≤ 1 := by nlinarith
    have hk2 : 1 ≤ n - z2 := by nlinarith
    have hz2eq : z2 = n - 1 := by omega
    subst hz2eq
    omega
  have hz1a : 2 ≤ z1 := by omega
  have hz1b : z1 ≤ d - 1 := by omega
  -- z2 ≥ 0
  have hz2lo : 0 ≤ z2 := by
    by_contra hcon
    have h1 : z2 ≤ -1 := by omega
    nlinarith
  -- z2 ≤ n − 1
  have hz2hi : z2 ≤ n - 1 := by
    by_contra hcon
    have h1 : n ≤ z2 := by omega
    nlinarith
  refine ⟨hz1a, hz1b, hz2lo, hz2hi, ?_, ?_⟩
  · nlinarith
  · nlinarith

end FLatticePaper.ArcBounds
