import Mathlib.Tactic

/-! # Lattice bounds for the odd free V roots (VGap-style, integer arithmetic)

For an odd site `z = (z1, z2)` (so `z1 + z2` is odd) with `t = n z1 − d z2`, `s = (d + n) z1 + (d − n) z2`, and `T = d² + 2dn − n²`,
the identities `T z2 = n s − (d + n) t` and `T z1 = (d − n) t + d s` hold. Under the closed-polygon bounds of an odd site and the
V-spectrum bound `2 − d + n ≤ s ≤ d + n − 2`, the following hold:
* `2d − n − T < t` (`lower_t`): the multiple `T z2` lies in `((d+n−2) T, (d+n) T)`, so `z2 = d + n − 1`; then `s = (d+n)k − (d−n)`
  with `k = z1 + d − n` forces `k = 1`, and `z1 + z2 = 2n` is even.
* `t < d` (`lt_top`): `t = d` forces `T z2 ∈ (−2T, 0)`, so `z2 = −1`, and `n s = n (n − d)` contradicts `s ≥ 2 − d + n`.
* `t < 2n − d` (`lt_2n_sub_d`): `T z2 ∈ (−T, T)`, so `z2 = 0`, and then `(d+n) z1 = s ∈ (−(d+n), d+n)` gives `z1 = 0`: even.
* `n − T < t` (`gt_n_sub_T`): `t = n − T` forces `T z2 ∈ ((d+n−1) T, (d+n) T)`, so no integer `z2`. -/

namespace FLatticePaper.VLattice

theorem s_range {n d s : ℤ} (hnd : n + 2 ≤ d)
    (hs : (0 ≤ s ∧ s ≤ 2 * n) ∨ (2 - d + n ≤ s ∧ s ≤ d + n - 2)) : 2 - d + n ≤ s ∧ s ≤ d + n - 2 := by
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · constructor <;> omega
  · exact ⟨h1, h2⟩

/-- `2 d − n − T < t` for an odd site of the V cut. -/
theorem lower_t {n d z1 z2 t s : ℤ} (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hodd : (z1 + z2) % 2 = 1)
    (ht : t = n * z1 - d * z2) (hs : s = (d + n) * z1 + (d - n) * z2)
    (htlo : n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ t)
    (hslo : 2 - d + n ≤ s) (hshi : s ≤ d + n - 2) :
    2 * d - n - (d ^ 2 + 2 * d * n - n ^ 2) < t := by
  by_contra hc
  push Not at hc
  have hTpos : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hV : (d ^ 2 + 2 * d * n - n ^ 2) * z2 = n * s - (d + n) * t := by
    rw [ht, hs]; ring
  have hn0 : (0:ℤ) ≤ n := by omega
  have hdn0 : (0:ℤ) ≤ d + n := by omega
  have hlow : (d + n) * (d ^ 2 + 2 * d * n - n ^ 2) + (2 * n - 2 * d * n + 2 * n ^ 2 - 2 * d ^ 2)
      ≤ (d ^ 2 + 2 * d * n - n ^ 2) * z2 := by
    rw [hV]
    nlinarith [mul_le_mul_of_nonneg_left hslo hn0, mul_le_mul_of_nonneg_left hc hdn0]
  have hup : (d ^ 2 + 2 * d * n - n ^ 2) * z2 ≤ (d + n) * (d ^ 2 + 2 * d * n - n ^ 2) - 2 * n := by
    rw [hV]
    nlinarith [mul_le_mul_of_nonneg_left hshi hn0, mul_le_mul_of_nonneg_left htlo hdn0]
  have hz2a : d + n - 2 < z2 := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hTpos.le]
  have hz2b : z2 < d + n := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hTpos.le]
  have hz2 : z2 = d + n - 1 := by omega
  -- the second coordinate fixes `k = z1 + d − n`: `(d + n) k = s + (d − n)`
  have hk : (d + n) * (z1 + d - n) = s + (d - n) := by
    rw [hs, hz2]; ring
  have hk1 : 0 < z1 + d - n := by
    by_contra h
    push Not at h
    nlinarith
  have hk2 : z1 + d - n < 2 := by
    by_contra h
    push Not at h
    nlinarith
  have hk3 : z1 + d - n = 1 := by omega
  omega

/-- `t < d` for an odd site of the V cut. -/
theorem lt_top {n d z1 z2 t s : ℤ} (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (ht : t = n * z1 - d * z2) (hs : s = (d + n) * z1 + (d - n) * z2)
    (hthi : t ≤ d) (hslo : 2 - d + n ≤ s) (hshi : s ≤ d + n - 2) :
    t < d := by
  by_contra hc
  push Not at hc
  have htd : t = d := le_antisymm hthi hc
  have hTpos : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hV : (d ^ 2 + 2 * d * n - n ^ 2) * z2 = n * s - (d + n) * t := by
    rw [ht, hs]; ring
  have hn0 : (0:ℤ) ≤ n := by omega
  have hlow : 2 * n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ (d ^ 2 + 2 * d * n - n ^ 2) * z2 := by
    rw [hV, htd]
    nlinarith [mul_le_mul_of_nonneg_left hslo hn0]
  have hup : (d ^ 2 + 2 * d * n - n ^ 2) * z2 ≤ n ^ 2 - 2 * n - d ^ 2 := by
    rw [hV, htd]
    nlinarith [mul_le_mul_of_nonneg_left hshi hn0]
  have hz2a : -2 < z2 := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hTpos.le]
  have hz2b : z2 < 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hTpos.le]
  have hz2 : z2 = -1 := by omega
  rw [hz2] at hV
  -- then `n s = n (n − d)`, so `s = n − d`, contradicting `s ≥ 2 − d + n`
  have hns : n * s = n * (n - d) := by nlinarith
  have hs' : s = n - d := mul_left_cancel₀ (by omega : n ≠ 0) hns
  omega

/-- `2 n − d > t` for an odd site of the V cut: the source of the `η = −1` middle. -/
theorem lt_2n_sub_d {n d z1 z2 t s : ℤ} (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hodd : (z1 + z2) % 2 = 1)
    (ht : t = n * z1 - d * z2) (hs : s = (d + n) * z1 + (d - n) * z2)
    (htd : t ≤ d) (hslo : 2 - d + n ≤ s) (hshi : s ≤ d + n - 2) :
    t < 2 * n - d := by
  by_contra hc
  push Not at hc
  have hTpos : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hV : (d ^ 2 + 2 * d * n - n ^ 2) * z2 = n * s - (d + n) * t := by
    rw [ht, hs]; ring
  have hn0 : (0:ℤ) ≤ n := by omega
  have hdn0 : (0:ℤ) ≤ d + n := by omega
  have hlo : -(d ^ 2 + 2 * d * n - n ^ 2) < (d ^ 2 + 2 * d * n - n ^ 2) * z2 := by
    rw [hV]
    nlinarith [mul_le_mul_of_nonneg_left hslo hn0, mul_le_mul_of_nonneg_left htd hdn0]
  have hhi : (d ^ 2 + 2 * d * n - n ^ 2) * z2 < d ^ 2 + 2 * d * n - n ^ 2 := by
    rw [hV]
    nlinarith [mul_le_mul_of_nonneg_left hshi hn0, mul_le_mul_of_nonneg_left hc hdn0]
  have hz2a : -1 < z2 := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hTpos.le]
  have hz2b : z2 < 1 := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hTpos.le]
  have hz2 : z2 = 0 := by omega
  rw [hz2] at ht hs
  -- `s = (d + n) z1` with `|s| < d + n`, so `z1 = 0`, and then `z1 + z2` is even
  have hz1 : z1 = 0 := by
    rcases lt_trichotomy z1 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  subst hz1
  subst hz2
  simp at hodd

/-- `n − T < t` for an odd site of the V cut. -/
theorem gt_n_sub_T {n d z1 z2 t s : ℤ} (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (ht : t = n * z1 - d * z2) (hs : s = (d + n) * z1 + (d - n) * z2)
    (htlo : n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ t)
    (hslo : 2 - d + n ≤ s) (hshi : s ≤ d + n - 2) :
    n - (d ^ 2 + 2 * d * n - n ^ 2) < t := by
  by_contra hc
  push Not at hc
  have htn : t = n - (d ^ 2 + 2 * d * n - n ^ 2) := le_antisymm hc htlo
  have hTpos : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hV : (d ^ 2 + 2 * d * n - n ^ 2) * z2 = n * s - (d + n) * t := by
    rw [ht, hs]; ring
  have hn0 : (0:ℤ) ≤ n := by omega
  have hlow : (d + n - 1) * (d ^ 2 + 2 * d * n - n ^ 2) < (d ^ 2 + 2 * d * n - n ^ 2) * z2 := by
    rw [hV, htn]
    nlinarith [mul_le_mul_of_nonneg_left hslo hn0]
  have hup : (d ^ 2 + 2 * d * n - n ^ 2) * z2 < (d + n) * (d ^ 2 + 2 * d * n - n ^ 2) := by
    rw [hV, htn]
    nlinarith [mul_le_mul_of_nonneg_left hshi hn0]
  have hz2a : d + n - 1 < z2 := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hTpos.le]
  have hz2b : z2 < d + n := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hTpos.le]
  omega

/-- `s(z) ≤ d − n − 2` for an odd site `z` of the V cut whose upper neighbour `z + (0, 1)` is a free V root, in the regime `2n ≤ d`:
the freeness of `z + (0, 1) − (1, 0)` gives `t < 2n + d − T` or `s < 3n + 2 − d`; the first case with `s ≥ 3n + 2 − d` forces
`z2 = d + n − 1`, and then `(d + n) ∣ s + d − n` contradicts `2n + 2 ≤ s + d − n ≤ d + n − 2`. -/
theorem s_le_of_free_nb {n d z1 z2 t s : ℤ} (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hV : 2 * n ≤ d)
    (hnodd : n % 2 = 1) (hdodd : d % 2 = 1) (hodd : (z1 + z2) % 2 = 1) (hspar : s % 2 = 0)
    (ht : t = n * z1 - d * z2) (hs : s = (d + n) * z1 + (d - n) * z2)
    (htlo : n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ t)
    (hfree : t < 2 * n + d - (d ^ 2 + 2 * d * n - n ^ 2) ∨ s < 3 * n + 2 - d)
    (hnb : (0 ≤ s + d - n ∧ s + d - n ≤ 2 * n) ∨ (2 - d + n ≤ s + d - n ∧ s + d - n ≤ d + n - 2)) :
    s ≤ d - n - 2 := by
  by_contra hc
  push Not at hc
  have hsge : d - n ≤ s := by omega
  by_cases hA : s < 3 * n + 2 - d
  · omega
  push Not at hA
  have hfree' : t < 2 * n + d - (d ^ 2 + 2 * d * n - n ^ 2) := by
    rcases hfree with h | h
    · exact h
    · omega
  have hsnb : s ≤ 2 * n - 2 := by
    rcases hnb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · omega
  have hTpos : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hV' : (d ^ 2 + 2 * d * n - n ^ 2) * z2 = n * s - (d + n) * t := by
    rw [ht, hs]; ring
  have hn0 : (0:ℤ) ≤ n := by omega
  have hdn0 : (0:ℤ) ≤ d + n := by omega
  have hlow : (d + n - 2) * (d ^ 2 + 2 * d * n - n ^ 2) < (d ^ 2 + 2 * d * n - n ^ 2) * z2 := by
    rw [hV']
    nlinarith [mul_le_mul_of_nonneg_left hA hn0, mul_le_mul_of_nonneg_left hfree'.le hdn0]
  have hup : (d ^ 2 + 2 * d * n - n ^ 2) * z2 < (d + n) * (d ^ 2 + 2 * d * n - n ^ 2) := by
    rw [hV']
    nlinarith [mul_le_mul_of_nonneg_left hsnb hn0, mul_le_mul_of_nonneg_left htlo hdn0]
  have hz2a : d + n - 2 < z2 := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hTpos.le]
  have hz2b : z2 < d + n := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hTpos.le]
  have hz2 : z2 = d + n - 1 := by omega
  have hk : (d + n) * (z1 + d - n) = s + (d - n) := by
    rw [hs, hz2]; ring
  have hk1 : 0 < z1 + d - n := by
    by_contra h
    push Not at h
    nlinarith
  have hk2 : z1 + d - n < 1 := by
    by_contra h
    push Not at h
    nlinarith
  omega

end FLatticePaper.VLattice
