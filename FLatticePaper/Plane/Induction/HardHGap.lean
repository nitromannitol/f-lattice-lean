import Mathlib
import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.Binary
import FLatticePaper.Plane.Induction.S3FreeBoundary

namespace FLatticePaper.HardHGap

open FLatticePaper

theorem gap_arith_free {n d t s u : ℤ} (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d) (hdodd : d % 2 = 1)
    (hcop : IsCoprime d n)
    (hid : (d ^ 2 + 2 * d * n - n ^ 2) * u = n * s - (d + n) * t)
    (ht1 : 2 ≤ t) (ht2 : t ≤ d + n - 2) (htev : t % 2 = 0)
    (hs1 : d ^ 2 + 2 * d * n - n ^ 2 + 2 - 2 * d ≤ s) (hs2 : s ≤ d ^ 2 + 2 * d * n - n ^ 2 + 2 * n) : False := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hL : 0 < d + n := by omega
  have hu_up : u ≤ n := by
    by_contra h
    push Not at h
    have h1 : (d ^ 2 + 2 * d * n - n ^ 2) * (n + 1) ≤ (d ^ 2 + 2 * d * n - n ^ 2) * u :=
      mul_le_mul_of_nonneg_left (by omega) hT.le
    have h2 : n * s ≤ n * (d ^ 2 + 2 * d * n - n ^ 2 + 2 * n) := mul_le_mul_of_nonneg_left hs2 (by omega)
    have h3 : (d + n) * 2 ≤ (d + n) * t := mul_le_mul_of_nonneg_left ht1 hL.le
    nlinarith
  have hu_lo : n - 2 ≤ u := by
    by_contra h
    push Not at h
    have hu3 : u ≤ n - 3 := by omega
    have h1 : (d ^ 2 + 2 * d * n - n ^ 2) * u ≤ (d ^ 2 + 2 * d * n - n ^ 2) * (n - 3) :=
      mul_le_mul_of_nonneg_left hu3 hT.le
    have h2 : n * (d ^ 2 + 2 * d * n - n ^ 2 + 2 - 2 * d) ≤ n * s := mul_le_mul_of_nonneg_left hs1 (by omega)
    have h3 : (d + n) * t ≤ (d + n) * (d + n - 2) := mul_le_mul_of_nonneg_left ht2 hL.le
    nlinarith
  rcases (show u = n - 2 ∨ u = n - 1 ∨ u = n by omega) with hu | hu | hu
  · -- u = n - 2: n | d (t - 2d), so t = 2d + n c with c ≤ -1, which contradicts the lower bound on t
    subst hu
    have hdiv : n ∣ d * (t - 2 * d) :=
      ⟨s - t - (2 * d - n) * (n - 2) - d ^ 2, by linear_combination hid⟩
    have hcop' : IsCoprime n d := hcop.symm
    have hdt : n ∣ t - 2 * d := hcop'.dvd_of_dvd_mul_left hdiv
    obtain ⟨c, hc⟩ := hdt
    have hc1 : c ≤ -1 := by
      by_contra h
      push Not at h
      nlinarith
    have hlow : n * (d ^ 2 + 2 * d * n - n ^ 2 + 2 - 2 * d) ≤ n * s := mul_le_mul_of_nonneg_left hs1 (by omega)
    have hmul : (d + n) * n * c ≤ -((d + n) * n) := by nlinarith
    nlinarith
  · -- u = n - 1
    subst hu
    have h2 : n * (d ^ 2 + 2 * d * n - n ^ 2 + 2 - 2 * d) ≤ n * s := mul_le_mul_of_nonneg_left hs1 (by omega)
    have ht_lo : d - n + 1 ≤ t := by nlinarith
    have hdiv : n ∣ d * (t - d) := ⟨s - (d ^ 2 + 2 * d * n - n ^ 2) - t + 2 * d - n, by linear_combination hid⟩
    have hcop' : IsCoprime n d := hcop.symm
    have hdt : n ∣ t - d := hcop'.dvd_of_dvd_mul_left hdiv
    obtain ⟨c, hc⟩ := hdt
    have hc0 : c = 0 := by
      have hc1 : c < 1 := by nlinarith
      have hc2 : -1 < c := by nlinarith
      omega
    have : t = d := by
      rw [hc0] at hc
      linarith
    omega
  · -- u = n
    rw [hu] at hid
    have hsT : (d + n) * t = n * (s - (d ^ 2 + 2 * d * n - n ^ 2)) := by linear_combination hid
    have hbound : t < n := by
      have h2 : n * (s - (d ^ 2 + 2 * d * n - n ^ 2)) ≤ n * (2 * n) :=
        mul_le_mul_of_nonneg_left (by linarith) (by omega)
      have h3 : (d + n) * t ≤ 2 * n * n := by linarith
      have h4 : (2 * n + 2) * t ≤ (d + n) * t := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    have hdvd : n ∣ t * (d + n) := ⟨s - (d ^ 2 + 2 * d * n - n ^ 2), by rw [mul_comm t (d + n)]; exact hsT⟩
    have hcopL : IsCoprime n (d + n) := by
      obtain ⟨a, b, hab⟩ := hcop
      exact ⟨b - a, a, by linear_combination hab⟩
    have hnt : n ∣ t := hcopL.dvd_of_dvd_mul_right hdvd
    have hle : n ≤ t := Int.le_of_dvd (by omega) hnt
    omega

end FLatticePaper.HardHGap
