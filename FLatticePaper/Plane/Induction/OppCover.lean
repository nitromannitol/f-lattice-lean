import FLatticePaper.Plane.Induction.OppWindow
import FLatticePaper.Plane.Induction.OppLattice

/-! # The coverage of the opposite points, case by case (generated).

For an opposite point `y = u + δ` (`u` a free V site with pieces `O`, `E0`, `E1`, `δ ∈ {−1,0,1}²`) the parent window of `σ(y)`
(from `OppWindow`) and the coverage of `s(y)` by the word's strips hold, except the two even corners excluded in `OppLattice`. -/

namespace FLatticePaper.OppCover

open FLatticePaper.OppWindow FLatticePaper.OppLattice

/-- `σ(u) ≡ u₁ + u₂` (mod 2) when `D ± N` are odd. -/
theorem sigma_parity {N D : ℤ} (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (u1 u2 : ℤ) :
    ((D + N) * u1 + (D - N) * u2) % 2 = (u1 + u2) % 2 := by
  obtain ⟨a, ha⟩ : ∃ a, D + N = 2 * a + 1 := ⟨(D + N) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, D - N = 2 * b + 1 := ⟨(D - N) / 2, by omega⟩
  rw [ha, hb]
  have e : (2 * a + 1) * u1 + (2 * b + 1) * u2 = 2 * (a * u1 + b * u2) + (u1 + u2) := by ring
  rw [e]
  generalize a * u1 + b * u2 = X
  omega

/-- The conjugate constant `C` is nonnegative. -/
theorem C_nonneg {n d D T C ε : ℤ} (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T) (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d)
    (hD2 : 2 ≤ D) (hCd : C * d = D * T + ε * (d - n)) (hε : ε = 1 ∨ ε = -1) : 0 ≤ C := by
  have hd0 : (0 : ℤ) < d := by linarith
  have hdn : (0 : ℤ) < d - n := by linarith
  have hn0 : (0 : ℤ) < n := by linarith
  have hDT : 0 ≤ (D - 2) * T := mul_nonneg (by linarith) hT0.le
  have hpos : 0 < D * T + ε * (d - n) := by
    rcases hε with rfl | rfl
    · nlinarith [mul_pos hd0 hdn, mul_pos hd0 hn0]
    · nlinarith [mul_pos hdn (show (0 : ℤ) < 2 * (d + n) - 1 by linarith), mul_pos hd0 hn0]
  have h2 : 0 < C * d := by linarith
  by_contra hc
  rw [not_le] at hc
  nlinarith

theorem cov_p0_O_az (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * (-1) - d * 0) (hy2 : n * u1 - d * u2 + n * (-1) - d * 0 ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 0 ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_O_az (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p0_O_za (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 0 - d * (-1)) (hy2 : n * u1 - d * u2 + n * 0 - d * (-1) ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * (-1) ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_O_za (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p0_O_zb (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 0 - d * 1) (hy2 : n * u1 - d * u2 + n * 0 - d * 1 ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 1 ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_O_zb (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p0_O_bz (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 1 - d * 0) (hy2 : n * u1 - d * u2 + n * 1 - d * 0 ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 0 ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_O_bz (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p0_E0_aa (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * (-1) - d * (-1)) (hy2 : n * u1 - d * u2 + n * (-1) - d * (-1) ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * (-1) ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_E0_aa (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩
  · by_contra hc
    rw [not_le] at hc
    have h1 : (d + n) * u1 + (d - n) * u2 < 1 := by linarith
    have hs : (d + n) * u1 + (d - n) * u2 = 0 := by
      generalize (d + n) * u1 + (d - n) * u2 = X at h1 hq1 ⊢
      omega
    have hye : (u1 - 1 + (u2 - 1)) % 2 = 0 := by omega
    exact no_plus_corner n d N D C T u1 u2 hT0 (by linarith [hCd]) (by linarith [hCn]) hn3 hnd hpD hpE hs hye (by linarith [hy1]) (by linarith [hy2])
  · linarith

theorem cov_p0_E0_ab (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * (-1) - d * 1) (hy2 : n * u1 - d * u2 + n * (-1) - d * 1 ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 1 ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_E0_ab (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p0_E0_zz (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 0 - d * 0) (hy2 : n * u1 - d * u2 + n * 0 - d * 0 ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 0 ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_E0_zz (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p0_E0_ba (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 1 - d * (-1)) (hy2 : n * u1 - d * u2 + n * 1 - d * (-1) ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * (-1) ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_E0_ba (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p0_E0_bb (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 1 - d * 1) (hy2 : n * u1 - d * u2 + n * 1 - d * 1 ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 1 ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_E0_bb (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p0_E1_aa (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * (-1) - d * (-1)) (hy2 : n * u1 - d * u2 + n * (-1) - d * (-1) ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * (-1) ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_E1_aa (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p0_E1_ab (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * (-1) - d * 1) (hy2 : n * u1 - d * u2 + n * (-1) - d * 1 ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 1 ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_E1_ab (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p0_E1_zz (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 0 - d * 0) (hy2 : n * u1 - d * u2 + n * 0 - d * 0 ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 0 ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_E1_zz (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p0_E1_ba (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 1 - d * (-1)) (hy2 : n * u1 - d * u2 + n * 1 - d * (-1) ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * (-1) ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_E1_ba (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p0_E1_bb (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 1 - d * 1) (hy2 : n * u1 - d * u2 + n * 1 - d * 1 ≤ 1)
    (hz1 : 2 * n - T + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ≤ -1) :
    (-1 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 1 ≤ 2 * D + 2 * N - 3) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p0_E1_bb (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_O_aa (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * (-1) - d * (-1)) (hy2 : n * u1 - d * u2 + n * (-1) - d * (-1) ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * (-1) ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_O_aa (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_O_ab (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * (-1) - d * 1) (hy2 : n * u1 - d * u2 + n * (-1) - d * 1 ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 1 ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_O_ab (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_O_zz (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 0 - d * 0) (hy2 : n * u1 - d * u2 + n * 0 - d * 0 ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 0 ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_O_zz (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_O_ba (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 1 - d * (-1)) (hy2 : n * u1 - d * u2 + n * 1 - d * (-1) ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * (-1) ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_O_ba (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_O_bb (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 1 - d * 1) (hy2 : n * u1 - d * u2 + n * 1 - d * 1 ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 1 ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_O_bb (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_E0_az (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * (-1) - d * 0) (hy2 : n * u1 - d * u2 + n * (-1) - d * 0 ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 0 ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_E0_az (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_E0_za (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 0 - d * (-1)) (hy2 : n * u1 - d * u2 + n * 0 - d * (-1) ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * (-1) ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_E0_za (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_E0_zb (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 0 - d * 1) (hy2 : n * u1 - d * u2 + n * 0 - d * 1 ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 1 ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_E0_zb (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_E0_bz (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 1 - d * 0) (hy2 : n * u1 - d * u2 + n * 1 - d * 0 ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 0 ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_E0_bz (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_E1_az (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * (-1) - d * 0) (hy2 : n * u1 - d * u2 + n * (-1) - d * 0 ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 0 ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_E1_az (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_E1_za (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 0 - d * (-1)) (hy2 : n * u1 - d * u2 + n * 0 - d * (-1) ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * (-1) ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_E1_za (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_E1_zb (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 0 - d * 1) (hy2 : n * u1 - d * u2 + n * 0 - d * 1 ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 1 ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_E1_zb (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_p1_E1_bz (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (1) * (d - n)) (hCn : C * n = N * T - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 1 - d * 0) (hy2 : n * u1 - d * u2 + n * 1 - d * 0 ≤ n - 1)
    (hz1 : d + n - 1 - T ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ≤ 1 - (d - n)) :
    (N - 3 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 0 ≤ 3 * D + N - 4) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inl rfl)
  have hW := win_p1_E1_bz (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_O_az (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * (-1) - d * 0) (hy2 : n * u1 - d * u2 + n * (-1) - d * 0 ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 0 ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_O_az (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_O_za (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 0 - d * (-1)) (hy2 : n * u1 - d * u2 + n * 0 - d * (-1) ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * (-1) ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_O_za (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_O_zb (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 0 - d * 1) (hy2 : n * u1 - d * u2 + n * 0 - d * 1 ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 1 ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_O_zb (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_O_bz (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 1 - d * 0) (hy2 : n * u1 - d * u2 + n * 1 - d * 0 ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 0 ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_O_bz (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_E0_aa (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * (-1) - d * (-1)) (hy2 : n * u1 - d * u2 + n * (-1) - d * (-1) ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * (-1) ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_E0_aa (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_E0_ab (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * (-1) - d * 1) (hy2 : n * u1 - d * u2 + n * (-1) - d * 1 ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 1 ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_E0_ab (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_E0_zz (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 0 - d * 0) (hy2 : n * u1 - d * u2 + n * 0 - d * 0 ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 0 ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_E0_zz (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_E0_ba (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 1 - d * (-1)) (hy2 : n * u1 - d * u2 + n * 1 - d * (-1) ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * (-1) ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_E0_ba (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_E0_bb (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 1 - d * 1) (hy2 : n * u1 - d * u2 + n * 1 - d * 1 ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 1 ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_E0_bb (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩
  · linarith
  · by_contra hc
    rw [not_le] at hc
    have h1 : 2 * n - 1 < (d + n) * u1 + (d - n) * u2 := by linarith
    have hs : (d + n) * u1 + (d - n) * u2 = 2 * n := by
      generalize (d + n) * u1 + (d - n) * u2 = X at h1 hq2 ⊢
      omega
    have hye : (u1 + 1 + (u2 + 1)) % 2 = 0 := by omega
    exact no_minus_corner n d N D C T u1 u2 hT0 (by linarith [hCd]) (by linarith [hCn]) hn3 hnd hpD hpE hs hye (by linarith [hy1]) (by linarith [hy2])

theorem cov_m0_E1_aa (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * (-1) - d * (-1)) (hy2 : n * u1 - d * u2 + n * (-1) - d * (-1) ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * (-1) ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_E1_aa (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_E1_ab (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * (-1) - d * 1) (hy2 : n * u1 - d * u2 + n * (-1) - d * 1 ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 1 ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_E1_ab (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_E1_zz (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 0 - d * 0) (hy2 : n * u1 - d * u2 + n * 0 - d * 0 ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 0 ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_E1_zz (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_E1_ba (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 1 - d * (-1)) (hy2 : n * u1 - d * u2 + n * 1 - d * (-1) ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * (-1) ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_E1_ba (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m0_E1_bb (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d + n - 1 - T ≤ n * u1 - d * u2 + n * 1 - d * 1) (hy2 : n * u1 - d * u2 + n * 1 - d * 1 ≤ 1)
    (hz1 : 2 * n + 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ≤ T - 1) :
    (3 - 2 * D ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 1 ≤ 2 * D + 2 * N + 1) ∧ (1 - 2 * d ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ≤ 2 * (d + n) - 1) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m0_E1_bb (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_O_aa (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * (-1) - d * (-1)) (hy2 : n * u1 - d * u2 + n * (-1) - d * (-1) ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * (-1) ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * (-1) ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_O_aa (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_O_ab (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * (-1) - d * 1) (hy2 : n * u1 - d * u2 + n * (-1) - d * 1 ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 1 ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 1 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_O_ab (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_O_zz (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 0 - d * 0) (hy2 : n * u1 - d * u2 + n * 0 - d * 0 ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 0 ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 0 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_O_zz (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_O_ba (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 1 - d * (-1)) (hy2 : n * u1 - d * u2 + n * 1 - d * (-1) ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * (-1) ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * (-1) ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_O_ba (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_O_bb (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 1)
    (hp1 : n - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d)
    (hq1 : 2 - d + n ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 1 - d * 1) (hy2 : n * u1 - d * u2 + n * 1 - d * 1 ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 1 ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 1 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 1 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_O_bb (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_E0_az (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * (-1) - d * 0) (hy2 : n * u1 - d * u2 + n * (-1) - d * 0 ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 0 ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_E0_az (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_E0_za (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 0 - d * (-1)) (hy2 : n * u1 - d * u2 + n * 0 - d * (-1) ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * (-1) ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_E0_za (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_E0_zb (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 0 - d * 1) (hy2 : n * u1 - d * u2 + n * 0 - d * 1 ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 1 ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_E0_zb (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_E0_bz (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ d + n - 2)
    (hq1 : 0 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ 2 * n)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 1 - d * 0) (hy2 : n * u1 - d * u2 + n * 1 - d * 0 ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 0 ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_E0_bz (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_E1_az (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * (-1) - d * 0) (hy2 : n * u1 - d * u2 + n * (-1) - d * 0 ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * (-1) + (D - N) * 0 ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * (-1) + (d - n) * 0 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_E1_az (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_E1_za (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 0 - d * (-1)) (hy2 : n * u1 - d * u2 + n * 0 - d * (-1) ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1)) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * (-1) ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * (-1) ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * (-1) ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_E1_za (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_E1_zb (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 0 - d * 1) (hy2 : n * u1 - d * u2 + n * 0 - d * 1 ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 1 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 0 + (D - N) * 1 ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 0 + (d - n) * 1 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_E1_zb (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

theorem cov_m1_E1_bz (N D n d T C u1 u2 : ℤ) (hT : T = d * d + 2 * d * n - n * n) (hT0 : 0 < T)
    (hCd : C * d = D * T + (-1) * (d - n)) (hCn : C * n = N * T - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
    (hσ : T * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hu : (u1 + u2) % 2 = 0)
    (hp1 : 2 - T ≤ n * u1 - d * u2) (hp2 : n * u1 - d * u2 ≤ 2 * n - T - 1)
    (hq1 : 2 * n + 2 ≤ (d + n) * u1 + (d - n) * u2) (hq2 : (d + n) * u1 + (d - n) * u2 ≤ d + n - 2)
    (hy1 : d - T + 1 ≤ n * u1 - d * u2 + n * 1 - d * 0) (hy2 : n * u1 - d * u2 + n * 1 - d * 0 ≤ n - 1)
    (hz1 : d + n - 1 ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0) (hz2 : (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ≤ T + 1 - (d - n)) :
    (N - 3 * D + 4 ≤ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 0 ∧ (D + N) * u1 + (D - N) * u2 + (D + N) * 1 + (D - N) * 0 ≤ 3 * D + N) ∧ (2 - 3 * d + n ≤ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ∧ (d + n) * u1 + (d - n) * u2 + (d + n) * 1 + (d - n) * 0 ≤ 3 * d + n - 2) := by
  have hσp : ((D + N) * u1 + (D - N) * u2) % 2 = 0 := by rw [sigma_parity hpD hpE]; exact hu
  have hC0 : 0 ≤ C := C_nonneg hT hT0 hn3 hnd hD2 hCd (Or.inr rfl)
  have hW := win_m1_E1_bz (N := N) (D := D) (n := n) (d := d) (T := T) (C := C) (tu := n * u1 - d * u2) (su := (d + n) * u1 + (d - n) * u2) (σu := (D + N) * u1 + (D - N) * u2)
    hT0 hC0 hCd hCn hCL hσ hT hn3 hnd hD2 hN0 hpD hpE hσp hp1 hp2 hq1 hq2 hy1 hy2 hz1 hz2
  refine ⟨hW, ?_, ?_⟩ <;> linarith

end FLatticePaper.OppCover
