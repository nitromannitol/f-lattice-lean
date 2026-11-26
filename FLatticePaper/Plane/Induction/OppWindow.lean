import Mathlib.Tactic

/-! # The σ-windows of the opposite collar (generated; box method with parity).
For a free V site `u` (grades `t`, `s`, `σ`) and `δ = (k, m)`, the point `y = u + δ` lies in the strict box of the
opposite collar. The parent window of `σ(y)` follows from the box corners, the identity `T σ = 2 ε t + C s`, and parity.
The lower window bound is first obtained as `σ(y) > Wlo − 2` (a linear fact), and parity gives `σ(y) ≥ Wlo`. -/

namespace FLatticePaper.OppWindow

/-! The family shares one binder list (the parent data, the strict box and the piece); each lemma uses a subset of it,
so the unused-variable linter is disabled for this generated module. -/
set_option linter.unusedVariables false

theorem win_p0_O_az (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * (-1) - d * 0)
     (hy2 : tu + n * (-1) - d * 0 ≤ 1) (hz1 : 2 * n - T + 1 ≤ su + (d + n) * (-1) + (d - n) * 0)
     (hz2 : su + (d + n) * (-1) + (d - n) * 0 ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * (-1) + (D - N) * 0 ∧ σu + (D + N) * (-1) + (D - N) * 0 ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * 0) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * 0) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * 0) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * (-1) + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * (-1) + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_O_za (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * 0 - d * (-1))
     (hy2 : tu + n * 0 - d * (-1) ≤ 1) (hz1 : 2 * n - T + 1 ≤ su + (d + n) * 0 + (d - n) * (-1))
     (hz2 : su + (d + n) * 0 + (d - n) * (-1) ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * 0 + (D - N) * (-1) ∧ σu + (D + N) * 0 + (D - N) * (-1) ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * (-1)) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * (-1)) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * (-1)) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 0 + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 0 + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_O_zb (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * 0 - d * 1)
     (hy2 : tu + n * 0 - d * 1 ≤ 1) (hz1 : 2 * n - T + 1 ≤ su + (d + n) * 0 + (d - n) * 1)
     (hz2 : su + (d + n) * 0 + (d - n) * 1 ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * 0 + (D - N) * 1 ∧ σu + (D + N) * 0 + (D - N) * 1 ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * 1) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * 1) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * 1) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 0 + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 0 + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_O_bz (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * 1 - d * 0)
     (hy2 : tu + n * 1 - d * 0 ≤ 1) (hz1 : 2 * n - T + 1 ≤ su + (d + n) * 1 + (d - n) * 0)
     (hz2 : su + (d + n) * 1 + (d - n) * 0 ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * 1 + (D - N) * 0 ∧ σu + (D + N) * 1 + (D - N) * 0 ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * 0) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * 0) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * 0) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 1 + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 1 + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_E0_aa (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d + n - 1 - T ≤ tu + n * (-1) - d * (-1)) (hy2 : tu + n * (-1) - d * (-1) ≤ 1)
     (hz1 : 2 * n - T + 1 ≤ su + (d + n) * (-1) + (d - n) * (-1))
     (hz2 : su + (d + n) * (-1) + (d - n) * (-1) ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * (-1) + (D - N) * (-1) ∧ σu + (D + N) * (-1) + (D - N) * (-1) ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * (-1)) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * (-1)) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * (-1)) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * (-1) + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * (-1) + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_E0_ab (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d + n - 1 - T ≤ tu + n * (-1) - d * 1) (hy2 : tu + n * (-1) - d * 1 ≤ 1)
     (hz1 : 2 * n - T + 1 ≤ su + (d + n) * (-1) + (d - n) * 1)
     (hz2 : su + (d + n) * (-1) + (d - n) * 1 ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * (-1) + (D - N) * 1 ∧ σu + (D + N) * (-1) + (D - N) * 1 ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * 1) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * 1) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * 1) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * (-1) + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * (-1) + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_E0_zz (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d + n - 1 - T ≤ tu + n * 0 - d * 0) (hy2 : tu + n * 0 - d * 0 ≤ 1)
     (hz1 : 2 * n - T + 1 ≤ su + (d + n) * 0 + (d - n) * 0)
     (hz2 : su + (d + n) * 0 + (d - n) * 0 ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * 0 + (D - N) * 0 ∧ σu + (D + N) * 0 + (D - N) * 0 ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * 0) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * 0) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * 0) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 0 + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 0 + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_E0_ba (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d + n - 1 - T ≤ tu + n * 1 - d * (-1)) (hy2 : tu + n * 1 - d * (-1) ≤ 1)
     (hz1 : 2 * n - T + 1 ≤ su + (d + n) * 1 + (d - n) * (-1))
     (hz2 : su + (d + n) * 1 + (d - n) * (-1) ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * 1 + (D - N) * (-1) ∧ σu + (D + N) * 1 + (D - N) * (-1) ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * (-1)) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * (-1)) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * (-1)) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 1 + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 1 + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_E0_bb (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d + n - 1 - T ≤ tu + n * 1 - d * 1) (hy2 : tu + n * 1 - d * 1 ≤ 1)
     (hz1 : 2 * n - T + 1 ≤ su + (d + n) * 1 + (d - n) * 1)
     (hz2 : su + (d + n) * 1 + (d - n) * 1 ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * 1 + (D - N) * 1 ∧ σu + (D + N) * 1 + (D - N) * 1 ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * 1) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * 1) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * 1) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 1 + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 1 + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_E1_aa (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * (-1) - d * (-1))
     (hy2 : tu + n * (-1) - d * (-1) ≤ 1)
     (hz1 : 2 * n - T + 1 ≤ su + (d + n) * (-1) + (d - n) * (-1))
     (hz2 : su + (d + n) * (-1) + (d - n) * (-1) ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * (-1) + (D - N) * (-1) ∧ σu + (D + N) * (-1) + (D - N) * (-1) ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * (-1)) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * (-1)) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * (-1)) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * (-1) + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * (-1) + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_E1_ab (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * (-1) - d * 1)
     (hy2 : tu + n * (-1) - d * 1 ≤ 1) (hz1 : 2 * n - T + 1 ≤ su + (d + n) * (-1) + (d - n) * 1)
     (hz2 : su + (d + n) * (-1) + (d - n) * 1 ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * (-1) + (D - N) * 1 ∧ σu + (D + N) * (-1) + (D - N) * 1 ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * 1) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * 1) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * 1) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * (-1) + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * (-1) + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_E1_zz (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * 0 - d * 0)
     (hy2 : tu + n * 0 - d * 0 ≤ 1) (hz1 : 2 * n - T + 1 ≤ su + (d + n) * 0 + (d - n) * 0)
     (hz2 : su + (d + n) * 0 + (d - n) * 0 ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * 0 + (D - N) * 0 ∧ σu + (D + N) * 0 + (D - N) * 0 ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * 0) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * 0) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * 0) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 0 + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 0 + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_E1_ba (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * 1 - d * (-1))
     (hy2 : tu + n * 1 - d * (-1) ≤ 1) (hz1 : 2 * n - T + 1 ≤ su + (d + n) * 1 + (d - n) * (-1))
     (hz2 : su + (d + n) * 1 + (d - n) * (-1) ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * 1 + (D - N) * (-1) ∧ σu + (D + N) * 1 + (D - N) * (-1) ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * (-1)) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * (-1)) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * (-1)) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 1 + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 1 + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p0_E1_bb (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * 1 - d * 1)
     (hy2 : tu + n * 1 - d * 1 ≤ 1) (hz1 : 2 * n - T + 1 ≤ su + (d + n) * 1 + (d - n) * 1)
     (hz2 : su + (d + n) * 1 + (d - n) * 1 ≤ -1) :
    -1 - 2 * D ≤ σu + (D + N) * 1 + (D - N) * 1 ∧ σu + (D + N) * 1 + (D - N) * 1 ≤ 2 * D + 2 * N - 3 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * 1) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * 1) - ((-1 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * 1) - ((-1 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 1 + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N - 3) + 1 - (σu + (D + N) * 1 + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_O_aa (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * (-1) - d * (-1))
     (hy2 : tu + n * (-1) - d * (-1) ≤ n - 1)
     (hz1 : d + n - 1 - T ≤ su + (d + n) * (-1) + (d - n) * (-1))
     (hz2 : su + (d + n) * (-1) + (d - n) * (-1) ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * (-1) + (D - N) * (-1) ∧ σu + (D + N) * (-1) + (D - N) * (-1) ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * (-1)) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * (-1)) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * (-1)) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * (-1) + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * (-1) + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_O_ab (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * (-1) - d * 1)
     (hy2 : tu + n * (-1) - d * 1 ≤ n - 1) (hz1 : d + n - 1 - T ≤ su + (d + n) * (-1) + (d - n) * 1)
     (hz2 : su + (d + n) * (-1) + (d - n) * 1 ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * (-1) + (D - N) * 1 ∧ σu + (D + N) * (-1) + (D - N) * 1 ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * 1) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * 1) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * 1) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * (-1) + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * (-1) + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_O_zz (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * 0 - d * 0)
     (hy2 : tu + n * 0 - d * 0 ≤ n - 1) (hz1 : d + n - 1 - T ≤ su + (d + n) * 0 + (d - n) * 0)
     (hz2 : su + (d + n) * 0 + (d - n) * 0 ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * 0 + (D - N) * 0 ∧ σu + (D + N) * 0 + (D - N) * 0 ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * 0) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * 0) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * 0) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * 0 + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * 0 + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_O_ba (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * 1 - d * (-1))
     (hy2 : tu + n * 1 - d * (-1) ≤ n - 1) (hz1 : d + n - 1 - T ≤ su + (d + n) * 1 + (d - n) * (-1))
     (hz2 : su + (d + n) * 1 + (d - n) * (-1) ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * 1 + (D - N) * (-1) ∧ σu + (D + N) * 1 + (D - N) * (-1) ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * (-1)) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * (-1)) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * (-1)) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * 1 + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * 1 + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_O_bb (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * 1 - d * 1)
     (hy2 : tu + n * 1 - d * 1 ≤ n - 1) (hz1 : d + n - 1 - T ≤ su + (d + n) * 1 + (d - n) * 1)
     (hz2 : su + (d + n) * 1 + (d - n) * 1 ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * 1 + (D - N) * 1 ∧ σu + (D + N) * 1 + (D - N) * 1 ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * 1) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * 1) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * 1) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * 1 + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * 1 + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_E0_az (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d - T + 1 ≤ tu + n * (-1) - d * 0) (hy2 : tu + n * (-1) - d * 0 ≤ n - 1)
     (hz1 : d + n - 1 - T ≤ su + (d + n) * (-1) + (d - n) * 0)
     (hz2 : su + (d + n) * (-1) + (d - n) * 0 ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * (-1) + (D - N) * 0 ∧ σu + (D + N) * (-1) + (D - N) * 0 ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * 0) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * 0) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * 0) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * (-1) + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * (-1) + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_E0_za (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d - T + 1 ≤ tu + n * 0 - d * (-1)) (hy2 : tu + n * 0 - d * (-1) ≤ n - 1)
     (hz1 : d + n - 1 - T ≤ su + (d + n) * 0 + (d - n) * (-1))
     (hz2 : su + (d + n) * 0 + (d - n) * (-1) ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * 0 + (D - N) * (-1) ∧ σu + (D + N) * 0 + (D - N) * (-1) ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * (-1)) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * (-1)) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * (-1)) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * 0 + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * 0 + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_E0_zb (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d - T + 1 ≤ tu + n * 0 - d * 1) (hy2 : tu + n * 0 - d * 1 ≤ n - 1)
     (hz1 : d + n - 1 - T ≤ su + (d + n) * 0 + (d - n) * 1)
     (hz2 : su + (d + n) * 0 + (d - n) * 1 ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * 0 + (D - N) * 1 ∧ σu + (D + N) * 0 + (D - N) * 1 ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * 1) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * 1) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * 1) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * 0 + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * 0 + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_E0_bz (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d - T + 1 ≤ tu + n * 1 - d * 0) (hy2 : tu + n * 1 - d * 0 ≤ n - 1)
     (hz1 : d + n - 1 - T ≤ su + (d + n) * 1 + (d - n) * 0)
     (hz2 : su + (d + n) * 1 + (d - n) * 0 ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * 1 + (D - N) * 0 ∧ σu + (D + N) * 1 + (D - N) * 0 ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * 0) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * 0) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * 0) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * 1 + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * 1 + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_E1_az (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * (-1) - d * 0)
     (hy2 : tu + n * (-1) - d * 0 ≤ n - 1) (hz1 : d + n - 1 - T ≤ su + (d + n) * (-1) + (d - n) * 0)
     (hz2 : su + (d + n) * (-1) + (d - n) * 0 ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * (-1) + (D - N) * 0 ∧ σu + (D + N) * (-1) + (D - N) * 0 ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * 0) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * 0) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * 0) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * (-1) + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * (-1) + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_E1_za (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * 0 - d * (-1))
     (hy2 : tu + n * 0 - d * (-1) ≤ n - 1) (hz1 : d + n - 1 - T ≤ su + (d + n) * 0 + (d - n) * (-1))
     (hz2 : su + (d + n) * 0 + (d - n) * (-1) ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * 0 + (D - N) * (-1) ∧ σu + (D + N) * 0 + (D - N) * (-1) ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * (-1)) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * (-1)) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * (-1)) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * 0 + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * 0 + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_E1_zb (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * 0 - d * 1)
     (hy2 : tu + n * 0 - d * 1 ≤ n - 1) (hz1 : d + n - 1 - T ≤ su + (d + n) * 0 + (d - n) * 1)
     (hz2 : su + (d + n) * 0 + (d - n) * 1 ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * 0 + (D - N) * 1 ∧ σu + (D + N) * 0 + (D - N) * 1 ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * 1) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * 1) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * 1) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * 0 + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * 0 + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_p1_E1_bz (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (1) * (d - n))
     (hCn : C * n = N * T - (1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (1) * n)
     (hσ : T * σu = 2 * (1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * 1 - d * 0)
     (hy2 : tu + n * 1 - d * 0 ≤ n - 1) (hz1 : d + n - 1 - T ≤ su + (d + n) * 1 + (d - n) * 0)
     (hz2 : su + (d + n) * 1 + (d - n) * 0 ≤ 1 - (d - n)) :
    N - 3 * D ≤ σu + (D + N) * 1 + (D - N) * 0 ∧ σu + (D + N) * 1 + (D - N) * 0 ≤ 3 * D + N - 4 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * 0) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * 0) - ((N - 3 * D) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * 0) - ((N - 3 * D) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N - 4) + 2 - (σu + (D + N) * 1 + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (3 * D + N - 4) + 2 - (σu + (D + N) * 1 + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_O_az (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * (-1) - d * 0)
     (hy2 : tu + n * (-1) - d * 0 ≤ 1) (hz1 : 2 * n + 1 ≤ su + (d + n) * (-1) + (d - n) * 0)
     (hz2 : su + (d + n) * (-1) + (d - n) * 0 ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * (-1) + (D - N) * 0 ∧ σu + (D + N) * (-1) + (D - N) * 0 ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * 0) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * 0) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * 0) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * (-1) + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * (-1) + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_O_za (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * 0 - d * (-1))
     (hy2 : tu + n * 0 - d * (-1) ≤ 1) (hz1 : 2 * n + 1 ≤ su + (d + n) * 0 + (d - n) * (-1))
     (hz2 : su + (d + n) * 0 + (d - n) * (-1) ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * 0 + (D - N) * (-1) ∧ σu + (D + N) * 0 + (D - N) * (-1) ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * (-1)) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * (-1)) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * (-1)) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 0 + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 0 + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_O_zb (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * 0 - d * 1)
     (hy2 : tu + n * 0 - d * 1 ≤ 1) (hz1 : 2 * n + 1 ≤ su + (d + n) * 0 + (d - n) * 1)
     (hz2 : su + (d + n) * 0 + (d - n) * 1 ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * 0 + (D - N) * 1 ∧ σu + (D + N) * 0 + (D - N) * 1 ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * 1) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * 1) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * 1) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 0 + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 0 + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_O_bz (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * 1 - d * 0)
     (hy2 : tu + n * 1 - d * 0 ≤ 1) (hz1 : 2 * n + 1 ≤ su + (d + n) * 1 + (d - n) * 0)
     (hz2 : su + (d + n) * 1 + (d - n) * 0 ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * 1 + (D - N) * 0 ∧ σu + (D + N) * 1 + (D - N) * 0 ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * 0) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * 0) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * 0) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 1 + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 1 + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_E0_aa (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d + n - 1 - T ≤ tu + n * (-1) - d * (-1)) (hy2 : tu + n * (-1) - d * (-1) ≤ 1)
     (hz1 : 2 * n + 1 ≤ su + (d + n) * (-1) + (d - n) * (-1))
     (hz2 : su + (d + n) * (-1) + (d - n) * (-1) ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * (-1) + (D - N) * (-1) ∧ σu + (D + N) * (-1) + (D - N) * (-1) ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * (-1)) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * (-1)) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * (-1)) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * (-1) + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * (-1) + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_E0_ab (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d + n - 1 - T ≤ tu + n * (-1) - d * 1) (hy2 : tu + n * (-1) - d * 1 ≤ 1)
     (hz1 : 2 * n + 1 ≤ su + (d + n) * (-1) + (d - n) * 1)
     (hz2 : su + (d + n) * (-1) + (d - n) * 1 ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * (-1) + (D - N) * 1 ∧ σu + (D + N) * (-1) + (D - N) * 1 ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * 1) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * 1) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * 1) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * (-1) + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * (-1) + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_E0_zz (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d + n - 1 - T ≤ tu + n * 0 - d * 0) (hy2 : tu + n * 0 - d * 0 ≤ 1)
     (hz1 : 2 * n + 1 ≤ su + (d + n) * 0 + (d - n) * 0)
     (hz2 : su + (d + n) * 0 + (d - n) * 0 ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * 0 + (D - N) * 0 ∧ σu + (D + N) * 0 + (D - N) * 0 ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * 0) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * 0) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * 0) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 0 + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 0 + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_E0_ba (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d + n - 1 - T ≤ tu + n * 1 - d * (-1)) (hy2 : tu + n * 1 - d * (-1) ≤ 1)
     (hz1 : 2 * n + 1 ≤ su + (d + n) * 1 + (d - n) * (-1))
     (hz2 : su + (d + n) * 1 + (d - n) * (-1) ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * 1 + (D - N) * (-1) ∧ σu + (D + N) * 1 + (D - N) * (-1) ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * (-1)) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * (-1)) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * (-1)) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 1 + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 1 + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_E0_bb (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d + n - 1 - T ≤ tu + n * 1 - d * 1) (hy2 : tu + n * 1 - d * 1 ≤ 1)
     (hz1 : 2 * n + 1 ≤ su + (d + n) * 1 + (d - n) * 1)
     (hz2 : su + (d + n) * 1 + (d - n) * 1 ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * 1 + (D - N) * 1 ∧ σu + (D + N) * 1 + (D - N) * 1 ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * 1) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * 1) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * 1) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 1 + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 1 + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_E1_aa (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * (-1) - d * (-1))
     (hy2 : tu + n * (-1) - d * (-1) ≤ 1) (hz1 : 2 * n + 1 ≤ su + (d + n) * (-1) + (d - n) * (-1))
     (hz2 : su + (d + n) * (-1) + (d - n) * (-1) ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * (-1) + (D - N) * (-1) ∧ σu + (D + N) * (-1) + (D - N) * (-1) ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * (-1)) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * (-1)) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * (-1)) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * (-1) + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * (-1) + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_E1_ab (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * (-1) - d * 1)
     (hy2 : tu + n * (-1) - d * 1 ≤ 1) (hz1 : 2 * n + 1 ≤ su + (d + n) * (-1) + (d - n) * 1)
     (hz2 : su + (d + n) * (-1) + (d - n) * 1 ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * (-1) + (D - N) * 1 ∧ σu + (D + N) * (-1) + (D - N) * 1 ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * 1) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * 1) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * 1) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * (-1) + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * (-1) + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_E1_zz (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * 0 - d * 0)
     (hy2 : tu + n * 0 - d * 0 ≤ 1) (hz1 : 2 * n + 1 ≤ su + (d + n) * 0 + (d - n) * 0)
     (hz2 : su + (d + n) * 0 + (d - n) * 0 ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * 0 + (D - N) * 0 ∧ σu + (D + N) * 0 + (D - N) * 0 ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * 0) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * 0) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * 0) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 0 + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 0 + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_E1_ba (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * 1 - d * (-1))
     (hy2 : tu + n * 1 - d * (-1) ≤ 1) (hz1 : 2 * n + 1 ≤ su + (d + n) * 1 + (d - n) * (-1))
     (hz2 : su + (d + n) * 1 + (d - n) * (-1) ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * 1 + (D - N) * (-1) ∧ σu + (D + N) * 1 + (D - N) * (-1) ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * (-1)) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * (-1)) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * (-1)) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 1 + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 1 + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m0_E1_bb (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d + n - 1 - T ≤ tu + n * 1 - d * 1)
     (hy2 : tu + n * 1 - d * 1 ≤ 1) (hz1 : 2 * n + 1 ≤ su + (d + n) * 1 + (d - n) * 1)
     (hz2 : su + (d + n) * 1 + (d - n) * 1 ≤ T - 1) :
    3 - 2 * D ≤ σu + (D + N) * 1 + (D - N) * 1 ∧ σu + (D + N) * 1 + (D - N) * 1 ≤ 2 * D + 2 * N + 1 := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * 1) % 2 = 0 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * 1) - ((3 - 2 * D) - 1)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * 1) - ((3 - 2 * D) - 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 1 + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (2 * D + 2 * N + 1) + 1 - (σu + (D + N) * 1 + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_O_aa (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * (-1) - d * (-1))
     (hy2 : tu + n * (-1) - d * (-1) ≤ n - 1)
     (hz1 : d + n - 1 ≤ su + (d + n) * (-1) + (d - n) * (-1))
     (hz2 : su + (d + n) * (-1) + (d - n) * (-1) ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * (-1) + (D - N) * (-1) ∧ σu + (D + N) * (-1) + (D - N) * (-1) ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * (-1)) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * (-1)) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * (-1)) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * (-1) + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * (-1) + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_O_ab (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * (-1) - d * 1)
     (hy2 : tu + n * (-1) - d * 1 ≤ n - 1) (hz1 : d + n - 1 ≤ su + (d + n) * (-1) + (d - n) * 1)
     (hz2 : su + (d + n) * (-1) + (d - n) * 1 ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * (-1) + (D - N) * 1 ∧ σu + (D + N) * (-1) + (D - N) * 1 ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * 1) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * 1) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * 1) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * (-1) + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * (-1) + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_O_zz (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * 0 - d * 0)
     (hy2 : tu + n * 0 - d * 0 ≤ n - 1) (hz1 : d + n - 1 ≤ su + (d + n) * 0 + (d - n) * 0)
     (hz2 : su + (d + n) * 0 + (d - n) * 0 ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * 0 + (D - N) * 0 ∧ σu + (D + N) * 0 + (D - N) * 0 ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * 0) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * 0) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * 0) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * 0 + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * 0 + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_O_ba (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * 1 - d * (-1))
     (hy2 : tu + n * 1 - d * (-1) ≤ n - 1) (hz1 : d + n - 1 ≤ su + (d + n) * 1 + (d - n) * (-1))
     (hz2 : su + (d + n) * 1 + (d - n) * (-1) ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * 1 + (D - N) * (-1) ∧ σu + (D + N) * 1 + (D - N) * (-1) ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * (-1)) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * (-1)) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * (-1)) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * 1 + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * 1 + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_O_bb (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 1) (hp1 : n - T ≤ tu) (hp2 : tu ≤ d) (hq1 : 2 - d + n ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * 1 - d * 1)
     (hy2 : tu + n * 1 - d * 1 ≤ n - 1) (hz1 : d + n - 1 ≤ su + (d + n) * 1 + (d - n) * 1)
     (hz2 : su + (d + n) * 1 + (d - n) * 1 ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * 1 + (D - N) * 1 ∧ σu + (D + N) * 1 + (D - N) * 1 ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (2 - d + n)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * 1) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * 1) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * 1) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * 1 + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * 1 + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_E0_az (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d - T + 1 ≤ tu + n * (-1) - d * 0) (hy2 : tu + n * (-1) - d * 0 ≤ n - 1)
     (hz1 : d + n - 1 ≤ su + (d + n) * (-1) + (d - n) * 0)
     (hz2 : su + (d + n) * (-1) + (d - n) * 0 ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * (-1) + (D - N) * 0 ∧ σu + (D + N) * (-1) + (D - N) * 0 ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * 0) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * 0) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * 0) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * (-1) + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * (-1) + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_E0_za (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d - T + 1 ≤ tu + n * 0 - d * (-1)) (hy2 : tu + n * 0 - d * (-1) ≤ n - 1)
     (hz1 : d + n - 1 ≤ su + (d + n) * 0 + (d - n) * (-1))
     (hz2 : su + (d + n) * 0 + (d - n) * (-1) ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * 0 + (D - N) * (-1) ∧ σu + (D + N) * 0 + (D - N) * (-1) ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * (-1)) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * (-1)) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * (-1)) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * 0 + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * 0 + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_E0_zb (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d - T + 1 ≤ tu + n * 0 - d * 1) (hy2 : tu + n * 0 - d * 1 ≤ n - 1)
     (hz1 : d + n - 1 ≤ su + (d + n) * 0 + (d - n) * 1)
     (hz2 : su + (d + n) * 0 + (d - n) * 1 ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * 0 + (D - N) * 1 ∧ σu + (D + N) * 0 + (D - N) * 1 ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * 1) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * 1) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * 1) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * 0 + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * 0 + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_E0_bz (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ d + n - 2) (hq1 : 0 ≤ su) (hq2 : su ≤ 2 * n)
     (hy1 : d - T + 1 ≤ tu + n * 1 - d * 0) (hy2 : tu + n * 1 - d * 0 ≤ n - 1)
     (hz1 : d + n - 1 ≤ su + (d + n) * 1 + (d - n) * 0)
     (hz2 : su + (d + n) * 1 + (d - n) * 0 ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * 1 + (D - N) * 0 ∧ σu + (D + N) * 1 + (D - N) * 0 ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (0)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((2 * n) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * 0) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * 0) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * 0) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * 1 + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * 1 + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_E1_az (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * (-1) - d * 0)
     (hy2 : tu + n * (-1) - d * 0 ≤ n - 1) (hz1 : d + n - 1 ≤ su + (d + n) * (-1) + (d - n) * 0)
     (hz2 : su + (d + n) * (-1) + (d - n) * 0 ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * (-1) + (D - N) * 0 ∧ σu + (D + N) * (-1) + (D - N) * 0 ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * (-1) + (D - N) * 0) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * (-1) + (D - N) * 0) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * (-1) + (D - N) * 0) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * (-1) + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * (-1) + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_E1_za (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * 0 - d * (-1))
     (hy2 : tu + n * 0 - d * (-1) ≤ n - 1) (hz1 : d + n - 1 ≤ su + (d + n) * 0 + (d - n) * (-1))
     (hz2 : su + (d + n) * 0 + (d - n) * (-1) ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * 0 + (D - N) * (-1) ∧ σu + (D + N) * 0 + (D - N) * (-1) ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * (-1)) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * (-1)) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * (-1)) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * 0 + (D - N) * (-1))) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * 0 + (D - N) * (-1)) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_E1_zb (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * 0 - d * 1)
     (hy2 : tu + n * 0 - d * 1 ≤ n - 1) (hz1 : d + n - 1 ≤ su + (d + n) * 0 + (d - n) * 1)
     (hz2 : su + (d + n) * 0 + (d - n) * 1 ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * 0 + (D - N) * 1 ∧ σu + (D + N) * 0 + (D - N) * 1 ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 0 + (D - N) * 1) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 0 + (D - N) * 1) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 0 + (D - N) * 1) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * 0 + (D - N) * 1)) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * 0 + (D - N) * 1) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

theorem win_m1_E1_bz (N D n d T C tu su σu : ℤ)
    (hT0 : 0 < T) (hC0 : 0 ≤ C) (hCd : C * d = D * T + (-1) * (d - n))
     (hCn : C * n = N * T - (-1) * (d + n)) (hCL : C * (d + n) = (D + N) * T - 2 * (-1) * n)
     (hσ : T * σu = 2 * (-1) * tu + C * su) (hT : T = d * d + 2 * d * n - n * n) (hn3 : 3 ≤ n)
     (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
     (hσp : σu % 2 = 0) (hp1 : 2 - T ≤ tu) (hp2 : tu ≤ 2 * n - T - 1) (hq1 : 2 * n + 2 ≤ su)
     (hq2 : su ≤ d + n - 2) (hy1 : d - T + 1 ≤ tu + n * 1 - d * 0)
     (hy2 : tu + n * 1 - d * 0 ≤ n - 1) (hz1 : d + n - 1 ≤ su + (d + n) * 1 + (d - n) * 0)
     (hz2 : su + (d + n) * 1 + (d - n) * 0 ≤ T + 1 - (d - n)) :
    N - 3 * D + 4 ≤ σu + (D + N) * 1 + (D - N) * 0 ∧ σu + (D + N) * 1 + (D - N) * 0 ≤ 3 * D + N := by
  have hA : 0 ≤ C * (su - (2 * n + 2)) := mul_nonneg hC0 (by linarith)
  have hB : 0 ≤ C * ((d + n - 2) - su) := mul_nonneg hC0 (by linarith)
  have hσyp : (σu + (D + N) * 1 + (D - N) * 0) % 2 = 1 := by omega
  constructor
  · have key : 0 < T * ((σu + (D + N) * 1 + (D - N) * 0) - ((N - 3 * D + 4) - 2)) := by nlinarith
    have h2 : 0 < (σu + (D + N) * 1 + (D - N) * 0) - ((N - 3 * D + 4) - 2) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega
  · have key : 0 < T * ((3 * D + N) + 2 - (σu + (D + N) * 1 + (D - N) * 0)) := by nlinarith
    have h2 : 0 < (3 * D + N) + 2 - (σu + (D + N) * 1 + (D - N) * 0) := by
      by_contra hh; rw [not_lt] at hh; nlinarith
    omega

end FLatticePaper.OppWindow
