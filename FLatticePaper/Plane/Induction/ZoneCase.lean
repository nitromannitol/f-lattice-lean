import FLatticePaper.Plane.Induction.ZoneSlip

/-! # The case analysis of the zone of I1 (task 49, step (d) of the fix), part one

The difference of the two `F`-values in `C = h₀(w) + (f q − h₀ q)` is `F(Z q) − F(Z w)` with `Z q = Z w + δ`,
`δ = (n_q + d_q, d_q − n_q)`. For `ε = N d_q − n_q D = ±1` the vector `δ − ε σ` (with `σ` the shortShift of the earlier word)
is a multiple of the kernel `κ`, so `F(Z q) = F(Z w + ε σ)`, and the difference is a slip of the earlier word.
-/

namespace FLatticePaper.Induction
open FLatticePaper

namespace ZoneCase

/-- The kernel period of `F`, iterated over all integers. -/
theorem F_kappa_iter (F : Site → ℤ) (N D : ℤ) (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y) (n : ℤ) :
    ∀ y : Site, F (y + (n * (D + N), n * (D - N))) = F y := by
  induction n using Int.induction_on with
  | zero => intro y; simp only [zero_mul, Prod.mk_zero_zero, add_zero]
  | succ k ih =>
    intro y
    have e : y + (((k : ℤ) + 1) * (D + N), ((k : ℤ) + 1) * (D - N))
        = (y + ((k : ℤ) * (D + N), (k : ℤ) * (D - N))) + (D + N, D - N) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e, hK, ih y]
  | pred k ih =>
    intro y
    have h := hK (y + ((-(k : ℤ) - 1) * (D + N), (-(k : ℤ) - 1) * (D - N)))
    have e : y + ((-(k : ℤ) - 1) * (D + N), (-(k : ℤ) - 1) * (D - N)) + (D + N, D - N)
        = y + ((-(k : ℤ)) * (D + N), (-(k : ℤ)) * (D - N)) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e, ih y] at h
    exact h.symm

/-- The lattice identity `δ = ε σ + n κ` for `δ = (n_q + d_q, d_q − n_q)`, `ε = N d_q − n_q D = ±1`,
`σ = (2 ε_u D_u, 2 ε_u N_u)` and `κ = (D + N, D − N)`, with the explicit `n = ε_u (N_u k₁ − D_u k₂)`. -/
theorem zone_step_lattice (N D nq dq Nu Du epsU : ℤ) (hdet : Nu * (D + N) - Du * (D - N) = epsU)
    (hε2 : epsU ^ 2 = 1) :
    ∃ n : ℤ, (nq + dq, dq - nq) = ((N * dq - nq * D) * (2 * epsU * Du), (N * dq - nq * D) * (2 * epsU * Nu))
      + (n * (D + N), n * (D - N)) := by
  have hk : (D - N) * (nq + dq - (N * dq - nq * D) * (2 * epsU * Du))
      - (D + N) * (dq - nq - (N * dq - nq * D) * (2 * epsU * Nu)) = 0 := by
    linear_combination (2 * (N * dq - nq * D) * epsU) * hdet + (2 * (N * dq - nq * D)) * hε2
  obtain ⟨h1, h2⟩ := ZoneSlip.lattice_kappa N D Nu Du epsU
    (nq + dq - (N * dq - nq * D) * (2 * epsU * Du)) (dq - nq - (N * dq - nq * D) * (2 * epsU * Nu))
    hdet hε2 hk
  refine ⟨epsU * (Nu * (nq + dq - (N * dq - nq * D) * (2 * epsU * Du))
      - Du * (dq - nq - (N * dq - nq * D) * (2 * epsU * Nu))), ?_⟩
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> linarith

/-- `Z(w − V_q)` is `Z w + δ`, so `F(Z(w − V_q)) = F(Z w + ε σ)` (kernel invariance of `F`). -/
theorem F_zq_eq (F : Site → ℤ) (N D nq dq Nu Du epsU : ℤ) (hdet : Nu * (D + N) - Du * (D - N) = epsU)
    (hε2 : epsU ^ 2 = 1) (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y) (w : Site) :
    F (-(w.2 - (nq + dq)), w.1 - (nq - dq) - 1) =
      F ((-w.2, w.1 - 1) + ((N * dq - nq * D) * (2 * epsU * Du), (N * dq - nq * D) * (2 * epsU * Nu))) := by
  obtain ⟨n, hn⟩ := zone_step_lattice N D nq dq Nu Du epsU hdet hε2
  have e : (-(w.2 - (nq + dq)), w.1 - (nq - dq) - 1)
      = (-w.2, w.1 - 1) + (nq + dq, dq - nq) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  rw [e, hn]
  have e2 : (-w.2, w.1 - 1) + (((N * dq - nq * D) * (2 * epsU * Du), (N * dq - nq * D) * (2 * epsU * Nu))
      + (n * (D + N), n * (D - N)))
      = ((-w.2, w.1 - 1) + ((N * dq - nq * D) * (2 * epsU * Du), (N * dq - nq * D) * (2 * epsU * Nu)))
        + (n * (D + N), n * (D - N)) := by
    abel
  rw [e2, F_kappa_iter F N D hK n]

/-- The difference of the sheet values when the zone step is `ε = −1`: `F(Z q) − F(Z w) = slip (Z w − σ)`. -/
theorem value_minus (F : Site → ℤ) (N D nq dq Nu Du epsU : ℤ) (hdet : Nu * (D + N) - Du * (D - N) = epsU)
    (hε2 : epsU ^ 2 = 1) (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y)
    (hε : N * dq - nq * D = -1) (w : Site) :
    F (-(w.2 - (nq + dq)), w.1 - (nq - dq) - 1) - F (-w.2, w.1 - 1)
      = ZoneSlip.slipU F (2 * epsU * Du, 2 * epsU * Nu) ((-w.2, w.1 - 1) - (2 * epsU * Du, 2 * epsU * Nu)) := by
  have hz : (-w.2, w.1 - 1) + ((-1 : ℤ) * (2 * epsU * Du), (-1 : ℤ) * (2 * epsU * Nu))
      = (-w.2, w.1 - 1) - (2 * epsU * Du, 2 * epsU * Nu) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [F_zq_eq F N D nq dq Nu Du epsU hdet hε2 hK w, hε, hz]
  unfold ZoneSlip.slipU
  have e : (-w.2, w.1 - 1) - (2 * epsU * Du, 2 * epsU * Nu) + (2 * epsU * Du, 2 * epsU * Nu)
      = (-w.2, w.1 - 1) := by abel
  rw [e]

/-- The difference of the sheet values when `ε = +1`: `F(Z q) − F(Z w) = − slip (Z w)`. -/
theorem value_plus (F : Site → ℤ) (N D nq dq Nu Du epsU : ℤ) (hdet : Nu * (D + N) - Du * (D - N) = epsU)
    (hε2 : epsU ^ 2 = 1) (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y)
    (hε : N * dq - nq * D = 1) (w : Site) :
    F (-(w.2 - (nq + dq)), w.1 - (nq - dq) - 1) - F (-w.2, w.1 - 1)
      = -ZoneSlip.slipU F (2 * epsU * Du, 2 * epsU * Nu) (-w.2, w.1 - 1) := by
  have hz : (-w.2, w.1 - 1) + ((1 : ℤ) * (2 * epsU * Du), (1 : ℤ) * (2 * epsU * Nu))
      = (-w.2, w.1 - 1) + (2 * epsU * Du, 2 * epsU * Nu) := by
    simp only [one_mul]
  rw [F_zq_eq F N D nq dq Nu Du epsU hdet hε2 hK w, hε, hz]
  unfold ZoneSlip.slipU
  ring

/-- The hypotheses on the earlier word used by the zone argument: the earlier child `(D − N, D + N)`, its kernel and
transverse periods, the slip range on the closed polygon, and the zero strip of the standard field in `t`. -/
structure ZoneHyp (F : Site → ℤ) (N D Nu Du epsU : ℤ) : Prop where
  hN : 0 < N
  hND : N < D
  hr : (D + N) % 2 = 1
  hdet : Nu * (D + N) - Du * (D - N) = epsU
  hepsU : epsU = 1 ∨ epsU = -1
  hodd : (Nu + Du) % 2 = 1
  hK : ∀ y : Site, F (y + (D + N, D - N)) = F y
  hT : ∀ y : Site, F (y + (-2 * N, 2 * D)) =
    F y + ((D - N) * y.1 - (D + N) * y.2) - (D ^ 2 + 2 * D * N - N ^ 2 + D)
  hslip : ∀ y : Site, ZoneSlip.PolyU N D y →
    0 ≤ ZoneSlip.slipU F (2 * epsU * Du, 2 * epsU * Nu) y ∧ ZoneSlip.slipU F (2 * epsU * Du, 2 * epsU * Nu) y ≤ 2
  hstrip : ∀ y : Site, 1 - (D + N) ≤ (D - N) * y.1 - (D + N) * y.2 →
    (D - N) * y.1 - (D + N) * y.2 ≤ (D - N) + 2 * (D + N) - 1 → F y = 0

/-- The shortShift has transverse grade `−2`. -/
theorem t_sigma (N D Nu Du epsU : ℤ) (hdet : Nu * (D + N) - Du * (D - N) = epsU) (hε2 : epsU ^ 2 = 1) :
    (D - N) * (2 * epsU * Du) - (D + N) * (2 * epsU * Nu) = -2 := by
  linear_combination (-2 * epsU) * hdet + (-2 : ℤ) * hε2

/-- The sign of the `ε = −1` zone difference: nonnegative wherever the transverse coordinate of `Z w` is at most `r`. -/
theorem zone_minus_nonneg (F : Site → ℤ) (N D nq dq Nu Du epsU : ℤ) (H : ZoneHyp F N D Nu Du epsU)
    (hε : N * dq - nq * D = -1) (hD2 : 2 ≤ D) (w : Site)
    (hj : (D - N) * (-w.2) - (D + N) * (w.1 - 1) ≤ D + N) :
    0 ≤ F (-(w.2 - (nq + dq)), w.1 - (nq - dq) - 1) - F (-w.2, w.1 - 1) := by
  have hε2 : epsU ^ 2 = 1 := by rcases H.hepsU with rfl | rfl <;> norm_num
  rw [value_minus F N D nq dq Nu Du epsU H.hdet hε2 H.hK hε w]
  have hσ := t_sigma N D Nu Du epsU H.hdet hε2
  have ht : (D - N) * ((-w.2, w.1 - 1) - (2 * epsU * Du, 2 * epsU * Nu)).1
      - (D + N) * ((-w.2, w.1 - 1) - (2 * epsU * Du, 2 * epsU * Nu)).2
      = (D - N) * (-w.2) - (D + N) * (w.1 - 1) + 2 := by
    simp only [Prod.fst_sub, Prod.snd_sub]
    linear_combination (-1 : ℤ) * hσ
  have hN := H.hN
  have hND := H.hND
  by_cases hc : (D - N) * ((-w.2, w.1 - 1) - (2 * epsU * Du, 2 * epsU * Nu)).1
      - (D + N) * ((-w.2, w.1 - 1) - (2 * epsU * Du, 2 * epsU * Nu)).2 ≤ D + N
  · exact (ZoneSlip.slip_sign F N D Nu Du epsU H.hN H.hND H.hr H.hdet H.hepsU H.hodd H.hK H.hT H.hslip _).1 hc
  · have hc' : D + N < (D - N) * (-w.2) - (D + N) * (w.1 - 1) + 2 := by linarith
    have hj' : D + N - 2 < (D - N) * (-w.2) - (D + N) * (w.1 - 1) := by linarith
    have e : (-w.2, w.1 - 1) - (2 * epsU * Du, 2 * epsU * Nu) + (2 * epsU * Du, 2 * epsU * Nu)
        = (-w.2, w.1 - 1) := by abel
    unfold ZoneSlip.slipU
    rw [e]
    have h1 := H.hstrip ((-w.2, w.1 - 1) - (2 * epsU * Du, 2 * epsU * Nu))
    have h2 := H.hstrip (-w.2, w.1 - 1)
    rw [h1 (by rw [ht]; linarith) (by rw [ht]; linarith), h2 (by linarith) (by linarith)]
    simp

/-- The sign of the `ε = +1` zone difference: nonnegative wherever the transverse grade of `Z w` is at least `r`. -/
theorem zone_plus_nonneg (F : Site → ℤ) (N D nq dq Nu Du epsU : ℤ) (H : ZoneHyp F N D Nu Du epsU)
    (hε : N * dq - nq * D = 1) (hD2 : 2 ≤ D) (w : Site)
    (hj : D + N ≤ (D - N) * (-w.2, w.1 - 1).1 - (D + N) * (-w.2, w.1 - 1).2) :
    0 ≤ F (-(w.2 - (nq + dq)), w.1 - (nq - dq) - 1) - F (-w.2, w.1 - 1) := by
  have hε2 : epsU ^ 2 = 1 := by rcases H.hepsU with rfl | rfl <;> norm_num
  rw [value_plus F N D nq dq Nu Du epsU H.hdet hε2 H.hK hε w]
  have hN := H.hN
  have hND := H.hND
  have hσ := t_sigma N D Nu Du epsU H.hdet hε2
  have ht2 : (D - N) * ((-w.2, w.1 - 1) + (2 * epsU * Du, 2 * epsU * Nu)).1
      - (D + N) * ((-w.2, w.1 - 1) + (2 * epsU * Du, 2 * epsU * Nu)).2
      = (D - N) * (-w.2, w.1 - 1).1 - (D + N) * (-w.2, w.1 - 1).2 - 2 := by
    simp only [Prod.fst_add, Prod.snd_add]
    linear_combination hσ
  by_cases hgt : D + N < (D - N) * (-w.2, w.1 - 1).1 - (D + N) * (-w.2, w.1 - 1).2
  · have := (ZoneSlip.slip_sign F N D Nu Du epsU H.hN H.hND H.hr H.hdet H.hepsU H.hodd H.hK H.hT H.hslip
      (-w.2, w.1 - 1)).2 hgt
    linarith
  · have heq : (D - N) * (-w.2, w.1 - 1).1 - (D + N) * (-w.2, w.1 - 1).2 = D + N :=
      le_antisymm (not_lt.mp hgt) hj
    have h1 := H.hstrip (-w.2, w.1 - 1) (by rw [heq]; linarith) (by rw [heq]; linarith)
    have h2 := H.hstrip ((-w.2, w.1 - 1) + (2 * epsU * Du, 2 * epsU * Nu))
      (by rw [ht2, heq]; linarith) (by rw [ht2, heq]; linarith)
    unfold ZoneSlip.slipU
    rw [h1, h2]
    simp

/-- The transverse grade of `Z w` is at most `r` when `w = z` lies in the box `0 ≤ z₁`, `0 ≤ z₂` (for `ε = −1`). -/
theorem tG_le_of_box (N D z1 z2 : ℤ) (hN : 0 < N) (hND : N < D) (hz1 : 0 ≤ z1) (hz2 : 0 ≤ z2) :
    (D - N) * (-z2) - (D + N) * (z1 - 1) ≤ D + N := by
  nlinarith

/-- The transverse grade of `Z(z − U)` is at least `r` for `z` in the box `z₁ ≤ d`, `z₂ ≤ n` (for `ε = +1`). -/
theorem tG_ge_of_box (N D nq dq z1 z2 : ℤ) (hN : 0 < N) (hND : N < D) (hz1 : z1 ≤ 2 * D + dq)
    (hz2 : z2 ≤ 2 * N + nq) :
    D + N ≤ (D - N) * (-(z2 - (2 * N + nq))) - (D + N) * (z1 - (2 * D + dq) - 1) := by
  nlinarith

/-- The exceptional line `N w₁ − D w₂ = −D` is `w = (kD, kN + 1)`, given `N d_q − n_q D = ±1`. -/
theorem exc_form (N D nq dq w1 w2 : ℤ) (hD : 0 < D) (hε : (N * dq - nq * D) ^ 2 = 1)
    (h : N * w1 - D * w2 = -D) :
    ∃ k : ℤ, w1 = k * D ∧ w2 = k * N + 1 := by
  refine ⟨(N * dq - nq * D) * (dq * (w2 - 1) - nq * w1), ?_, ?_⟩
  · linear_combination ((N * dq - nq * D) * dq) * h - w1 * hε
  · have hk : D * (w2 - 1 - N * ((N * dq - nq * D) * (dq * (w2 - 1) - nq * w1))) = 0 := by
      linear_combination (-1 : ℤ) * h + N * (((N * dq - nq * D) * dq) * h - w1 * hε)
    rcases mul_eq_zero.mp hk with h0 | h0
    · omega
    · linarith

/-- The value `h₀(0,1) = −1`. -/
theorem harmonic_zero_one : harmonicGrid (0, 1) = -1 := by
  norm_num [harmonicGrid]

/-- One step along the exceptional line: `h₀(w) + F(Z(w − V_q))` changes by `−2ε` when `w` moves by `U_p = (2D, 2N)`. -/
theorem psi_step (F : Site → ℤ) (N D nq dq Nu Du epsU : ℤ) (H : ZoneHyp F N D Nu Du epsU) (m : ℤ) :
    harmonicGrid (2 * (m + 1) * D, 2 * (m + 1) * N + 1)
      + F (-(2 * (m + 1) * N + 1 - (nq + dq)), 2 * (m + 1) * D - (nq - dq) - 1)
    = harmonicGrid (2 * m * D, 2 * m * N + 1)
      + F (-(2 * m * N + 1 - (nq + dq)), 2 * m * D - (nq - dq) - 1)
      - 2 * (N * dq - nq * D) := by
  have hc : 2 * (-(D ^ 2 + 2 * D * N - N ^ 2) - N) = -2 * (D + N) * (D - N) - (D + N) ^ 2 + (D - N) ^ 2
      - (D + N) + (D - N) := by ring
  have hh := ZoneHarmonic.harmonicGrid_sub_shift (2 * (m + 1) * D, 2 * (m + 1) * N + 1) (D + N) (D - N)
    (-(D ^ 2 + 2 * D * N - N ^ 2) - N) hc
  have e1 : (2 * (m + 1) * D, 2 * (m + 1) * N + 1) - ((D + N) + (D - N), (D + N) - (D - N))
      = (2 * m * D, 2 * m * N + 1) := by
    ext <;> simp <;> ring
  rw [e1] at hh
  simp only at hh
  have hT' := H.hT (-(2 * m * N + 1 - (nq + dq)), 2 * m * D - (nq - dq) - 1)
  have e2 : (-(2 * m * N + 1 - (nq + dq)), 2 * m * D - (nq - dq) - 1) + (-2 * N, 2 * D)
      = (-(2 * (m + 1) * N + 1 - (nq + dq)), 2 * (m + 1) * D - (nq - dq) - 1) := by
    ext <;> simp <;> ring
  rw [e2] at hT'
  simp only at hT'
  linear_combination hh + hT'

/-- The exceptional line: `h₀(w_l) + F(Z(w_l − V_q)) = −1 − 2ε l` for `w_l = (2lD, 2lN + 1)`, given `ε = ±1`. -/
theorem psi_line (F : Site → ℤ) (N D nq dq Nu Du epsU : ℤ) (H : ZoneHyp F N D Nu Du epsU)
    (hε : N * dq - nq * D = 1 ∨ N * dq - nq * D = -1) (l : ℤ) :
    harmonicGrid (2 * l * D, 2 * l * N + 1)
      + F (-(2 * l * N + 1 - (nq + dq)), 2 * l * D - (nq - dq) - 1)
    = -1 - 2 * (N * dq - nq * D) * l := by
  induction l using Int.induction_on with
  | zero =>
    have e0 : (2 * (0 : ℤ) * D, 2 * (0 : ℤ) * N + 1) = (0, 1) := by
      ext <;> simp
    have hz : F (-(2 * (0 : ℤ) * N + 1 - (nq + dq)), 2 * (0 : ℤ) * D - (nq - dq) - 1) = 0 := by
      have ht : (D - N) * (-(2 * (0 : ℤ) * N + 1 - (nq + dq))) - (D + N) * (2 * (0 : ℤ) * D - (nq - dq) - 1)
          = 2 * N - 2 * (N * dq - nq * D) := by
        ring
      have hN := H.hN
      have hND := H.hND
      have h1 := H.hstrip (-(2 * (0 : ℤ) * N + 1 - (nq + dq)), 2 * (0 : ℤ) * D - (nq - dq) - 1)
        (by rw [ht]; rcases hε with h | h <;> rw [h] <;> linarith)
        (by rw [ht]; rcases hε with h | h <;> rw [h] <;> linarith)
      exact h1
    rw [e0, harmonic_zero_one, hz]
    simp
  | succ k ih =>
    rw [psi_step F N D nq dq Nu Du epsU H k]
    linear_combination ih
  | pred k ih =>
    have hs := psi_step F N D nq dq Nu Du epsU H (-(k : ℤ) - 1)
    have e : (-(k : ℤ) - 1 + 1) = -(k : ℤ) := by ring
    rw [e] at hs
    linear_combination (-1 : ℤ) * hs + ih

/-- The `t_p`-window of the zone: with `d = 2D + d_q`, `n = 2N + n_q`, `ε = N d_q − n_q D = ±1`, the grade
`p = N w₁ − D w₂` satisfies `−D ≤ p ≤ N + 2D − 1` when `t(w) = n w₁ − d w₂` is in `[1 − d, d + n − 1]` and `ε w₁ ∈ [−d, 0]`. -/
theorem tp_window (N D nq dq w1 w2 : ℤ) (hD : 0 < D) (hd : 0 < 2 * D + dq)
    (hε1 : -1 ≤ N * dq - nq * D)
    (hlo : 1 - (2 * D + dq) ≤ (2 * N + nq) * w1 - (2 * D + dq) * w2)
    (hhi : (2 * N + nq) * w1 - (2 * D + dq) * w2 ≤ (2 * D + dq) + (2 * N + nq) - 1)
    (hεlo : -(2 * D + dq) ≤ (N * dq - nq * D) * w1) (hεhi : (N * dq - nq * D) * w1 ≤ 0) :
    -D ≤ N * w1 - D * w2 ∧ N * w1 - D * w2 ≤ N + 2 * D - 1 := by
  have hid : (2 * D + dq) * (N * w1 - D * w2)
      = D * ((2 * N + nq) * w1 - (2 * D + dq) * w2) + (N * dq - nq * D) * w1 := by ring
  constructor
  · by_contra hc
    have hc' : N * w1 - D * w2 ≤ -D - 1 := by omega
    nlinarith
  · by_contra hc
    have hc' : N + 2 * D ≤ N * w1 - D * w2 := by omega
    nlinarith

/-- The quarter-turn field minus the harmonic grid is `F` at the quarter turn. -/
theorem qtf_sub_h0 (F : Site → ℤ) (x : Site) :
    quarterTurnField F x - harmonicGrid x = F (-x.2, x.1 - 1) := by
  unfold quarterTurnField
  rw [quarterTurn_site]
  ring

/-- Step (d), the case `ε = −1` (`W = 0`): the sheet is nonnegative on the zone. -/
theorem I1_core_minus (F : Site → ℤ) (N D nq dq Nu Du epsU cq : ℤ) (H : ZoneHyp F N D Nu Du epsU)
    (hε : N * dq - nq * D = -1) (hdq : 0 < 2 * D + dq)
    (hcq : 2 * cq = dq * dq + 2 * dq * nq - nq * nq - dq - nq)
    (hzs : ∀ x : Site, 1 - D ≤ N * x.1 - D * x.2 → N * x.1 - D * x.2 ≤ N + 2 * D - 1 → quarterTurnField F x = 0)
    (hzev : ∀ x : Site, (x.1 + x.2) % 2 = 0 → N * x.1 - D * x.2 = -D → quarterTurnField F x = 0)
    (z1 z2 : ℤ) (hz1 : 0 ≤ z1) (hz1' : z1 ≤ 2 * D + dq) (hz2 : 0 ≤ z2) (hz2' : z2 ≤ 2 * N + nq)
    (ht1 : 1 - (2 * D + dq) ≤ (2 * N + nq) * z1 - (2 * D + dq) * z2)
    (ht2 : (2 * N + nq) * z1 - (2 * D + dq) * z2 ≤ (2 * D + dq) + (2 * N + nq) - 1) :
    0 ≤ quarterTurnField F (z1 - (1 - 0) * dq - (nq - dq + (N * dq - nq * D) * dq),
          z2 - (1 - 0) * nq - (nq + dq + (N * dq - nq * D) * nq))
      + (nq * (z1 - (1 - 0) * dq) - dq * (z2 - (1 - 0) * nq)) + (cq + 2 * 0) := by
  have hN := H.hN
  have hND := H.hND
  have hr := H.hr
  have hD2 : 2 ≤ D := by omega
  have hsheet := ZoneSheet.sheet_eq_harmonic F N D nq dq cq 0 z1 z2 (Or.inl ⟨rfl, hε⟩) hcq
    (fun x => ZoneHarmonic.quarterTurnField_add_Up F N D H.hT x)
  rw [hsheet]
  simp only [zero_mul, sub_zero]
  rw [qtf_sub_h0]
  have hj : (D - N) * (-(z1, z2).2) - (D + N) * ((z1, z2).1 - 1) ≤ D + N :=
    tG_le_of_box N D z1 z2 hN hND hz1 hz2
  have hmin := zone_minus_nonneg F N D nq dq Nu Du epsU H hε hD2 (z1, z2) hj
  simp only at hmin
  by_cases hs : N * z1 - D * z2 = -D
  · obtain ⟨k, hk1, hk2⟩ := exc_form N D nq dq z1 z2 (by omega) (by rw [hε]; norm_num) hs
    rcases Int.even_or_odd k with ⟨l, hl⟩ | ⟨l, hl⟩
    · have e1 : z1 = 2 * l * D := by rw [hk1, hl]; ring
      have e2 : z2 = 2 * l * N + 1 := by rw [hk2, hl]; ring
      subst e1 e2
      have hpsi := psi_line F N D nq dq Nu Du epsU H (Or.inr hε) l
      have hl0 : 0 ≤ l := by nlinarith
      have hl1 : 1 ≤ l := by
        by_contra hc
        have h0 : l = 0 := by omega
        subst h0
        have e0 : (2 * N + nq) * (2 * (0 : ℤ) * D) - (2 * D + dq) * (2 * (0 : ℤ) * N + 1)
            = -(2 * D + dq) := by ring
        linarith
      rw [hpsi, hε]
      linarith
    · have e1 : z1 = (2 * l + 1) * D := by rw [hk1, hl]
      have e2 : z2 = (2 * l + 1) * N + 1 := by rw [hk2, hl]
      obtain ⟨c, hc⟩ : ∃ c : ℤ, D + N = 2 * c + 1 := ⟨(D + N - 1) / 2, by omega⟩
      have hsum : z1 + z2 = 2 * (2 * l * c + l + c + 1) := by
        rw [e1, e2]
        linear_combination (2 * l + 1) * hc
      have hpar : (z1 + z2) % 2 = 0 := by
        rw [hsum]
        simp
      have hf : quarterTurnField F (z1, z2) = 0 := hzev (z1, z2) hpar hs
      unfold quarterTurnField at hf
      rw [quarterTurn_site] at hf
      simp only at hf
      linarith
  · have hb := tp_window N D nq dq z1 z2 (by omega) hdq (by linarith) ht1 ht2
      (by rw [hε]; linarith) (by rw [hε]; linarith)
    obtain ⟨hlo', hhi'⟩ := hb
    have key : ∀ p : ℤ, -D ≤ p → p ≠ -D → 1 - D ≤ p := fun p h1 h2 => by omega
    have hs1 : 1 - D ≤ N * z1 - D * z2 := key _ hlo' hs
    have hf0 : quarterTurnField F (z1, z2) = 0 := hzs (z1, z2) hs1 hhi'
    unfold quarterTurnField at hf0
    rw [quarterTurn_site] at hf0
    simp only at hf0
    linarith

end ZoneCase

end FLatticePaper.Induction
