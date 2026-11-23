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

end ZoneCase

end FLatticePaper.Induction
