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

end ZoneCase

end FLatticePaper.Induction
