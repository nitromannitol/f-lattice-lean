import FLatticePaper.Plane.Induction.ZoneSheet

/-! # The slip sign on the earlier word (task 49, step (c) of the fix: inequality (1) of Q4-strips)

For the earlier conjugate frame `u` with child `(b, r) = (D − N, D + N)`, kernel `κ = (r, b)`, transverse `τ = (−2N, 2D)`,
odd parent `N_u/D_u` with `ε_u = N_u d_u − n_u D_u` and shortShift `σ = (2 ε_u D_u, 2 ε_u N_u)`, put
`t(y) = b y₁ − r y₂` and `slip y = F y − F(y + σ)`. The slip is in `[0, 2]` on the closed polygon `PolyU` (slipRange), it is
invariant under `κ` and increases by `2` under `τ` (both from the packet periods), and `t(σ) = −2`. Every site is a window point
`y₀` (with `t(y₀) ∈ (r − 2B, r]`) moved by `m τ + n κ`, where `m` is the number of periods of `t`, so `slip y = slip y₀ + 2m`:
it is nonnegative when `t(y) ≤ r` and nonpositive when `t(y) > r`.
-/

namespace FLatticePaper.Induction
open FLatticePaper

namespace ZoneSlip

/-- The closed polygon of the earlier child `(D − N, D + N)` in the coordinates `t = (D − N) y₁ − (D + N) y₂` and
`s = 2D y₁ + 2N y₂` (the period denominator is `T = 2B`, `B = D² + 2DN − N²`), the even and odd cases of `closedPolygon`. -/
def PolyU (N D : ℤ) (y : Site) : Prop :=
  (EvenSite y ∧ 2 - 2 * (D ^ 2 + 2 * D * N - N ^ 2) ≤ (D - N) * y.1 - (D + N) * y.2 ∧
      (D - N) * y.1 - (D + N) * y.2 ≤ 2 * D - 2 ∧
      0 ≤ 2 * D * y.1 + 2 * N * y.2 ∧
      2 * D * y.1 + 2 * N * y.2 ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * (D - N)) ∨
  (¬EvenSite y ∧ (D - N) - 2 * (D ^ 2 + 2 * D * N - N ^ 2) ≤ (D - N) * y.1 - (D + N) * y.2 ∧
      (D - N) * y.1 - (D + N) * y.2 ≤ D + N ∧
      2 - 2 * N ≤ 2 * D * y.1 + 2 * N * y.2 ∧
      2 * D * y.1 + 2 * N * y.2 ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * D - 2)

/-- A shift of `s` by a multiple of `T > 0` into any window of length `T`. -/
theorem exists_shift (s lo T : ℤ) (hT : 0 < T) :
    ∃ p : ℤ, lo ≤ s + p * T ∧ s + p * T ≤ lo + T - 1 := by
  have h1 := Int.emod_nonneg (s - lo) hT.ne'
  have h2 := Int.emod_lt_of_pos (s - lo) hT
  have h3 : (s - lo) % T = (s - lo) - T * ((s - lo) / T) := Int.emod_def _ _
  refine ⟨-((s - lo) / T), ?_, ?_⟩ <;> linarith

/-- The parity of the window point: `y₁ + p κ` has the parity of `j₀` (since `2D` is even and `Du + Nu` is odd). -/
theorem parity_shift (N D Nu Du epsU j0 p k : ℤ) (hepsU : epsU = 1 ∨ epsU = -1) (hk : Du + Nu = 2 * k + 1) :
    ((-epsU * Du * j0 + p * (D + N)) + (-epsU * Nu * j0 + p * (D - N))) % 2 = j0 % 2 := by
  rcases hepsU with rfl | rfl
  · have e : (-1 * Du * j0 + p * (D + N)) + (-1 * Nu * j0 + p * (D - N))
        = j0 + 2 * (-j0 * (k + 1) + D * p) := by
      linear_combination (-j0) * hk
    rw [e, Int.add_mul_emod_self_left]
  · have e : (-(-1) * Du * j0 + p * (D + N)) + (-(-1) * Nu * j0 + p * (D - N))
        = j0 + 2 * (k * j0 + D * p) := by
      linear_combination j0 * hk
    rw [e, Int.add_mul_emod_self_left]

/-- The window point: for `r − 2B < j₀ ≤ r` (with `r = D + N` odd, `0 < N < D`) some site of the closed polygon has
`t = j₀`. -/
theorem window_point (N D Nu Du epsU j0 : ℤ) (hN : 0 < N) (hND : N < D) (hr : (D + N) % 2 = 1)
    (hdet : Nu * (D + N) - Du * (D - N) = epsU) (hepsU : epsU = 1 ∨ epsU = -1) (hodd : (Nu + Du) % 2 = 1)
    (hj1 : D + N - 2 * (D ^ 2 + 2 * D * N - N ^ 2) < j0) (hj2 : j0 ≤ D + N) :
    ∃ y : Site, PolyU N D y ∧ (D - N) * y.1 - (D + N) * y.2 = j0 := by
  have hε2 : epsU ^ 2 = 1 := by rcases hepsU with rfl | rfl <;> norm_num
  have hT : 0 < 2 * (D ^ 2 + 2 * D * N - N ^ 2) := by nlinarith
  obtain ⟨k, hk⟩ : ∃ k, Du + Nu = 2 * k + 1 := ⟨(Du + Nu - 1) / 2, by omega⟩
  have ht1 : (D - N) * (-epsU * Du * j0) - (D + N) * (-epsU * Nu * j0) = j0 := by
    linear_combination (epsU * j0) * hdet + j0 * hε2
  have hpD : 2 * D * (-epsU * Du * j0) + 2 * N * (-epsU * Nu * j0)
      = 2 * D * (-epsU * Du * j0) + 2 * N * (-epsU * Nu * j0) := rfl
  rcases (show j0 % 2 = 0 ∨ j0 % 2 = 1 by omega) with hev | hod
  · obtain ⟨p, hp1, hp2⟩ := exists_shift (2 * D * (-epsU * Du * j0) + 2 * N * (-epsU * Nu * j0)) 0
      (2 * (D ^ 2 + 2 * D * N - N ^ 2)) hT
    refine ⟨(-epsU * Du * j0 + p * (D + N), -epsU * Nu * j0 + p * (D - N)), Or.inl ?_, ?_⟩
    · have hE : EvenSite (-epsU * Du * j0 + p * (D + N), -epsU * Nu * j0 + p * (D - N)) := by
        unfold EvenSite
        rw [show ((-epsU * Du * j0 + p * (D + N), -epsU * Nu * j0 + p * (D - N))).1 +
            (-epsU * Du * j0 + p * (D + N), -epsU * Nu * j0 + p * (D - N)).2
            = (-epsU * Du * j0 + p * (D + N)) + (-epsU * Nu * j0 + p * (D - N)) from rfl]
        rw [parity_shift N D Nu Du epsU j0 p k hepsU hk, hev]
      refine ⟨hE, ?_, ?_, ?_, ?_⟩
      · simp only
        rw [show (D - N) * (-epsU * Du * j0 + p * (D + N)) - (D + N) * (-epsU * Nu * j0 + p * (D - N)) = j0 by
          linear_combination ht1]
        nlinarith
      · simp only
        rw [show (D - N) * (-epsU * Du * j0 + p * (D + N)) - (D + N) * (-epsU * Nu * j0 + p * (D - N)) = j0 by
          linear_combination ht1]
        omega
      · simp only
        have hs : 2 * D * (-epsU * Du * j0 + p * (D + N)) + 2 * N * (-epsU * Nu * j0 + p * (D - N))
            = 2 * D * (-epsU * Du * j0) + 2 * N * (-epsU * Nu * j0) + p * (2 * (D ^ 2 + 2 * D * N - N ^ 2)) := by
          ring
        rw [hs]
        linarith
      · simp only
        have hs : 2 * D * (-epsU * Du * j0 + p * (D + N)) + 2 * N * (-epsU * Nu * j0 + p * (D - N))
            = 2 * D * (-epsU * Du * j0) + 2 * N * (-epsU * Nu * j0) + p * (2 * (D ^ 2 + 2 * D * N - N ^ 2)) := by
          ring
        rw [hs]
        linarith
    · simp only
      linear_combination ht1
  · obtain ⟨p, hp1, hp2⟩ := exists_shift (2 * D * (-epsU * Du * j0) + 2 * N * (-epsU * Nu * j0)) (2 - 2 * N)
      (2 * (D ^ 2 + 2 * D * N - N ^ 2)) hT
    refine ⟨(-epsU * Du * j0 + p * (D + N), -epsU * Nu * j0 + p * (D - N)), Or.inr ?_, ?_⟩
    · have hNE : ¬EvenSite (-epsU * Du * j0 + p * (D + N), -epsU * Nu * j0 + p * (D - N)) := by
        unfold EvenSite
        rw [show ((-epsU * Du * j0 + p * (D + N), -epsU * Nu * j0 + p * (D - N))).1 +
            (-epsU * Du * j0 + p * (D + N), -epsU * Nu * j0 + p * (D - N)).2
            = (-epsU * Du * j0 + p * (D + N)) + (-epsU * Nu * j0 + p * (D - N)) from rfl]
        rw [parity_shift N D Nu Du epsU j0 p k hepsU hk, hod]
        omega
      refine ⟨hNE, ?_, ?_, ?_, ?_⟩
      · simp only
        rw [show (D - N) * (-epsU * Du * j0 + p * (D + N)) - (D + N) * (-epsU * Nu * j0 + p * (D - N)) = j0 by
          linear_combination ht1]
        omega
      · simp only
        rw [show (D - N) * (-epsU * Du * j0 + p * (D + N)) - (D + N) * (-epsU * Nu * j0 + p * (D - N)) = j0 by
          linear_combination ht1]
        omega
      · simp only
        have hs : 2 * D * (-epsU * Du * j0 + p * (D + N)) + 2 * N * (-epsU * Nu * j0 + p * (D - N))
            = 2 * D * (-epsU * Du * j0) + 2 * N * (-epsU * Nu * j0) + p * (2 * (D ^ 2 + 2 * D * N - N ^ 2)) := by
          ring
        rw [hs]
        linarith
      · simp only
        have hs : 2 * D * (-epsU * Du * j0 + p * (D + N)) + 2 * N * (-epsU * Nu * j0 + p * (D - N))
            = 2 * D * (-epsU * Du * j0) + 2 * N * (-epsU * Nu * j0) + p * (2 * (D ^ 2 + 2 * D * N - N ^ 2)) := by
          ring
        rw [hs]
        nlinarith
    · simp only
      linear_combination ht1

/-- The slip `F y − F (y + σ)` of the earlier standard field. -/
def slipU (F : Site → ℤ) (σ : Site) (y : Site) : ℤ := F y - F (y + σ)

/-- The drift along `τ = (−2N, 2D)`: the slip increases by `2`, since `t(σ) = −2` and `F(y + τ) = F y + t(y) − (B + D)`. -/
theorem slip_tau_step (F : Site → ℤ) (N D Nu Du epsU : ℤ) (hdet : Nu * (D + N) - Du * (D - N) = epsU)
    (hε2 : epsU ^ 2 = 1)
    (hT : ∀ y : Site, F (y + (-2 * N, 2 * D)) = F y + ((D - N) * y.1 - (D + N) * y.2) - (D ^ 2 + 2 * D * N - N ^ 2 + D))
    (y : Site) :
    slipU F (2 * epsU * Du, 2 * epsU * Nu) (y + (-2 * N, 2 * D)) = slipU F (2 * epsU * Du, 2 * epsU * Nu) y + 2 := by
  have hσ : (D - N) * (2 * epsU * Du) - (D + N) * (2 * epsU * Nu) = -2 := by
    linear_combination (-2 * epsU) * hdet + (-2 : ℤ) * hε2
  have h1 := hT y
  have h2 := hT (y + (2 * epsU * Du, 2 * epsU * Nu))
  unfold slipU
  have e : y + (-2 * N, 2 * D) + (2 * epsU * Du, 2 * epsU * Nu)
      = (y + (2 * epsU * Du, 2 * epsU * Nu)) + (-2 * N, 2 * D) := by abel
  rw [e, h2, h1]
  simp only [Prod.fst_add, Prod.snd_add]
  linear_combination (-1 : ℤ) * hσ

/-- The drift along `κ = (D + N, D − N)`: the slip is invariant, since `κ` is a kernel period of the standard field. -/
theorem slip_kappa_step (F : Site → ℤ) (N D Nu Du epsU : ℤ)
    (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y) (y : Site) :
    slipU F (2 * epsU * Du, 2 * epsU * Nu) (y + (D + N, D - N)) = slipU F (2 * epsU * Du, 2 * epsU * Nu) y := by
  unfold slipU
  have e : y + (D + N, D - N) + (2 * epsU * Du, 2 * epsU * Nu)
      = (y + (2 * epsU * Du, 2 * epsU * Nu)) + (D + N, D - N) := by abel
  rw [e, hK, hK]

/-- Iterating the `τ`-drift over all integers `m`. -/
theorem slip_tau_iter (F : Site → ℤ) (N D Nu Du epsU : ℤ) (hdet : Nu * (D + N) - Du * (D - N) = epsU)
    (hε2 : epsU ^ 2 = 1)
    (hT : ∀ y : Site, F (y + (-2 * N, 2 * D)) = F y + ((D - N) * y.1 - (D + N) * y.2) - (D ^ 2 + 2 * D * N - N ^ 2 + D))
    (m : ℤ) : ∀ y : Site,
      slipU F (2 * epsU * Du, 2 * epsU * Nu) (y + (m * (-2 * N), m * (2 * D)))
        = slipU F (2 * epsU * Du, 2 * epsU * Nu) y + 2 * m := by
  induction m using Int.induction_on with
  | zero => intro y; simp only [zero_mul, Prod.mk_zero_zero, add_zero, mul_zero]
  | succ k ih =>
    intro y
    have e : y + (((k : ℤ) + 1) * (-2 * N), ((k : ℤ) + 1) * (2 * D))
        = (y + ((k : ℤ) * (-2 * N), (k : ℤ) * (2 * D))) + (-2 * N, 2 * D) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e, slip_tau_step F N D Nu Du epsU hdet hε2 hT, ih y]
    ring
  | pred k ih =>
    intro y
    have h := slip_tau_step F N D Nu Du epsU hdet hε2 hT
      (y + ((-(k : ℤ) - 1) * (-2 * N), (-(k : ℤ) - 1) * (2 * D)))
    have e : y + ((-(k : ℤ) - 1) * (-2 * N), (-(k : ℤ) - 1) * (2 * D)) + (-2 * N, 2 * D)
        = y + ((-(k : ℤ)) * (-2 * N), (-(k : ℤ)) * (2 * D)) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e, ih y] at h
    linarith

/-- Iterating the `κ`-invariance over all integers `n`. -/
theorem slip_kappa_iter (F : Site → ℤ) (N D Nu Du epsU : ℤ)
    (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y) (n : ℤ) : ∀ y : Site,
      slipU F (2 * epsU * Du, 2 * epsU * Nu) (y + (n * (D + N), n * (D - N)))
        = slipU F (2 * epsU * Du, 2 * epsU * Nu) y := by
  induction n using Int.induction_on with
  | zero => intro y; simp only [zero_mul, Prod.mk_zero_zero, add_zero]
  | succ k ih =>
    intro y
    have e : y + (((k : ℤ) + 1) * (D + N), ((k : ℤ) + 1) * (D - N))
        = (y + ((k : ℤ) * (D + N), (k : ℤ) * (D - N))) + (D + N, D - N) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e, slip_kappa_step F N D Nu Du epsU hK, ih y]
  | pred k ih =>
    intro y
    have h := slip_kappa_step F N D Nu Du epsU hK
      (y + ((-(k : ℤ) - 1) * (D + N), (-(k : ℤ) - 1) * (D - N)))
    have e : y + ((-(k : ℤ) - 1) * (D + N), (-(k : ℤ) - 1) * (D - N)) + (D + N, D - N)
        = y + ((-(k : ℤ)) * (D + N), (-(k : ℤ)) * (D - N)) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e, ih y] at h
    exact h.symm

/-- Both drifts together: `slip (y + (m τ + n κ)) = slip y + 2m`. -/
theorem slip_shift_both (F : Site → ℤ) (N D Nu Du epsU : ℤ) (hdet : Nu * (D + N) - Du * (D - N) = epsU)
    (hε2 : epsU ^ 2 = 1)
    (hT : ∀ y : Site, F (y + (-2 * N, 2 * D)) = F y + ((D - N) * y.1 - (D + N) * y.2) - (D ^ 2 + 2 * D * N - N ^ 2 + D))
    (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y) (m n : ℤ) (y : Site) :
    slipU F (2 * epsU * Du, 2 * epsU * Nu) (y + (m * (-2 * N) + n * (D + N), m * (2 * D) + n * (D - N)))
      = slipU F (2 * epsU * Du, 2 * epsU * Nu) y + 2 * m := by
  have e : y + (m * (-2 * N) + n * (D + N), m * (2 * D) + n * (D - N))
      = (y + (n * (D + N), n * (D - N))) + (m * (-2 * N), m * (2 * D)) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  rw [e, slip_tau_iter F N D Nu Du epsU hdet hε2 hT m, slip_kappa_iter F N D Nu Du epsU hK n y]

/-- The lattice fact: a site with `t = 0` is a multiple of the kernel `κ = (D + N, D − N)`, with the explicit multiple
`n = ε_u (N_u k₁ − D_u k₂)`. -/
theorem lattice_kappa (N D Nu Du epsU k1 k2 : ℤ) (hdet : Nu * (D + N) - Du * (D - N) = epsU)
    (hε2 : epsU ^ 2 = 1) (hk : (D - N) * k1 - (D + N) * k2 = 0) :
    k1 = (epsU * (Nu * k1 - Du * k2)) * (D + N) ∧ k2 = (epsU * (Nu * k1 - Du * k2)) * (D - N) := by
  constructor
  · linear_combination (-(epsU * k1)) * hdet + (-(epsU * Du)) * hk + (-k1) * hε2
  · linear_combination (-(epsU * k2)) * hdet + (-(epsU * Nu)) * hk + (-k2) * hε2

/-- Step (c), inequality (1) of Q4-strips: on the earlier word the slip `F y − F (y + σ)` is nonnegative where
`t(y) ≤ r` and nonpositive where `t(y) > r` (`r = D + N`). -/
theorem slip_sign (F : Site → ℤ) (N D Nu Du epsU : ℤ) (hN : 0 < N) (hND : N < D) (hr : (D + N) % 2 = 1)
    (hdet : Nu * (D + N) - Du * (D - N) = epsU) (hepsU : epsU = 1 ∨ epsU = -1) (hodd : (Nu + Du) % 2 = 1)
    (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y)
    (hT : ∀ y : Site, F (y + (-2 * N, 2 * D)) = F y + ((D - N) * y.1 - (D + N) * y.2) - (D ^ 2 + 2 * D * N - N ^ 2 + D))
    (hslip : ∀ y : Site, PolyU N D y →
      0 ≤ slipU F (2 * epsU * Du, 2 * epsU * Nu) y ∧ slipU F (2 * epsU * Du, 2 * epsU * Nu) y ≤ 2)
    (y : Site) :
    ((D - N) * y.1 - (D + N) * y.2 ≤ D + N → 0 ≤ slipU F (2 * epsU * Du, 2 * epsU * Nu) y) ∧
    (D + N < (D - N) * y.1 - (D + N) * y.2 → slipU F (2 * epsU * Du, 2 * epsU * Nu) y ≤ 0) := by
  have hε2 : epsU ^ 2 = 1 := by rcases hepsU with rfl | rfl <;> norm_num
  have hT0 : 0 < 2 * (D ^ 2 + 2 * D * N - N ^ 2) := by nlinarith
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = (D - N) * y.1 - (D + N) * y.2 := ⟨_, rfl⟩
  have hrem := Int.emod_def (D + N - t) (2 * (D ^ 2 + 2 * D * N - N ^ 2))
  have hr0 := Int.emod_nonneg (D + N - t) hT0.ne'
  have hr1 := Int.emod_lt_of_pos (D + N - t) hT0
  obtain ⟨y0, hP0, hty0⟩ := window_point N D Nu Du epsU
    (D + N - (D + N - t) % (2 * (D ^ 2 + 2 * D * N - N ^ 2)))
    hN hND hr hdet hepsU hodd (by linarith) (by linarith)
  set m := (D + N - t) / (2 * (D ^ 2 + 2 * D * N - N ^ 2)) with hm
  have hmj : (D + N - (D + N - t) % (2 * (D ^ 2 + 2 * D * N - N ^ 2))) - t
      = 2 * (D ^ 2 + 2 * D * N - N ^ 2) * m := by
    linarith
  have hk0 : (D - N) * (y.1 - y0.1 - m * (-2 * N)) - (D + N) * (y.2 - y0.2 - m * (2 * D)) = 0 := by
    linear_combination (-1 : ℤ) * ht - hty0 - hmj
  obtain ⟨hk1, hk2⟩ := lattice_kappa N D Nu Du epsU (y.1 - y0.1 - m * (-2 * N)) (y.2 - y0.2 - m * (2 * D))
    hdet hε2 hk0
  have hy : y = y0 + (m * (-2 * N) + (epsU * (Nu * (y.1 - y0.1 - m * (-2 * N)) - Du * (y.2 - y0.2 - m * (2 * D))))
      * (D + N), m * (2 * D) + (epsU * (Nu * (y.1 - y0.1 - m * (-2 * N)) - Du * (y.2 - y0.2 - m * (2 * D))))
      * (D - N)) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> linarith
  have hsl := slip_shift_both F N D Nu Du epsU hdet hε2 hT hK m
    (epsU * (Nu * (y.1 - y0.1 - m * (-2 * N)) - Du * (y.2 - y0.2 - m * (2 * D)))) y0
  rw [← hy] at hsl
  obtain ⟨h0, h2⟩ := hslip y0 hP0
  constructor
  · intro hle
    have hm0 : 0 ≤ m := by
      by_contra hneg
      have hm1' : m ≤ -1 := by omega
      have hTm : (2 * (D ^ 2 + 2 * D * N - N ^ 2)) * m ≤ -(2 * (D ^ 2 + 2 * D * N - N ^ 2)) := by
        nlinarith
      linarith
    linarith
  · intro hgt
    have hm1 : m ≤ -1 := by
      by_contra hneg
      have hm0' : 0 ≤ m := by omega
      have : 0 ≤ (2 * (D ^ 2 + 2 * D * N - N ^ 2)) * m := mul_nonneg hT0.le hm0'
      linarith
    linarith

end ZoneSlip

end FLatticePaper.Induction
