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

end ZoneSlip

end FLatticePaper.Induction
