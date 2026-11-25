import FLatticePaper.Plane.Induction.CapRecursion
import FLatticePaper.Plane.Induction.QuadraticCap
import Mathlib.Tactic.IntervalCases

/-! # The diagonal cap in general `(N, D)`-grades (the abstract form of `CapRay.ray_cap`)

`CapRay.ray_cap` proves the diagonal cap for a frame's packet, with the grades `tGrade = N x − D y` (`N = child.num`, `D = child.den`)
and `sGrade = (D+N) x + (D−N) y`. The proof uses only the grades, the binary laplacian, the zero strip, the harmonic strip and the two
same-sheet monotonicities; none of the frame's geometry. This module states it for arbitrary integers `N, D`, so that it applies to a
residual field whose strips are the same windows in its own `(N, D)` grades (the rotated long V case, `N = (d−n)/2`, `D = (d+n)/2`).

The strips are the windows of `HasStrips`: the zero window `1 − D ≤ N x − D y ≤ N + 2D − 1`, and the harmonic window
`1 − 2D ≤ (D+N) x + (D−N) y ≤ 2(D+N) − 1`, on which the field is `harmonicGrid`. -/

namespace FLatticePaper.CapRayGrades

open FLatticePaper FLatticePaper.Induction FLatticePaper.CapRecursion

/-- **A start of the ray with odd parity.** For coprime `N, D` with `D + N` odd there are `p, q` with `N p − D q = 2 − N` and
`p + q` odd: shift a solution by `(D, N)`, which keeps `N p − D q` and changes `p + q` by `D + N`. -/
theorem ray_start_odd (N D : ℤ) (hcop : IsCoprime N D) (hodd : (D + N) % 2 = 1) :
    ∃ p q : ℤ, N * p - D * q = 2 - N ∧ (p + q) % 2 = 1 := by
  obtain ⟨u, v, huv⟩ := hcop
  have h0 : N * ((2 - N) * u) - D * (-((2 - N) * v)) = 2 - N := by linear_combination (2 - N) * huv
  by_cases hpar : ((2 - N) * u + -((2 - N) * v)) % 2 = 1
  · exact ⟨(2 - N) * u, -((2 - N) * v), h0, hpar⟩
  · refine ⟨(2 - N) * u + D, -((2 - N) * v) + N, ?_, ?_⟩
    · linear_combination h0
    · omega

/-- **The diagonal cap in `(N, D)`-grades.** For `p, q` with `N p − D q = 2 − N` and `p + q` odd, `N ≥ 3`, `D − N ≥ 4`, the
zero strip, the harmonic strip and the two sheet monotonicities in the `(N, D)`-grades, and the anchor ranges `J, K`, the ray
satisfies `m(k) ≤ F (p+k, q+k)` for `k ≤ K`. Only `0 < N < D` is used: the proper conditions `3 ≤ N`, `4 ≤ D − N` of the H
frame are not needed here (checked by a probe build; the conclusion also holds numerically at the rotated words with `N ∈ {1,2}`). -/
theorem ray_cap_NDgrades {F : Field} (N D : ℤ)
    (hN0 : 0 < N) (hNDlt : N < D)
    (hbin : ∀ x : Site, laplacian F x = -1 ∨ laplacian F x = 0)
    (hzero : ∀ w : Site, 1 - D ≤ N * w.1 - D * w.2 → N * w.1 - D * w.2 ≤ N + 2 * D - 1 → F w = 0)
    (hharm : ∀ w : Site, 1 - 2 * D ≤ (D + N) * w.1 + (D - N) * w.2 → (D + N) * w.1 + (D - N) * w.2 ≤ 2 * (D + N) - 1 →
      F w = FLatticePaper.Induction.harmonicGrid w)
    (hodd : ∀ u v : Site, ¬ EvenSite u → ¬ EvenSite v → N * u.1 - D * u.2 ≤ N * v.1 - D * v.2 →
      N * v.1 - D * v.2 ≤ 0 → F u ≤ F v)
    (heven : ∀ u v : Site, EvenSite u → EvenSite v → N * u.1 - D * u.2 ≤ N * v.1 - D * v.2 →
      N * v.1 - D * v.2 ≤ 0 → F u ≤ F v)
    {p q : ℤ} (hs : N * p - D * q = 2 - N) (hpq : (p + q) % 2 = 1)
    (J K : ℕ)
    (hJ1 : 2 * N * (J : ℤ) ≤ N + D - 2)
    (hJ2 : N + D - 2 < 2 * N * ((J : ℤ) + 1))
    (hK : 2 * N * (K : ℤ) ≤ 3 * D + 3 * N - 1) :
    ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)) := by
  have hND' : N < D := hNDlt
  -- the diagonal monotonicity of the odd sheet on the ray
  have hmono : ∀ n : ℕ, n ≤ J → F (p + (n : ℤ), q + ((n : ℤ) + 2)) ≤ F (p + ((n : ℤ) + 2), q + ((n : ℤ) + 2)) := by
    intro n hn
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := by positivity
    apply hodd
    · unfold EvenSite; simp only; omega
    · unfold EvenSite; simp only; omega
    · nlinarith
    · nlinarith
  -- the zero strip values at the first two ray sites
  have hA0 : 0 ≤ F (p, q) := by
    have h := hzero (p, q) (by dsimp only; nlinarith) (by dsimp only; nlinarith)
    rw [h]
  have hA1 : 0 ≤ F (p + 1, q + 1) := by
    have h := hzero (p + 1, q + 1) (by dsimp only; nlinarith) (by dsimp only; nlinarith)
    rw [h]
  -- the even anchors B_j
  have hB : ∀ j : ℕ, j ≤ J → F (p + (j : ℤ) + 1, q + (j : ℤ)) ≤ FLatticePaper.QuadraticCap.capMin j := by
    intro j hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · have h := hzero (p + 0 + 1, q + 0) (by dsimp only; nlinarith) (by dsimp only; nlinarith)
        simp only [Nat.cast_zero, add_zero] at h ⊢
        rw [h, FLatticePaper.QuadraticCap.capMin_zero]
      · have h := hzero (p + ((1 : ℕ) : ℤ) + 1, q + ((1 : ℕ) : ℤ)) (by dsimp only; push_cast; nlinarith)
          (by dsimp only; push_cast; nlinarith)
        simp only [Nat.cast_one] at h ⊢
        rw [h, FLatticePaper.QuadraticCap.capMin_one]
    · have hjz : (2 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj2
      have hjJ : (j : ℤ) ≤ J := by exact_mod_cast hj
      have hj1 : (1 : ℤ) ≤ (j : ℤ) := by omega
      have hu : EvenSite (p + (j : ℤ) + 1, q + (j : ℤ)) := by unfold EvenSite; simp only; omega
      have hv : EvenSite (1 - (j : ℤ), (j : ℤ) - 1) := by unfold EvenSite; simp only; omega
      have hle := heven (p + (j : ℤ) + 1, q + (j : ℤ)) (1 - (j : ℤ), (j : ℤ) - 1) hu hv
        (by dsimp only; nlinarith) (by dsimp only; nlinarith)
      have hanc := hharm (1 - (j : ℤ), (j : ℤ) - 1)
        (by dsimp only; nlinarith) (by dsimp only; nlinarith)
      rw [FLatticePaper.CapRecursion.harmonicGrid_anchor] at hanc
      rw [hanc] at hle
      exact hle
  -- the odd anchors m(k) ≤ F(p+k, q+k) for J+2 < k ≤ K
  have hanchor : ∀ k : ℕ, J + 2 < k → k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)) := by
    intro k hk1 hk2
    have hkJ : (J : ℤ) + 3 ≤ (k : ℤ) := by exact_mod_cast hk1
    have hkK : (k : ℤ) ≤ (K : ℤ) := by exact_mod_cast hk2
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
    have hanc := hharm (2 - (k : ℤ), (k : ℤ) - 1)
      (by dsimp only; nlinarith) (by dsimp only; nlinarith)
    rw [FLatticePaper.CapRecursion.harmonicGrid_anchor_odd] at hanc
    have hle := hodd (2 - (k : ℤ), (k : ℤ) - 1) (p + (k : ℤ), q + (k : ℤ))
      (by unfold EvenSite; simp only; omega) (by unfold EvenSite; simp only; omega)
      (by dsimp only; nlinarith) (by dsimp only; nlinarith)
    rw [hanc] at hle
    exact hle
  exact diag_cap F p q hpq hbin J K hmono hA0 hA1 hB hanchor

end FLatticePaper.CapRayGrades
