import FLatticePaper.Plane.Induction.OppCover
import FLatticePaper.Plane.Induction.OppPieces
import FLatticePaper.Plane.Induction.OppYBox

/-! # The core dispatch of the opposite collar (generated).

Given a free V site `u = (u₁, u₂)` of the child and its shift `(k, m) ∈ {−1,0,1}²`, the opposite point `Y = u + (k, m)` has its parity,
the parent windows of the parent quarter turn at `x = Y − V_q`, and the coverage of `s(Y)`. The case split is on the piece of `u`
and the parity of `Y` (six sub-lemmas, one per case, each with its nine shifts), so that each declaration is under the heartbeat budget. -/

namespace FLatticePaper.OppCore

open FLatticePaper FLatticePaper.W1 FLatticePaper.OppCover

theorem core_plus_O_0 (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = 1)
    (hCd : C * d = D * w1T n d + (1) * (d - n)) (hCn : C * n = N * w1T n d - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (h1 : (¬ EvenSite (u1, u2) ∧ n - w1T n d ≤ w1t n d (u1, u2) ∧ w1t n d (u1, u2) ≤ d ∧ 2 - d + n ≤ w1s n d (u1, u2) ∧ w1s n d (u1, u2) ≤ d + n - 2)) (h2 : (EvenSite (u1 + k, u2 + m) ∧ d + n - 1 - w1T n d ≤ w1t n d (u1 + k, u2 + m) ∧ w1t n d (u1 + k, u2 + m) ≤ 1 ∧ 2 * n - w1T n d + 1 ≤ w1s n d (u1 + k, u2 + m) ∧ w1s n d (u1 + k, u2 + m) ≤ -1)) :
    (EvenSite (u1 + k, u2 + m) ∧ (1 - 2 * D ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 2 * D + 2 * N - 1) ∧ (1 - 2 * d ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 2 * (d + n) - 1)) := by
  have hT0 : 0 < w1T n d := by unfold w1T; nlinarith
  have hσ : w1T n d * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2) := by
    linear_combination (-(u1 + u2)) * hCd + (u2 - u1) * hCn
  dsimp only [w1t, w1s] at h1 h2
  rcases hk with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_p0_O_az N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_p0_O_za N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_p0_O_zb N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_p0_O_bz N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega

theorem core_plus_O_1 (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = 1)
    (hCd : C * d = D * w1T n d + (1) * (d - n)) (hCn : C * n = N * w1T n d - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (h1 : (¬ EvenSite (u1, u2) ∧ n - w1T n d ≤ w1t n d (u1, u2) ∧ w1t n d (u1, u2) ≤ d ∧ 2 - d + n ≤ w1s n d (u1, u2) ∧ w1s n d (u1, u2) ≤ d + n - 2)) (h2 : (¬ EvenSite (u1 + k, u2 + m) ∧ d - w1T n d + 1 ≤ w1t n d (u1 + k, u2 + m) ∧ w1t n d (u1 + k, u2 + m) ≤ n - 1 ∧ d + n - 1 - w1T n d ≤ w1s n d (u1 + k, u2 + m) ∧ w1s n d (u1 + k, u2 + m) ≤ 1 - d + n)) :
    (¬ EvenSite (u1 + k, u2 + m) ∧ (N - 3 * D + 2 ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 3 * D + N - 2) ∧ (2 - 3 * d + n ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 3 * d + n - 2)) := by
  have hT0 : 0 < w1T n d := by unfold w1T; nlinarith
  have hσ : w1T n d * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2) := by
    linear_combination (-(u1 + u2)) * hCd + (u2 - u1) * hCn
  dsimp only [w1t, w1s] at h1 h2
  rcases hk with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_p1_O_aa N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_p1_O_ab N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_p1_O_zz N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_p1_O_ba N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_p1_O_bb N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩

theorem core_plus_E0_0 (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = 1)
    (hCd : C * d = D * w1T n d + (1) * (d - n)) (hCn : C * n = N * w1T n d - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (h1 : (EvenSite (u1, u2) ∧ 2 - w1T n d ≤ w1t n d (u1, u2) ∧ w1t n d (u1, u2) ≤ d + n - 2 ∧ 0 ≤ w1s n d (u1, u2) ∧ w1s n d (u1, u2) ≤ 2 * n)) (h2 : (EvenSite (u1 + k, u2 + m) ∧ d + n - 1 - w1T n d ≤ w1t n d (u1 + k, u2 + m) ∧ w1t n d (u1 + k, u2 + m) ≤ 1 ∧ 2 * n - w1T n d + 1 ≤ w1s n d (u1 + k, u2 + m) ∧ w1s n d (u1 + k, u2 + m) ≤ -1)) :
    (EvenSite (u1 + k, u2 + m) ∧ (1 - 2 * D ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 2 * D + 2 * N - 1) ∧ (1 - 2 * d ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 2 * (d + n) - 1)) := by
  have hT0 : 0 < w1T n d := by unfold w1T; nlinarith
  have hσ : w1T n d * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2) := by
    linear_combination (-(u1 + u2)) * hCd + (u2 - u1) * hCn
  dsimp only [w1t, w1s] at h1 h2
  rcases hk with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p0_E0_aa N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p0_E0_ab N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p0_E0_zz N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p0_E0_ba N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p0_E0_bb N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩

theorem core_plus_E0_1 (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = 1)
    (hCd : C * d = D * w1T n d + (1) * (d - n)) (hCn : C * n = N * w1T n d - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (h1 : (EvenSite (u1, u2) ∧ 2 - w1T n d ≤ w1t n d (u1, u2) ∧ w1t n d (u1, u2) ≤ d + n - 2 ∧ 0 ≤ w1s n d (u1, u2) ∧ w1s n d (u1, u2) ≤ 2 * n)) (h2 : (¬ EvenSite (u1 + k, u2 + m) ∧ d - w1T n d + 1 ≤ w1t n d (u1 + k, u2 + m) ∧ w1t n d (u1 + k, u2 + m) ≤ n - 1 ∧ d + n - 1 - w1T n d ≤ w1s n d (u1 + k, u2 + m) ∧ w1s n d (u1 + k, u2 + m) ≤ 1 - d + n)) :
    (¬ EvenSite (u1 + k, u2 + m) ∧ (N - 3 * D + 2 ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 3 * D + N - 2) ∧ (2 - 3 * d + n ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 3 * d + n - 2)) := by
  have hT0 : 0 < w1T n d := by unfold w1T; nlinarith
  have hσ : w1T n d * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2) := by
    linear_combination (-(u1 + u2)) * hCd + (u2 - u1) * hCn
  dsimp only [w1t, w1s] at h1 h2
  rcases hk with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p1_E0_az N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p1_E0_za N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p1_E0_zb N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p1_E0_bz N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega

theorem core_plus_E1_0 (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = 1)
    (hCd : C * d = D * w1T n d + (1) * (d - n)) (hCn : C * n = N * w1T n d - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (h1 : (EvenSite (u1, u2) ∧ 2 * n + 2 ≤ w1s n d (u1, u2) ∧ w1s n d (u1, u2) ≤ d + n - 2 ∧ 2 - w1T n d ≤ w1t n d (u1, u2) ∧ w1t n d (u1, u2) ≤ 2 * n - w1T n d - 1)) (h2 : (EvenSite (u1 + k, u2 + m) ∧ d + n - 1 - w1T n d ≤ w1t n d (u1 + k, u2 + m) ∧ w1t n d (u1 + k, u2 + m) ≤ 1 ∧ 2 * n - w1T n d + 1 ≤ w1s n d (u1 + k, u2 + m) ∧ w1s n d (u1 + k, u2 + m) ≤ -1)) :
    (EvenSite (u1 + k, u2 + m) ∧ (1 - 2 * D ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 2 * D + 2 * N - 1) ∧ (1 - 2 * d ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 2 * (d + n) - 1)) := by
  have hT0 : 0 < w1T n d := by unfold w1T; nlinarith
  have hσ : w1T n d * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2) := by
    linear_combination (-(u1 + u2)) * hCd + (u2 - u1) * hCn
  dsimp only [w1t, w1s] at h1 h2
  rcases hk with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p0_E1_aa N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p0_E1_ab N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p0_E1_zz N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p0_E1_ba N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p0_E1_bb N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩

theorem core_plus_E1_1 (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
    (hCd : C * d = D * w1T n d + (1) * (d - n)) (hCn : C * n = N * w1T n d - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (h1 : (EvenSite (u1, u2) ∧ 2 * n + 2 ≤ w1s n d (u1, u2) ∧ w1s n d (u1, u2) ≤ d + n - 2 ∧ 2 - w1T n d ≤ w1t n d (u1, u2) ∧ w1t n d (u1, u2) ≤ 2 * n - w1T n d - 1)) (h2 : (¬ EvenSite (u1 + k, u2 + m) ∧ d - w1T n d + 1 ≤ w1t n d (u1 + k, u2 + m) ∧ w1t n d (u1 + k, u2 + m) ≤ n - 1 ∧ d + n - 1 - w1T n d ≤ w1s n d (u1 + k, u2 + m) ∧ w1s n d (u1 + k, u2 + m) ≤ 1 - d + n)) :
    (¬ EvenSite (u1 + k, u2 + m) ∧ (N - 3 * D + 2 ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 3 * D + N - 2) ∧ (2 - 3 * d + n ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 3 * d + n - 2)) := by
  have hT0 : 0 < w1T n d := by unfold w1T; nlinarith
  have hσ : w1T n d * ((D + N) * u1 + (D - N) * u2) = 2 * (1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2) := by
    linear_combination (-(u1 + u2)) * hCd + (u2 - u1) * hCn
  dsimp only [w1t, w1s] at h1 h2
  rcases hk with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p1_E1_az N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1], by linarith [hcov.1.2]⟩, ⟨by linarith [hcov.2.1], by linarith [hcov.2.2]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p1_E1_za N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1], by linarith [hcov.1.2]⟩, ⟨by linarith [hcov.2.1], by linarith [hcov.2.2]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p1_E1_zb N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1], by linarith [hcov.1.2]⟩, ⟨by linarith [hcov.2.1], by linarith [hcov.2.2]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_p1_E1_bz N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1], by linarith [hcov.1.2]⟩, ⟨by linarith [hcov.2.1], by linarith [hcov.2.2]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega

theorem core_plus (n d N D C nq dq u1 u2 k m : ℤ)
    (hL : (d + n) % 2 = 0) (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = 1)
    (hCd : C * d = D * w1T n d + (1) * (d - n)) (hCn : C * n = N * w1T n d - (1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (hfree : FLatticePaper.W1OffCollar.freeVn n d (u1, u2))
    (hc : FLatticePaper.W1.StrictInterior n d ((u1 + k, u2 + m) + (d, n))) :
    (EvenSite (u1 + k, u2 + m) ∧ (1 - 2 * D ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 2 * D + 2 * N - 1) ∧ (1 - 2 * d ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 2 * (d + n) - 1)) ∨ (¬ EvenSite (u1 + k, u2 + m) ∧ (N - 3 * D + 2 ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 3 * D + N - 2) ∧ (2 - 3 * d + n ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 3 * d + n - 2)) := by
  have hfv := FLatticePaper.OppPieces.freeVn_pieces hn3 hnd hfree
  have hyb := FLatticePaper.OppYBox.ybox_plus hL (u1 + k, u2 + m) hc
  rcases hfv with h1 | h1 | h1 <;> rcases hyb with h2 | h2
  · exact Or.inl (core_plus_O_0 n d N D C nq dq u1 u2 k m hn3 hnd hD2 hN0 hpD hpE hdet hCd hCn hCL hk hm h1 h2)
  · exact Or.inr (core_plus_O_1 n d N D C nq dq u1 u2 k m hn3 hnd hD2 hN0 hpD hpE hdet hCd hCn hCL hk hm h1 h2)
  · exact Or.inl (core_plus_E0_0 n d N D C nq dq u1 u2 k m hn3 hnd hD2 hN0 hpD hpE hdet hCd hCn hCL hk hm h1 h2)
  · exact Or.inr (core_plus_E0_1 n d N D C nq dq u1 u2 k m hn3 hnd hD2 hN0 hpD hpE hdet hCd hCn hCL hk hm h1 h2)
  · exact Or.inl (core_plus_E1_0 n d N D C nq dq u1 u2 k m hn3 hnd hD2 hN0 hpD hpE hdet hCd hCn hCL hk hm h1 h2)
  · exact Or.inr (core_plus_E1_1 n d N D C nq dq u1 u2 k m hn3 hnd hD2 hN0 hpD hpE hCd hCn hCL hk hm h1 h2)

theorem core_minus_O_0 (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = -1)
    (hCd : C * d = D * w1T n d + (-1) * (d - n)) (hCn : C * n = N * w1T n d - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (-1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (h1 : (¬ EvenSite (u1, u2) ∧ n - w1T n d ≤ w1t n d (u1, u2) ∧ w1t n d (u1, u2) ≤ d ∧ 2 - d + n ≤ w1s n d (u1, u2) ∧ w1s n d (u1, u2) ≤ d + n - 2)) (h2 : (EvenSite (u1 + k, u2 + m) ∧ d + n - 1 - w1T n d ≤ w1t n d (u1 + k, u2 + m) ∧ w1t n d (u1 + k, u2 + m) ≤ 1 ∧ 2 * n + 1 ≤ w1s n d (u1 + k, u2 + m) ∧ w1s n d (u1 + k, u2 + m) ≤ w1T n d - 1)) :
    (EvenSite (u1 + k, u2 + m) ∧ (1 - 2 * D ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 2 * D + 2 * N - 1) ∧ (1 - 2 * d ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 2 * (d + n) - 1)) := by
  have hT0 : 0 < w1T n d := by unfold w1T; nlinarith
  have hσ : w1T n d * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2) := by
    linear_combination (-(u1 + u2)) * hCd + (u2 - u1) * hCn
  dsimp only [w1t, w1s] at h1 h2
  rcases hk with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_m0_O_az N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_m0_O_za N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_m0_O_zb N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_m0_O_bz N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega

theorem core_minus_O_1 (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = -1)
    (hCd : C * d = D * w1T n d + (-1) * (d - n)) (hCn : C * n = N * w1T n d - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (-1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (h1 : (¬ EvenSite (u1, u2) ∧ n - w1T n d ≤ w1t n d (u1, u2) ∧ w1t n d (u1, u2) ≤ d ∧ 2 - d + n ≤ w1s n d (u1, u2) ∧ w1s n d (u1, u2) ≤ d + n - 2)) (h2 : (¬ EvenSite (u1 + k, u2 + m) ∧ d - w1T n d + 1 ≤ w1t n d (u1 + k, u2 + m) ∧ w1t n d (u1 + k, u2 + m) ≤ n - 1 ∧ d + n - 1 ≤ w1s n d (u1 + k, u2 + m) ∧ w1s n d (u1 + k, u2 + m) ≤ w1T n d + 1 - d + n)) :
    (¬ EvenSite (u1 + k, u2 + m) ∧ (N - 3 * D + 2 ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 3 * D + N - 2) ∧ (2 - 3 * d + n ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 3 * d + n - 2)) := by
  have hT0 : 0 < w1T n d := by unfold w1T; nlinarith
  have hσ : w1T n d * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2) := by
    linear_combination (-(u1 + u2)) * hCd + (u2 - u1) * hCn
  dsimp only [w1t, w1s] at h1 h2
  rcases hk with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_m1_O_aa N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_m1_O_ab N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_m1_O_zz N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_m1_O_ba N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 1 := by omega
    have hcov := cov_m1_O_bb N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩

theorem core_minus_E0_0 (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = -1)
    (hCd : C * d = D * w1T n d + (-1) * (d - n)) (hCn : C * n = N * w1T n d - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (-1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (h1 : (EvenSite (u1, u2) ∧ 2 - w1T n d ≤ w1t n d (u1, u2) ∧ w1t n d (u1, u2) ≤ d + n - 2 ∧ 0 ≤ w1s n d (u1, u2) ∧ w1s n d (u1, u2) ≤ 2 * n)) (h2 : (EvenSite (u1 + k, u2 + m) ∧ d + n - 1 - w1T n d ≤ w1t n d (u1 + k, u2 + m) ∧ w1t n d (u1 + k, u2 + m) ≤ 1 ∧ 2 * n + 1 ≤ w1s n d (u1 + k, u2 + m) ∧ w1s n d (u1 + k, u2 + m) ≤ w1T n d - 1)) :
    (EvenSite (u1 + k, u2 + m) ∧ (1 - 2 * D ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 2 * D + 2 * N - 1) ∧ (1 - 2 * d ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 2 * (d + n) - 1)) := by
  have hT0 : 0 < w1T n d := by unfold w1T; nlinarith
  have hσ : w1T n d * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2) := by
    linear_combination (-(u1 + u2)) * hCd + (u2 - u1) * hCn
  dsimp only [w1t, w1s] at h1 h2
  rcases hk with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m0_E0_aa N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m0_E0_ab N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m0_E0_zz N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m0_E0_ba N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m0_E0_bb N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩

theorem core_minus_E0_1 (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = -1)
    (hCd : C * d = D * w1T n d + (-1) * (d - n)) (hCn : C * n = N * w1T n d - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (-1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (h1 : (EvenSite (u1, u2) ∧ 2 - w1T n d ≤ w1t n d (u1, u2) ∧ w1t n d (u1, u2) ≤ d + n - 2 ∧ 0 ≤ w1s n d (u1, u2) ∧ w1s n d (u1, u2) ≤ 2 * n)) (h2 : (¬ EvenSite (u1 + k, u2 + m) ∧ d - w1T n d + 1 ≤ w1t n d (u1 + k, u2 + m) ∧ w1t n d (u1 + k, u2 + m) ≤ n - 1 ∧ d + n - 1 ≤ w1s n d (u1 + k, u2 + m) ∧ w1s n d (u1 + k, u2 + m) ≤ w1T n d + 1 - d + n)) :
    (¬ EvenSite (u1 + k, u2 + m) ∧ (N - 3 * D + 2 ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 3 * D + N - 2) ∧ (2 - 3 * d + n ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 3 * d + n - 2)) := by
  have hT0 : 0 < w1T n d := by unfold w1T; nlinarith
  have hσ : w1T n d * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2) := by
    linear_combination (-(u1 + u2)) * hCd + (u2 - u1) * hCn
  dsimp only [w1t, w1s] at h1 h2
  rcases hk with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m1_E0_az N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m1_E0_za N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m1_E0_zb N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hp1, hp2, hq1, hq2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m1_E0_bz N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega

theorem core_minus_E1_0 (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = -1)
    (hCd : C * d = D * w1T n d + (-1) * (d - n)) (hCn : C * n = N * w1T n d - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (-1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (h1 : (EvenSite (u1, u2) ∧ 2 * n + 2 ≤ w1s n d (u1, u2) ∧ w1s n d (u1, u2) ≤ d + n - 2 ∧ 2 - w1T n d ≤ w1t n d (u1, u2) ∧ w1t n d (u1, u2) ≤ 2 * n - w1T n d - 1)) (h2 : (EvenSite (u1 + k, u2 + m) ∧ d + n - 1 - w1T n d ≤ w1t n d (u1 + k, u2 + m) ∧ w1t n d (u1 + k, u2 + m) ≤ 1 ∧ 2 * n + 1 ≤ w1s n d (u1 + k, u2 + m) ∧ w1s n d (u1 + k, u2 + m) ≤ w1T n d - 1)) :
    (EvenSite (u1 + k, u2 + m) ∧ (1 - 2 * D ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 2 * D + 2 * N - 1) ∧ (1 - 2 * d ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 2 * (d + n) - 1)) := by
  have hT0 : 0 < w1T n d := by unfold w1T; nlinarith
  have hσ : w1T n d * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2) := by
    linear_combination (-(u1 + u2)) * hCd + (u2 - u1) * hCn
  dsimp only [w1t, w1s] at h1 h2
  rcases hk with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m0_E1_aa N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m0_E1_ab N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m0_E1_zz N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m0_E1_ba N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m0_E1_bb N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩

theorem core_minus_E1_1 (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = -1)
    (hCd : C * d = D * w1T n d + (-1) * (d - n)) (hCn : C * n = N * w1T n d - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (-1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (h1 : (EvenSite (u1, u2) ∧ 2 * n + 2 ≤ w1s n d (u1, u2) ∧ w1s n d (u1, u2) ≤ d + n - 2 ∧ 2 - w1T n d ≤ w1t n d (u1, u2) ∧ w1t n d (u1, u2) ≤ 2 * n - w1T n d - 1)) (h2 : (¬ EvenSite (u1 + k, u2 + m) ∧ d - w1T n d + 1 ≤ w1t n d (u1 + k, u2 + m) ∧ w1t n d (u1 + k, u2 + m) ≤ n - 1 ∧ d + n - 1 ≤ w1s n d (u1 + k, u2 + m) ∧ w1s n d (u1 + k, u2 + m) ≤ w1T n d + 1 - d + n)) :
    (¬ EvenSite (u1 + k, u2 + m) ∧ (N - 3 * D + 2 ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 3 * D + N - 2) ∧ (2 - 3 * d + n ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 3 * d + n - 2)) := by
  have hT0 : 0 < w1T n d := by unfold w1T; nlinarith
  have hσ : w1T n d * ((D + N) * u1 + (D - N) * u2) = 2 * (-1) * (n * u1 - d * u2) + C * ((d + n) * u1 + (d - n) * u2) := by
    linear_combination (-(u1 + u2)) * hCd + (u2 - u1) * hCn
  dsimp only [w1t, w1s] at h1 h2
  rcases hk with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m1_E1_az N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m1_E1_za N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m1_E1_zb N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega
  · obtain ⟨hp0, hq1, hq2, hp1, hp2⟩ := h1
    obtain ⟨hy0, hy1, hy2, hz1, hz2⟩ := h2
    simp only [EvenSite] at hp0
    have hu : (u1 + u2) % 2 = 0 := by omega
    have hcov := cov_m1_E1_bz N D n d (w1T n d) C u1 u2 (by unfold w1T; ring) hT0 hCd hCn hCL hσ hn3 hnd hD2 hN0 hpD hpE hu
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hy0, ⟨by linarith [hcov.1.1, hdet], by linarith [hcov.1.2, hdet]⟩, ⟨by linarith [hcov.2.1, hdet], by linarith [hcov.2.2, hdet]⟩⟩
  · exfalso
    simp only [EvenSite] at h1 h2
    omega

theorem core_minus (n d N D C nq dq u1 u2 k m : ℤ)
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1) (hdet : N * dq - D * nq = -1)
    (hCd : C * d = D * w1T n d + (-1) * (d - n)) (hCn : C * n = N * w1T n d - (-1) * (d + n))
    (hCL : C * (d + n) = (D + N) * w1T n d - 2 * (-1) * n)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (hfree : FLatticePaper.W1OffCollar.freeVn n d (u1, u2))
    (hc : FLatticePaper.W1.StrictInterior n d (u1 + k, u2 + m)) :
    (EvenSite (u1 + k, u2 + m) ∧ (1 - 2 * D ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 2 * D + 2 * N - 1) ∧ (1 - 2 * d ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 2 * (d + n) - 1)) ∨ (¬ EvenSite (u1 + k, u2 + m) ∧ (N - 3 * D + 2 ≤ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ∧ (D + N) * (u1 + k - (nq - dq)) + (D - N) * (u2 + m - (nq + dq)) ≤ 3 * D + N - 2) ∧ (2 - 3 * d + n ≤ (d + n) * (u1 + k) + (d - n) * (u2 + m) ∧ (d + n) * (u1 + k) + (d - n) * (u2 + m) ≤ 3 * d + n - 2)) := by
  have hfv := FLatticePaper.OppPieces.freeVn_pieces hn3 hnd hfree
  have hyb := FLatticePaper.OppYBox.ybox_minus (u1 + k, u2 + m) hc
  rcases hfv with h1 | h1 | h1 <;> rcases hyb with h2 | h2
  · exact Or.inl (core_minus_O_0 n d N D C nq dq u1 u2 k m hn3 hnd hD2 hN0 hpD hpE hdet hCd hCn hCL hk hm h1 h2)
  · exact Or.inr (core_minus_O_1 n d N D C nq dq u1 u2 k m hn3 hnd hD2 hN0 hpD hpE hdet hCd hCn hCL hk hm h1 h2)
  · exact Or.inl (core_minus_E0_0 n d N D C nq dq u1 u2 k m hn3 hnd hD2 hN0 hpD hpE hdet hCd hCn hCL hk hm h1 h2)
  · exact Or.inr (core_minus_E0_1 n d N D C nq dq u1 u2 k m hn3 hnd hD2 hN0 hpD hpE hdet hCd hCn hCL hk hm h1 h2)
  · exact Or.inl (core_minus_E1_0 n d N D C nq dq u1 u2 k m hn3 hnd hD2 hN0 hpD hpE hdet hCd hCn hCL hk hm h1 h2)
  · exact Or.inr (core_minus_E1_1 n d N D C nq dq u1 u2 k m hn3 hnd hD2 hN0 hpD hpE hdet hCd hCn hCL hk hm h1 h2)

end FLatticePaper.OppCore
