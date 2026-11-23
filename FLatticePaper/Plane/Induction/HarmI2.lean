import FLatticePaper.Plane.Induction.ZoneCase
import FLatticePaper.Plane.Induction.ZoneHarmonic

/-! # The harmonic region of I2 (task 49, the fix's harmonic region, eq. (4))

With `U_q = (d_q, n_q)`, `V_p = (−(D − N), D + N)` and `ε = N d_q − n_q D`, the harmonic residue
`R(u) = f(u − U_q) − h₀(u)` (with `f = quarterTurnField F`) changes by `−ε` under `u ↦ u + V_p`.
-/

namespace FLatticePaper.Induction
open Farey FLatticePaper

namespace HarmI2

/-- The harmonic residue `R(u) = f(u − U_q) − h₀(u)` (eq. (4) of the fix). -/
def harmR (F : Site → ℤ) (dq nq : ℤ) (u : Site) : ℤ :=
  quarterTurnField F (u.1 - dq, u.2 - nq) - harmonicGrid u

/-- An integer `c` with `2c = 2ND − N² + D² − N − D`, the constant of the shift along `(N − D, N + D)`. -/
theorem exists_half_pair (N D : ℤ) :
    ∃ c : ℤ, 2 * c = -2 * N * (-D) - N ^ 2 + (-D) ^ 2 - N + (-D) := by
  obtain ⟨l, hl⟩ := Int.even_mul_succ_self N
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self D
  exact ⟨N * D - l + k, by linear_combination hl - hk⟩

/-- The shift `u ↦ u + V_p` changes the residue by `−ε`. -/
theorem harmR_shift_Vp (F : Site → ℤ) (N D nq dq : ℤ) (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y)
    (u : Site) :
    harmR F dq nq (u.1 + -(D - N), u.2 + (D + N)) = harmR F dq nq u - (N * dq - nq * D) := by
  obtain ⟨c, hc⟩ := exists_half_pair N D
  have hZ : F (-((u.2 - nq) + (D + N)), (u.1 - dq) - (D - N) - 1) = F (-(u.2 - nq), (u.1 - dq) - 1) :=
    ZoneHarmonic.fZ_add_Vp F N D hK (u.1 - dq, u.2 - nq)
  have h1 := ZoneHarmonic.harmonicGrid_sub_shift (u.1 + -(D - N) - dq, u.2 + (D + N) - nq) N (-D) c hc
  have e1 : (u.1 + -(D - N) - dq, u.2 + (D + N) - nq) - (N + -D, N - -D) = (u.1 - dq, u.2 - nq) := by
    ext
    · first | (simp; done) | (simp; ring)
    · first | (simp; done) | (simp; ring)
  rw [e1] at h1
  have h2 := ZoneHarmonic.harmonicGrid_sub_shift (u.1 + -(D - N), u.2 + (D + N)) N (-D) c hc
  have e2 : (u.1 + -(D - N), u.2 + (D + N)) - (N + -D, N - -D) = u := by
    ext
    · first | (simp; done) | (simp; ring)
    · first | (simp; done) | (simp; ring)
  rw [e2] at h2
  simp only at h1 h2
  unfold harmR
  rw [quarterTurnField, quarterTurnField]
  simp only [quarterTurn_site]
  ring_nf at hZ h1 h2 ⊢
  linear_combination hZ + h1 - h2

/-- The parent step of the harmonic region: `f(u) ≤ f(u − U_q)` for `u` with `1 − r ≤ s_p(u) ≤ 2r + 1` and `−ε u₂ ≥ 0`.
The sign comes from the parent step (`hps`, the form of `ParentStepSign` with `N, D`), and the two values vanish on the
zero strip of the quarter-turn field where the sign does not apply. -/
theorem key_le (F : Site → ℤ) (N D nq dq : ℤ) (hN : 0 < N) (hND : N < D) (hevQ : (nq + dq) % 2 = 0)
    (hps : ∀ x x' : Site, (x.1 + x.2) % 2 = (x'.1 + x'.2) % 2 →
      N * x.1 - D * x.2 = N * x'.1 - D * x'.2 + 1 →
      ((N * x.1 - D * x.2 < N) → quarterTurnField F x' ≤ quarterTurnField F x) ∧
      (N ≤ N * x.1 - D * x.2 → quarterTurnField F x ≤ quarterTurnField F x'))
    (hzs : ∀ x : Site, 1 - D ≤ N * x.1 - D * x.2 → N * x.1 - D * x.2 ≤ N + 2 * D - 1 →
      quarterTurnField F x = 0)
    (hε : N * dq - nq * D = 1 ∨ N * dq - nq * D = -1) (u : Site)
    (hm1 : 1 - (D + N) ≤ (D + N) * u.1 + (D - N) * u.2)
    (hm2 : (D + N) * u.1 + (D - N) * u.2 ≤ 2 * (D + N) + 1)
    (hy : 0 ≤ -(N * dq - nq * D) * u.2) :
    quarterTurnField F u ≤ quarterTurnField F (u.1 - dq, u.2 - nq) := by
  have hD : 0 < D := by omega
  have hB : 0 ≤ D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  have hkeq : (D + N) * (N * u.1 - D * u.2)
      = N * ((D + N) * u.1 + (D - N) * u.2) - (D ^ 2 + 2 * D * N - N ^ 2) * u.2 := by ring
  have hpar : ((u.1 - dq) + (u.2 - nq)) % 2 = (u.1 + u.2) % 2 := by omega
  have ht_w : N * (u.1 - dq) - D * (u.2 - nq) = (N * u.1 - D * u.2) - (N * dq - nq * D) := by ring
  rcases hε with hε1 | hε1
  · rw [hε1] at hy ht_w
    have hu2 : u.2 ≤ 0 := by linarith
    have hlo : -N < N * u.1 - D * u.2 := by
      by_contra hc
      have hc' := not_lt.mp hc
      nlinarith
    have hps' := hps u (u.1 - dq, u.2 - nq) (by simpa using hpar.symm)
      (by simp only; rw [ht_w]; linarith)
    by_cases hc : N ≤ N * u.1 - D * u.2
    · exact hps'.2 hc
    · have h1 := hzs u (by linarith) (by linarith)
      have h2 := hzs (u.1 - dq, u.2 - nq) (by simp only; rw [ht_w]; linarith) (by simp only; rw [ht_w]; linarith)
      rw [h1, h2]
  · rw [hε1] at hy ht_w
    have hu2 : 0 ≤ u.2 := by linarith
    have hhi : N * u.1 - D * u.2 ≤ 2 * N := by
      by_contra hc
      have hc' := not_le.mp hc
      nlinarith
    have hps' := hps (u.1 - dq, u.2 - nq) u (by simpa using hpar)
      (by simp only; rw [ht_w]; linarith)
    by_cases hc : N * u.1 - D * u.2 + 1 < N
    · exact hps'.1 (by simp only; rw [ht_w]; linarith)
    · have h1 := hzs u (by linarith) (by linarith)
      have h2 := hzs (u.1 - dq, u.2 - nq) (by simp only; rw [ht_w]; linarith) (by simp only; rw [ht_w]; linarith)
      rw [h1, h2]

/-- The values of `F ∘ Z` on the three ranges of `m = s_p(u)`: zero on the strip, `−1` at `m = 2r`, and at least `−1` at
`m = 2r + 1` (binarity at an odd site whose inputs lie on the strips). -/
theorem G_zero (F : Site → ℤ) (N D Nu Du epsU : ℤ) (H : ZoneCase.ZoneHyp F N D Nu Du epsU) (u : Site)
    (hlo : 1 - (D + N) ≤ (D + N) * u.1 + (D - N) * u.2) (hhi : (D + N) * u.1 + (D - N) * u.2 ≤ 2 * (D + N) - 1) :
    F (-u.2, u.1 - 1) = 0 := by
  apply H.hstrip
  · nlinarith [H.hN, H.hND]
  · nlinarith [H.hN, H.hND]

theorem G_minus_two (F : Site → ℤ) (N D Nu Du epsU : ℤ) (H : ZoneCase.ZoneHyp F N D Nu Du epsU)
    (hsharm : ∀ y : Site, 1 - 2 * (D + N) ≤ 2 * D * y.1 + 2 * N * y.2 →
      2 * D * y.1 + 2 * N * y.2 ≤ 2 * (2 * D) - 1 → F y = harmonicGrid y)
    (u : Site) (hm : (D + N) * u.1 + (D - N) * u.2 = 2 * (D + N)) :
    F (-u.2, u.1 - 1) = -1 := by
  have hε2 : epsU ^ 2 = 1 := by rcases H.hepsU with rfl | rfl <;> norm_num
  have hk : (D - N) * (-u.2) - (D + N) * (u.1 - 2) = 0 := by linear_combination (-1 : ℤ) * hm
  obtain ⟨e1, e2⟩ := ZoneSlip.lattice_kappa N D Nu Du epsU (-u.2) (u.1 - 2) H.hdet hε2 hk
  have hZ : (-u.2, u.1 - 1) = (0, 1) + ((epsU * (Nu * (-u.2) - Du * (u.1 - 2))) * (D + N),
      (epsU * (Nu * (-u.2) - Du * (u.1 - 2))) * (D - N)) := by
    ext
    · simp only [Prod.fst_add]; linarith
    · simp only [Prod.snd_add]; linarith
  rw [hZ, ZoneCase.F_kappa_iter F N D H.hK]
  rw [hsharm (0, 1) (by nlinarith [H.hN, H.hND]) (by nlinarith [H.hN, H.hND])]
  exact ZoneCase.harmonic_zero_one

theorem G_minus_three (F : Site → ℤ) (N D Nu Du epsU : ℤ) (H : ZoneCase.ZoneHyp F N D Nu Du epsU)
    (hbin : ∀ c : Site, laplacian F c = -1 ∨ laplacian F c = 0)
    (u : Site) (hm : (D + N) * u.1 + (D - N) * u.2 = 2 * (D + N) + 1) :
    -1 ≤ F (-u.2, u.1 - 1) := by
  -- σ = Z u − (0, 1) has transverse grade −1, so it is an odd site
  have hr := H.hr
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, D - N = 2 * β + 1 := ⟨(D - N - 1) / 2, by omega⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℤ, D + N = 2 * ρ + 1 := ⟨(D + N - 1) / 2, by omega⟩
  set σ : Site := (-u.2, u.1 - 2) with hσ
  have htσ : (D - N) * σ.1 - (D + N) * σ.2 = -1 := by
    rw [hσ]
    linear_combination (-1 : ℤ) * hm
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, σ.1 + σ.2 = 2 * Q - 1 := by
    refine ⟨-β * σ.1 + ρ * σ.2 + σ.2, ?_⟩
    rw [hβ, hρ] at htσ
    linear_combination htσ
  have hodd : ¬ EvenSite σ := by
    unfold EvenSite
    rw [hQ]
    omega
  have hneg : incomingNeg σ = (σ.1, σ.2 - 1) := by
    unfold incomingNeg
    rw [if_neg hodd]
  have hpos : incomingPos σ = (σ.1, σ.2 + 1) := by
    unfold incomingPos
    rw [if_neg hodd]
  have hσ0 : F σ = 0 := by
    apply H.hstrip
    · nlinarith [H.hN, H.hND]
    · nlinarith [H.hN, H.hND]
  have hσ1 : F (σ.1, σ.2 - 1) = 0 := by
    apply H.hstrip
    · nlinarith [H.hN, H.hND]
    · nlinarith [H.hN, H.hND]
  have hZ : (σ.1, σ.2 + 1) = (-u.2, u.1 - 1) := by
    ext
    · simp only [hσ]
    · simp only [hσ]; ring
  have hlap := hbin σ
  unfold laplacian at hlap
  rw [hneg, hpos, hZ, hσ0, hσ1] at hlap
  rcases hlap with h | h <;> linarith

theorem harmR_ge_G (F : Site → ℤ) (N D nq dq : ℤ) (hN : 0 < N) (hND : N < D) (hevQ : (nq + dq) % 2 = 0)
    (hps : ∀ x x' : Site, (x.1 + x.2) % 2 = (x'.1 + x'.2) % 2 →
      N * x.1 - D * x.2 = N * x'.1 - D * x'.2 + 1 →
      ((N * x.1 - D * x.2 < N) → quarterTurnField F x' ≤ quarterTurnField F x) ∧
      (N ≤ N * x.1 - D * x.2 → quarterTurnField F x ≤ quarterTurnField F x'))
    (hzs : ∀ x : Site, 1 - D ≤ N * x.1 - D * x.2 → N * x.1 - D * x.2 ≤ N + 2 * D - 1 →
      quarterTurnField F x = 0)
    (hε : N * dq - nq * D = 1 ∨ N * dq - nq * D = -1) (u : Site)
    (hm1 : 1 - (D + N) ≤ (D + N) * u.1 + (D - N) * u.2)
    (hm2 : (D + N) * u.1 + (D - N) * u.2 ≤ 2 * (D + N) + 1)
    (hy : 0 ≤ -(N * dq - nq * D) * u.2) :
    F (-u.2, u.1 - 1) ≤ harmR F dq nq u := by
  have key := key_le F N D nq dq hN hND hevQ hps hzs hε u hm1 hm2 hy
  unfold harmR
  unfold quarterTurnField at key ⊢
  simp only [quarterTurn_site] at key ⊢
  linarith

theorem harmR_nonneg (F : Site → ℤ) (N D Nu Du epsU nq dq : ℤ) (H : ZoneCase.ZoneHyp F N D Nu Du epsU)
    (hsharm : ∀ y : Site, 1 - 2 * (D + N) ≤ 2 * D * y.1 + 2 * N * y.2 →
      2 * D * y.1 + 2 * N * y.2 ≤ 2 * (2 * D) - 1 → F y = harmonicGrid y)
    (hbin : ∀ c : Site, laplacian F c = -1 ∨ laplacian F c = 0)
    (hevQ : (nq + dq) % 2 = 0)
    (hps : ∀ x x' : Site, (x.1 + x.2) % 2 = (x'.1 + x'.2) % 2 →
      N * x.1 - D * x.2 = N * x'.1 - D * x'.2 + 1 →
      ((N * x.1 - D * x.2 < N) → quarterTurnField F x' ≤ quarterTurnField F x) ∧
      (N ≤ N * x.1 - D * x.2 → quarterTurnField F x ≤ quarterTurnField F x'))
    (hzs : ∀ x : Site, 1 - D ≤ N * x.1 - D * x.2 → N * x.1 - D * x.2 ≤ N + 2 * D - 1 →
      quarterTurnField F x = 0)
    (hε : N * dq - nq * D = 1 ∨ N * dq - nq * D = -1) (u : Site)
    (hm1 : 1 - (D + N) ≤ (D + N) * u.1 + (D - N) * u.2)
    (hm2 : (D + N) * u.1 + (D - N) * u.2 ≤ 2 * (D + N) + 1)
    (hy : 0 ≤ -(N * dq - nq * D) * u.2)
    (hbig : 2 * (D + N) ≤ (D + N) * u.1 + (D - N) * u.2 → (D + N) ≤ -(N * dq - nq * D) * u.2) :
    0 ≤ harmR F dq nq u := by
  have hN := H.hN
  have hND := H.hND
  have hA := harmR_ge_G F N D nq dq hN hND hevQ hps hzs hε u hm1 hm2 hy
  by_cases hlow : (D + N) * u.1 + (D - N) * u.2 ≤ 2 * (D + N) - 1
  · have hz := G_zero F N D Nu Du epsU H u hm1 hlow
    linarith
  · have hge : 2 * (D + N) ≤ (D + N) * u.1 + (D - N) * u.2 := by
      have h1 := Int.lt_iff_add_one_le.mp (not_le.mp hlow)
      linarith
    have hbigD := hbig hge
    have hF : -1 ≤ F (-u.2, u.1 - 1) := by
      rcases (show (D + N) * u.1 + (D - N) * u.2 = 2 * (D + N) ∨
          (D + N) * u.1 + (D - N) * u.2 = 2 * (D + N) + 1 from by
            generalize (D + N) * u.1 + (D - N) * u.2 = mv at hge hm2 ⊢
            omega) with h | h
      · rw [G_minus_two F N D Nu Du epsU H hsharm u h]
      · exact G_minus_three F N D Nu Du epsU H hbin u h
    rcases hε with hε1 | hε1
    · rw [hε1] at hbigD hy
      have hsh := harmR_shift_Vp F N D nq dq H.hK u
      rw [hε1] at hsh
      have hu' : (D + N) * (u.1 + -(D - N)) + (D - N) * (u.2 + (D + N)) = (D + N) * u.1 + (D - N) * u.2 := by
        ring
      have hG' : F (-(u.2 + (D + N)), u.1 + -(D - N) - 1) = F (-u.2, u.1 - 1) := by
        rw [show u.1 + -(D - N) - 1 = u.1 - (D - N) - 1 by ring]
        exact ZoneHarmonic.fZ_add_Vp F N D H.hK u
      have hA' := harmR_ge_G F N D nq dq hN hND hevQ hps hzs (Or.inl hε1) (u.1 + -(D - N), u.2 + (D + N))
        (by simp only; rw [hu']; exact hm1) (by simp only; rw [hu']; exact hm2)
        (by simp only; rw [hε1]; linarith)
      simp only at hA' hG'
      linarith
    · rw [hε1] at hbigD hy
      have hsh := harmR_shift_Vp F N D nq dq H.hK (u.1 + (D - N), u.2 - (D + N))
      have e : (u.1 + (D - N) + -(D - N), u.2 - (D + N) + (D + N)) = u := by
        ext <;> simp
        ring
      rw [e, hε1] at hsh
      have hu' : (D + N) * (u.1 + (D - N)) + (D - N) * (u.2 - (D + N)) = (D + N) * u.1 + (D - N) * u.2 := by
        ring
      have hG' : F (-(u.2 - (D + N)), u.1 + (D - N) - 1) = F (-u.2, u.1 - 1) := by
        have h := ZoneHarmonic.fZ_add_Vp F N D H.hK (u.1 + (D - N), u.2 - (D + N))
        rw [show -(u.2 - (D + N) + (D + N)) = -u.2 by ring,
          show u.1 + (D - N) - (D - N) - 1 = u.1 - 1 by ring] at h
        exact h.symm
      have hA' := harmR_ge_G F N D nq dq hN hND hevQ hps hzs (Or.inr hε1) (u.1 + (D - N), u.2 - (D + N))
        (by simp only; rw [hu']; exact hm1) (by simp only; rw [hu']; exact hm2)
        (by simp only; rw [hε1]; linarith)
      simp only at hA' hG'
      linarith

/-- The window of the harmonic region, lower side: on the closed polygon `z₂ ≥ 0`. -/
theorem geo_nonneg (n d z1 z2 : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hA : 2 - d + n ≤ (d + n) * z1 + (d - n) * z2) (hB : n * z1 - d * z2 ≤ d + n - 1) : 0 ≤ z2 := by
  by_contra h
  have hz2 : z2 ≤ -1 := by omega
  have h1 : 1 ≤ z1 := by
    by_contra hc
    have hc' : z1 ≤ 0 := by omega
    nlinarith
  nlinarith

/-- The window of the harmonic region, upper side: on the closed polygon with `s ≤ 2L − 1`, `z₂ ≤ L = d + n`. -/
theorem geo_le (n d z1 z2 : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hC : 1 - (d * d + 2 * d * n - n * n) ≤ n * z1 - d * z2)
    (hD : (d + n) * z1 + (d - n) * z2 ≤ 2 * (d + n) - 1) : z2 ≤ d + n := by
  by_contra h
  have hz : d + n + 1 ≤ z2 := by omega
  have p2 : z1 ≤ n + 1 - d := by
    by_contra hc
    have hc' : n + 2 - d ≤ z1 := by omega
    nlinarith
  nlinarith

/-- The window of the harmonic region for the shifted point `u = z − W(n − d, n + d)`: the sign `−ε u₂ ∈ [0, L]`, the range
`1 − r ≤ s_p(u) ≤ 2r + 1` and the condition `s_p(u) ≥ 2r ⇒ −ε u₂ ≥ r` (the fix's region of the harmonic step). -/
theorem geo_window (N D nq dq n d z1 z2 W : ℤ) (hnN : n = 2 * N + nq) (hdD : d = 2 * D + dq)
    (hW : (W = 0 ∧ N * dq - nq * D = -1) ∨ (W = 1 ∧ N * dq - nq * D = 1))
    (hN : 1 ≤ N) (hND : N < D)
    (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hr : (D + N) % 2 = 1)
    (hT : 1 - (d * d + 2 * d * n - n * n) ≤ n * z1 - d * z2)
    (hB : n * z1 - d * z2 ≤ d + n - 1)
    (hA : 2 - d + n ≤ (d + n) * z1 + (d - n) * z2)
    (hD : (d + n) * z1 + (d - n) * z2 ≤ 2 * (d + n) - 1) :
    0 ≤ -(N * dq - nq * D) * (z2 - W * (n + d)) ∧
    1 - (D + N) ≤ (D + N) * (z1 - W * (n - d)) + (D - N) * (z2 - W * (n + d)) ∧
    (D + N) * (z1 - W * (n - d)) + (D - N) * (z2 - W * (n + d)) ≤ 2 * (D + N) + 1 ∧
    (2 * (D + N) ≤ (D + N) * (z1 - W * (n - d)) + (D - N) * (z2 - W * (n + d)) →
      (D + N) ≤ -(N * dq - nq * D) * (z2 - W * (n + d))) := by
  have hz2lo := geo_nonneg n d z1 z2 hn hnd hA hB
  have hz2hi := geo_le n d z1 z2 hn hnd hT hD
  have hid : (n + d) * ((D + N) * (z1 - W * (n - d)) + (D - N) * (z2 - W * (n + d)))
      = (D + N) * ((d + n) * z1 + (d - n) * z2) - 2 * (N * dq - nq * D) * (z2 - W * (n + d)) := by
    subst hnN hdD
    ring
  have hc0 : 0 ≤ -(N * dq - nq * D) * (z2 - W * (n + d)) := by
    rcases hW with ⟨h0, he⟩ | ⟨h1, he⟩
    · rw [he, h0]; linarith
    · rw [he, h1]; linarith
  have hcU : -(N * dq - nq * D) * (z2 - W * (n + d)) ≤ n + d := by
    rcases hW with ⟨h0, he⟩ | ⟨h1, he⟩
    · rw [he, h0]; linarith
    · rw [he, h1]; linarith
  generalize hc : -(N * dq - nq * D) * (z2 - W * (n + d)) = c at hc0 hcU ⊢
  have hcid : (n + d) * ((D + N) * (z1 - W * (n - d)) + (D - N) * (z2 - W * (n + d)))
      = (D + N) * ((d + n) * z1 + (d - n) * z2) + 2 * c := by
    rw [hid, ← hc]; ring
  generalize hm : (D + N) * (z1 - W * (n - d)) + (D - N) * (z2 - W * (n + d)) = m at hcid ⊢
  have hr0 : 0 < D + N := by omega
  have hnd0 : 0 < d + n := by omega
  have hmlo : 1 - (D + N) ≤ m := by
    by_contra hcon
    have hm' : m ≤ -(D + N) := by omega
    nlinarith
  have hmhi : m ≤ 2 * (D + N) + 1 := by
    by_contra hcon
    have hm' : 2 * (D + N) + 2 ≤ m := by omega
    nlinarith
  refine ⟨hc0, hmlo, hmhi, ?_⟩
  intro hbig
  have hbig' : 2 * (D + N) ≤ m := hbig
  generalize hs : (d + n) * z1 + (d - n) * z2 = s at hcid hA hD
  by_cases hm2 : m = 2 * (D + N)
  · rw [hm2] at hcid
    by_cases hs1 : s = 2 * (d + n) - 1
    · rw [hs1] at hcid
      have h2c : 2 * c = D + N := by nlinarith
      omega
    · have hq : 2 ≤ 2 * (d + n) - s := by omega
      nlinarith
  · have hm3 : m = 2 * (D + N) + 1 := by omega
    rw [hm3] at hcid
    nlinarith

/-- The other sheet at `ε = −1` (`W = 0`) minus `h₀` is the residue `R(z)`. -/
theorem sheetA_eq_harmR (F : Site → ℤ) (dq nq : ℤ) (z : Site) :
    quarterTurnField F (z.1 - (1 - 0) * dq, z.2 - (1 - 0) * nq) - harmonicGrid z = harmR F dq nq z := by
  unfold harmR
  simp only [sub_zero, one_mul]

/-- An integer `c` with `2c = −2αβ − α² + β² − α + β` (the constant of the harmonic shift along `(α+β, α−β)`). -/
theorem exists_const (α β : ℤ) : ∃ c : ℤ, 2 * c = -2 * α * β - α ^ 2 + β ^ 2 - α + β := by
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self α
  obtain ⟨l, hl⟩ := Int.even_mul_succ_self β
  exact ⟨-α * β - k + l, by linear_combination hk - hl⟩

/-- `F ∘ Z` is invariant under the shift `2V_p`. -/
theorem F_Z_two (F : Site → ℤ) (N D : ℤ) (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y) (a : Site) :
    F (-(a.2 + 2 * (D + N)), a.1 - 2 * (D - N) - 1) = F (-a.2, a.1 - 1) := by
  have h1 := ZoneHarmonic.fZ_add_Vp F N D hK a
  have h2 := ZoneHarmonic.fZ_add_Vp F N D hK (a.1 - (D - N), a.2 + (D + N))
  have e : (-(a.2 + 2 * (D + N)), a.1 - 2 * (D - N) - 1)
      = (-((a.2 + (D + N)) + (D + N)), (a.1 - (D - N)) - (D - N) - 1) := by
    rw [Prod.mk.injEq]
    constructor <;> ring
  simp only at h2
  rw [e, h2, h1]

/-- The other sheet at `ε = +1` (`W = 1`) minus `h₀` is the residue at `z − V`, `V = (n − d, n + d)`, `n = 2N + n_q`,
`d = 2D + d_q` (the identity of the fix's harmonic region, with the parent argument `u − U_q + 2V_p`). -/
theorem sheetC_eq_harmR (F : Site → ℤ) (N D nq dq cq : ℤ)
    (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y) (hε : N * dq - nq * D = 1)
    (hcq : 2 * cq = dq * dq + 2 * dq * nq - nq * nq - dq - nq) (z : Site) :
    quarterTurnField F (z.1 - (1 - 1) * dq - (nq - dq + (N * dq - nq * D) * dq),
        z.2 - (1 - 1) * nq - (nq + dq + (N * dq - nq * D) * nq))
      + (nq * (z.1 - (1 - 1) * dq) - dq * (z.2 - (1 - 1) * nq)) + (cq + 2 * 1) - harmonicGrid z
    = harmR F dq nq (z.1 - ((2 * N + nq) - (2 * D + dq)), z.2 - ((2 * N + nq) + (2 * D + dq))) := by
  obtain ⟨c1, hc1⟩ := exists_const (2 * N) (-2 * D)
  obtain ⟨c2, hc2⟩ := exists_const (2 * N + nq) (-(2 * D + dq))
  have hK2 : 2 * (c1 - c2 + cq + 2 + 4 * D * nq + 2 * D * dq - 2 * N * nq) = 0 := by
    linear_combination hc1 - hc2 + hcq - 4 * hε
  have hconst : c1 - c2 + cq + 2 + 4 * D * nq + 2 * D * dq - 2 * N * nq = 0 := by linarith
  rw [hε]
  have hA := F_Z_two F N D hK (z.1 - ((2 * N + nq) - (2 * D + dq)) - dq, z.2 - ((2 * N + nq) + (2 * D + dq)) - nq)
  have hH1 := ZoneHarmonic.harmonicGrid_sub_shift
    (z.1 - (1 - 1) * dq - (nq - dq + 1 * dq), z.2 - (1 - 1) * nq - (nq + dq + 1 * nq)) (2 * N) (-2 * D) c1 hc1
  have e1 : (z.1 - (1 - 1) * dq - (nq - dq + 1 * dq), z.2 - (1 - 1) * nq - (nq + dq + 1 * nq))
      - (2 * N + -2 * D, 2 * N - -2 * D)
      = (z.1 - ((2 * N + nq) - (2 * D + dq)) - dq, z.2 - ((2 * N + nq) + (2 * D + dq)) - nq) := by
    rw [Prod.mk_sub_mk, Prod.mk.injEq]
    constructor <;> ring
  rw [e1] at hH1
  have hH2 := ZoneHarmonic.harmonicGrid_sub_shift z (2 * N + nq) (-(2 * D + dq)) c2 hc2
  have e2 : z - ((2 * N + nq) + -(2 * D + dq), (2 * N + nq) - -(2 * D + dq))
      = (z.1 - ((2 * N + nq) - (2 * D + dq)), z.2 - ((2 * N + nq) + (2 * D + dq))) := by
    rw [Prod.mk_sub_mk, Prod.mk.injEq]
    constructor <;> ring
  rw [e2] at hH2
  unfold harmR
  unfold quarterTurnField
  simp only [quarterTurn_site]
  ring_nf at hA hH1 hH2 hconst ⊢
  linear_combination hA + hH1 - hH2 + hconst

end HarmI2

end FLatticePaper.Induction
