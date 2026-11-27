import FLatticePaper.Plane.Induction.CapRay
import FLatticePaper.Plane.Induction.WiredCovered

/-! # The all-slope cap ray on the wider depth range `2nK ≤ 3d + 5n − 1`

`CapRay.ray_cap` needs the depth bound `2nK ≤ 3d + 3n − 1`, which is exactly the harmonic strip condition for the odd anchor at
`k = K`. The top depth is covered by the odd anchor at `K − 1` (the strip condition is `2n(K−1) ≤ 3d + 3n − 1`), with the
monotone comparison of `CapRay`, whenever `d + 2n − 1 ≤ nK`; below that the anchor at `k` itself is used. The statement is the
same diagonal cap as `CapRay.ray_cap`, on the wider range `2nK ≤ 3d + 5n − 1`. -/

namespace FLatticePaper.CapRayWide

open FLatticePaper FLatticePaper.Induction FLatticePaper.CapAnchors FLatticePaper.CapRecursion
open FLatticePaper.SheetMonoChild FLatticePaper.CapRay

theorem ray_cap_wide (frame : ChildFrame) {F : Field} (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    (hN3 : 3 ≤ frame.child.num) (hND : 4 ≤ frame.child.den - frame.child.num)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num)
    (J K : ℕ)
    (hJ1 : 2 * frame.child.num * (J : ℤ) ≤ frame.child.num + frame.child.den - 2)
    (hJ2 : frame.child.num + frame.child.den - 2 < 2 * frame.child.num * ((J : ℤ) + 1))
    (hK : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1) :
    ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)) := by
  have hodd := sheetMono_odd_of_signed frame hP hsig
  have heven := sheetMono_even_of_signed frame hP hsig
  obtain ⟨N, hN⟩ : ∃ N, frame.child.num = N := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, frame.child.den = D := ⟨_, rfl⟩
  have tg : ∀ x y : ℤ, frame.tGrade (x, y) = N * x - D * y := fun x y => by
    simp only [ChildFrame.tGrade, hN, hD]
  simp only [hN, hD] at hs hJ1 hJ2 hK hN3 hND
  have hpq := start_parity frame (p := p) (q := q) (by rw [hN, hD]; exact hs)
  have hbin := hP.binary
  have hN0 : 0 < N := by omega
  have hND' : N < D := by omega
  -- the diagonal monotonicity of the odd sheet on the ray (from `hsig`)
  have hmono : ∀ n : ℕ, n ≤ J → F (p + (n : ℤ), q + ((n : ℤ) + 2)) ≤ F (p + ((n : ℤ) + 2), q + ((n : ℤ) + 2)) := by
    intro n hn
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := by positivity
    apply hodd
    · unfold EvenSite; simp only; omega
    · unfold EvenSite; simp only; omega
    · rw [tg, tg]; nlinarith
    · rw [tg]; nlinarith
  -- the zero strip values
  have hA0 : 0 ≤ F (p, q) := by
    have h := zero_value hP.strips (z := (p, q)) (by rw [tg, hD]; nlinarith) (by rw [tg, hN, hD]; nlinarith)
    rw [h]
  have hA1 : 0 ≤ F (p + 1, q + 1) := by
    have h := zero_value hP.strips (z := (p + 1, q + 1)) (by rw [tg, hD]; nlinarith) (by rw [tg, hN, hD]; nlinarith)
    rw [h]
  -- the even anchors: B_0, B_1 by the zero strip, B_j for j ≥ 2 by the even monotonicity and the harmonic anchor
  have hB : ∀ j : ℕ, j ≤ J → F (p + (j : ℤ) + 1, q + (j : ℤ)) ≤ FLatticePaper.QuadraticCap.capMin j := by
    intro j hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · have h := zero_value hP.strips (z := (p + 0 + 1, q + 0)) (by simp only [tg]; nlinarith) (by simp only [tg]; nlinarith)
        simp only [Nat.cast_zero, add_zero] at h ⊢
        rw [h, FLatticePaper.QuadraticCap.capMin_zero]
      · have h := zero_value hP.strips (z := (p + ((1 : ℕ) : ℤ) + 1, q + ((1 : ℕ) : ℤ))) (by simp only [tg, Nat.cast_one]; nlinarith) (by simp only [tg, Nat.cast_one]; nlinarith)
        simp only [Nat.cast_one] at h ⊢
        rw [h, FLatticePaper.QuadraticCap.capMin_one]
    · have hjz : (2 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj2
      have hjJ : (j : ℤ) ≤ J := by exact_mod_cast hj
      have hj1 : (1 : ℤ) ≤ (j : ℤ) := by omega
      have hu : EvenSite (p + (j : ℤ) + 1, q + (j : ℤ)) := by unfold EvenSite; simp only; omega
      have hv : EvenSite (1 - (j : ℤ), (j : ℤ) - 1) := by unfold EvenSite; simp only; omega
      have hle := heven (p + (j : ℤ) + 1, q + (j : ℤ)) (1 - (j : ℤ), (j : ℤ) - 1) hu hv
        (by rw [tg, tg]; nlinarith) (by rw [tg]; nlinarith)
      have hlo : 1 - 2 * frame.child.den ≤ 2 * frame.child.num * (1 - (j : ℤ)) := by
        rw [hN, hD]; nlinarith
      have hhi : 2 * frame.child.num * (1 - (j : ℤ)) ≤ 2 * (frame.child.den + frame.child.num) - 1 := by
        rw [hN, hD]; nlinarith
      have hanc := anchor_value hP.strips (j : ℤ) hlo hhi
      rw [hanc] at hle
      exact hle
  -- the odd anchors for J+2 < k ≤ K. If `D + 2N − 1 ≤ N k`, the anchor at index `k − 1` is in the harmonic strip (since
  -- `2N(k−1) ≤ 3D+3N−1` by `hK`), and `capMin k ≤ capMin (k−1)`; otherwise the anchor at `k` itself is in the strip.
  have hanchor : ∀ k : ℕ, J + 2 < k → k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)) := by
    intro k hk1 hk2
    have hkJ : (J : ℤ) + 3 ≤ (k : ℤ) := by exact_mod_cast hk1
    have hkK : (k : ℤ) ≤ (K : ℤ) := by exact_mod_cast hk2
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
    have hk1' : (1 : ℤ) ≤ (k : ℤ) := by omega
    have hNkK : N * (k : ℤ) ≤ N * (K : ℤ) := mul_le_mul_of_nonneg_left hkK hN0.le
    have hNk0 : N * ((J : ℤ) + 3) ≤ N * (k : ℤ) := mul_le_mul_of_nonneg_left hkJ hN0.le
    have hNJ : 0 ≤ N * (J : ℤ) := mul_nonneg hN0.le (by positivity)
    have hvneg : N * (p + (k : ℤ)) - D * (q + (k : ℤ)) ≤ 0 := by
      have := mul_nonneg (sub_nonneg.2 hND'.le) hk0
      linarith
    by_cases hA : D + 2 * N - 1 ≤ N * (k : ℤ)
    · have hlo : 1 - 2 * D ≤ D + 3 * N - 2 * N * ((k : ℤ) - 1) := by
        linarith
      have hhi : D + 3 * N - 2 * N * ((k : ℤ) - 1) ≤ 2 * (D + N) - 1 := by
        linarith
      have hanc := anchor_value_odd hP.strips ((k : ℤ) - 1) (by rw [hN, hD]; exact hlo) (by rw [hN, hD]; exact hhi)
      have hle := hodd (2 - ((k : ℤ) - 1), ((k : ℤ) - 1) - 1) (p + (k : ℤ), q + (k : ℤ))
        (by unfold EvenSite; simp only; omega) (by unfold EvenSite; simp only; omega)
        (by rw [tg, tg]; linarith) (by rw [tg]; exact hvneg)
      rw [hanc] at hle
      have h2a := FLatticePaper.QuadraticCap.two_capMin (k : ℤ)
      have h2b := FLatticePaper.QuadraticCap.two_capMin ((k : ℤ) - 1)
      have hdiff : FLatticePaper.QuadraticCap.capMin (k : ℤ) ≤ FLatticePaper.QuadraticCap.capMin ((k : ℤ) - 1) := by
        linarith
      exact le_trans hdiff hle
    · have hA' := not_le.mp hA
      have hlo : 1 - 2 * D ≤ D + 3 * N - 2 * N * (k : ℤ) := by
        linarith
      have hhi : D + 3 * N - 2 * N * (k : ℤ) ≤ 2 * (D + N) - 1 := by
        linarith
      have hanc := anchor_value_odd hP.strips (k : ℤ) (by rw [hN, hD]; exact hlo) (by rw [hN, hD]; exact hhi)
      have hle := hodd (2 - (k : ℤ), (k : ℤ) - 1) (p + (k : ℤ), q + (k : ℤ))
        (by unfold EvenSite; simp only; omega) (by unfold EvenSite; simp only; omega)
        (by rw [tg, tg]; linarith) (by rw [tg]; exact hvneg)
      rw [hanc] at hle
      exact hle
  exact diag_cap F p q hpq hbin J K hmono hA0 hA1 hB hanchor

/-- **The cap ray for a proper frame on the wider depth range** (`n ≥ 3`, `d − n ≥ 4`, `2nK ≤ 3d + 5n − 1`): the same start as
`CapRay.ray_start`, with `ray_cap_wide`. -/
theorem hAS_wide_of_proper {frame : FLatticePaper.Induction.ChildFrame} {G : Field} (hP : frame.Packet G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    (hN3 : 3 ≤ frame.child.num) (hND : 4 ≤ frame.child.den - frame.child.num) (K : ℕ)
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1) :
    ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
      ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)) := by
  obtain ⟨p, q, hs⟩ := FLatticePaper.CapRay.ray_start frame
  have hX : 0 ≤ frame.child.num + frame.child.den - 2 := by omega
  obtain ⟨J, hJ1, hJ2⟩ := FLatticePaper.WiredCovered.floor_bounds (frame.child.num + frame.child.den - 2)
    (2 * frame.child.num) (by omega) hX
  exact ⟨p, q, hs, ray_cap_wide frame hP hsig hN3 hND hs J K hJ1 hJ2 hKr⟩

end FLatticePaper.CapRayWide
