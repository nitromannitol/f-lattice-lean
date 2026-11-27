import FLatticePaper.Plane.Induction.RootArith

/-! # The free closure of a bottom root, in grades

For the conjugate child `(n', d') = (D − N, D + N)` (period `T' = 2T`, `T = D² + 2DN − N²`), a span shift changes the grades of a
root `z` by `t ↦ t − 2Tj`, `s ↦ s + 2Ti`. A root `z = zTurn x` of the parent point `x = (x₁, x₂)` has `t(z) = D + N − v` and
`s(z) = 2 (u − N)`, with `u = N x₁ − D x₂` and `v = (D+N) x₁ + (D−N) x₂`.

The free sets of the conjugate child are described by grade conditions (`closedPolygon`, the H and V spectra, and the one-pixel
boundary). `free_closure_B` says: if some shift of `z` is free, then the parent point is in one of the two classes
(`u = 0`, `v ≡ 0 mod 2T` for even `x`; `u = N`, `v ≡ D + N mod 2T` for odd `x`). -/

namespace FLatticePaper.RootFree

/-- The conjugate closed polygon in grades: even `t`, or odd `t`. -/
def polyG (N D T t s : ℤ) : Prop :=
  (t % 2 = 0 → 2 - 2 * T ≤ t ∧ t ≤ 2 * D - 2 ∧ 0 ≤ s ∧ s ≤ 2 * T + 2 * (D - N)) ∧
    (t % 2 = 1 → D - N - 2 * T ≤ t ∧ t ≤ D + N ∧ 2 - 2 * N ≤ s ∧ s ≤ 2 * T + 2 * D - 2)

/-- The H spectrum of the conjugate child. -/
def hSpecG (N D t : ℤ) : Prop :=
  (t % 2 = 0 ∧ 2 ≤ t ∧ t ≤ 2 * D - 2) ∨ (t % 2 = 1 ∧ D - N ≤ t ∧ t ≤ D + N)

/-- The V spectrum of the conjugate child. -/
def vSpecG (N D s : ℤ) : Prop :=
  s % 2 = 0 ∧ ((0 ≤ s ∧ s ≤ 2 * (D - N)) ∨ (2 - 2 * N ≤ s ∧ s ≤ 2 * D - 2))

/-- A free H point of the conjugate child, in grades (`f − (0,1)` has grades `(t + (D+N), s − 2N)`). -/
def FreeGradeH (N D T t s : ℤ) : Prop :=
  polyG N D T t s ∧ ¬ polyG N D T (t + (D + N)) (s - 2 * N) ∧ hSpecG N D t

/-- A free V point of the conjugate child, in grades (`f − (1,0)` has grades `(t − (D−N), s − 2D)`). -/
def FreeGradeV (N D T t s : ℤ) : Prop :=
  polyG N D T t s ∧ ¬ polyG N D T (t - (D - N)) (s - 2 * D) ∧ vSpecG N D s

/-- The H case with `w` odd: the integrality lattice forces `q ∈ {−1, 0}`, and each value is excluded. -/
theorem fh_even_impossible (N D q m : ℤ) (hN : 0 < N) (hND : N < D)
    (hw_odd : ((D + N) * q + (D - N) * m) % 2 = 1)
    (hw1 : N - D + 2 ≤ (D + N) * q + (D - N) * m) (hw2 : (D + N) * q + (D - N) * m ≤ D + N - 2)
    (hs1 : -N ≤ m * D - N * q) (hs2 : m * D - N * q ≤ D - 1) : False := by
  obtain ⟨w, hw⟩ : ∃ w, w = (D + N) * q + (D - N) * m := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = m * D - N * q := ⟨_, rfl⟩
  rw [← hw] at hw_odd hw1 hw2
  rw [← hs] at hs1 hs2
  have key1 : q * (D * D + 2 * D * N - N * N) = D * w - (D - N) * s := by
    rw [hw, hs]; ring
  have key2 : m * (D * D + 2 * D * N - N * N) = N * w + (D + N) * s := by
    rw [hw, hs]; ring
  have hTpos : 0 < D * D + 2 * D * N - N * N := by nlinarith
  have hq_hi : q * (D * D + 2 * D * N - N * N) ≤ (D * D + 2 * D * N - N * N) - 2 * D := by
    nlinarith
  have hq_lo : 2 * D * N - 2 * D * D + 3 * D - N ≤ q * (D * D + 2 * D * N - N * N) := by
    nlinarith
  have hq0 : q ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith
  have hq1 : -1 ≤ q := by
    by_contra h
    push Not at h
    nlinarith
  rcases (show q = -1 ∨ q = 0 by omega) with hq | hq
  · -- q = −1: s = mD + N ∈ [−N, D − 1]
    subst hq
    have hm : m = -1 ∨ m = 0 := by
      have h1 : m ≤ 0 := by
        by_contra h
        push Not at h
        nlinarith
      have h2 : -1 ≤ m := by
        by_contra h
        push Not at h
        nlinarith
      omega
    rcases hm with hm | hm
    · subst hm
      omega
    · subst hm
      omega
  · -- q = 0: s = mD ∈ [−N, D − 1] forces m = 0, then w = 0 is even
    subst hq
    have hm : m = 0 := by
      by_contra h
      rcases lt_or_gt_of_ne h with h1 | h1
      · nlinarith
      · nlinarith
    subst hm
    omega

/-- **The free closure of a bottom root.** If some span shift of `z = zTurn x` is free, the parent point `x` is in one of the
two classes: for even `x` (odd root), `u = 0` and `v ≡ 0 (mod 2T)`; for odd `x` (even root), `u = N` and `v ≡ D + N (mod 2T)`. -/
theorem free_closure_B (N D T x1 x2 : ℤ) (hN : 0 < N) (hND : N < D) (hodd : (N + D) % 2 = 1)
    (hcop : IsCoprime N D) (hT : T = D * D + 2 * D * N - N * N)
    (hwin : ((x1 + x2) % 2 = 0 → 1 - (D + N) ≤ N * x1 - D * x2 ∧ N * x1 - D * x2 ≤ 0) ∧
      ((x1 + x2) % 2 = 1 → 1 - D ≤ N * x1 - D * x2 ∧ N * x1 - D * x2 ≤ N))
    (hfree : ∃ i j : ℤ,
      FreeGradeH N D T (D + N - ((D + N) * x1 + (D - N) * x2) - 2 * T * j)
          (2 * (N * x1 - D * x2 - N) + 2 * T * i) ∨
        FreeGradeV N D T (D + N - ((D + N) * x1 + (D - N) * x2) - 2 * T * j)
          (2 * (N * x1 - D * x2 - N) + 2 * T * i)) :
    ((x1 + x2) % 2 = 0 → N * x1 - D * x2 = 0 ∧ ∃ k, (D + N) * x1 + (D - N) * x2 = 2 * T * k) ∧
    ((x1 + x2) % 2 = 1 → N * x1 - D * x2 = N ∧
      ∃ k, (D + N) * x1 + (D - N) * x2 - (D + N) = 2 * T * k) := by
  subst hT
  obtain ⟨a, ha⟩ : ∃ a, D + N = 2 * a + 1 := ⟨(D + N - 1) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, D - N = 2 * b + 1 := ⟨(D - N - 1) / 2, by omega⟩
  have hvpar : ((D + N) * x1 + (D - N) * x2) % 2 = (x1 + x2) % 2 := by
    have e : (D + N) * x1 + (D - N) * x2 = (x1 + x2) + 2 * (a * x1 + b * x2) := by
      rw [ha, hb]; ring
    rw [e, Int.add_mul_emod_self_left]
  have hTbig : 2 * D + 2 * N - 2 < D * D + 2 * D * N - N * N := by nlinarith
  refine ⟨fun hpar => ?_, fun hpar => ?_⟩
  · -- x even: the H-odd case gives the class; the V-odd case is excluded by the window
    have hwin' := hwin.1 hpar
    obtain ⟨hu1, hu2⟩ := hwin'
    have hv0 : ((D + N) * x1 + (D - N) * x2) % 2 = 0 := by rw [hvpar]; exact hpar
    obtain ⟨i, j, hfree⟩ := hfree
    rcases hfree with hfh | hfv
    · obtain ⟨-, -, hspec⟩ := hfh
      unfold hSpecG at hspec
      obtain ⟨Q, hQ⟩ : ∃ Q, Q = (D * D + 2 * D * N - N * N) * j := ⟨_, rfl⟩
      have h2Q : 2 * (D * D + 2 * D * N - N * N) * j = 2 * Q := by rw [hQ]; ring
      rw [h2Q] at hspec
      obtain ⟨V, hV⟩ : ∃ V, V = (D + N) * x1 + (D - N) * x2 := ⟨_, rfl⟩
      rw [← hV] at hspec hv0
      have ht1 : (D + N - V - 2 * Q) % 2 = 1 := by omega
      have hodd' : (D + N - V - 2 * Q) % 2 = 1 := ht1
      have hspec' : D - N ≤ D + N - V - 2 * Q ∧ D + N - V - 2 * Q ≤ D + N := by
        rcases hspec with h | h
        · omega
        · exact ⟨h.2.1, h.2.2⟩
      obtain ⟨j0, hj0⟩ : ∃ j0, D + N - (D + N - V - 2 * Q) = 2 * j0 := ⟨(V + 2 * Q) / 2, by omega⟩
      have hv : (D + N) * x1 + (D - N) * x2 = 2 * j0 + 2 * (D * D + 2 * D * N - N * N) * (-j) := by
        rw [← hV]
        linear_combination hj0 - 2 * hQ
      have := FLatticePaper.RootArith.arith_even N D x1 x2 j0 (-j) hN hND hodd hu1 hu2 (by omega) (by omega) hv
      exact ⟨this.1, -j, this.2⟩
    · -- the V-odd case: 2 − 2N ≤ s ≤ 2D − 2 and s = 2(u − N) + 2Ti force i = 0 and u ∈ [1, D + N − 1]
      obtain ⟨-, -, hvs⟩ := hfv
      unfold vSpecG at hvs
      have hs1 : 2 - 2 * N ≤ 2 * (N * x1 - D * x2 - N) + 2 * (D * D + 2 * D * N - N * N) * i := by
        rcases hvs.2 with h | h
        · linarith [h.1]
        · exact h.1
      have hs2 : 2 * (N * x1 - D * x2 - N) + 2 * (D * D + 2 * D * N - N * N) * i ≤ 2 * D - 2 := by
        rcases hvs.2 with h | h
        · linarith [h.2]
        · exact h.2
      exfalso
      rcases lt_trichotomy i 0 with hi | hi | hi
      · have hi' : i ≤ -1 := by omega
        have : (D * D + 2 * D * N - N * N) * i ≤ -(D * D + 2 * D * N - N * N) := by nlinarith
        nlinarith
      · subst hi
        nlinarith
      · have hi' : 1 ≤ i := by omega
        have : (D * D + 2 * D * N - N * N) ≤ (D * D + 2 * D * N - N * N) * i := by nlinarith
        nlinarith
  · -- x odd: the H-even case is impossible; the V-even case gives the class
    have hv1 : ((D + N) * x1 + (D - N) * x2) % 2 = 1 := by rw [hvpar]; omega
    have hwin' := hwin.2 hpar
    obtain ⟨hu1, hu2⟩ := hwin'
    obtain ⟨i, j, hfree⟩ := hfree
    rcases hfree with hfh | hfv
    · exfalso
      obtain ⟨-, -, hspec⟩ := hfh
      unfold hSpecG at hspec
      obtain ⟨Q, hQ⟩ : ∃ Q, Q = (D * D + 2 * D * N - N * N) * j := ⟨_, rfl⟩
      have h2Q : 2 * (D * D + 2 * D * N - N * N) * j = 2 * Q := by rw [hQ]; ring
      rw [h2Q] at hspec
      obtain ⟨V, hV⟩ : ∃ V, V = (D + N) * x1 + (D - N) * x2 := ⟨_, rfl⟩
      rw [← hV] at hspec hv1
      have hspec' : 2 ≤ D + N - V - 2 * Q ∧ D + N - V - 2 * Q ≤ 2 * D - 2 := by
        rcases hspec with h | h
        · exact ⟨h.2.1, h.2.2⟩
        · omega
      have hw_eq : (D + N) * (x1 + 2 * D * j) + (D - N) * (x2 + 2 * N * j)
          = V + 2 * Q := by
        rw [hV, hQ]; ring
      have hsm : (x2 + 2 * N * j) * D - N * (x1 + 2 * D * j) = -(N * x1 - D * x2) := by ring
      refine fh_even_impossible N D (x1 + 2 * D * j) (x2 + 2 * N * j) hN hND ?_ ?_ ?_ ?_ ?_
      · rw [hw_eq]; omega
      · rw [hw_eq]; omega
      · rw [hw_eq]; omega
      · rw [hsm]; omega
      · rw [hsm]; omega
    · obtain ⟨hpoly, -, hvs⟩ := hfv
      unfold vSpecG at hvs
      obtain ⟨Q, hQ⟩ : ∃ Q, Q = (D * D + 2 * D * N - N * N) * j := ⟨_, rfl⟩
      have h2Q : 2 * (D * D + 2 * D * N - N * N) * j = 2 * Q := by rw [hQ]; ring
      obtain ⟨V, hV⟩ : ∃ V, V = (D + N) * x1 + (D - N) * x2 := ⟨_, rfl⟩
      rw [← hV] at hv1
      have ht_even : (D + N - V - 2 * (D * D + 2 * D * N - N * N) * j) % 2 = 0 := by
        rw [h2Q]; omega
      have hs0 : 0 ≤ 2 * (N * x1 - D * x2 - N) + 2 * (D * D + 2 * D * N - N * N) * i := by
        exact (hpoly.1 (by rw [← hV]; exact ht_even)).2.2.1
      have hs2 : 2 * (N * x1 - D * x2 - N) + 2 * (D * D + 2 * D * N - N * N) * i ≤ 2 * D - 2 := by
        rcases hvs.2 with h | h
        · linarith [h.2]
        · exact h.2
      have hl0 : 0 ≤ N * x1 - D * x2 - N + (D * D + 2 * D * N - N * N) * i := by linarith
      have hl1 : N * x1 - D * x2 - N + (D * D + 2 * D * N - N * N) * i ≤ D - 1 := by linarith
      exact FLatticePaper.RootArith.arith_odd N D x1 x2 i hN hND hodd hcop hpar hu1 hu2 hl0 hl1

end FLatticePaper.RootFree
