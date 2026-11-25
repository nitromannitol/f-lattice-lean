import FLatticePaper.Tiles.SubCeilOdd

/-! Task Q25 (sub), the even bottom: the ceiling pack of the child `childQ` and its thresholds.

The even child word `x` has length `M = (D + N)/2` and `N` letters `q`, so its ceiling pack has the step `g (j + 1) = g j + M ε j − N`
and the bounds `0 ≤ g j < M` (`CeilPackE`). The cursor grade of block `k` is `e_k = 2Nk − (D + N) Y_k` (with `Y_k = Yc ε k` of
`SubCeilOdd`). In regime A (`2N ≤ M`) `e_k = 2 (M − N − g (k+1))`, and in regime B (`M < 2N`) `e_k = 2 (N − g (k−1))`. -/

namespace FLatticePaper.Tiles.SubCeilEven

open FLatticePaper.Tiles.SubCeilOdd

/-- The ceiling pack of the even child: length `L = M`, `N` letters `q`, `0 ≤ g < M`. -/
structure CeilPackE (N M : ℤ) (L : ℕ) (ε g : ℕ → ℤ) : Prop where
  hε : ∀ j, ε j = 0 ∨ ε j = 1
  hg0 : g 0 = 0
  hstep : ∀ j, j < L → g (j + 1) = g j + M * ε j - N
  hbd : ∀ j, j ≤ L → 0 ≤ g j ∧ g j < M
  hgL : g L = 0
  hL : (L : ℤ) = M

/-- The grade of the cursor of block `k` with the total `c = D + N`. -/
def ecE (N c : ℤ) (ε : ℕ → ℤ) (k : ℕ) : ℤ := 2 * N * k - c * Yc ε k

/-- The `q`-count of the first `k` letters. -/
def qsum (ε : ℕ → ℤ) (k : ℕ) : ℤ := ∑ j ∈ Finset.range k, ε j

theorem g_eq_qsum (N M : ℤ) (L : ℕ) (ε g : ℕ → ℤ) (h : CeilPackE N M L ε g) :
    ∀ k : ℕ, k ≤ L → g k = M * qsum ε k - N * k := by
  intro k
  induction k with
  | zero => intro _; simp [h.hg0, qsum]
  | succ k ih =>
    intro hk
    have s := h.hstep k (by omega)
    have ih' := ih (by omega)
    rw [s, ih']
    unfold qsum
    rw [Finset.sum_range_succ]
    push_cast
    ring

theorem eps_zero_E (N M : ℤ) (hN : 1 ≤ N) (_hM : N < M) (L : ℕ) (hL1 : 1 ≤ L) (ε g : ℕ → ℤ)
    (h : CeilPackE N M L ε g) : ε 0 = 1 := by
  have h1 := h.hstep 0 (by omega)
  rw [h.hg0] at h1
  have hb := h.hbd 1 (by omega)
  rcases h.hε 0 with h0 | h0
  · rw [h0] at h1
    simp only [mul_zero, zero_add] at h1
    omega
  · exact h0

/-- Regime A (`2N ≤ M`): no two consecutive `q` letters. -/
theorem noqq_E (N M : ℤ) (hA : 2 * N ≤ M) (L : ℕ) (ε g : ℕ → ℤ) (h : CeilPackE N M L ε g)
    (j : ℕ) (hj : j + 2 ≤ L) : ¬ (ε j = 1 ∧ ε (j + 1) = 1) := by
  rintro ⟨h1, h2⟩
  have s1 := h.hstep j (by omega)
  have s2 := h.hstep (j + 1) (by omega)
  have b := h.hbd (j + 2) hj
  have hbj := h.hbd j (by omega)
  rw [h1] at s1
  rw [h2] at s2
  have hL := h.hL
  linarith [b.2, hbj.1]

/-- Regime A: the north indicator of block `j` is the next letter. -/
theorem hasN_A_E (N M : ℤ) (hA : 2 * N ≤ M) (L : ℕ) (ε g : ℕ → ℤ) (h : CeilPackE N M L ε g)
    (j : ℕ) (hj : j + 2 ≤ L) : hasNI ε j = ε (j + 1) := by
  have hq := noqq_E N M hA L ε g h j hj
  have F2 : ¬ (ε j = 1 ∧ tY ε j = 1) := by
    by_cases hj0 : j = 0
    · subst hj0
      simp [tY]
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      rw [tY_succ]
      intro hc
      exact noqq_E N M hA L ε g h m (by omega) ⟨hc.2, hc.1⟩
  rcases h.hε j with h0 | h0 <;> rcases h.hε (j + 1) with h1 | h1
  all_goals (simp [hasNI, tY, h0, h1] at F2 hq ⊢; try omega)

/-- Regime B (`M < 2N`): no two consecutive `0` letters. -/
theorem no00_B (N M : ℤ) (hB : M < 2 * N) (L : ℕ) (ε g : ℕ → ℤ) (h : CeilPackE N M L ε g)
    (j : ℕ) (hj : j + 2 ≤ L) : ¬ (ε j = 0 ∧ ε (j + 1) = 0) := by
  rintro ⟨h1, h2⟩
  have s1 := h.hstep j (by omega)
  have s2 := h.hstep (j + 1) (by omega)
  have b := h.hbd (j + 2) hj
  have hbj := h.hbd j (by omega)
  rw [h1] at s1
  rw [h2] at s2
  have hL := h.hL
  linarith [b.1, hbj.2]

/-- Regime B: the north indicator of block `m + 1` is the letter `ε m`. -/
theorem hasN_B_E (N M : ℤ) (hB : M < 2 * N) (L : ℕ) (ε g : ℕ → ℤ) (h : CeilPackE N M L ε g)
    (m : ℕ) (hm : m + 3 ≤ L) : hasNI ε (m + 1) = ε m := by
  have n1 := no00_B N M hB L ε g h m (by omega)
  have n2 := no00_B N M hB L ε g h (m + 1) (by omega)
  rcases h.hε m with h0 | h0 <;> rcases h.hε (m + 1) with h1 | h1 <;>
    rcases h.hε (m + 1 + 1) with h2 | h2 <;>
    simp [hasNI, tY_succ, h0, h1, h2] at n1 n2 ⊢

/-- Regime A: the grade of block `k` is `2 (M − N − g (k+1))`. -/
theorem ecE_A (N M D : ℤ) (hM : D + N = 2 * M) (hA : 2 * N ≤ M) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPackE N M L ε g) (e0 : ε 0 = 1) :
    ∀ k : ℕ, k + 1 ≤ L → ecE N (D + N) ε k = 2 * (M - N - g (k + 1)) := by
  intro k hk
  have hY : Yc ε k = qsum ε (k + 1) - 1 := by
    have key : ∀ j : ℕ, j + 1 ≤ L → Yc ε j = qsum ε (j + 1) - 1 := by
      intro j
      induction j with
      | zero => intro _; simp [Yc, qsum, e0]
      | succ j ih =>
        intro hj
        rw [Yc_succ, ih (by omega), hasN_A_E N M hA L ε g h j (by omega)]
        unfold qsum
        rw [Finset.sum_range_succ _ (j + 1), Finset.sum_range_succ _ j]
        ring
    exact key k hk
  have hg := g_eq_qsum N M L ε g h (k + 1) hk
  unfold ecE
  rw [hY, hM]
  push_cast at hg ⊢
  linarith [hg]

/-- Regime B: the grade of block `m + 1` is `2 (N − g m)`. -/
theorem ecE_B (N M D : ℤ) (hM : D + N = 2 * M) (hB : M < 2 * N) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPackE N M L ε g) (e0 : ε 0 = 1) (m : ℕ) (hm : m + 2 ≤ L) :
    ecE N (D + N) ε (m + 1) = 2 * (N - g m) := by
  have key : ∀ j : ℕ, j + 2 ≤ L → Yc ε (j + 1) = qsum ε j := by
    intro j
    induction j with
    | zero => intro _; simp [Yc, qsum, hasNI_zero ε e0]
    | succ j ih =>
      intro hj
      rw [Yc_succ, ih (by omega), hasN_B_E N M hB L ε g h j (by omega)]
      unfold qsum
      rw [Finset.sum_range_succ]
  have hY := key m hm
  have hg := g_eq_qsum N M L ε g h m (by omega)
  unfold ecE
  rw [hY, hM]
  push_cast at hg ⊢
  linarith [hg]

/-! ### The thresholds of the block types (both regimes), with `D + N = 2M` -/

/-- Regime A, block `j` of type EE (`ε (j+1) = 0`): the grade plus `N` is at most `K1 = D − 2N`. -/
theorem thrA_EE_E (N M D : ℤ) (hM : D + N = 2 * M) (hA : 2 * N ≤ M) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPackE N M L ε g) (e0 : ε 0 = 1) (j : ℕ) (hj : j + 2 ≤ L) (he : ε (j + 1) = 0) :
    ecE N (D + N) ε j + N ≤ D - 2 * N := by
  rw [ecE_A N M D hM hA L ε g h e0 j (by omega)]
  have s := h.hstep (j + 1) (by omega)
  have b := h.hbd (j + 2) hj
  rw [he] at s
  linarith [b.1]

/-- Regime A, block `j` of type EN (`ε (j+1) = 1`): `K1 − N < e ≤ D − N`. -/
theorem thrA_EN_E (N M D : ℤ) (hM : D + N = 2 * M) (hA : 2 * N ≤ M) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPackE N M L ε g) (e0 : ε 0 = 1) (j : ℕ) (hj : j + 2 ≤ L) (he : ε (j + 1) = 1) :
    (D - 2 * N) - N < ecE N (D + N) ε j ∧ ecE N (D + N) ε j ≤ D - N := by
  rw [ecE_A N M D hM hA L ε g h e0 j (by omega)]
  have s := h.hstep (j + 1) (by omega)
  have b1 := h.hbd (j + 1) (by omega)
  have b2 := h.hbd (j + 2) hj
  rw [he] at s
  constructor <;> linarith [b1.1, b2.2]

/-- Regime A, the window of block `j`: `K1 − D < e ≤ K1 + N`. -/
theorem winA_E (N M D : ℤ) (hM : D + N = 2 * M) (hA : 2 * N ≤ M) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPackE N M L ε g) (e0 : ε 0 = 1) (j : ℕ) (hj : j + 1 ≤ L) :
    (D - 2 * N) - D < ecE N (D + N) ε j ∧ ecE N (D + N) ε j ≤ (D - 2 * N) + N := by
  rw [ecE_A N M D hM hA L ε g h e0 j hj]
  have b := h.hbd (j + 1) hj
  constructor <;> linarith [b.1, b.2]

/-- Regime A, the last block `L − 1`: the grade is at most `D − N`. -/
theorem lastA_E (N M D : ℤ) (hM : D + N = 2 * M) (hA : 2 * N ≤ M) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPackE N M L ε g) (e0 : ε 0 = 1) (hL1 : 1 ≤ L) :
    ecE N (D + N) ε (L - 1) ≤ D - N := by
  rw [ecE_A N M D hM hA L ε g h e0 (L - 1) (by omega)]
  have e : L - 1 + 1 = L := by omega
  rw [e, h.hgL]
  linarith

/-- Regime B, block `m + 1` of type EE (`ε m = 0`): the grade plus `N` is at most `K1 = N`. -/
theorem thrB_EE_E (N M D : ℤ) (hM : D + N = 2 * M) (hB : M < 2 * N) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPackE N M L ε g) (e0 : ε 0 = 1) (m : ℕ) (hm : m + 2 ≤ L) (he : ε m = 0) :
    ecE N (D + N) ε (m + 1) + N ≤ N := by
  rw [ecE_B N M D hM hB L ε g h e0 m hm]
  have s := h.hstep m (by omega)
  have b := h.hbd (m + 1) (by omega)
  rw [he] at s
  linarith [b.1]

/-- Regime B, block `m + 1` of type EN (`ε m = 1`, `ε (m+1) = 0`): `K1 − N < e ≤ D − N` with `K1 = N`. -/
theorem thrB_EN_E (N M D : ℤ) (hM : D + N = 2 * M) (hB : M < 2 * N) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPackE N M L ε g) (e0 : ε 0 = 1) (m : ℕ) (hm : m + 3 ≤ L) (hm1 : ε m = 1)
    (he : ε (m + 1) = 0) :
    N - N < ecE N (D + N) ε (m + 1) ∧ ecE N (D + N) ε (m + 1) ≤ D - N := by
  rw [ecE_B N M D hM hB L ε g h e0 m (by omega)]
  have s1 := h.hstep m (by omega)
  have s2 := h.hstep (m + 1) (by omega)
  have b1 := h.hbd (m + 1) (by omega)
  have b2 := h.hbd (m + 2) (by omega)
  rw [hm1] at s1
  rw [he] at s2
  constructor <;> linarith [b1.1, b1.2, b2.1]

/-- Regime B, block `m + 1` of type NE (`ε m = 1`, `ε (m+1) = 1`): `D − N < e`. -/
theorem thrB_NE_E (N M D : ℤ) (hM : D + N = 2 * M) (hB : M < 2 * N) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPackE N M L ε g) (e0 : ε 0 = 1) (m : ℕ) (hm : m + 3 ≤ L) (hm1 : ε m = 1)
    (he : ε (m + 1) = 1) :
    D - N < ecE N (D + N) ε (m + 1) := by
  rw [ecE_B N M D hM hB L ε g h e0 m (by omega)]
  have s1 := h.hstep m (by omega)
  have s2 := h.hstep (m + 1) (by omega)
  have b2 := h.hbd (m + 2) (by omega)
  rw [hm1] at s1
  rw [he] at s2
  linarith [b2.2]

/-- Regime B, the window of block `m + 1`: `K1 − D < e ≤ K1 + N` with `K1 = N`. -/
theorem winB_E (N M D : ℤ) (hM : D + N = 2 * M) (hB : M < 2 * N) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPackE N M L ε g) (e0 : ε 0 = 1) (m : ℕ) (hm : m + 2 ≤ L) :
    N - D < ecE N (D + N) ε (m + 1) ∧ ecE N (D + N) ε (m + 1) ≤ N + N := by
  rw [ecE_B N M D hM hB L ε g h e0 m hm]
  have b := h.hbd m (by omega)
  constructor <;> linarith [b.1, b.2]

/-- Regime B, the last block `L − 1`: the grade is at most `D − N`. -/
theorem lastB_E (N M D : ℤ) (hM : D + N = 2 * M) (_hN : 1 ≤ N) (hNM : N < M) (hB : M < 2 * N) (L : ℕ)
    (ε g : ℕ → ℤ) (h : CeilPackE N M L ε g) (e0 : ε 0 = 1) (hL2 : 2 ≤ L) :
    ecE N (D + N) ε (L - 1) ≤ D - N := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 2 := ⟨L - 2, by omega⟩
  have e : k + 2 - 1 = k + 1 := by omega
  rw [e, ecE_B N M D hM hB (k + 2) ε g h e0 k le_rfl]
  have s1 := h.hstep k (by omega)
  have s2 := h.hstep (k + 1) (by omega)
  have hL := h.hgL
  have b0 := h.hbd k (by omega)
  have b1 := h.hbd (k + 1) (by omega)
  have hε1 : ε (k + 1) = 0 := by
    rcases h.hε (k + 1) with h1 | h1
    · exact h1
    · rw [h1] at s2
      have : g (k + 2) = g (k + 1) + M - N := by linarith
      rw [hL] at this
      linarith [b1.1]
  rw [hε1] at s2
  have hgk : g (k + 1) = N := by linarith
  rcases h.hε k with hk0 | hk0
  · rw [hk0] at s1
    linarith
  · rw [hk0] at s1
    linarith

end FLatticePaper.Tiles.SubCeilEven
