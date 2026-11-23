import Mathlib

/-! # Task 97: the quadratic cap arithmetic (ALL_SLOPE_STEP, "The uniform quadratic cap")

`capMin k = −k(k−1)/2` is the parabola `m` of the cap. The recurrence of the cap, `2m(k−1) − 1 − m(k−2) = m(k)`, and the monotonicity
`A_k ≥ 2A_(k−1) − 1 − B_(k−2)` give `A_k ≥ m(k)` by induction, as long as the `B`-bound `B_j ≤ m(j)` holds (ALL_SLOPE_STEP: `B_j ≤ m(j)` for
`j ≤ floor(u)`, from the even harmonic anchors). Beyond that range the odd anchors give `A_k ≥ m(k)` directly (named as the anchor inequality).
The strip, anchor and admission facts are the hypotheses; this file proves only the arithmetic. -/

namespace FLatticePaper.QuadraticCap

/-- The parabola `m(k) = −k(k−1)/2` of the cap. -/
def capMin (k : ℤ) : ℤ := -(k * (k - 1) / 2)

theorem two_capMin (k : ℤ) : 2 * capMin k = -(k * (k - 1)) := by
  unfold capMin
  obtain ⟨t, ht⟩ := Int.even_mul_pred_self k
  rw [ht]
  omega

/-- The cap recurrence `2m(k−1) − 1 − m(k−2) = m(k)`. -/
theorem capMin_rec (k : ℤ) : 2 * capMin (k - 1) - 1 - capMin (k - 2) = capMin k := by
  have h1 := two_capMin (k - 1)
  have h2 := two_capMin (k - 2)
  have h0 := two_capMin k
  have h : 2 * (2 * capMin (k - 1) - 1 - capMin (k - 2)) = 2 * capMin k := by
    linear_combination 2 * h1 - h2 - h0
  omega

theorem capMin_zero : capMin 0 = 0 := by
  unfold capMin
  norm_num

theorem capMin_one : capMin 1 = 0 := by
  unfold capMin
  norm_num

/-- **The cap induction** (ALL_SLOPE_STEP): if `B_j ≤ m(j)` for `j ≤ J` and `A_k ≥ 2A_(k−1) − 1 − B_(k−2)` for `2 ≤ k ≤ J + 2`, with
`A_0, A_1 ≥ 0`, then `A_k ≥ m(k)` for `k ≤ J + 2`. -/
theorem cap_induction (A B : ℕ → ℤ) (J : ℕ) (hA0 : 0 ≤ A 0) (hA1 : 0 ≤ A 1)
    (hB : ∀ j : ℕ, j ≤ J → B j ≤ capMin j)
    (hrec : ∀ k : ℕ, 2 ≤ k → k ≤ J + 2 → 2 * A (k - 1) - 1 - B (k - 2) ≤ A k) :
    ∀ k : ℕ, k ≤ J + 2 → capMin k ≤ A k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    match k, ih, hk with
    | 0, _, _ => simp [capMin_zero, hA0]
    | 1, _, _ => simp [capMin_one, hA1]
    | (n + 2), ih, hk =>
      have hn1 : capMin ((n + 1 : ℕ) : ℤ) ≤ A (n + 1) := ih (n + 1) (by omega) (by omega)
      have hBn : B n ≤ capMin (n : ℤ) := hB n (by omega)
      have hr := hrec (n + 2) (by omega) hk
      have hsub1 : n + 2 - 1 = n + 1 := by omega
      have hsub2 : n + 2 - 2 = n := by omega
      rw [hsub1, hsub2] at hr
      have hcap := capMin_rec ((n : ℤ) + 2)
      have e1 : (n : ℤ) + 2 - 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      have e2 : (n : ℤ) + 2 - 2 = (n : ℤ) := by ring
      rw [e1, e2] at hcap
      have e3 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
      rw [e3]
      linarith

/-- **The cap, with the odd anchors beyond `J + 2`** (ALL_SLOPE_STEP, the anchor range up to `K*`): the `B`-bound and the recurrence on
`[0, J + 2]`, and the odd anchor inequality `m(k) ≤ A_k` for `J + 2 < k ≤ K`, give `A_k ≥ m(k)` for every `k ≤ K`. -/
theorem cap_with_anchors (A B : ℕ → ℤ) (J K : ℕ) (hA0 : 0 ≤ A 0) (hA1 : 0 ≤ A 1)
    (hB : ∀ j : ℕ, j ≤ J → B j ≤ capMin j)
    (hrec : ∀ k : ℕ, 2 ≤ k → k ≤ J + 2 → 2 * A (k - 1) - 1 - B (k - 2) ≤ A k)
    (hanchor : ∀ k : ℕ, J + 2 < k → k ≤ K → capMin k ≤ A k) :
    ∀ k : ℕ, k ≤ K → capMin k ≤ A k := by
  intro k hk
  by_cases h : k ≤ J + 2
  · exact cap_induction A B J hA0 hA1 hB hrec k h
  · exact hanchor k (by omega) hk

end FLatticePaper.QuadraticCap
