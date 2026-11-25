import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Task w3, step 3 (core): the sheet potential is nondecreasing for `j ≥ 1` from the transport and the earlier trace.

Named inputs (the Lean statements of the w3 steps 1(b) and 2(a)–(c)):
* the earlier trace along the query index is a step function `f` with increments in `{0, η}`;
* the query at `j` has earlier value `f(k_j)` with `k_j = j − c` (phase zero, `η = −1`) or `k_j = d − 1 − j` (phase one, `η = +1`).

`Ψ(j) = K − Φ(j)`. With these, `Ψ(j) ≤ Ψ(j+1)` for `j ≥ 1`. -/

namespace FLatticePaper.PsiMono

/-- **Phase zero (`η = −1`):** `f` is nonincreasing, `k_j = j − c` increases by one, so `Φ` is nonincreasing and `Ψ` nondecreasing. -/
theorem mono_W0 (f : ℤ → ℤ) (hstep : ∀ k, f (k + 1) ≤ f k) (c K : ℤ) (N : ℕ) (Φ : ℕ → ℤ)
    (hΦ : ∀ j : ℕ, 1 ≤ j → j < N → Φ j = f ((j : ℤ) - c)) :
    ∀ j : ℕ, 1 ≤ j → j + 1 < N → K - Φ j ≤ K - Φ (j + 1) := by
  intro j hj hjN
  have h1 := hΦ j hj (by omega)
  have h2 := hΦ (j + 1) (by omega) hjN
  have e : ((j + 1 : ℕ) : ℤ) - c = ((j : ℤ) - c) + 1 := by push_cast; ring
  rw [e] at h2
  have := hstep ((j : ℤ) - c)
  linarith

/-- **Phase one (`η = +1`):** `f` is nondecreasing and the query ordinate `d − 1 − j` decreases by one. The last query
(ordinate `0`, the endpoint `V'_0`) is only bounded: `Φ(j) ≤ f(1)` there (`hEnd`). Hence `Ψ` is nondecreasing. -/
theorem mono_W1 (f : ℤ → ℤ) (hstep : ∀ k, f k ≤ f (k + 1)) (d K : ℤ) (N : ℕ) (hN : (N : ℤ) ≤ d) (Φ : ℕ → ℤ)
    (hΦ : ∀ j : ℕ, 1 ≤ j → j < N → d - 1 - (j : ℤ) ≠ 0 → Φ j = f (d - 1 - (j : ℤ)))
    (hEnd : ∀ j : ℕ, 1 ≤ j → j < N → d - 1 - (j : ℤ) = 0 → Φ j ≤ f 1) :
    ∀ j : ℕ, 1 ≤ j → j + 1 < N → K - Φ j ≤ K - Φ (j + 1) := by
  intro j hj hjN
  have hjd : (j : ℤ) + 1 < d := by omega
  by_cases hk : d - 1 - ((j + 1 : ℕ) : ℤ) = 0
  · have h2 := hEnd (j + 1) (by omega) hjN hk
    have hj1 : d - 1 - (j : ℤ) = 1 := by omega
    have h1 := hΦ j hj (by omega) (by omega)
    rw [hj1] at h1
    linarith
  · have h2 := hΦ (j + 1) (by omega) hjN hk
    have hk' : d - 1 - (j : ℤ) ≠ 0 := by omega
    have h1 := hΦ j hj (by omega) hk'
    have hs := hstep (d - 1 - ((j + 1 : ℕ) : ℤ))
    have e : d - 1 - ((j + 1 : ℕ) : ℤ) + 1 = d - 1 - (j : ℤ) := by omega
    rw [e] at hs
    linarith

end FLatticePaper.PsiMono
