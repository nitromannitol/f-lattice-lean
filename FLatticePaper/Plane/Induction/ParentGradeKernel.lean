import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination

/-! Task 72 / Q31 psi (i): the kernel of the parent grade.

For the odd parent `N/D` of a child frame with `ε = N d − D n = ±1`, put `r = D + N` and `c_p = D − N`. The parent grade of a site
`(a, b)` is `s_p(a, b) = r a + c_p b`, and the parent deck vector is `V_p = (−c_p, r)` (`tipVertex`). Since `N + D` is odd and
`N, D` are coprime, `r` and `c_p` are coprime, so the kernel of `s_p` is exactly `ℤ · V_p`: two sites of the same parent grade differ
by an integer multiple of `V_p`, with no parity condition. -/

namespace FLatticePaper.ParentGradeKernel

/-- `N` and `D` are coprime, from `ε = N d − D n = ±1`. -/
theorem isCoprime_ND (N D n d ε : ℤ) (hε : ε = N * d - D * n) (hε1 : ε = 1 ∨ ε = -1) :
    IsCoprime N D := by
  have hsq : ε * ε = 1 := by rcases hε1 with h | h <;> rw [h] <;> norm_num
  refine ⟨ε * d, -(ε * n), ?_⟩
  linear_combination hsq - ε * hε

/-- `r = D + N` and `c_p = D − N` are coprime when `D + N` is odd. -/
theorem isCoprime_r_cp (N D : ℤ) (hcop : IsCoprime N D) (hodd : (D + N) % 2 = 1) :
    IsCoprime (D + N) (D - N) := by
  obtain ⟨x, y, hxy⟩ := hcop
  obtain ⟨m, hm⟩ : ∃ m, D + N = 2 * m + 1 := ⟨(D + N - 1) / 2, by omega⟩
  refine ⟨1 - m * (x + y), -m * (y - x), ?_⟩
  linear_combination hm - 2 * m * hxy

/-- **Same parent grade ⇒ `V_p`-multiple.** If `r a + c_p b = 0` with `r, c_p` coprime and `r ≠ 0`, then `(a, b) = k (−c_p, r)`. -/
theorem vp_multiple (r c a b : ℤ) (hcop : IsCoprime r c) (hr : r ≠ 0) (h : r * a + c * b = 0) :
    ∃ k : ℤ, a = -c * k ∧ b = r * k := by
  have hdvd : r ∣ c * b := ⟨-a, by linear_combination h⟩
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left hdvd
  refine ⟨k, ?_, hk⟩
  subst hk
  have : r * (a + c * k) = 0 := by linear_combination h
  have := (mul_eq_zero.mp this).resolve_left hr
  linear_combination this

/-- The parent grade `s_p(a, b) = r a + c_p b` with the kernel `V_p`: two sites of the same grade differ by `k V_p`
(stated with the odd parent `N/D`, `r = D + N`, `c_p = D − N`). -/
theorem same_grade_vp (N D : ℤ) (hcop : IsCoprime N D) (hodd : (D + N) % 2 = 1) (hr : D + N ≠ 0)
    (a b a' b' : ℤ) (h : (D + N) * a + (D - N) * b = (D + N) * a' + (D - N) * b') :
    ∃ k : ℤ, a - a' = -(D - N) * k ∧ b - b' = (D + N) * k := by
  obtain ⟨k, hk1, hk2⟩ := vp_multiple (D + N) (D - N) (a - a') (b - b')
    (isCoprime_r_cp N D hcop hodd) hr (by linear_combination h)
  exact ⟨k, hk1, hk2⟩

end FLatticePaper.ParentGradeKernel
