import FLatticePaper.Plane.Induction.W1Constructor

/-! # Task 89 (1): the strict interior is finite

`StrictInterior n d` is the open parity-resolved rectangle `b − T < t < a`, `h < s < T + c` with the affine maps `t = n x − d y` and
`s = (d + n) x + (d − n) y`. Their determinant is `T = d² + 2dn − n²`, which is positive for `1 ≤ n`, `n + 2 ≤ d`. So `(t, s)` is injective on
ℤ², and the strict interior (a bounded region: the bounds `a, b, c, h` are parity-resolved constants) is the preimage of a finite box. -/

namespace FLatticePaper.W1Finite

open FLatticePaper FLatticePaper.W1

/-- The det of `(t, s)` is `T`. -/
theorem det_eq_T (n d : ℤ) : n * (d - n) - (-d) * (d + n) = w1T n d := by
  unfold w1T
  ring

/-- `(t, s)` is injective when `T ≠ 0`. -/
theorem t_s_injective (n d : ℤ) (hT : w1T n d ≠ 0) (x y : Site)
    (h : w1t n d x = w1t n d y ∧ w1s n d x = w1s n d y) : x = y := by
  obtain ⟨h1, h2⟩ := h
  unfold w1t at h1
  unfold w1s at h2
  have hx : (w1T n d) * (x.1 - y.1) = 0 := by
    unfold w1T
    linear_combination (d - n) * h1 + d * h2
  have hy : (w1T n d) * (x.2 - y.2) = 0 := by
    unfold w1T
    linear_combination (-(d + n)) * h1 + n * h2
  have ex : x.1 = y.1 := by
    have := (mul_eq_zero.mp hx).resolve_left hT
    omega
  have ey : x.2 = y.2 := by
    have := (mul_eq_zero.mp hy).resolve_left hT
    omega
  exact Prod.ext ex ey

/-- **The strict interior is finite** (task 89 (1)): for `1 ≤ n` and `n + 2 ≤ d`. -/
theorem strictInterior_finite (n d : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) :
    {c : Site | StrictInterior n d c}.Finite := by
  have hT : w1T n d ≠ 0 := by
    unfold w1T
    nlinarith
  set K : ℤ := 2 * (|n| + |d| + |w1T n d|) + 2 with hK
  have hn1 := le_abs_self n
  have hn2 := neg_abs_le n
  have hd1 := le_abs_self d
  have hd2 := neg_abs_le d
  have hT1 := le_abs_self (w1T n d)
  have hT2 := neg_abs_le (w1T n d)
  have an := abs_nonneg n
  have ad := abs_nonneg d
  have aT := abs_nonneg (w1T n d)
  have hbox : {c : Site | StrictInterior n d c} ⊆
      (fun c : Site => (w1t n d c, w1s n d c)) ⁻¹' (Set.Icc (-K) K ×ˢ Set.Icc (-K) K) := by
    intro c hc
    obtain ⟨h1, h2, h3, h4⟩ := hc
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc]
    simp only [w1b, w1a, w1h, w1c] at h1 h2 h3 h4
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> split_ifs at h1 h2 h3 h4 <;> linarith
  have hinj : Set.InjOn (fun c : Site => (w1t n d c, w1s n d c))
      ((fun c : Site => (w1t n d c, w1s n d c)) ⁻¹' (Set.Icc (-K) K ×ˢ Set.Icc (-K) K)) := by
    intro x _ y _ hxy
    exact t_s_injective n d hT x y (Prod.mk.inj hxy)
  exact (((Set.finite_Icc (-K) K).prod (Set.finite_Icc (-K) K)).preimage hinj).subset hbox

end FLatticePaper.W1Finite
