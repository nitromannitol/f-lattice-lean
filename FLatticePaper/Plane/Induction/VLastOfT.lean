import FLatticePaper.Plane.Induction.HX1Residue
import FLatticePaper.Plane.Induction.LowerBand

/-! # An even free V site with `t = L - P` is `vLast`

For an even free V site `z` with `t(z) = L - P` (`L = d + n`, `P` the period denominator), the inverse identities give
`P (a - (n - d + 1)) = d (s - 2n)` and `P (b - (n + d - 1)) = n (s - 2n)`. Coprimality of `d` and `n` gives `s = 2n + P k`,
and the V spectrum (`s ≤ 2n` or `s ≤ L - 2`, with `s ≥ 0`) forces `k = 0`, so `(a, b) = (n - d + 1, n + d - 1)`. -/

namespace FLatticePaper.VLastOfT

open Farey FLatticePaper FLatticePaper.Induction

/-- The integer core: `t = L - P` and the V spectrum force `(a, b) = vLast`. -/
theorem core_vLast_of_t (n d P a b t s : ℤ) (hn0 : 0 < n) (hnd : n < d) (hdn : 2 ≤ d - n)
    (hP : P = d ^ 2 + 2 * d * n - n ^ 2) (hcop : IsCoprime d n)
    (hA : P * a = (d - n) * t + d * s) (hB : P * b = n * s - (d + n) * t)
    (ht : t = d + n - P) (hs0 : 0 ≤ s) (hspec : s ≤ 2 * n ∨ s ≤ d + n - 2) (hPd : 2 * d ≤ P) :
    a = n - d + 1 ∧ b = n + d - 1 := by
  have hPpos : 0 < P := by omega
  have hα : P * (a - (n - d + 1)) = d * (s - 2 * n) := by
    linear_combination hA + (d - n) * ht - hP
  have hβ : P * (b - (n + d - 1)) = n * (s - 2 * n) := by
    linear_combination hB - (d + n) * ht + hP
  have hkey : n * (a - (n - d + 1)) = d * (b - (n + d - 1)) := by
    have h0 : P * (n * (a - (n - d + 1)) - d * (b - (n + d - 1))) = 0 := by
      linear_combination n * hα - d * hβ
    have h1 := (mul_eq_zero.mp h0).resolve_left hPpos.ne'
    linarith
  have hdvd : d ∣ n * (a - (n - d + 1)) := ⟨b - (n + d - 1), hkey⟩
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left hdvd
  have hdpos : 0 < d := by omega
  have hβk : b - (n + d - 1) = n * k := by
    have h1 : d * (b - (n + d - 1)) = d * (n * k) := by
      rw [← hkey, hk]; ring
    exact mul_left_cancel₀ hdpos.ne' h1
  have hsk : s - 2 * n = P * k := by
    have h1 : d * (s - 2 * n) = d * (P * k) := by
      rw [← hα, hk]; ring
    exact mul_left_cancel₀ hdpos.ne' h1
  have hk0 : 0 ≤ k := by
    by_contra h
    have h' : k ≤ -1 := by omega
    nlinarith
  have hk1 : k ≤ 0 := by
    by_contra h
    have h' : 1 ≤ k := by omega
    rcases hspec with h2 | h2 <;> nlinarith
  have hk' : k = 0 := by omega
  subst hk'
  have hα0 : a - (n - d + 1) = 0 := by rw [hk]; ring
  constructor
  · omega
  · omega

end FLatticePaper.VLastOfT

namespace FLatticePaper.VLastOfT

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

/-- **An even free V site with `t = L - P` is `vLast`.** -/
theorem vLast_of_tGrade (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z)
    (ht : frame.tGrade z = frame.child.den + frame.child.num - frame.child.periodDenominator) :
    z = frame.vLast := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  obtain ⟨hs0, -, -, -⟩ := frame.root_bounds hz hev
  obtain ⟨-, -, hvs⟩ := hz
  have hvs' : frame.sGrade z % 2 = 0 ∧
      ((0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num) ∨
        (2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
          frame.sGrade z ≤ frame.child.den + frame.child.num - 2)) := hvs
  have hspec : frame.sGrade z ≤ 2 * frame.child.num ∨
      frame.sGrade z ≤ frame.child.den + frame.child.num - 2 := by
    rcases hvs'.2 with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  have hcop : IsCoprime frame.child.den frame.child.num := frame.child_reduced.symm
  have hPd : 2 * frame.child.den ≤ frame.child.periodDenominator := by
    rw [hP]; nlinarith
  obtain ⟨ha, hb⟩ := core_vLast_of_t frame.child.num frame.child.den frame.child.periodDenominator
    z.1 z.2 (frame.tGrade z) (frame.sGrade z) hn0 hnd hdn hP hcop (frame.ident_a z) (frame.ident_b z)
    ht hs0 hspec hPd
  unfold ChildFrame.vLast
  exact Prod.ext (by omega) (by omega)

end FLatticePaper.VLastOfT
