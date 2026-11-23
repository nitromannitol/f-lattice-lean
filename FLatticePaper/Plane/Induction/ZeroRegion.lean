import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ByContra

/-! # The zero region of I1 (task 49, step 2)

The zero region of the fix Q4-strips: for an even child `n/d` with `0 < n < d` (the child of a proper word, with `n + d` even),
the points `z` of the closed polygon with `t(z) ≥ 1 − d` have coordinates `0 ≤ x ≤ d` and `0 ≤ y ≤ n`. The lemma below states this
for the grades `t = n x − d y`, `s = (d + n) x + (d − n) y`, with the common bounds that the two parities of the closed polygon
imply: `1 − d ≤ t ≤ d + n − 1` and `2 − d + n ≤ s ≤ T + d + n − 2`, where `T = d² + 2dn − n²`. The later steps of the zero region
(the identity `C(z) = f(w) + g(j − 2ε) − g(j)` and the cases `W = 0, 1`) build on it. -/

namespace FLatticePaper.Induction.ZeroRegion

theorem zeroRegion_box (n d x y : ℤ) (hn : 0 < n) (hnd : n < d)
    (ht1 : 1 - d ≤ n * x - d * y) (ht2 : n * x - d * y ≤ d + n - 1)
    (hs1 : 2 - d + n ≤ (d + n) * x + (d - n) * y)
    (hs2 : (d + n) * x + (d - n) * y ≤ d * d + 2 * d * n - n * n + d + n - 2) :
    0 ≤ x ∧ x ≤ d ∧ 0 ≤ y ∧ y ≤ n := by
  have hd : 0 < d := by omega
  have hdn : 0 < d - n := by omega
  have hdn' : 0 < d + n := by omega
  have hx0 : 0 ≤ x := by
    by_contra hx
    have hx1 : x ≤ -1 := by omega
    have hnx : n * x ≤ -n := by nlinarith
    have hy : y ≤ 0 := by nlinarith
    have hs : (d + n) * x + (d - n) * y ≤ -(d + n) := by nlinarith
    nlinarith
  have hxd : x ≤ d := by
    by_contra hx
    have hx1 : d + 1 ≤ x := by omega
    have hy : n ≤ y := by nlinarith
    have hs : (d + n) * (d + 1) + (d - n) * n ≤ (d + n) * x + (d - n) * y := by nlinarith
    nlinarith
  have hy0 : 0 ≤ y := by
    by_contra hy
    have hy1 : y ≤ -1 := by omega
    have hx1 : x ≤ 0 := by nlinarith
    have hs : (d + n) * x + (d - n) * y ≤ n - d := by nlinarith
    nlinarith
  have hyn : y ≤ n := by
    by_contra hy
    have hy1 : n + 1 ≤ y := by omega
    have hnx : n * x ≤ n * d := by nlinarith
    nlinarith
  exact ⟨hx0, hxd, hy0, hyn⟩

end FLatticePaper.Induction.ZeroRegion
