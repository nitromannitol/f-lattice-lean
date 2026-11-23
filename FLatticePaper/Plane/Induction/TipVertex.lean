import FLatticePaper.Plane.Induction.TipWhiteness

/-! Task 72 (TIP_THEOREM, the tip vertex): the vertex `v = V_p` of the cut tip, derived from the frame.

`V_p` is the parent's V vertex `(n_p − d_p, n_p + d_p)` in child coordinates (the parent `odd` of the child). With
`eps = n_p d − d_p n` (`ChildFrame.eps_eq`) and `B = L d_p + c n_p`:

* `t(V_p) = −B`, `s(V_p) = 2 eps` (both are identities in `n_p, d_p, n, d`, using `eps_eq`);
* `V_p` is even (its coordinates have the same parity as `2 n_p`).

So the tip values `t(v) = −B`, `s(v) = 2 eps` of TIP_THEOREM are derived, not assumed. The phase is `eps`: W1 is `eps = 1`
(`s = 2`), W0 is `eps = −1` (`s = −2`). The nonbase bounds `0 ≤ B` and `5L ≤ T − B` remain hypotheses. -/

namespace FLatticePaper.Induction

namespace TipVertex

open ShortPassages TipWhiteness

/-- The tip vertex `V_p = (n_p − d_p, n_p + d_p)` in child coordinates. -/
def tipVertex (frame : ChildFrame) : Site :=
  (frame.parents.odd.num - frame.parents.odd.den, frame.parents.odd.num + frame.parents.odd.den)

/-- The tip's `B = L d_p + c n_p`, with `L = d + n` and `c = d − n`. -/
def tipB (frame : ChildFrame) : ℤ :=
  (frame.child.den + frame.child.num) * frame.parents.odd.den +
    (frame.child.den - frame.child.num) * frame.parents.odd.num

/-- **`t(V_p) = −B`.** -/
theorem tGrade_tipVertex (frame : ChildFrame) : frame.tGrade (tipVertex frame) = -tipB frame := by
  unfold ChildFrame.tGrade tipVertex tipB
  ring

/-- **`s(V_p) = 2 eps`.** -/
theorem sGrade_tipVertex (frame : ChildFrame) : frame.sGrade (tipVertex frame) = 2 * frame.eps := by
  rw [frame.eps_eq]
  unfold ChildFrame.sGrade tipVertex
  ring

/-- The tip vertex is even. -/
theorem evenSite_tipVertex (frame : ChildFrame) : EvenSite (tipVertex frame) := by
  show ((frame.parents.odd.num - frame.parents.odd.den) + (frame.parents.odd.num + frame.parents.odd.den)) % 2 = 0
  omega

/-- **The W1 tip, with its whiteness, from the frame.** For `eps = 1` the tip vertex has `s = 2`, and its root and middle are white
(`TipWhiteness.W1_tip_white`), given the nonbase bounds on `B`. -/
theorem W1_tip_white_of_eps {F : Field} (frame : ChildFrame) (hS : frame.HasStrips F) (heps : frame.eps = 1)
    (hB0 : 0 ≤ tipB frame)
    (hB2 : 5 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator - tipB frame) :
    laplacian F (tipVertex frame) = 0 ∧ laplacian F ((tipVertex frame).1 - 1, (tipVertex frame).2) = 0 := by
  have hv := evenSite_tipVertex frame
  have ht := tGrade_tipVertex frame
  have hs : frame.sGrade (tipVertex frame) = 2 := by
    rw [sGrade_tipVertex, heps]
    norm_num
  exact W1_tip_white frame hS hv ht hs hB0 hB2

/-- **The W0 root, with its whiteness, from the frame.** For `eps = −1` the tip vertex has `s = −2`, and the W0 root
`V_p + (1,0)` is white. -/
theorem W0_root_white_of_eps {F : Field} (frame : ChildFrame) (hS : frame.HasStrips F) (heps : frame.eps = -1)
    (hB0 : 0 ≤ tipB frame)
    (hB2 : 5 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator - tipB frame) :
    laplacian F ((tipVertex frame).1 + 1, (tipVertex frame).2) = 0 := by
  have hv := evenSite_tipVertex frame
  have ht := tGrade_tipVertex frame
  have hs : frame.sGrade (tipVertex frame) = -2 := by
    rw [sGrade_tipVertex, heps]
    norm_num
  exact W0_tip_root_white frame hS hv ht hs hB0 hB2

end TipVertex

end FLatticePaper.Induction
