import FLatticePaper.Plane.Induction.CutTipEscape
import FLatticePaper.Plane.Induction.TipVertex

/-! Task 72 (TIP_THEOREM, the W1 cut-tip escape with its grade wired): the grade `J = ceil(slip / 2)` and the boundary profiles.

The escape game grade is `J_η(z) = ceil(D_η(z) / 2)`, `D_η = ChildFrame.slip F η`. The two boundary profiles of TIP_THEOREM are
the values of the slip on the V cut (source: `.work/fields/canonical/cut_origin/ANCESTRAL_PSI_V_CUT_PROOF.md` §§1–3, with the
V-arc range `VArcOffers`):

* `D_η(V_p) = −1` at the tip root `V_p` (so `J = 0`);
* `D_η(V_p + (−1,1)) = −2` at the port (so `J = −1`).

The profiles are hypotheses here (named). The permits of the route edges are `slipPermits` in the source; they are kept as
hypotheses `hru`, `hpu` until the sheet gap values at the route sites are derived (see the report). The whiteness of the root and
the middle is derived (`TipWhiteness.W1_tip_white`). -/

namespace FLatticePaper

open Farey FLatticePaper.Induction

/-- `J = ceil(D / 2)` for an integer slip `D`. -/
def tipJ (D : ℤ) : ℤ := (D + 1) / 2

theorem tipJ_port_lt_root : tipJ (-2) < tipJ (-1) := by
  unfold tipJ
  norm_num

/-- **The W1 cut-tip escape, with the grade wired.** Given the W1 tip (`eps = 1`), the boundary profiles `D(V_p) = −1` and
`D(V_p + (−1,1)) = −2`, and the two permitted route edges, the tip escapes at depth two in the restricted game with grade
`J_η = ceil(slip F η / 2)`. -/
theorem tip_W1_escape_profiles {F : Field} (frame : ChildFrame) (hS : frame.HasStrips F) {η : ℤ}
    (heps : frame.eps = 1) (hB0 : 0 ≤ TipVertex.tipB frame)
    (hB2 : 5 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator - TipVertex.tipB frame)
    {permits : Site → Site → Prop}
    (hD0 : frame.slip F η (TipVertex.tipVertex frame) = -1)
    (hD1 : frame.slip F η (TipVertex.tipVertex frame + (-1, 1)) = -2)
    (hru : permits (TipVertex.tipVertex frame) (TipVertex.tipVertex frame + (-1, 0)))
    (hpu : permits (TipVertex.tipVertex frame + (-1, 0)) (TipVertex.tipVertex frame + (-1, 1))) :
    RestrictedEscapesWithin F (fun z => tipJ (frame.slip F η z)) permits
      (tipJ (frame.slip F η (TipVertex.tipVertex frame))) 2 (TipVertex.tipVertex frame) := by
  obtain ⟨hr, hu⟩ := TipVertex.W1_tip_white_of_eps frame hS heps hB0 hB2
  have hu' : laplacian F (TipVertex.tipVertex frame + (-1, 0)) = 0 := by
    rw [show TipVertex.tipVertex frame + (-1, 0) =
      ((TipVertex.tipVertex frame).1 - 1, (TipVertex.tipVertex frame).2) from by ext <;> (simp; try omega)]
    exact hu
  have hy : tipJ (frame.slip F η (TipVertex.tipVertex frame + (-1, 1))) <
      tipJ (frame.slip F η (TipVertex.tipVertex frame)) := by
    rw [hD0, hD1]
    exact tipJ_port_lt_root
  exact tip_W1_escape (TipVertex.evenSite_tipVertex frame) hr hu' hru hpu hy

end FLatticePaper
