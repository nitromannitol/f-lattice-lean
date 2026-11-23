import FLatticePaper.Plane.Induction.Q3White
import FLatticePaper.Plane.Induction.OddRise

/-! Task 61, paragraph 1 (the rise forces both centres black) and its use in the V-block contradiction.

`rise_partner_neg/pos` (OddRise.lean) give, for a black centre `c` with a rise `slipIncrement = 1` at an input `u` of the
slip `D_η` with shift `σ` (`σ` even), that the other input falls by one and the translate `c + σ` is black. The sum
`e₁ + e₂ = Δ F(c) − Δ F(c + σ)` lies in `{0, −1}` (binarity), and the unit slip `|e| ≤ 1` forces the partner to `−1`.
The odd middle level `±1` is this unit bound; the ranges `D_±` are not needed for this step.

Here `σ = U_q = (d_q, n_q)`: the rise at a V-block centre `x = v + iU_p` gives the partner `x + U_q`, and
`black_centres_contradiction` (Q3White.lean) excludes the pair. The unit slip for the shift `U_q` is a named input
`hU`: the producer supplies the unit slip for the shift `shortShift = εU_p`, which is a different shift (see the report). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

namespace ChildFrame
variable (frame : ChildFrame)

/-- The shift `U_q = (d_q, n_q)` of the even parent; `d_q + n_q` is even, so the shift is an even site. -/
theorem evenSite_Uq : EvenSite (frame.parents.even.den, frame.parents.even.num) := by
  have hep : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  unfold EvenSite
  dsimp only
  omega

/-- A rise at a black centre `x` of the V block (input `u` of `x`, slip increment `1` along `U_q`) makes the translate
`x + U_q` black. -/
theorem partner_black_of_rise {F : Field} (hP : frame.Packet F)
    (hU : HasUnitSlip F (fun z => F (z + (frame.parents.even.den, frame.parents.even.num))))
    {x u : Site} (hc : laplacian F x = -1) (hu : u = incomingNeg x ∨ u = incomingPos x)
    (hrise : slipIncrement F (fun z => F (z + (frame.parents.even.den, frame.parents.even.num))) x u = 1) :
    laplacian F (x + (frame.parents.even.den, frame.parents.even.num)) = -1 := by
  have hσ := frame.evenSite_Uq
  rcases hu with rfl | rfl
  · exact (rise_partner_neg hσ hP.binary hU hc hrise).2
  · exact (rise_partner_pos hσ hP.binary hU hc hrise).2

/-- Paragraph 1 with paragraph 10: a rise at a black V-block centre `x = v + iU_p` (`v ∈ freeV`, `x, x + U_q ∈ E`) is
impossible. -/
theorem no_rise_at_block_centre {F : Field} (hP : frame.Packet F)
    (hU : HasUnitSlip F (fun z => F (z + (frame.parents.even.den, frame.parents.even.num))))
    {v x : Site} {i : ℤ} {u : Site} (hv : v ∈ frame.freeV)
    (hx : x = v + (i * (2 * frame.parents.odd.den), i * (2 * frame.parents.odd.num)))
    (hxE : x ∈ frame.closedPolygon)
    (hxuE : x + (frame.parents.even.den, frame.parents.even.num) ∈ frame.closedPolygon)
    (hc : laplacian F x = -1) (hu : u = incomingNeg x ∨ u = incomingPos x)
    (hrise : slipIncrement F (fun z => F (z + (frame.parents.even.den, frame.parents.even.num))) x u = 1) :
    False :=
  frame.black_centres_contradiction hP hv hx hxE hxuE hc
    (frame.partner_black_of_rise hP hU hc hu hrise)

end ChildFrame

end FLatticePaper.Induction
