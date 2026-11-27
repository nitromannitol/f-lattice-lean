import FLatticePaper.Plane.Induction.RefuteTree
import FLatticePaper.Plane.Induction.FreeWebClaims
import FLatticePaper.Plane.Induction.Q3White
import FLatticePaper.Plane.Induction.FreePolicy

/-! # Refutation certificates of the V entries of the minus row, easy regime: the free classes C1 and C2

For the minus row (`η = −1`) the entry `x = V_{−k}` (negative ordinate) is a free V site (`x ∈ freeV`), so its only permitted input is
its prescribed direction (`FreePresc` with the zero translate): `W = (−1,0)` at an even site (class C1) and `N = (0,1)` at an odd site
(class C2). The white rule (`RefuteTree.Refuted.white`) then refutes `x` from the earlier entry it points to, the laplacian at a free V
site being zero (`laplacian_eq_zero_of_freeV`). -/

namespace FLatticePaper.RowVRefute

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.RefuteTree FLatticePaper.FreePolicy FLatticePaper.FreeClosure
open FLatticePaper.FreeWebClaims

/-- A site with negative ordinate is neither `vFirst` (ordinate `0`) nor `vLast` (ordinate `n + d − 1 > 0`). -/
theorem ne_special {frame : ChildFrame} {x : Site} (hneg : x.2 < 0) :
    x ≠ FLatticePaper.Induction.vFirst ∧ x ≠ frame.vLast := by
  obtain ⟨hn, -, -, hd, -⟩ := frame.child_facts
  constructor
  · intro h
    rw [h] at hneg
    simp [FLatticePaper.Induction.vFirst] at hneg
  · intro h
    rw [h] at hneg
    unfold ChildFrame.vLast at hneg
    simp at hneg
    omega

/-- The prescribed V direction at an odd site off the two special sites: north for `η = −1`. -/
theorem prescribedV_odd {frame : ChildFrame} {η : ℤ} (hη : η = -1) {x : Site} (hodd : ¬ EvenSite x)
    (h1 : x ≠ FLatticePaper.Induction.vFirst) (h2 : x ≠ frame.vLast) : frame.prescribedV η x = (0, 1) := by
  unfold ChildFrame.prescribedV
  rw [if_neg h1, if_neg h2, if_neg hodd]
  subst hη
  simp

/-- The prescribed V direction at an even site off the two special sites: west for `η = −1`. -/
theorem prescribedV_even {frame : ChildFrame} {η : ℤ} (hη : η = -1) {x : Site} (hev : EvenSite x)
    (h1 : x ≠ FLatticePaper.Induction.vFirst) (h2 : x ≠ frame.vLast) : frame.prescribedV η x = (-1, 0) := by
  unfold ChildFrame.prescribedV
  rw [if_neg h1, if_neg h2, if_pos hev]
  subst hη
  simp

/-- **Class C2.** An odd free V site below the origin, whose north neighbour is an earlier entry, is refuted. -/
theorem refuted_odd_north {frame : ChildFrame} {F : Field} (hS : frame.HasStrips F) {η : ℤ} (hη : η = -1)
    {E C : Site → Prop} {x : Site} (hx : x ∈ frame.freeV) (hodd : ¬ EvenSite x) (hneg : x.2 < 0)
    (hE : E (x + (0, 1))) : Refuted frame F η E C x := by
  obtain ⟨h1, h2⟩ := ne_special (frame := frame) hneg
  refine Refuted.white (frame.laplacian_eq_zero_of_freeV hS hx) ?_ (Refuted.earlier hE)
  right
  refine ⟨frame.laplacian_eq_zero_of_freeV hS hx, Or.inl ⟨fc_of_freeV frame hx, 0, zero_mem_span frame, Or.inr ⟨?_, ?_⟩⟩⟩
  · simpa using hx
  · rw [add_zero, prescribedV_odd hη hodd h1 h2]

/-- **Class C1.** An even free V site below the origin, whose west neighbour is an earlier entry, is refuted. -/
theorem refuted_even_west {frame : ChildFrame} {F : Field} (hS : frame.HasStrips F) {η : ℤ} (hη : η = -1)
    {E C : Site → Prop} {x : Site} (hx : x ∈ frame.freeV) (hev : EvenSite x) (hneg : x.2 < 0)
    (hE : E (x + (-1, 0))) : Refuted frame F η E C x := by
  obtain ⟨h1, h2⟩ := ne_special (frame := frame) hneg
  refine Refuted.white (frame.laplacian_eq_zero_of_freeV hS hx) ?_ (Refuted.earlier hE)
  right
  refine ⟨frame.laplacian_eq_zero_of_freeV hS hx, Or.inl ⟨fc_of_freeV frame hx, 0, zero_mem_span frame, Or.inr ⟨?_, ?_⟩⟩⟩
  · simpa using hx
  · rw [add_zero, prescribedV_even hη hev h1 h2]

end FLatticePaper.RowVRefute

