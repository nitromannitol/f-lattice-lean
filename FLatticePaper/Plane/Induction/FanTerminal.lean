import FLatticePaper.Plane.Induction.FanPropagation
import FLatticePaper.Plane.Induction.W1Exit

/-! # Task 98 (3): the fan's first exit lies on the closed polygon (FIXED_FREE §9's terminals)

A fan from an interior contact (`frame.openRect v₀`) leaves the open rectangle at a first point `w`. That point is an input of the last
interior point (the steps are inputs), so `w` lies in the closed polygon (`W1Exit.rectInputs`). So the first exit is a contact of the fort
on the boundary of the polygon, `w ∈ closedPolygon ∖ openRect`. The paid removal of the boundary contacts (FIXED_FREE §9: each terminal is
already excluded, or strictly smaller in `K`) is the hypothesis `hpaid`; with it the fort containing an interior contact is impossible. -/

namespace FLatticePaper.FanTerminal

open FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone FLatticePaper.FanPropagation

/-- **The first exit of a fan from an interior contact is a boundary contact of the fort on the closed polygon.** -/
theorem fan_terminal_closed (frame : ChildFrame) {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hle : ∀ x, m x ≤ F x) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0) (hv0 : frame.openRect v0) :
    ∃ w : Site, w ∈ S ∧ F w = m w ∧ w ∈ frame.closedPolygon ∧ ¬ frame.openRect w := by
  obtain ⟨hpos, hnlt, hdn, -, -⟩ := frame.child_facts
  have hn : 1 ≤ frame.child.num := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hSI0 : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den v0 :=
    (FLatticePaper.W1Exit.openRect_iff frame v0).mp hv0
  obtain ⟨k, next, hnext, hmem, hfc, hcon, hint⟩ :=
    fan_first_exit hfort hm hme hle frame.child.num frame.child.den hn hnd v0 hv0S hv0c
  cases k with
  | zero => exact absurd hSI0 hcon
  | succ k' =>
    have hpred : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (next^[k'] ⟨v0, hv0S, hv0c⟩).1 :=
      hint k' (Nat.lt_succ_self k')
    have hpredOpen : frame.openRect (next^[k'] ⟨v0, hv0S, hv0c⟩).1 :=
      (FLatticePaper.W1Exit.openRect_iff frame _).mpr hpred
    have hsucc : next^[k' + 1] ⟨v0, hv0S, hv0c⟩ = next (next^[k'] ⟨v0, hv0S, hv0c⟩) :=
      Function.iterate_succ_apply' next k' _
    have hcl : (next^[k' + 1] ⟨v0, hv0S, hv0c⟩).1 ∈ frame.closedPolygon := by
      rw [hsucc]
      exact FLatticePaper.W1Exit.rectInputs frame _ hpredOpen _ (hnext _).2
    exact ⟨(next^[k' + 1] ⟨v0, hv0S, hv0c⟩).1, hmem, hfc, hcl,
      fun h => hcon ((FLatticePaper.W1Exit.openRect_iff frame _).mp h)⟩

/-- **The fan contradiction on the polygon** (FIXED_FREE §9): a true fort of `F` with an interior contact is impossible, once every
boundary contact of the fort on the closed polygon is paid (removed, or strictly smaller in `K`, by the earlier schedule). -/
theorem fan_terminal_contradiction (frame : ChildFrame) {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hle : ∀ x, m x ≤ F x) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0) (hv0 : frame.openRect v0)
    (hpaid : ∀ w : Site, w ∈ frame.closedPolygon → ¬ frame.openRect w → w ∈ S → F w = m w → False) : False := by
  obtain ⟨w, hwS, hwc, hwcl, hwout⟩ := fan_terminal_closed frame hfort hm hme hle v0 hv0S hv0c hv0
  exact hpaid w hwcl hwout hwS hwc

end FLatticePaper.FanTerminal
