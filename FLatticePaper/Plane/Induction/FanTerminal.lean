import FLatticePaper.Plane.Induction.FanPropagation
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.W1Finite

/-! # Task 98 (3): the fan's first exit lies on the closed polygon (FIXED_FREE §9's terminals), with the window on the closed polygon only

The window hypothesis is `m ≤ F` on the closed polygon (the note's hypothesis), used only at the inputs of open-rectangle points, where
`W1Exit.rectInputs` places them in the closed polygon. The interior predicate is `frame.openRect`, whose finiteness is `strictInterior_finite`.
A fan from an open-rectangle contact leaves the open rectangle at a first point `w`; `w` is an input of the last interior point, so it lies
on the closed polygon. The paid exclusion of boundary contacts (FIXED_FREE §9) is the hypothesis `hpaid`. The north-start variant is the
fan of the high-slope H midpoint (FIXED_FREE §9: the first step is the canonical north input). -/

namespace FLatticePaper.FanTerminal

open FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone FLatticePaper.FanPropagation

/-- The finiteness of the open rectangle. -/
theorem openRect_finite (frame : ChildFrame) : {c : Site | frame.openRect c}.Finite := by
  obtain ⟨hpos, hnlt, hdn, -, -⟩ := frame.child_facts
  have hset : {c : Site | frame.openRect c} = {c : Site | FLatticePaper.W1.StrictInterior frame.child.num frame.child.den c} := by
    ext c
    exact FLatticePaper.W1Exit.openRect_iff frame c
  rw [hset]
  exact FLatticePaper.W1Finite.strictInterior_finite frame.child.num frame.child.den (by omega) (by omega)

/-- The window of a fan on the closed polygon: `m ≤ F` on the closed polygon gives the window at the inputs of the open rectangle. -/
theorem window_open {F m : Field} (frame : ChildFrame)
    (hwin : ∀ i ∈ frame.closedPolygon, m i ≤ F i) : WindowOn (fun z => frame.openRect z) F m := by
  intro x hx i hi
  exact hwin i (FLatticePaper.W1Exit.rectInputs frame x hx i hi)

/-- **The first exit of a fan with a given step function**: a contact of `S` on the closed polygon outside the open rectangle. -/
theorem fan_terminal_of_next (frame : ChildFrame) {F m : Field} {S : Set Site} (next : FanT F m S → FanT F m S)
    (hr : ∀ v : FanT F m S, frame.openRect v.1 → FanRules next v) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0)
    (hv0 : frame.openRect v0) :
    ∃ w : Site, w ∈ S ∧ F w = m w ∧ w ∈ frame.closedPolygon ∧ ¬ frame.openRect w := by
  obtain ⟨k, hk, hj⟩ := fan_first_exit_of next hr (openRect_finite frame) ⟨v0, hv0S, hv0c⟩
  cases k with
  | zero => exact absurd hv0 hk
  | succ k' =>
    have hpredOpen : frame.openRect (next^[k'] ⟨v0, hv0S, hv0c⟩).1 := hj k' (Nat.lt_succ_self k')
    have hsucc : next^[k' + 1] ⟨v0, hv0S, hv0c⟩ = next (next^[k'] ⟨v0, hv0S, hv0c⟩) :=
      Function.iterate_succ_apply' next k' _
    have hcl : (next^[k' + 1] ⟨v0, hv0S, hv0c⟩).1 ∈ frame.closedPolygon := by
      rw [hsucc]
      exact FLatticePaper.W1Exit.rectInputs frame _ hpredOpen _ (hr _ hpredOpen).2
    have hmem := (next^[k' + 1] ⟨v0, hv0S, hv0c⟩).2.1
    have hcon := (next^[k' + 1] ⟨v0, hv0S, hv0c⟩).2.2
    exact ⟨(next^[k' + 1] ⟨v0, hv0S, hv0c⟩).1, hmem, hcon, hcl, hk⟩

/-- **The first exit of a fan from an open-rectangle contact** (the fan with the existence of the steps). -/
theorem fan_terminal_closed (frame : ChildFrame) {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : ∀ i ∈ frame.closedPolygon, m i ≤ F i) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0)
    (hv0 : frame.openRect v0) :
    ∃ w : Site, w ∈ S ∧ F w = m w ∧ w ∈ frame.closedPolygon ∧ ¬ frame.openRect w := by
  obtain ⟨next, hr⟩ := fan_path_exists hfort hm hme (window_open frame hwin)
  exact fan_terminal_of_next frame next hr v0 hv0S hv0c hv0

/-- **The north-start fan** (FIXED_FREE §9, the high-slope H midpoint): an odd interior contact whose north input is a contact of `S`
starts with the north step; its first exit is a boundary contact on the closed polygon. -/
theorem fan_terminal_north (frame : ChildFrame) {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : ∀ i ∈ frame.closedPolygon, m i ≤ F i) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0)
    (hv0 : frame.openRect v0) (hodd : ¬ EvenSite v0) (hnS : incomingPos v0 ∈ S)
    (hnc : F (incomingPos v0) = m (incomingPos v0)) :
    ∃ w : Site, w ∈ S ∧ F w = m w ∧ w ∈ frame.closedPolygon ∧ ¬ frame.openRect w := by
  obtain ⟨next, hr, _⟩ := fan_path_exists_north hfort hm hme (window_open frame hwin) v0 hv0S hv0c hodd hnS hnc
  exact fan_terminal_of_next frame next (fun v hv => hr v hv) v0 hv0S hv0c hv0

/-- **The fan contradiction on the polygon** (FIXED_FREE §9): a true fort of `F` with an interior contact is impossible, once every
boundary contact of the fort on the closed polygon is paid (removed, or strictly smaller in `K`, by the earlier schedule). -/
theorem fan_terminal_contradiction (frame : ChildFrame) {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : ∀ i ∈ frame.closedPolygon, m i ≤ F i) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0)
    (hv0 : frame.openRect v0)
    (hpaid : ∀ w : Site, w ∈ frame.closedPolygon → ¬ frame.openRect w → w ∈ S → F w = m w → False) : False := by
  obtain ⟨w, hwS, hwc, hwcl, hwout⟩ := fan_terminal_closed frame hfort hm hme hwin v0 hv0S hv0c hv0
  exact hpaid w hwcl hwout hwS hwc

/-- **The north-start fan contradiction** (FIXED_FREE §9): the north-start fan from an interior odd contact is impossible under the paid
exclusion of the boundary contacts. -/
theorem fan_terminal_north_contradiction (frame : ChildFrame) {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : ∀ i ∈ frame.closedPolygon, m i ≤ F i) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0)
    (hv0 : frame.openRect v0) (hodd : ¬ EvenSite v0) (hnS : incomingPos v0 ∈ S)
    (hnc : F (incomingPos v0) = m (incomingPos v0))
    (hpaid : ∀ w : Site, w ∈ frame.closedPolygon → ¬ frame.openRect w → w ∈ S → F w = m w → False) : False := by
  obtain ⟨w, hwS, hwc, hwcl, hwout⟩ := fan_terminal_north frame hfort hm hme hwin v0 hv0S hv0c hv0 hodd hnS hnc
  exact hpaid w hwcl hwout hwS hwc

end FLatticePaper.FanTerminal
