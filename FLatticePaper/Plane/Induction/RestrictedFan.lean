import FLatticePaper.Plane.Induction.FanTerminal
import FLatticePaper.Plane.Induction.AuxRankQ1
import FLatticePaper.Plane.Induction.RankFromForts
import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.W1Exit

/-! # The fan closure in the restricted-fort form (Q1 fans for the no-fort)

A restricted fort `S` for `permitsQ1` (`IsRestrictedFort`) is an incoming fort at the nonfree sites: a nonfree black site has an input
in `S` (both inputs are permitted), a nonfree white site has both inputs in `S` (both are permitted). So the fan machinery of
`FanTerminal` applies to `S` with the nonfree predicate `N = Nonfree` (its open-rectangle points are nonfree, `strictInterior_nonfree`).
Consequence (`fan_exit_restricted`): a fan from an open-rectangle contact of `S` leaves the open rectangle at a closed-polygon contact
`w ∈ S`. Identifying that exit with an earlier row entry (which is excluded from `S`) is the next step (rank 4). -/

namespace FLatticePaper.RestrictedFan

open FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeClosure

/-- A restricted fort is a fort at the nonfree sites. -/
theorem fortAt_nonfree_of_restricted (frame : ChildFrame) {F : Field} {η : ℤ} {S : Set Site}
    (hS : IsRestrictedFort F (permitsQ1 frame F η) S) : FortAt (Nonfree frame) F S := by
  intro site hsite hN
  have hnfc : ¬ freeClosure frame site := by
    rintro ⟨s, hs, h⟩
    exact hN s hs ((Set.mem_union _ _ _).2 h)
  rcases hS site hsite with ⟨hl, hA⟩ | ⟨hl, hA, hB⟩
  · -- black: both inputs are permitted
    refine Or.inl ⟨hl, ?_⟩
    rcases hA with (h | h) | (h | h)
    · exact Or.inl h
    · exact absurd (Or.inl ⟨hl, Or.inl rfl⟩ : permitsQ1 frame F η site (incomingNeg site)) h
    · exact Or.inr h
    · exact absurd (Or.inl ⟨hl, Or.inr rfl⟩ : permitsQ1 frame F η site (incomingPos site)) h
  · -- white, nonfree: both inputs are permitted
    refine Or.inr ⟨hl, ?_, ?_⟩
    · rcases hA with h | h
      · exact h
      · exact absurd (Or.inr ⟨hl, Or.inr ⟨hnfc, Or.inl rfl⟩⟩ : permitsQ1 frame F η site (incomingNeg site)) h
    · rcases hB with h | h
      · exact h
      · exact absurd (Or.inr ⟨hl, Or.inr ⟨hnfc, Or.inr rfl⟩⟩ : permitsQ1 frame F η site (incomingPos site)) h

/-- **The fan exit in the restricted form.** A fan from an open-rectangle contact `v0 ∈ S` (with `F v0 = m v0`) leaves the open
rectangle at a closed-polygon contact `w ∈ S` with `F w = m w`, given the comparison `m ≤ F` on the closed polygon. -/
theorem fan_exit_restricted (frame : ChildFrame) {F m : Field} {η : ℤ} {S : Set Site}
    (hS : IsRestrictedFort F (permitsQ1 frame F η) S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : ∀ i ∈ frame.closedPolygon, m i ≤ F i) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0)
    (hv0 : frame.openRect v0) :
    ∃ w : Site, w ∈ S ∧ F w = m w ∧ w ∈ frame.closedPolygon ∧ ¬ frame.openRect w :=
  FanTerminal.fan_terminal_closed_fortAt frame (N := Nonfree frame) (fortAt_nonfree_of_restricted frame hS)
    (fun x hx => strictInterior_nonfree frame ((W1Exit.openRect_iff frame x).1 hx)) hm hme hwin v0 hv0S hv0c hv0

end FLatticePaper.RestrictedFan
