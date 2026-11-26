import FLatticePaper.Plane.Induction.RouteRegion

/-! # The short route at a white middle: the regional argument with the two-site region `{m, nxt}`

For a white middle `m` in the strict interior `R` (the derivation region of `W1Forced`) whose route successor `nxt` is an input of `m`
and is white, and whose next route site `z` is an input of `nxt` outside `R`, the canonical policy keeps `nxt` at `m`.

Region `S = {m, nxt}`, arrows `K = {(m, nxt), (nxt, z)}`, rank `r = 2, 1, 0` on `m, nxt, z`
(`RegionalCompat.regional_forced` through `RouteRegion.nonfree_policy_of_region`). The closure needs only `nxt` (in `R`) to
enter `S`; the black rule and the black-middle cases do not occur because both sites of `S` are white. -/

namespace FLatticePaper.RouteRegional

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.CanonForced FLatticePaper.SquareClauses

theorem white_route_policy {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : W1Forced frame.child.num frame.child.den G)
    {m nxt z : Site}
    (hm : StrictInterior frame.child.num frame.child.den m) (hmw : laplacian G m = 0)
    (hin : nxt = incomingNeg m ∨ nxt = incomingPos m)
    (hnw : laplacian G nxt = 0)
    (hzin : z = incomingNeg nxt ∨ z = incomingPos nxt)
    (hzR : ¬ StrictInterior frame.child.num frame.child.den z) (hzm : z ≠ m) :
    C.policy m nxt := by
  have hnm : nxt ≠ m := FLatticePaper.RouteRegion.input_ne m nxt hin
  have hzn : z ≠ nxt := FLatticePaper.RouteRegion.input_ne nxt z hzin
  obtain ⟨o, hf⟩ := hW1 m hm hmw
  have key := FLatticePaper.RouteRegion.nonfree_policy_of_region C
    (R := StrictInterior frame.child.num frame.child.den)
    (S := fun x => x = m ∨ x = nxt)
    (K := fun x u => (x = m ∧ u = nxt) ∨ (x = nxt ∧ u = z))
    (r := fun x => if x = m then 2 else if x = nxt then 1 else 0)
    (by
      intro x u h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [h1, h2, hnm]
      · simp [h1, h2, hzn, hzm, hnm])
    (by
      intro x u hx h hu
      rcases h with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact Or.inr h2
      · exact absurd (h2 ▸ hu) hzR)
    (by
      intro x hx hl
      rcases hx with h1 | h1
      · rw [h1, hmw] at hl
        norm_num at hl
      · rw [h1, hnw] at hl
        norm_num at hl)
    (by
      intro x hx hl
      rcases hx with h1 | h1
      · exact ⟨nxt, Or.inl ⟨h1, rfl⟩, by rw [h1]; exact hin⟩
      · exact ⟨z, Or.inr ⟨h1, rfl⟩, by rw [h1]; exact hzin⟩)
    hmw (Or.inl rfl) hf
  obtain ⟨hK, hpol⟩ := key
  rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2] at hpol
    exact hpol
  · exact absurd h1.symm hnm

end FLatticePaper.RouteRegional
