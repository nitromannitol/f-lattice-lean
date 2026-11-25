import FLatticePaper.Plane.Induction.ReturnTable

/-! # Shape 1 of the return table (AUDIT_FREE_THREE_STEP_RETURNS §2, "H odd midpoint": `z+N → z+E+N → z+E → z`)

For an odd free root `z = (z1, z2)`, the chain is `x₁ = z+N` (even, fan rule: east to `z+E+N`), `x₂ = z+E+N` (odd, fan rule: south to
`z+E`), `x₃ = z+E` (even, nonfree with free input `z`, selects `z`). Each chain edge is secured by `EdgeOK` (`ReturnTable`):
a black site retains its input, and a non-free white with a forced edge retains the forced input. The fan compatibility
`fan_agrees_of_witness` says the forced input of a non-free white of the fan `D` is its designated fan successor `sel`.
So an edge `x → sel x` is secured as soon as `x ∈ D`, `x` is non-free, and `x` is black or has a forced edge.

The reduction below takes as named inputs: the fan `D` with its successor function `sel` (`hfan`), the membership of the chain
points in `D`, their non-freeness, the forced edges at the white chain points, the designations `sel`, and the `S`-memberships of
the chain points. Their geometric sources are the fan construction and the grade bounds of `sheetParentSet`. -/

namespace FLatticePaper.ReturnShapes

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1FreeHfree FLatticePaper.ReturnTable

/-- A fan-designated edge is secured: `x` is black (both inputs retained), or a non-free white whose forced input is the designated one. -/
theorem edgeOK_of_fan {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {sel : Site → Site} {D : Set Site}
    (hfan : ∀ c i, ForcedEdge G seed c i → c ∈ D → Nonfree frame c → sel c = i)
    {x y : Site} (hxD : x ∈ D) (hnf : Nonfree frame x) (hbin : laplacian G x = -1 ∨ laplacian G x = 0)
    (hforced : laplacian G x = 0 → ∃ i, ForcedEdge G seed x i)
    (hsel : sel x = y) (hy : y = incomingNeg x ∨ y = incomingPos x) : EdgeOK G seed x y := by
  rcases hbin with hb | hw
  · exact Or.inl ⟨hb, hy⟩
  · obtain ⟨i, hi⟩ := hforced hw
    have hiy : i = y := (hfan x i hi hxD hnf).symm.trans hsel
    exact Or.inr (hiy ▸ hi)

theorem incomingPos_of_even {x : Site} (h : EvenSite x) : incomingPos x = (x.1 + 1, x.2) := by
  unfold incomingPos
  rw [if_pos h]

theorem incomingNeg_of_even' {x : Site} (h : EvenSite x) : incomingNeg x = (x.1 - 1, x.2) := by
  unfold incomingNeg
  rw [if_pos h]

theorem incomingNeg_of_odd {x : Site} (h : ¬ EvenSite x) : incomingNeg x = (x.1, x.2 - 1) := by
  unfold incomingNeg
  rw [if_neg h]

/-- **Shape 1 from its edges**: the table's first shape with `EdgeOK` edges and `S`-memberships gives the policy's table. -/
theorem shapeOne_of_edgeOK {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (P : OldPolicyData frame G seed η) {S : Set Site} {z1 z2 : ℤ} (hz : (z1 + z2) % 2 = 1)
    (hS : (z1, z2 + 1) ∈ S ∧ (z1 + 1, z2 + 1) ∈ S ∧ (z1 + 1, z2) ∈ S)
    (e1 : EdgeOK G seed (z1, z2 + 1) (z1 + 1, z2 + 1))
    (e2 : EdgeOK G seed (z1 + 1, z2 + 1) (z1 + 1, z2))
    (e3 : EdgeOK G seed (z1 + 1, z2) (z1, z2)) :
    TableShape P.retained S (z1, z2) :=
  tableShape_of_edgeOK P ⟨z1, z2, rfl, Or.inl ⟨hz, hS, e1, e2, e3⟩⟩

/-- **Shape 1 from the fan.** Given the fan `D` (with forced-white compatibility `hfan`), the chain points in `D` and non-free, the
designated successors `sel` along the chain (east from the even `z+N`, south from the odd `z+E+N`, west from the even `z+E`), the forced
edges at the white chain points and their `S`-memberships, the policy's table holds at the odd free root `(z1, z2)`. -/
theorem shapeOne_of_fan {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (P : OldPolicyData frame G seed η) {S : Set Site} {sel : Site → Site} {D : Set Site}
    (hfan : ∀ c i, ForcedEdge G seed c i → c ∈ D → Nonfree frame c → sel c = i)
    {z1 z2 : ℤ} (hz : (z1 + z2) % 2 = 1)
    (hS : (z1, z2 + 1) ∈ S ∧ (z1 + 1, z2 + 1) ∈ S ∧ (z1 + 1, z2) ∈ S)
    (hD1 : (z1, z2 + 1) ∈ D) (hD2 : (z1 + 1, z2 + 1) ∈ D) (hD3 : (z1 + 1, z2) ∈ D)
    (hnf1 : Nonfree frame (z1, z2 + 1)) (hnf2 : Nonfree frame (z1 + 1, z2 + 1)) (hnf3 : Nonfree frame (z1 + 1, z2))
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (hF1 : laplacian G (z1, z2 + 1) = 0 → ∃ i, ForcedEdge G seed (z1, z2 + 1) i)
    (hF2 : laplacian G (z1 + 1, z2 + 1) = 0 → ∃ i, ForcedEdge G seed (z1 + 1, z2 + 1) i)
    (hF3 : laplacian G (z1 + 1, z2) = 0 → ∃ i, ForcedEdge G seed (z1 + 1, z2) i)
    (hs1 : sel (z1, z2 + 1) = (z1 + 1, z2 + 1))
    (hs2 : sel (z1 + 1, z2 + 1) = (z1 + 1, z2))
    (hs3 : sel (z1 + 1, z2) = (z1, z2)) :
    TableShape P.retained S (z1, z2) := by
  have hev1 : EvenSite (z1, z2 + 1) := by unfold EvenSite; simp only; omega
  have hod2 : ¬ EvenSite (z1 + 1, z2 + 1) := by unfold EvenSite; simp only; omega
  have hev3 : EvenSite (z1 + 1, z2) := by unfold EvenSite; simp only; omega
  refine shapeOne_of_edgeOK P hz hS ?_ ?_ ?_
  · exact edgeOK_of_fan hfan hD1 hnf1 (hbin _) hF1 hs1 (Or.inr (by simp [incomingPos_of_even hev1]))
  · exact edgeOK_of_fan hfan hD2 hnf2 (hbin _) hF2 hs2 (Or.inl (by simp [incomingNeg_of_odd hod2]))
  · exact edgeOK_of_fan hfan hD3 hnf3 (hbin _) hF3 hs3 (Or.inl (by simp [incomingNeg_of_even' hev3]))

end FLatticePaper.ReturnShapes
