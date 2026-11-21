import FLatticePaper.Tiles.RowOverlap

/-! The crossing lemma. If `S'` is edge-connected, meets `S`, and is not contained in `S`, then some cell of `S'` outside
`S` shares an edge with a cell of `S`: the boundary edge of `S` between them has the cell on the far side in `S'`.
The proof follows a chain of edge-adjacent cells of `S'` from a common cell to a cell outside `S`. It uses only the
edge-connectivity of `S'`; row convexity is not needed for this form. -/

namespace FLatticePaper.Tiles

theorem crossing_into {S S' : CellTile} (hE : EdgeConnected S') (hint : ∃ x, x ∈ S ∧ x ∈ S')
    (hnot : ¬ S' ⊆ S) : ∃ p ∈ S, ∃ q ∈ S', q ∉ S ∧ CellAdj p q := by
  obtain ⟨o, ho, hoS'⟩ := hint
  obtain ⟨b, hbS', hbS⟩ : ∃ b ∈ S', b ∉ S := by
    by_contra h
    exact hnot fun x hx => by_contra fun hxS => h ⟨x, hx, hxS⟩
  have hchain := hE o hoS' b hbS'
  obtain ⟨a, c, ha, hc, hac⟩ := cross_of_chain (R := fun z : GInt => z ∈ S) ho hchain hbS
  obtain ⟨-, hcS', hadj⟩ := hac
  exact ⟨a, ha, c, hcS', hc, hadj⟩

/-- Reduction of `NoFirstCrossing` to packing: if distinct cells of `T` are never congruent modulo the lattice (no
nonzero lattice vector is a difference of two cells of `T`), then no nonzero lattice translate overlaps `T`. -/
theorem noFirstCrossing_of_packing {T : CellTile} {v₁ v₂ : GInt}
    (hpack : ∀ x ∈ T, ∀ y ∈ T, x - y ∈ latticeOf v₁ v₂ → x = y) : NoFirstCrossing T v₁ v₂ := by
  refine ⟨fun u hu hu0 hov => ?_⟩
  obtain ⟨x, hx, hxu⟩ := hov
  have hdiff : x - (x - u) = u := by abel
  have heq := hpack x hx (x - u) hxu (by rw [hdiff]; exact hu)
  exact absurd (sub_eq_self.mp heq.symm) hu0

end FLatticePaper.Tiles
