import FLatticePaper.Plane.Induction.RestrictedPassage

/-! # The minimal slice of a restricted fort keeps its pair along the passage (Q1 l.13, l.40)

Let `K = P + J`. At a site `z` of a restricted fort `S` where `K` is minimal over `S`, the passage (`RestrictedPassage.restricted_successor`)
gives an input `u ∈ S` with `K u ≤ K z`. Minimality forces `K u = K z`. If the passage edges are componentwise nonincreasing (`P u ≤ P z`,
`J u ≤ J z`, the lower-contact transfer of Q1 l.13, named here as `hpass`), then equality of the sums forces equality of both components:
the passage keeps the pair. -/

namespace FLatticePaper.SlicePassage

open FLatticePaper FLatticePaper.Induction FLatticePaper.RestrictedPassage

theorem minimal_passage_pair {frame : ChildFrame} {F : Field} {η : ℤ} {S : Set Site}
    (hS : FLatticePaper.IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F η) S)
    (K P J : Site → ℤ) (hK : ∀ z, K z = P z + J z)
    (hBlack : ∀ z u : Site, laplacian F z = -1 → Edge u z → K u ≤ K z)
    (hFree : ∀ z : Site, laplacian F z = 0 → FreeClosure.freeClosure frame z →
      ∃ p : Site, Edge p z ∧ FreePolicy.FreePresc frame η z p ∧ K p ≤ K z)
    (hNonfree : ∀ z : Site, laplacian F z = 0 → ¬ FreeClosure.freeClosure frame z →
      ∃ u : Site, Edge u z ∧ K u ≤ K z)
    (hpass : ∀ z u : Site, Edge u z → P u ≤ P z ∧ J u ≤ J z)
    (z : Site) (hz : z ∈ S) (hmin : ∀ w ∈ S, K z ≤ K w) :
    ∃ u ∈ S, Edge u z ∧ P u = P z ∧ J u = J z := by
  obtain ⟨u, huS, hEu, hKu⟩ := restricted_successor hS K hBlack hFree hNonfree z hz
  have hc := hpass z u hEu
  have hm := hmin u huS
  have e1 := hK z
  have e2 := hK u
  refine ⟨u, huS, hEu, ?_, ?_⟩ <;> omega

end FLatticePaper.SlicePassage
