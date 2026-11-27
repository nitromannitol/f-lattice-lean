import FLatticePaper.Tiles.SurgicalOdometers
import FLatticePaper.Tiles.StackedMoreover

/-! # Item (c) of `lemma:weak_standard_odometer_properties`: lattice adjacent odometers are compatible

The text proves (c) by the stacked common extension: the two odometers restrict to the families of the stacked strings they
share, and those families agree on their common domain (`CrossCommon`, Section 5). This file states that reduction exactly.
The inputs that connect the odometers to the families (the restriction of each odometer to its family, and the covering of
the common domain by both families) are hypotheses here, named at their use. The lattice adjacency is recorded in the
statement and is not needed for the conclusion. -/

namespace FLatticePaper.Tiles

/-- Compatibility from the stacked common extension: if `o` restricts to `P` and `o'` restricts to `M`, the families agree on
their common domain (`CrossCommon P M`), and every common point of `o` and `o'` lies in a tile of `P` and in a tile of `M`, then
`o` and `o'` are compatible with offset constant `0`. -/
theorem compatible_of_cross (o o' : PartialOdometer) (P M : PTFamily) (hcross : CrossCommon P M)
    (hP : ∀ k < P.n, ∀ x ∈ P.dom k, o.val x = P.odo k x)
    (hM : ∀ j < M.n, ∀ x ∈ M.dom j, o'.val x = M.odo j x)
    (hcov : ∀ x ∈ o.dom ∩ o'.dom, (∃ k < P.n, x ∈ P.dom k) ∧ (∃ j < M.n, x ∈ M.dom j)) :
    Compatible o o' := by
  refine ⟨0, fun x hx => ?_⟩
  obtain ⟨⟨k, hk, hxk⟩, ⟨j, hj, hxj⟩⟩ := hcov x hx
  rw [hP k hk x hxk, hM j hj x hxj, hcross k hk j hj x hxk hxj]
  simp

/-- Item (c) as stated in the text, reduced to the stacked common extension: lattice adjacent odometers are compatible,
provided the stacked data of the reduction are given (`compatible_of_cross`). The lattice adjacency is not used. -/
theorem lattice_compatible_of_cross (n d : ℤ) (i : Bool) (c c' vi : GInt) (o o' : PartialOdometer)
    (P M : PTFamily) (hcross : CrossCommon P M)
    (hP : ∀ k < P.n, ∀ x ∈ P.dom k, o.val x = P.odo k x)
    (hM : ∀ j < M.n, ∀ x ∈ M.dom j, o'.val x = M.odo j x)
    (hcov : ∀ x ∈ o.dom ∩ o'.dom, (∃ k < P.n, x ∈ P.dom k) ∧ (∃ j < M.n, x ∈ M.dom j)) :
    LatticeAdjacent n d i c c' vi o o' → Compatible o o' :=
  fun _ => compatible_of_cross o o' P M hcross hP hM hcov

end FLatticePaper.Tiles
