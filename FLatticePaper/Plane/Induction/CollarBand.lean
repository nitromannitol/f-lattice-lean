import FLatticePaper.Plane.Induction.CollarGlue
import FLatticePaper.Plane.Induction.NonfreeBridge

/-! Task 72 (hcollar, the strictness of the collar squares, lemma (a)).

Lemma 1 of the four: a free root is a translate of a free point by the child deck. If `z` is not nonfree, some deck translate
`z + (i U + j V)` lies in `freeH ∪ freeV`, where `U = (d, n)` and `V = (n − d, n + d)` are the child kernel and transverse. -/

namespace FLatticePaper.CollarBand

open Farey FLatticePaper FLatticePaper.Induction

/-- A root that is not nonfree has a deck translate in the free H or free V set. -/
theorem exists_translate_of_not_nonfree (frame : ChildFrame) {z : Site} (hz : ¬ Nonfree frame z) :
    ∃ i j : ℤ, z + (i * frame.child.den + j * (frame.child.num - frame.child.den),
      i * frame.child.num + j * (frame.child.num + frame.child.den)) ∈ frame.freeH ∪ frame.freeV := by
  unfold Nonfree at hz
  obtain ⟨v, hv⟩ := not_forall.mp hz
  obtain ⟨hvs, hmem⟩ := Classical.not_imp.mp hv
  have hmem' := not_not.mp hmem
  obtain ⟨i, j, rfl⟩ := hvs
  refine ⟨i, j, ?_⟩
  have e : PeriodDeck.combine frame.child.modifiedDeck i j =
      (i * frame.child.den + j * (frame.child.num - frame.child.den),
        i * frame.child.num + j * (frame.child.num + frame.child.den)) := by
    unfold PeriodDeck.combine
    rw [ChildFrame.child_modifiedDeck_kernel, ChildFrame.child_modifiedDeck_transverse]
  rw [← e]
  exact hmem'

end FLatticePaper.CollarBand
