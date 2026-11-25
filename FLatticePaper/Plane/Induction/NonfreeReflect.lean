import FLatticePaper.Plane.Induction.CollarTop
import FLatticePaper.Plane.Induction.FreeVReflect
import FLatticePaper.Plane.Induction.FreeClosure
import FLatticePaper.Plane.Induction.NonfreeBridge

/-! # The centre reflection carries the nonfree class (Q34, sign `−1`)

If `ρ c = centre − c` has a free span translate, so does `c`: the `freeH` translate by `CollarTop.freeH_reflect` (with the transverse),
the `freeV` translate by `FreeVReflect.freeV_reflect_word` (with the kernel). Since `centre = kernel + transverse + (1,−1)`, the two
reflections differ by span vectors, and the span is closed under negation and addition (`span_add_mem`, `span_neg_mem`). -/

namespace FLatticePaper.NonfreeReflect

open Farey FLatticePaper FLatticePaper.Induction

/-- **`ρ` carries nonfree sites to nonfree sites:** a free span translate of `centre − c` gives one of `c`. -/
theorem not_freeClosure_centre {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (c : Site)
    (hc : ¬ FLatticePaper.FreeClosure.freeClosure (frameAt word) c) :
    ¬ FLatticePaper.FreeClosure.freeClosure (frameAt word) ((frameAt word).centre - c) := by
  rintro ⟨s, hs, hmem⟩
  apply hc
  rcases hmem with hH | hV
  · have key := CollarTop.freeH_reflect (frameAt word) hH
    have hT : (frameAt word).child.modifiedDeck.transverse ∈ (frameAt word).child.modifiedDeck.span := by
      rw [(frameAt word).child_modifiedDeck_transverse]
      exact Vdeck_mem_span (frameAt word)
    refine ⟨-s - (frameAt word).child.modifiedDeck.transverse,
      span_add_mem (span_neg_mem hs) (span_neg_mem hT), Or.inl ?_⟩
    have e : (frameAt word).centre - ((frameAt word).centre - c + s + (frameAt word).child.modifiedDeck.transverse) =
        c + (-s - (frameAt word).child.modifiedDeck.transverse) := by
      unfold ChildFrame.centre
      ext <;> simp <;> ring
    rw [← e]
    exact key
  · have key := FreeVReflect.freeV_reflect_word h hV
    have hK : (frameAt word).child.modifiedDeck.kernel ∈ (frameAt word).child.modifiedDeck.span := by
      rw [(frameAt word).child_modifiedDeck_kernel]
      exact Kdeck_mem_span (frameAt word)
    refine ⟨-s - (frameAt word).child.modifiedDeck.kernel,
      span_add_mem (span_neg_mem hs) (span_neg_mem hK), Or.inr ?_⟩
    have e : ((1 : ℤ), (-1 : ℤ)) + (frameAt word).child.modifiedDeck.transverse -
        ((frameAt word).centre - c + s) = c + (-s - (frameAt word).child.modifiedDeck.kernel) := by
      unfold ChildFrame.centre
      ext <;> simp <;> ring
    rw [← e]
    exact key

end FLatticePaper.NonfreeReflect
