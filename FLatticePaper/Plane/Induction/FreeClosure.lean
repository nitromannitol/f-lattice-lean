import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! Task w3, hgames item 5: the deck-invariant free set at a general frame.

`freeClosure frame c` is the deck closure of the H/V free boundary `freeH ∪ freeV`: `c` is free when some deck translate
`c + s`, `s` in the span of the kernel and the transverse vector, lies in `freeH` or `freeV`. The closure is the candidate for the
field `free` of `CanonicalPolicy`; its invariance under the span is generic (the span is an additive group). -/

namespace FLatticePaper.FreeClosure

open Farey FLatticePaper FLatticePaper.Induction

/-- The deck closure of the free H/V boundary of a child frame. -/
def freeClosure (frame : ChildFrame) (c : Site) : Prop :=
  ∃ s ∈ frame.child.modifiedDeck.span, (c + s) ∈ frame.freeH ∨ (c + s) ∈ frame.freeV

theorem span_sub {deck : PeriodDeck} {a b : Site} (ha : a ∈ deck.span) (hb : b ∈ deck.span) : a - b ∈ deck.span := by
  obtain ⟨i, j, rfl⟩ := ha
  obtain ⟨i', j', rfl⟩ := hb
  exact ⟨i - i', j - j', by ext <;> simp [PeriodDeck.combine] <;> ring⟩

theorem span_add {deck : PeriodDeck} {a b : Site} (ha : a ∈ deck.span) (hb : b ∈ deck.span) : a + b ∈ deck.span := by
  obtain ⟨i, j, rfl⟩ := ha
  obtain ⟨i', j', rfl⟩ := hb
  exact ⟨i + i', j + j', by ext <;> simp [PeriodDeck.combine] <;> ring⟩

/-- **Deck invariance of the free set**: translation by a span element permutes the closure. -/
theorem freeClosure_add_span (frame : ChildFrame) {step : Site} (hstep : step ∈ frame.child.modifiedDeck.span) (c : Site) :
    freeClosure frame (c + step) ↔ freeClosure frame c := by
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨step + s, span_add hstep hs, ?_⟩
    rwa [show c + (step + s) = c + step + s by abel]
  · rintro ⟨s, hs, h⟩
    refine ⟨s - step, span_sub hs hstep, ?_⟩
    rwa [show c + s = c + step + (s - step) by abel] at h

/-- The closure contains the free boundary itself (the zero translate). -/
theorem mem_freeClosure_of_freeH (frame : ChildFrame) {c : Site} (h : c ∈ frame.freeH) : freeClosure frame c := by
  refine ⟨0, ?_, Or.inl ?_⟩
  · exact ⟨0, 0, by ext <;> simp [PeriodDeck.combine]⟩
  · simpa using h

end FLatticePaper.FreeClosure
