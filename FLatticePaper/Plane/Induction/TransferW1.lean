import FLatticePaper.Plane.Induction.TransferSat
import FLatticePaper.Plane.Induction.W1Bridge
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.NonfreeBridge

/-! # (T) at the strict interior, from `W1Forced` of the word

`W1Forced` of `standardField word` gives, at each strict-interior white `c`, a derivation `ForcedEdgeIn` whose unit squares lie in the strict
interior. Such squares are contained in the closed polygon (their corners by `strictInterior_closedRect`, their inputs by `rectInputs`), so
`transfer_hT_of_contained` applies to them. With a satisfying selection of `F` (W), forced inputs are unique (`forced_sound`), so the
unrestricted derivation `hf` of `c` has the same output as the contained one. This gives the hypothesis `hT` of `ComparisonTransfer` at
strict-interior contacts, for the derivations of `ForcedEdge` with empty seed.

Order: `W1Forced(MW word)` is produced by `W1Forced_of_tables_rk` from the conjugate's `W1Forced`, the conjugate's policy and its table rows,
and the collar input; it does not use the passage or the fans at `word`, so this closure is not circular (`W1Step`, `W1NonfreeHsqC`,
`W1FreeHfree`, `W1FreeBound` do not import the passage, fan or schedule modules). -/

namespace FLatticePaper.TransferW1

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.TransferSat FLatticePaper.PassagePR
open FLatticePaper.W1MSheet

/-- A strict-interior site of a child frame, with its two inputs, lies in the closed polygon (the corners of the strict interior are its
own star). -/
theorem strictInterior_star (frame : ChildFrame) {z : Site}
    (hz : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den z) :
    StarIn (fun y => y ∈ frame.closedPolygon) z := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hcl : z ∈ frame.closedPolygon := by
    rw [FLatticePaper.W1.closedPolygon_eq_closedRect]
    exact FLatticePaper.W1.strictInterior_closedRect (by omega) (by omega) z hz
  have hopen := (FLatticePaper.W1Exit.openRect_iff frame z).2 hz
  refine ⟨hcl, ?_, ?_⟩
  · exact FLatticePaper.W1Exit.rectInputs frame z hopen (incomingNeg z) (Or.inl rfl)
  · exact FLatticePaper.W1Exit.rectInputs frame z hopen (incomingPos z) (Or.inr rfl)

/-- The zero vector lies in the deck span. -/
theorem zero_deck_mem (frame : ChildFrame) : (0 : Site) ∈ frame.child.modifiedDeck.span :=
  ⟨0, 0, by ext <;> simp [PeriodDeck.combine]⟩

/-- A nonfree site of the closed polygon is in the strict interior: a point of `E` outside `StrictInterior` is free, or its translate by
`−V` or `−K` is free (`outside_SI_free`), and `0`, `−V`, `−K` lie in the deck span, which `Nonfree` excludes. -/
theorem nonfree_strictInterior (frame : ChildFrame) {z : Site} (hz : z ∈ frame.closedPolygon) (hnf : Nonfree frame z) :
    FLatticePaper.W1.StrictInterior frame.child.num frame.child.den z := by
  by_contra hns
  rcases outside_SI_free frame z hz hns with h | h | h
  · exact hnf 0 (zero_deck_mem frame) (by rw [add_zero]; exact h)
  · exact hnf (-Vdeck frame) (span_neg_mem (Vdeck_mem_span frame)) h
  · exact hnf (-Kdeck frame) (span_neg_mem (Kdeck_mem_span frame)) h

/-- **(T) at strict-interior contacts** (task 104 closure): for a comparison field `m` of `standardField word`, a strict-interior white contact
`c` with `F c = m c`, and an unrestricted unseeded forced derivation `ForcedEdge F ∅ c o`, the forced input satisfies `F o = m o`; so `m o < F o`
is excluded and `hT` of `ComparisonTransfer` holds there. It uses (W) and `W1Forced` of the standard field. -/
theorem hT_strict {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {m : Field} (hm : IsCmpField word m) {c o : Site}
    (hSI : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : laplacian (standardField word) c = 0) (hc : standardField word c = m c)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) c o) :
    standardField word o = m o := by
  obtain ⟨o', hf'⟩ := hW1 c hSI hw
  have hR : ∀ z, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den z →
      StarIn (fun y => y ∈ (frameAt word).closedPolygon) z :=
    fun z hz => strictInterior_star (frameAt word) hz
  have h1 := transfer_hT_of_contained h hSE hPR hW hR hm hw hc hf'
  obtain ⟨selF, hselF, hsqF⟩ := hW
  have hseed : ∀ x i, (fun (_ _ : Site) => False) x i → selF x = i := fun _ _ e => e.elim
  have e1 := forced_sound (standardField word) (fun _ _ => False) selF hselF hseed hsqF c o hf
  have e2 := forced_sound (standardField word) (fun _ _ => False) selF hselF hseed hsqF c o'
    (FLatticePaper.W1.forcedEdgeIn_forced hf')
  have ho : o = o' := e1.symm.trans e2
  rw [ho]
  exact h1

/-- **(T) at strict-interior contacts from `W1Forced` of the sheet minimum**: the standard field's `W1Forced` is the bridge image of the sheet
minimum's (`W1Bridge.W1Forced_standardField_of_MW`). -/
theorem hT_strict_of_MW {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hWMW : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (MW word))
    {m : Field} (hm : IsCmpField word m) {c o : Site}
    (hSI : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : laplacian (standardField word) c = 0) (hc : standardField word c = m c)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) c o) :
    standardField word o = m o :=
  hT_strict h hSE hPR hW (FLatticePaper.W1Bridge.W1Forced_standardField_of_MW word h hSE hWMW) hm hSI hw hc hf

end FLatticePaper.TransferW1
