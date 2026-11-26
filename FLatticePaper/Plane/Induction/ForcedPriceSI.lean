import FLatticePaper.Plane.Induction.PassagePR
import FLatticePaper.Plane.Induction.TransferW1
import FLatticePaper.Plane.Induction.ComparisonEmpty
import FLatticePaper.Plane.Induction.AuxRankSign
import FLatticePaper.Plane.Induction.WordPolicy
import FLatticePaper.Plane.Induction.CanonicalPermit
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! The forced price monotonicity of the word policy, with the concrete premises: no comparison data.

* `PriceRangeOn word` is the strong estimates' price range (`hWord.priceRange`).
* `HasSatSelection` comes from the aux rank (`hasSat_of_strict`): the aux graph gives a selection with a strict rank.
* The comparison hypothesis `hT` is `TransferW1.hT_strict` at strict-interior centres: it says the compare field agrees with the
  standard field at the forced output, so `m o < F o` is impossible and the clause `EC` (taken to be `False`) holds vacuously.
* A nonfree white is translated into the strict interior by a span element (`closedPolygon_covers`), as in `WordPolicy.forced_monotone_word`. -/

namespace FLatticePaper.ForcedPriceSI

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankSign FLatticePaper.FreeClosure FLatticePaper.FreePolicy
  FLatticePaper.SquareClauses FLatticePaper.PassagePR FLatticePaper.WordPolicy

theorem priceRangeOn_of_strong {word : Word} (hWord : StrongCore word) : PriceRangeOn word :=
  fun z hz => hWord.priceRange z hz

/-- A selection from the aux rank of sign η: blacks keep both inputs, whites their aux input, with the strict rank. -/
theorem hasSat_of_aux {word : Word} (η : ℤ) (hη : η = 1 ∨ η = -1) (hWord : StrongCore word)
    {R : Site → ℤ} (hstrict : ∀ c i, auxS (frameAt word) (standardField word) η c i → R i < R c) :
    HasSatSelection (standardField word) := by
  refine hasSat_of_strict (R := R) hWord.packet.binary ?_ ?_
  · intro c hc i hi
    have := hstrict c i (Or.inl ⟨hc, hi⟩)
    omega
  · intro c
    by_cases hc : laplacian (standardField word) c = 0
    · obtain ⟨i, hi⟩ := auxS_exists (frameAt word) η hη (evenSite_shortShift (frameAt word)) hWord.packet.binary
        hWord.F1_unitSlip (CanonicalPermit.standardField_reflect_core hWord) hc
      exact ⟨i, fun _ => ⟨auxS_edge hη hi, by have := hstrict c i hi; omega⟩⟩
    · exact ⟨incomingNeg c, fun h0 => absurd h0 hc⟩

/-- The forced price monotonicity at a nonfree white, with the strict-interior comparison and no comparison data. -/
theorem forced_monotone_PR (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongCore word)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (hW : HasSatSelection (standardField word))
    {c o : Site} (hl : laplacian (standardField word) c = 0) (hnc : ¬ freeClosure (frameAt word) c)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) c o) :
    (frameAt word).price (standardField word) o ≤ (frameAt word).price (standardField word) c := by
  obtain ⟨y, hy, a, b, rfl⟩ := (frameAt word).closedPolygon_covers c
  have hs : (frameAt word).child.modifiedDeck.combine a b ∈ (frameAt word).child.modifiedDeck.span := ⟨a, b, rfl⟩
  have hnv := span_neg_mem hs
  have hyl : laplacian (standardField word) y = 0 := by
    rw [← laplacian_span_inv (frameAt word) (standardField word) hWord.packet hs y]
    exact hl
  have hnc' : ¬ freeClosure (frameAt word) y := fun hy' => hnc ((freeClosure_add_span (frameAt word) hs y).mpr hy')
  have hSI := FLatticePaper.TransferW1.nonfree_strictInterior (frameAt word) hy (nonfree_of_not_closure (frameAt word) hnc')
  have hyf : ForcedEdge (standardField word) (fun _ _ => False) y (o + -((frameAt word).child.modifiedDeck.combine a b)) := by
    have hf' := forcedEdge_add (standardField word) (evenSite_of_span (frameAt word) hnv)
      (fun z => laplacian_span_inv (frameAt word) (standardField word) hWord.packet hnv z) hf
    rw [add_neg_cancel_right] at hf'
    exact hf'
  obtain ⟨u, hu, eu⟩ := input_unit y _ (forcedEdge_input hyf)
  have hoE : o + -((frameAt word).child.modifiedDeck.combine a b) ∈ (frameAt word).closedPolygon := by
    rw [eu]
    exact PriceDeck.si_neighbour_mem (frameAt word) hSI u hu
  have hT : ∀ m, IsCmpField word m → ∀ c o, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (standardField word) c = 0 → standardField word c = m c →
      ForcedEdge (standardField word) (fun _ _ => False) c o → o ∈ (frameAt word).closedPolygon →
      m o < standardField word o → False := by
    intro m hm c o hSIc hw0 hc0 hf0 _ hlt
    have heq := FLatticePaper.TransferW1.hT_strict h hSE (priceRangeOn_of_strong hWord) hW hW1 hm hSIc hw0 hc0 hf0
    exact absurd heq (ne_of_gt hlt)
  have hkey := price_nonincrease_forced_PR h hSE (priceRangeOn_of_strong hWord) (fun _ => False) hT
    (fun m _ => not_false) hSI hyl hy hyf hoE
  have h1 := ChainDeck.price_combine (frameAt word) hWord.packet a b (o + -((frameAt word).child.modifiedDeck.combine a b))
  have e : o + -((frameAt word).child.modifiedDeck.combine a b) + (frameAt word).child.modifiedDeck.combine a b = o := by
    abel
  rw [e] at h1
  have h2 := ChainDeck.price_combine (frameAt word) hWord.packet a b y
  rw [h1, h2]
  linarith

/-- **The word's price monotonicity along the free-edge policy**, with the strict-interior comparison and no comparison data:
blacks by `black_monotone_word`, free whites by `hfreeP`, nonfree whites by `forced_monotone_PR` (with `HasSatSelection`). -/
theorem word_price_nonincreasing_SI (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongCore word)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (hW : HasSatSelection (standardField word)) (η : ℤ)
    (hfreeP : ∀ c i, laplacian (standardField word) c = 0 → freeClosure (frameAt word) c →
      FreePresc (frameAt word) η c i →
      (frameAt word).price (standardField word) i ≤ (frameAt word).price (standardField word) c) :
    NonincreasingAlong ((frameAt word).price (standardField word)) (freePolicy (frameAt word) (standardField word) η) := by
  have hex : ForcedExists (frameAt word) (standardField word) := forcedExists_of (frameAt word) hWord.packet hW1
  intro c i hci
  unfold freePolicy at hci
  rcases hci with ⟨hl, hE⟩ | ⟨hl, ⟨hcl, hp⟩ | ⟨hn, hs⟩⟩
  · exact black_monotone_word word h hSE hWord hl hE
  · exact hfreeP c i hl hcl hp
  · rw [hs]
    exact forced_monotone_PR word h hSE hWord hW1 hW hl hn (forcedSel_spec (hex c hn hl))

end FLatticePaper.ForcedPriceSI
