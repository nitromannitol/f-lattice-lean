import FLatticePaper.Plane.Induction.FreeChain
import FLatticePaper.Plane.Induction.ComparisonTransfer
import FLatticePaper.Plane.Induction.ComparisonEmpty
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.TransferW1
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.StrongPriceValues
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! hgames, items 11–12 for the word: the policy specialised to `F = standardField word` on `frameAt word`.

The price inequalities along the policy edges:
* black edges: `price_nonincrease_black` at a polygon representative (the price drifts by the same amount at a centre and its input under
  a span translate, so the representative reduces the claim to the polygon);
* forced edges (nonfree whites): `price_nonincrease_forced` at a strict-interior representative (its forced output is in the polygon,
  `si_neighbour_mem`);
* prescribed edges (free whites): a named premise `hfreeP` (the signed H/V neighbour price, not yet in the repo).

The raw slip permit is a named premise `hslip` (item 8); the rounded slip `J` is monotone by `roundedSlip_mono`, so item 12 for `J` follows
from it. The word's strong estimates and comparison data are premises of the step. -/

namespace FLatticePaper.WordPolicy

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreePolicy FLatticePaper.FreeClosure FLatticePaper.SquareClauses

/-- An edge translates: if `i` is an input of `y + s` (`s` even), then `i − s` is an input of `y`. -/
theorem edge_translate (frame : ChildFrame) {i y : Site} {a b : ℤ}
    (h : Edge i (y + frame.child.modifiedDeck.combine a b)) : Edge (i - frame.child.modifiedDeck.combine a b) y := by
  have he : EvenSite (frame.child.modifiedDeck.combine a b) := ChainDeck.combine_even frame a b
  unfold Edge at h ⊢
  rcases h with h | h
  · left
    rw [h, DeckSelection.incomingNeg_add_even he]
    abel
  · right
    rw [h, DeckSelection.incomingPos_add_even he]
    abel

/-- A forced output `o` of a strict-interior centre is an input at unit distance, hence in the polygon. -/
theorem input_unit (y o : Site) (h : o = incomingNeg y ∨ o = incomingPos y) :
    ∃ u : Site, (u = (0, 1) ∨ u = (0, -1) ∨ u = (1, 0) ∨ u = (-1, 0)) ∧ o = y + u := by
  by_cases he : EvenSite y
  · rcases h with h | h
    · rw [inNeg_even he] at h
      exact ⟨(-1, 0), Or.inr (Or.inr (Or.inr rfl)), by rw [h]; ext <;> simp [sub_eq_add_neg]⟩
    · rw [inPos_even he] at h
      exact ⟨(1, 0), Or.inr (Or.inr (Or.inl rfl)), by rw [h]; ext <;> simp⟩
  · rcases h with h | h
    · rw [inNeg_odd he] at h
      exact ⟨(0, -1), Or.inr (Or.inl rfl), by rw [h]; ext <;> simp [sub_eq_add_neg]⟩
    · rw [inPos_odd he] at h
      exact ⟨(0, 1), Or.inl rfl, by rw [h]; ext <;> simp⟩

theorem nonfree_of_not_closure (frame : ChildFrame) {c : Site} (h : ¬ freeClosure frame c) : Nonfree frame c := by
  intro v hv hmem
  exact h ⟨v, hv, (Set.mem_union _ _ _).mp hmem⟩

/-- **The black edges.** A black retained edge does not increase the primitive price (`price_nonincrease_black`, at a polygon representative). -/
theorem black_monotone_word (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongCore word)
    {c i : Site} (hb : laplacian (standardField word) c = -1) (hE : Edge i c) :
    (frameAt word).price (standardField word) i ≤ (frameAt word).price (standardField word) c := by
  obtain ⟨y, hy, a, b, rfl⟩ := (frameAt word).closedPolygon_covers c
  have hs : (frameAt word).child.modifiedDeck.combine a b ∈ (frameAt word).child.modifiedDeck.span := ⟨a, b, rfl⟩
  have hyb : laplacian (standardField word) y = -1 := by
    rw [← laplacian_span_inv (frameAt word) (standardField word) hWord.packet hs y]
    exact hb
  have hi' := edge_translate (frameAt word) hE
  have hkey := price_nonincrease_black h hSE hWord hWord.packet hy hyb hi'
  have h1 := ChainDeck.price_combine (frameAt word) hWord.packet a b (i - (frameAt word).child.modifiedDeck.combine a b)
  rw [sub_add_cancel] at h1
  have h2 := ChainDeck.price_combine (frameAt word) hWord.packet a b y
  rw [h1, h2]
  linarith

/-- **The forced edges.** A forced edge of a nonfree white does not increase the primitive price (`price_nonincrease_forced`, at a
strict-interior representative whose forced output lies in the polygon). -/
theorem forced_monotone_word (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongCore word)
    (EC : Field → Prop)
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 → standardField word c = m c →
      ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EC m)
    (hW : ∀ m, IsCmpField word m → ¬ EC m)
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
  have hkey := price_nonincrease_forced h hSE hWord EC hT hW hyl hy hyf hoE
  have h1 := ChainDeck.price_combine (frameAt word) hWord.packet a b (o + -((frameAt word).child.modifiedDeck.combine a b))
  have e : o + -((frameAt word).child.modifiedDeck.combine a b) + (frameAt word).child.modifiedDeck.combine a b = o := by
    abel
  rw [e] at h1
  have h2 := ChainDeck.price_combine (frameAt word) hWord.packet a b y
  rw [h1, h2]
  linarith

/-- **Items 11 (primitive price), the policy on the word.** The retained edges of `freePolicy` do not increase the primitive price,
given the word's strong estimates, the forced existence, the comparison data (`EC`, `hT`, `hW`) and the free-edge price premise `hfreeP`. -/
theorem word_price_nonincreasing (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongCore word)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (EC : Field → Prop)
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 → standardField word c = m c →
      ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EC m)
    (hW : ∀ m, IsCmpField word m → ¬ EC m) (η : ℤ)
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
    exact forced_monotone_word word h hSE hWord EC hT hW hl hn (forcedSel_spec (hex c hn hl))

/-- **Item 12 (the rounded slip).** `J = roundedSlip` is nonincreasing along the policy edges, given the raw slip permit on them. -/
theorem word_J_nonincreasing (word : Word) (η : ℤ)
    (hslip : ∀ c i, freePolicy (frameAt word) (standardField word) η c i →
      (frameAt word).slip (standardField word) η i ≤ (frameAt word).slip (standardField word) η c) :
    ∀ c i, freePolicy (frameAt word) (standardField word) η c i →
      (frameAt word).cutGrade (standardField word) 0 1 η i ≤ (frameAt word).cutGrade (standardField word) 0 1 η c := by
  intro c i hci
  have hm := StrongPriceValues.roundedSlip_mono (frameAt word) (standardField word) η (hslip c i hci)
  unfold ChildFrame.cutGrade
  simp only [zero_mul, zero_add, one_mul]
  exact hm

/-- **Item 8 (the raw-slip permit) is the slip premise itself:** `slipPermits` on the shifted field is `slip i ≤ slip c`. -/
theorem word_permitted (word : Word) (η : ℤ)
    (hslip : ∀ c i, freePolicy (frameAt word) (standardField word) η c i →
      (frameAt word).slip (standardField word) η i ≤ (frameAt word).slip (standardField word) η c) :
    ∀ c i, freePolicy (frameAt word) (standardField word) η c i →
      slipPermits (standardField word) (fun z => standardField word (z + η • (frameAt word).shortShift)) c i := by
  intro c i hci
  have hm := hslip c i hci
  unfold ChildFrame.slip at hm
  unfold slipPermits slipIncrement
  linarith

/-- **The named inputs of the word's signed policy:** the primitive price (items 11), the permit and the rounded slip (items 8, 12), the strict
rank and the exceptional west input, with the premises listed in the module header. -/
theorem word_named_inputs (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongCore word)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (EC : Field → Prop)
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 → standardField word c = m c →
      ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EC m)
    (hW : ∀ m, IsCmpField word m → ¬ EC m) (η : ℤ) (R : Site → ℤ)
    (hfreeP : ∀ c i, laplacian (standardField word) c = 0 → freeClosure (frameAt word) c →
      FreePresc (frameAt word) η c i →
      (frameAt word).price (standardField word) i ≤ (frameAt word).price (standardField word) c)
    (hslip : ∀ c i, freePolicy (frameAt word) (standardField word) η c i →
      (frameAt word).slip (standardField word) η i ≤ (frameAt word).slip (standardField word) η c)
    (hstrict : ∀ c i, freePolicy (frameAt word) (standardField word) η c i → R i < R c)
    (hwest : (frameAt word).eps = 1 → freePolicy (frameAt word) (standardField word) η
      ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1)
      (incomingNeg ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1))) :
    FreeNamedInputs (frameAt word) (standardField word) η R :=
  { permitted := word_permitted word η hslip
    nonincreasingP := fun c i hci => by
      have hm := word_price_nonincreasing word h hSE hWord hW1 EC hT hW η hfreeP c i hci
      rw [cutGrade_one_zero_one, cutGrade_one_zero_one]
      exact hm
    nonincreasingJ := word_J_nonincreasing word η hslip
    strictRank := hstrict
    westAtException := hwest }

end FLatticePaper.WordPolicy
