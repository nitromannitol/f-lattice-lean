import FLatticePaper.Plane.Induction.ComparisonEmpty

/-! # Task 103 (the price input of the comparison passage, acyclic): the comparison transfer lemmas with the word's price range as the hypothesis

`PriceRangeOn word` is the price range `c₀ − 1 ≤ P ≤ c₀` on the closed polygon. It is supplied by `priceRange_of_conjugate` (from the conjugate's
strong estimates and the recurrence of `M`), not by the word's own strong estimates. The lemmas are the `ComparisonFields` / `ComparisonTransfer` /
`ComparisonEmpty` lemmas that used `hWord.priceRange`, restated with `hPR : PriceRangeOn word` (the proofs are unchanged up to that substitution;
`_PR` marks the restatement). -/

namespace FLatticePaper.PassagePR

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses

/-- The price range of the word on the closed polygon: `c₀ − 1 ≤ P ≤ c₀`. -/
def PriceRangeOn (word : Word) : Prop :=
  ∀ z ∈ (frameAt word).closedPolygon,
    (frameAt word).cutPrice - 1 ≤ (frameAt word).price (standardField word) z ∧
      (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice

/-- `cmpLow ≤ F` on the closed polygon: the word's price lower bound `P ≥ c₀ − 1`, with `c₀` the cut price. -/
theorem cmpLow_le_of_price_PR {word : Word} (hPR : PriceRangeOn word) :
    ∀ z ∈ (frameAt word).closedPolygon,
      FLatticePaper.Contacts.cmpLow (standardField word) (frameAt word).parentShift (frameAt word).eps
        ((frameAt word).parents.odd.num, -(frameAt word).parents.odd.den) (frameAt word).cutPrice z ≤
        standardField word z := by
  intro z hz
  have hp := hPR z hz
  unfold ChildFrame.price ChildFrame.parentSlope at hp
  unfold FLatticePaper.Contacts.cmpLow
  have e : z + -(frameAt word).parentShift = z - (frameAt word).parentShift := (sub_eq_add_neg z _).symm
  rw [e]
  have hs : (frameAt word).eps * (((frameAt word).parents.odd.num, -(frameAt word).parents.odd.den).1 * z.1 +
      ((frameAt word).parents.odd.num, -(frameAt word).parents.odd.den).2 * z.2) =
      (frameAt word).eps * ((frameAt word).parents.odd.num * z.1 - (frameAt word).parents.odd.den * z.2) := by
    ring
  linarith [hp.1, hs]

/-- Each comparison field lies below `F` on the closed polygon (ComparisonFields). -/
theorem isCmp_le_on_E_PR {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word) {m : Field} (hm : IsCmpField word m) :
    ∀ z ∈ (frameAt word).closedPolygon, m z ≤ standardField word z := by
  rcases hm with rfl | rfl | rfl
  · exact cmpLow_le_of_price_PR hPR
  · exact cmpUp_le_of_slip h hSE
  · exact cmpDown_le_of_slip h hSE

/-- **The transfer step (T) and the W1 no-refutation (W) give the forced-contact property.** A contact forced-white root `c` of the
comparison field `m` has every forced input `o` a contact: otherwise (T) produces an empty clause `EC m`, which (W) excludes.
`EC m` is "a finite empty clause for `m`" in the unit closure. -/
theorem forced_contact_transfer_PR {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word) {seed : Site → Site → Prop}
    (EC : Field → Prop)
    (hT : ∀ m, IsCmpField word m → ∀ c o, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (standardField word) c = 0 →
      standardField word c = m c → SquareClauses.ForcedEdge (standardField word) seed c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EC m)
    (hW : ∀ m, IsCmpField word m → ¬ EC m)
    {m : Field} (hm : IsCmpField word m) {c o : Site} (hSIc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : laplacian (standardField word) c = 0)
    (hc : standardField word c = m c) (hf : SquareClauses.ForcedEdge (standardField word) seed c o)
    (hoE : o ∈ (frameAt word).closedPolygon) : standardField word o = m o := by
  by_contra hne
  have hle := isCmp_le_on_E_PR h hSE hPR hm o hoE
  exact hW m hm (hT m hm c o hSIc hw hc hf hoE (lt_of_le_of_ne hle (fun e => hne e.symm)))

/-- `P` does not increase along a forced white edge (task 70 (c)): a lower contact root forces a lower contact input (T, W);
a non-lower root has `P = c₀` on the whole range. -/
theorem price_nonincrease_forced_PR {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word) {seed : Site → Site → Prop}
    (EC : Field → Prop)
    (hT : ∀ m, IsCmpField word m → ∀ c o, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (standardField word) c = 0 →
      standardField word c = m c → SquareClauses.ForcedEdge (standardField word) seed c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EC m)
    (hW : ∀ m, IsCmpField word m → ¬ EC m)
    {c o : Site} (hSIc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : SquareClauses.ForcedEdge (standardField word) seed c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (frameAt word).price (standardField word) o ≤ (frameAt word).price (standardField word) c := by
  have hpc := hPR c hcE
  have hpo := hPR o hoE
  by_cases hlow : (frameAt word).price (standardField word) c = (frameAt word).cutPrice - 1
  · have hc' := (price_eq_low_iff c).mp hlow
    have ho' := forced_contact_transfer_PR h hSE hPR EC hT hW (Or.inl rfl) hSIc hw hc' hf hoE
    have := (price_eq_low_iff o).mpr ho'
    omega
  · omega

/-- `J₊` does not increase along a forced white edge (task 70 (c)): `J₊ = ⌈D₊/2⌉` with `D₊ ∈ [0, 2]`; `J₊ = 0` exactly at the
contact of `cmpUp`, whose forced input is a contact (T, W). -/
theorem jplus_nonincrease_forced_PR {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word) {seed : Site → Site → Prop}
    (EC : Field → Prop)
    (hT : ∀ m, IsCmpField word m → ∀ c o, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (standardField word) c = 0 →
      standardField word c = m c → SquareClauses.ForcedEdge (standardField word) seed c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EC m)
    (hW : ∀ m, IsCmpField word m → ¬ EC m)
    {c o : Site} (hSIc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : SquareClauses.ForcedEdge (standardField word) seed c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (standardField word o - standardField word (o + (frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + (frameAt word).shortShift) + 1) / 2 := by
  have hDc := slipRange_of_strong h hSE c hcE
  have hDo := slipRange_of_strong h hSE o hoE
  by_cases hz : standardField word c - standardField word (c + (frameAt word).shortShift) = 0
  · have hc' : standardField word c = cmpUpW word c := by
      unfold cmpUpW FLatticePaper.Contacts.cmpUp
      linarith
    have ho' := forced_contact_transfer_PR h hSE hPR EC hT hW (Or.inr (Or.inl rfl)) hSIc hw hc' hf hoE
    unfold cmpUpW FLatticePaper.Contacts.cmpUp at ho'
    omega
  · omega

/-- `J₋` does not increase along a forced white edge (task 70 (c)): `J₋ = ⌈D₋/2⌉` with `D₋ ∈ [−2, 0]`; `J₋ = −1` exactly at the
contact of `cmpDown`, whose forced input is a contact (T, W). -/
theorem jminus_nonincrease_forced_PR {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word)
    (hpk : (frameAt word).Packet (standardField word)) {seed : Site → Site → Prop}
    (EC : Field → Prop)
    (hT : ∀ m, IsCmpField word m → ∀ c o, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (standardField word) c = 0 →
      standardField word c = m c → SquareClauses.ForcedEdge (standardField word) seed c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EC m)
    (hW : ∀ m, IsCmpField word m → ¬ EC m)
    {c o : Site} (hSIc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : SquareClauses.ForcedEdge (standardField word) seed c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (standardField word o - standardField word (o + -(frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + -(frameAt word).shortShift) + 1) / 2 := by
  have hDc := slip_minus_range h hSE hpk c hcE
  have hDo := slip_minus_range h hSE hpk o hoE
  by_cases hz : standardField word c - standardField word (c + -(frameAt word).shortShift) = -2
  · have hc' : standardField word c = cmpDownW word c := by
      unfold cmpDownW FLatticePaper.Contacts.cmpDown
      linarith
    have ho' := forced_contact_transfer_PR h hSE hPR EC hT hW (Or.inr (Or.inr rfl)) hSIc hw hc' hf hoE
    unfold cmpDownW FLatticePaper.Contacts.cmpDown at ho'
    omega
  · omega

/-- `P` does not increase along a black edge (task 70 (c)). -/
theorem price_nonincrease_black_PR {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word)
    (hpk : (frameAt word).Packet (standardField word)) {c i : Site}
    (hcE : c ∈ (frameAt word).closedPolygon) (hb : laplacian (standardField word) c = -1)
    (hi : i = FLatticePaper.incomingNeg c ∨ i = FLatticePaper.incomingPos c) :
    (frameAt word).price (standardField word) i ≤ (frameAt word).price (standardField word) c := by
  have hiE := input_mem_black hpk hcE hb hi
  have hpc := hPR c hcE
  have hpi := hPR i hiE
  by_cases hlow : (frameAt word).price (standardField word) c = (frameAt word).cutPrice - 1
  · have hc' := (price_eq_low_iff c).mp hlow
    have hpair := black_pair hpk (isCmp_binary hpk (Or.inl rfl : IsCmpField word (cmpLowW word)))
      (isCmp_le_on_E_PR h hSE hPR (Or.inl rfl : IsCmpField word (cmpLowW word))) hcE hb hc' hi
    have := (price_eq_low_iff i).mpr hpair
    omega
  · omega

/-- **Forced contacts from (T) and (W).** For the unseeded unit proofs, a contact forced-white root has a contact forced input,
where (T) is the hypothesis `hT` with the concrete empty clause and (W) is `hW`. -/
theorem forced_contact_of_sat_PR {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word)
    (hT : ∀ m, IsCmpField word m → ∀ c o, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (standardField word) c = 0 →
      standardField word c = m c → ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → False)
    {m : Field} (hm : IsCmpField word m) {c o : Site} (hSIc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : laplacian (standardField word) c = 0)
    (hc : standardField word c = m c) (hf : ForcedEdge (standardField word) (fun _ _ => False) c o)
    (hoE : o ∈ (frameAt word).closedPolygon) : standardField word o = m o :=
  forced_contact_transfer_PR h hSE hPR (fun _ => False) hT (fun _ _ h => h) hm hSIc hw hc hf hoE

/-- `P` does not increase along unseeded forced white edges, from (T) with the concrete empty clause and (W). -/
theorem price_nonincrease_forced_of_sat_PR {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word)
    (hT : ∀ m, IsCmpField word m → ∀ c o, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (standardField word) c = 0 →
      standardField word c = m c → ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → False)
    {c o : Site} (hSIc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (frameAt word).price (standardField word) o ≤ (frameAt word).price (standardField word) c :=
  price_nonincrease_forced_PR h hSE hPR (fun _ => False) hT (fun _ _ h => h) hSIc hw hcE hf hoE

/-- `J₊` does not increase along unseeded forced white edges, from (T) with the concrete empty clause and (W). -/
theorem jplus_nonincrease_forced_of_sat_PR {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word)
    (hT : ∀ m, IsCmpField word m → ∀ c o, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (standardField word) c = 0 →
      standardField word c = m c → ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → False)
    {c o : Site} (hSIc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (standardField word o - standardField word (o + (frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + (frameAt word).shortShift) + 1) / 2 :=
  jplus_nonincrease_forced_PR h hSE hPR (fun _ => False) hT (fun _ _ h => h) hSIc hw hcE hf hoE

/-- `J₋` does not increase along unseeded forced white edges, from (T) with the concrete empty clause and (W). -/
theorem jminus_nonincrease_forced_of_sat_PR {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word)
    (hT : ∀ m, IsCmpField word m → ∀ c o, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (standardField word) c = 0 →
      standardField word c = m c → ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → False)
    {c o : Site} (hSIc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (standardField word o - standardField word (o + -(frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + -(frameAt word).shortShift) + 1) / 2 :=
  jminus_nonincrease_forced_PR h hSE hPR (packet_of_strong h hSE) (fun _ => False) hT (fun _ _ h => h) hSIc hw hcE hf hoE

end FLatticePaper.PassagePR
