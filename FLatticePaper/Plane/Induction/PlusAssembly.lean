import FLatticePaper.Plane.Induction.PlusFinal
import FLatticePaper.Plane.Induction.FinalAssemblyMinus
import FLatticePaper.Plane.Induction.WordPlusEasy
import FLatticePaper.Plane.Induction.ChainDeck
import FLatticePaper.Plane.Induction.RestrictedFortShift
import FLatticePaper.Plane.Induction.FortPairMin
import FLatticePaper.Plane.Induction.FortAtRestricted
import FLatticePaper.Plane.Induction.PassageRank
import FLatticePaper.Plane.Induction.ForcedPriceSI
import FLatticePaper.Plane.Induction.Seams
import FLatticePaper.Plane.Induction.CutOnePerProper
import FLatticePaper.Plane.Induction.PassageInv

/-! # `RestrictedNoFort` for `permitsQ1` at sign `+1` on the easy words

As for the minus sign, with the plus objects: `kPlusW = price + roundedSlip 1`, the plus row (`plus_row_word`), the plus fort point
lemma (`PlusFinal.fort_point_is_label_plus`). On the closed polygon `P ≤ cutPrice` and `J_+ ≥ 0` (from the slip range), so a point
with `K = cutPrice` and `J_+ ≤ 0` is the pair `(cutPrice, 0)`; `J_+ ≤ 0` at the free endpoint comes from the passage invariant
of the passage (the passage does not increase `J_+` from the minimum, which has `J_+ = 0`). -/

namespace FLatticePaper.PlusAssembly

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeRows
  FLatticePaper.WordMinusEasy FLatticePaper.WordPlusEasy FLatticePaper.WordDischarge FLatticePaper.PlusFinal
  FLatticePaper.W1Seeds FLatticePaper.WordWebHyp FLatticePaper.WordVPattern FLatticePaper.FinalAssemblyMinus
  FLatticePaper.FinalCoverMinus FLatticePaper.FreeEnum FLatticePaper.KMinBridge

/-- `kPlusW` is the price plus the rounded slip for `η = +1`. -/
theorem kPlusW_eq (word : Word) (z : Site) :
    kPlusW word z = (frameAt word).price (standardField word) z +
      (frameAt word).roundedSlip (standardField word) 1 z := by
  unfold kPlusW jPlusW ChildFrame.roundedSlip ChildFrame.slip
  simp only [one_smul]

/-- **The pair `(cutPrice, 0)` on the closed polygon for the plus sign**, from `K_+ = cutPrice` and `J_+ ≤ 0`. -/
theorem pair_of_kPlus_eq {word : Word} (hS : StrongCore word) {f : Site}
    (hf : f ∈ (frameAt word).closedPolygon) (hK : kPlusW word f = (frameAt word).cutPrice)
    (hJ : (frameAt word).roundedSlip (standardField word) 1 f ≤ 0) :
    (frameAt word).price (standardField word) f = (frameAt word).cutPrice ∧
      (frameAt word).roundedSlip (standardField word) 1 f = 0 := by
  have hP := hS.priceRange f hf
  have hD := hS.slipRange f hf
  have hJ0 : 0 ≤ (frameAt word).roundedSlip (standardField word) 1 f := by
    unfold ChildFrame.roundedSlip
    omega
  rw [kPlusW_eq] at hK
  constructor <;> omega

/-- The length of the plus row. -/
theorem length_plusRow (r L d : ℤ) :
    (plusRow r L d).length = (r + 1).toNat + 2 + (L - r - 2).toNat + (d - 1).toNat := by
  unfold plusRow
  simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]

/-- **Every plus row site is outside a restricted fort of the word** (the list form of `plus_row_word`). -/
theorem plusSites_not_mem {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hSE : StrongEstimates (conjWord word))
    (hTrW : TraceFromPsi.TraceAt word) (hTrC : TraceFromPsi.TraceAt (conjWord word))
    (hnd : 2 * (frameAt word).child.num ≤ (frameAt word).child.den)
    {S : Set Site}
    (hres : IsRestrictedFort (standardField word) (permitsQ1 (frameAt word) (standardField word) 1) S)
    (hK : ∀ z ∈ S, (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
      (frameAt word).roundedSlip (standardField word) 1 z)
    (e : Site)
    (he : e ∈ PlusRowWiring.plusSites (frameAt word) ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) :
    e ∉ S := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  have hlen : k < (PlusRowWiring.plusSites (frameAt word)
      ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)).length :=
    (List.getElem?_eq_some_iff.mp hk).1
  have hlen' : k < ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num + 1).toNat + 2 +
      ((frameAt word).child.den + (frameAt word).child.num - ((frameAt word).parents.odd.den +
        (frameAt word).parents.odd.num) - 2).toNat + ((frameAt word).child.den - 1).toNat := by
    unfold PlusRowWiring.plusSites rowSites at hlen
    rw [List.length_map, length_plusRow] at hlen
    exact hlen
  exact plus_row_word hw hS hpar hSE hTrC hTrW hnd hres hK k e hlen' hk

/-- **`RestrictedNoFort` for `permitsQ1` at sign `+1`, at an easy word.** The named inputs: `hW` and `hW1` (the Q36 inputs),
`hz0` (the translate minimum lies in the closed polygon) and `hJpass` (the free endpoint of the passage has `J_+ ≤ 0`, the
monotonicity of the passage from the minimum `J_+ = 0`). -/
theorem restrictedNoFort_plus_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hSE : StrongEstimates (conjWord word))
    (hTrW : TraceFromPsi.TraceAt word) (hTrC : TraceFromPsi.TraceAt (conjWord word))
    (hnd : 2 * (frameAt word).child.num ≤ (frameAt word).child.den)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (hz0 : ∀ (S' : Set Site) (r' : Site),
      IsRestrictedFort (standardField word) (permitsQ1 (frameAt word) (standardField word) 1) S' →
      (∀ z ∈ S', (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
        (frameAt word).roundedSlip (standardField word) 1 z) →
      r' ∈ S' → (frameAt word).price (standardField word) r' = (frameAt word).cutPrice →
      (frameAt word).roundedSlip (standardField word) 1 r' = 0 → r' ∈ (frameAt word).closedPolygon) :
    RestrictedNoFort (standardField word)
      (fun z => (frameAt word).price (standardField word) z +
        (frameAt word).roundedSlip (standardField word) 1 z)
      (permitsQ1 (frameAt word) (standardField word) 1) := by
  intro level S hne hres hlev
  have hper := hS.packet.periods
  have hPD : ∀ z, (frameAt word).price (standardField word) (z + (frameAt word).child.modifiedDeck.kernel) =
      (frameAt word).price (standardField word) z + -1 ∧
      (frameAt word).price (standardField word) (z + (frameAt word).child.modifiedDeck.transverse) =
      (frameAt word).price (standardField word) z + 0 := by
    intro z
    have h1 := ChainDeck.price_kernel_mul (frameAt word) hS.packet 1 z
    have h2 := ChainDeck.price_transverse_mul (frameAt word) hS.packet 1 z
    rw [one_smul] at h1 h2
    exact ⟨by rw [h1]; ring, by rw [h2]; ring⟩
  have hSD : ∀ z, (frameAt word).slip (standardField word) 1 (z + (frameAt word).child.modifiedDeck.kernel) =
      (frameAt word).slip (standardField word) 1 z + 0 ∧
      (frameAt word).slip (standardField word) 1 (z + (frameAt word).child.modifiedDeck.transverse) =
      (frameAt word).slip (standardField word) 1 z + 2 * 1 := by
    intro z
    exact ⟨by rw [ChildFrame.slip_kernel (frameAt word) (standardField word) hper 1 z]; ring,
      ChildFrame.slip_transverse (frameAt word) (standardField word) hper 1 z⟩
  have hL : ∀ (c : Site) (i j : ℤ), laplacian (standardField word)
      (c + (frameAt word).child.modifiedDeck.combine i j) = laplacian (standardField word) c :=
    fun c i j => laplacian_add_combine hper c i j
  obtain ⟨T, -, hres', ⟨r', hr'S, hr'p, hr's⟩, hK'⟩ :=
    FortPairMin.exists_fort_translate_c0 (frameAt word) (standardField word) 1 (Or.inl rfl) hPD hSD hL hres hne
      level hlev
  have hcutr : kPlusW word r' = (frameAt word).cutPrice := by
    rw [kPlusW_eq, hr'p, hr's]
    ring
  have hmin : ∀ w ∈ RestrictedFortShift.shiftSet S T, kPlusW word r' ≤ kPlusW word w := by
    intro w hw'
    rw [hcutr, kPlusW_eq]
    simpa [hr'p, hr's] using hK' w hw'
  have hfort := fortAt_nonfree_of_restricted (frameAt word) (standardField word) 1 hres'
  have hcR := hz0 (RestrictedFortShift.shiftSet S T) r' hres' hK' hr'S hr'p hr's
  have hI0 : PassageInv.InvP word r' := by
    unfold PassageInv.InvP
    exact ⟨hr'p.le, hr's.le⟩
  obtain ⟨f, hfS, hfE, hfK, hfn, hfI⟩ := PassageInv.plus_passage_inv hw hSE
    (ForcedPriceSI.priceRangeOn_of_strong hS) hW hW1 hfort hr'S hcR hmin hI0
  have hpf := PassageInv.plus_pair_of_inv hfI (hfK.trans hcutr)
  have hex : ∃ v ∈ (frameAt word).child.modifiedDeck.span,
      f + v ∈ (frameAt word).freeH ∪ (frameAt word).freeV := by
    by_contra hcon
    exact hfn (fun v hv hmem => hcon ⟨v, hv, hmem⟩)
  obtain ⟨v, hv, hg⟩ := hex
  obtain ⟨ℓ, hℓ, hfℓ⟩ := PlusFinal.fort_point_is_label_plus hw hS hSE hTrW hTrC
    (CutOnePerProper.cutOnePerOrdinate_of_proper hw) hv hg hpf
  have hnot := plusSites_not_mem hw hS hpar hSE hTrW hTrC hnd hres' hK' ℓ hℓ
  exact hnot (hfℓ ▸ hfS)

end FLatticePaper.PlusAssembly
