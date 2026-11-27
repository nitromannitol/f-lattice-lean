import FLatticePaper.Plane.Induction.PlusRowAssembly
import FLatticePaper.Plane.Induction.WordMinusEasy
import FLatticePaper.Plane.Induction.RowVPlus
import FLatticePaper.Plane.Induction.NativeGrade
import FLatticePaper.Plane.Induction.WordBoundary
import FLatticePaper.Plane.Induction.OppWordCover
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Tiles.SiteScope
import FLatticePaper.Plane.Induction.EndpointStrips
import FLatticePaper.Plane.Induction.RoutePlus
import FLatticePaper.Plane.Induction.RowVTailRow
import FLatticePaper.Plane.Induction.FreeNonfree
import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.FaceRows
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.VChain
import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.SheetFacts
import FLatticePaper.Plane.Induction.WordVPattern
import FLatticePaper.Farey.Numerators

/-! # The plus endpoint facts and the plus row up to its H block, at the word (eta = 1, easy regime)

The facts of `PlusVm1` and of the plus prefix are proved from the word's strips and odd band, the free sites `H_0` and `V_0`,
the trace-based boundary price, and the deck vector `Vdeck` (which carries `(1,-1)` to `vLast`). -/

namespace FLatticePaper.WordPlusEasy

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeRows
  FLatticePaper.W1Seeds FLatticePaper.WordWebHyp FLatticePaper.WordVPattern FLatticePaper.WordDischarge
  FLatticePaper.WordMinusEasy FLatticePaper.PlusRowWiring

/-- The V label `V_{-2}` is the site `(1,-2)`. -/
theorem vAt_neg_two_eq (frame : ChildFrame) : RowAt.vAt frame (-2) = ((1 : ℤ), (-2 : ℤ)) := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  rw [RoutePlus.vAt_neg_eq frame (-2) (by omega) (by omega)]
  have hk : (-2 + (frame.child.den + frame.child.num)).toNat = (frame.child.num + frame.child.den - 2).toNat := by
    congr 1
    ring
  rw [hk]
  have hz := VChain.freeV_eq_vpath frame (frame.child.num + frame.child.den - 2).toNat
    (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2)
    (EndpointStrips.fVP frame) (by simp only; omega)
  rw [← hz]
  ext <;> simp [RoutePlus.Vt]

/-- The laplacian at `(2,-2)` vanishes: `G(1,-2) = G(2,-2) = G(3,-2) = -1` (the strip and the odd band). -/
theorem lap_2m2 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) (hreg : 2 * frame.child.num ≤ frame.child.den)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → G z = harmonicGrid z) :
    laplacian G ((2 : ℤ), (-2 : ℤ)) = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  obtain ⟨hn2, hd2⟩ := frame.child_odd
  rw [EndpointStrips.lap_even_eq G (2, -2) (by unfold EvenSite; norm_num)]
  have gA : G (2, -2) = -1 :=
    (EndpointStrips.harmAt hS 2 (-2) (4 * frame.child.num) (by rw [EndpointStrips.sG]; ring) (by omega) (by omega)).trans
      EndpointStrips.hg2m2
  have gB : G (1, -2) = -1 :=
    (EndpointStrips.harmAt hS 1 (-2) (3 * frame.child.num - frame.child.den) (by rw [EndpointStrips.sG]; ring)
      (by omega) (by omega)).trans EndpointStrips.hg1m2
  have gC : G (3, -2) = -1 := by
    rw [hO (3, -2) (by unfold EvenSite; norm_num) (by rw [EndpointStrips.sG]; omega)
      (by rw [EndpointStrips.sG]; omega)]
    unfold harmonicGrid
    norm_num
  show G (1, -2) + G (3, -2) - 2 * G (2, -2) = 0
  rw [gA, gB, gC]
  norm_num

/-- The free prescription `(1,-1) → (2,-1)` at `eta = 1`, through the deck vector (which carries `(1,-1)` to `vLast`). -/
theorem freePresc_Vm1 (frame : ChildFrame) :
    FreePolicy.FreePresc frame 1 ((1 : ℤ), (-1 : ℤ)) ((2 : ℤ), (-1 : ℤ)) := by
  have hv : ((1 : ℤ), (-1 : ℤ)) + Vdeck frame = frame.vLast := by
    unfold Vdeck ChildFrame.vLast
    ext <;> simp <;> ring
  refine ⟨Vdeck frame, Vdeck_mem_span frame, Or.inr ⟨?_, ?_⟩⟩
  · rw [hv]
    exact FreeVOrdinate.vLast_mem_freeV frame
  · rw [hv, FaceRows.prescV_vLast]
    norm_num

/-- The free prescription `(1,0) → (1,-1)` at `eta = 1` (`H_0` with its north-south prescription `(0,-1)`). -/
theorem freePresc_H0_plus (frame : ChildFrame) :
    ∀ i, FreePolicy.FreePresc frame 1 ((1 : ℤ), (0 : ℤ)) i ↔ i = ((1 : ℤ), (-1 : ℤ)) := by
  intro i
  have hm : FLatticePaper.Induction.hFirst ∈ frame.freeH := FLatticePaper.PsiMonoOffset.hFirst_mem_freeH frame
  have h := FreePolicy.freePresc_iff_H frame 1 hm i
  have hp : frame.prescribedH 1 FLatticePaper.Induction.hFirst = (0, -1) := frame.prescribedH_hFirst 1
  rw [hp] at h
  show FreePolicy.FreePresc frame 1 FLatticePaper.Induction.hFirst i ↔ i = ((1 : ℤ), (-1 : ℤ))
  rw [h]
  have hsum : FLatticePaper.Induction.hFirst + ((0 : ℤ), (-1 : ℤ)) = ((1 : ℤ), (-1 : ℤ)) := by
    norm_num [FLatticePaper.Induction.hFirst]
  rw [hsum]

/-- **The plus V tail is outside the restricted fort**, by strong induction over the positions, from the prefix and `plus_href_row`. -/
theorem plus_tail_removed (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {r : ℤ} (hr0 : 0 ≤ r)
    {S : Set Site} (hres : IsRestrictedFort F (permitsQ1 frame F 1) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F 1 z)
    (hPre : ∀ (j : ℕ) (e : Site), j < (r + 1).toNat + 2 → (plusSites frame r)[j]? = some e → e ∉ S) :
    ∀ (j : ℕ) (e : Site), (r + 1).toNat + 2 ≤ j →
      j < (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat →
      (plusSites frame r)[j]? = some e → e ∉ S := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro e hlo hhi he
    have hE : ∀ x, (∃ k' : ℕ, k' < j ∧ (plusSites frame r)[k']? = some x) → x ∉ S := by
      rintro x ⟨k', hk', hkx⟩
      by_cases hk3 : k' < (r + 1).toNat + 2
      · exact hPre k' x hk3 hkx
      · exact ih k' hk' x (by omega) (by omega) hkx
    have href := RowVPlus.plus_href_row hP hS hO hd2 hr0 j e he hlo (by omega)
    exact RefuteTree.refuted_not_mem frame F (Or.inl rfl) hres hK
      (E := fun x => ∃ k' : ℕ, k' < j ∧ (plusSites frame r)[k']? = some x) (C := fun _ => False) hE
      (fun x hx => hx.elim) _ href

/-- **The plus prefix at the word** (`r = brk word`). -/
theorem plusPrefix_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hSE : StrongEstimates (conjWord word)) (hTrC : TraceFromPsi.TraceAt (conjWord word))
    (hTrW : TraceFromPsi.TraceAt word)
    (hnd : 2 * (frameAt word).child.num ≤ (frameAt word).child.den)
    {S : Set Site} (hres : IsRestrictedFort (standardField word) (permitsQ1 (frameAt word) (standardField word) 1) S)
    (hK : ∀ z ∈ S, (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
      (frameAt word).roundedSlip (standardField word) 1 z) :
    ∀ (j : ℕ) (e : Site), j < (brk word + 1).toNat + 2 →
      (plusSites (frameAt word) (brk word))[j]? = some e → e ∉ S := by
  have hr1 : 1 ≤ brk word := by
    have := brk_pos word
    omega
  have hPHv := hPH_word hTrW ((2 : ℤ), (0 : ℤ)) (EndpointStrips.fH20 (frameAt word))
  exact PlusRowPrefix.plus_prefix_removed (frameAt word) (standardField word) hS.packet (brk word) hr1
    (hrL2_word word) (fun k hk => roundedSlip_plus_vpath hw hSE hTrC k hk)
    (fun z h1 h2 => OppWordCover.word_strip hS z (by omega) (by omega))
    (hO_word hS hpar) hnd (RowVTailRow.vAt_neg_one_eq (frameAt word)) (vAt_neg_two_eq (frameAt word))
    (EndpointStrips.lap_w1m1 hS.packet.strips) (freePresc_Vm1 (frameAt word))
    (EndpointStrips.lap_b2m1 hS.packet.strips)
    (lap_2m2 hS.packet.strips hnd (hO_word hS hpar))
    (by
      rintro ⟨s, hs, h⟩
      exact FreeNonfree.nonfree_2m2 (frame := frameAt word) s hs (h.elim Or.inl Or.inr))
    hPHv.1
    (WordBoundary.roundedSlip_freeH_word hw hSE (Or.inl rfl) (EndpointStrips.fH20 (frameAt word))).le
    (Or.inl (fun h => by
      have := hPHv.2 h
      norm_num [FLatticePaper.Induction.hFirst] at this))
    (hH0w_word hS) ((freePresc_H0_plus (frameAt word) ((1 : ℤ), (-1 : ℤ))).mpr rfl)
    (hV0w_word hS) (((hV0p_word 1) ((1 : ℤ), (0 : ℤ))).mpr rfl) hres hK

/-- **The whole plus row of an easy word is outside the restricted fort** (`eta = 1`): the prefix, the positive V tail (`plus_href_row`)
and the H block; the H block uses the cap `hAS` and the bound `V_index_plus`. -/
theorem plus_row_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hSE : StrongEstimates (conjWord word)) (hTrC : TraceFromPsi.TraceAt (conjWord word))
    (hTrW : TraceFromPsi.TraceAt word)
    (hnd : 2 * (frameAt word).child.num ≤ (frameAt word).child.den)
    {S : Set Site} (hres : IsRestrictedFort (standardField word) (permitsQ1 (frameAt word) (standardField word) 1) S)
    (hK : ∀ z ∈ S, (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
      (frameAt word).roundedSlip (standardField word) 1 z) :
    ∀ (j : ℕ) (e : Site), j < (brk word + 1).toNat + 2 + ((frameAt word).child.den + (frameAt word).child.num - brk word - 2).toNat
        + ((frameAt word).child.den - 1).toNat →
      (plusSites (frameAt word) (brk word))[j]? = some e → e ∉ S := by
  have h3 : 3 ≤ 2 * (frameAt word).parents.odd.num + 1 * (frameAt word).parents.even.num :=
    Farey.current_even_num_ge_three word hw
  have hc := ZoneI1.child_num_eq (frameAt word)
  obtain ⟨hdo, hno, hle, hpar2⟩ := NativeGrade.odd_parent_facts (frameAt word)
  obtain ⟨hpb0, hpa0, hpc0, hpe0⟩ := FLatticePaper.Tiles.SiteScope.parents_bounds word
  have hpa : 0 ≤ (frameAt word).parents.odd.num := hpa0
  have hpc : 1 ≤ (frameAt word).parents.even.num := hpc0
  have hpe : (frameAt word).parents.even.num ≤ (frameAt word).parents.even.den := by
    have h : 0 ≤ (frameAt word).parents.even.den - (frameAt word).parents.even.num := hpe0
    omega
  have hn1 : 1 ≤ (frameAt word).child.num := by omega
  have hnb2 : 2 ≤ (frameAt word).child.num := by omega
  have hpb' : (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den := by
    have h : 1 ≤ (frameAt word).parents.odd.den - (frameAt word).parents.odd.num := hpb0
    omega
  have hL : 0 < (frameAt word).child.den + (frameAt word).child.num := by
    obtain ⟨hn0, -, -, -, -⟩ := (frameAt word).child_facts
    omega
  have hPre := plusPrefix_word hw hS hpar hSE hTrC hTrW hnd hres hK
  have hTail := plus_tail_removed (frameAt word) (standardField word) hS.packet
    (fun z h1 h2 => OppWordCover.word_strip hS z (by omega) (by omega)) (hO_word hS hpar) hnd
    (le_of_lt (brk_pos word)) hres hK hPre
  exact PlusRowAssembly.plus_row_up_to_H_removed (frameAt word) (standardField word) hS.packet (hsig_word hS)
    (hZ2_word hS hpar) (hZ3_word hS hpar) hn1 hnd hnb2 hpa hpb' hpc hpe (cap_word hS hnd)
    (brk word) rfl (fun k hk => roundedSlip_plus_vpath hw hSE hTrC k hk)
    (fun z h1 h2 => OppWordCover.word_strip hS z (by omega) (by omega)) (hO_word hS hpar)
    (RowVTailRow.vAt_neg_one_eq (frameAt word)) (vAt_neg_two_eq (frameAt word))
    (EndpointStrips.lap_w1m1 hS.packet.strips) (freePresc_Vm1 (frameAt word))
    (EndpointStrips.lap_b2m1 hS.packet.strips)
    (lap_2m2 hS.packet.strips hnd (hO_word hS hpar))
    (by
      rintro ⟨s, hs, h⟩
      exact FreeNonfree.nonfree_2m2 (frame := frameAt word) s hs (h.elim Or.inl Or.inr))
    (hPH_word hTrW ((2 : ℤ), (0 : ℤ)) (EndpointStrips.fH20 (frameAt word))).1
    (WordBoundary.roundedSlip_freeH_word hw hSE (Or.inl rfl) (EndpointStrips.fH20 (frameAt word))).le
    (Or.inl (fun h => by
      have := (hPH_word hTrW ((2 : ℤ), (0 : ℤ)) (EndpointStrips.fH20 (frameAt word))).2 h
      norm_num [FLatticePaper.Induction.hFirst] at this))
    (hH0w_word hS) ((freePresc_H0_plus (frameAt word) ((1 : ℤ), (-1 : ℤ))).mpr rfl)
    (hV0w_word hS) (((hV0p_word 1) ((1 : ℤ), (0 : ℤ))).mpr rfl) hL hres hK hTail

end FLatticePaper.WordPlusEasy
