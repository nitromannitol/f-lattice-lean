import FLatticePaper.Plane.Induction.AuxRank
import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.SlipPermitH2
import FLatticePaper.Plane.Induction.SlipPermitVend
import FLatticePaper.Plane.Induction.CanonicalPermit
import FLatticePaper.Plane.Induction.SlipMinusPermit
import FLatticePaper.Plane.Induction.BothFreeGrades
import FLatticePaper.Plane.Induction.ChildNumerator

/-! The `permitted` field of the word's free-edge signed policy, for both signs.

A `freePolicy` edge `c → i` is a black edge (both inputs), a free white edge `i = c + prescribed(c+t)` with `c+t` free H or V
(`FreePresc`), or a nonfree white edge `i = forcedSel c`. The slip permit `slip η i ≤ slip η c` is:
* black: `black_permit_plus` (sign +1) and `black_permit_neg` (sign −1), given `OddBlackNoRise`;
* free H: `SlipPermitH2.slip_permit_H` (both signs);
* free V: the sign +1 permit `CanonicalPermit.slip_permit_freeV_canonical` (and `SlipPermitVend.slip_permit_Vend` at `V_end`), and the
  sign −1 permit `SlipMinusPermit.slip_permit_freeV_minus`, both at the representative `c+t`, translated back by `slip_combine`;
* nonfree white: `AuxRank.forced_permitted` (sign +1) from the aux rank; the sign −1 forced permit is a named input. -/

namespace FLatticePaper.FreePermitted

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreePolicy FLatticePaper.AuxRank FLatticePaper.FreeClosure
  FLatticePaper.SquareClauses

/-- `slipPermits` on the `η`-shifted field is the slip inequality `slip η i ≤ slip η c`. -/
theorem slipPermits_iff_slip {word : Word} (η : ℤ) (c i : Site) :
    slipPermits (standardField word) (fun z => standardField word (z + η • (frameAt word).shortShift)) c i ↔
      (frameAt word).slip (standardField word) η i ≤ (frameAt word).slip (standardField word) η c := by
  unfold slipPermits slipIncrement ChildFrame.slip
  constructor <;> intro hh <;> linarith

/-- Translation: a permit at the representative `c' = c + t`, `i' = i + t` gives the permit at `c, i` (the drift `2ηj` cancels). -/
theorem slip_le_of_translate {word : Word} (hW : StrongEstimates word) (η : ℤ) {c i c' i' t : Site}
    (ht : t ∈ (frameAt word).child.modifiedDeck.span) (hc' : c' = c + t) (hi' : i' = i + t)
    (h' : (frameAt word).slip (standardField word) η i' ≤ (frameAt word).slip (standardField word) η c') :
    (frameAt word).slip (standardField word) η i ≤ (frameAt word).slip (standardField word) η c := by
  obtain ⟨a, b, rfl⟩ := ht
  have d1 := SlipPermitH2.slip_combine (frameAt word) hW.packet.periods η a b i
  have d2 := SlipPermitH2.slip_combine (frameAt word) hW.packet.periods η a b c
  subst hc' hi'
  linarith

theorem vFirst_ne_vLast {word : Word} :
    FLatticePaper.Induction.vFirst ≠ (frameAt word).vLast := by
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := (frameAt word).child_facts
  intro e
  have e2 := congrArg Prod.snd e
  simp [FLatticePaper.Induction.vFirst, ChildFrame.vLast] at e2
  omega

/-- The free V permit for sign +1 at a free V white `c'` with `i' = c' + prescribedV 1 c'`. -/
theorem freeV_permit_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongEstimates word)
    (hSE : StrongEstimates (conjWord word))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    {c' : Site} (hc' : c' ∈ (frameAt word).freeV) :
    (frameAt word).slip (standardField word) 1 (c' + (frameAt word).prescribedV 1 c') ≤
      (frameAt word).slip (standardField word) 1 c' := by
  by_cases hvl : c' = (frameAt word).vLast
  · subst hvl
    rw [BothFreeGrades.prescribedV_vLast (frameAt word) 1 (vFirst_ne_vLast (word := word))]
    have k := SlipPermitVend.slip_permit_Vend hW
    unfold slipPermits slipIncrement at k
    dsimp only at k
    unfold ChildFrame.slip
    simp only [one_smul] at k ⊢
    linarith
  · exact CanonicalPermit.slip_permit_freeV_canonical h hW hSE G hc' hvl

/-- The sign +1 `permitted` field. Named inputs: `OddBlackNoRise` of the word's shifted field, `ForcedExists` (the forced inputs at the
nonfree whites), and the aux rank `R` (`hstrict`). -/
theorem permitted_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongEstimates word)
    (hSE : StrongEstimates (conjWord word))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hOdd : OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hex : ForcedExists (frameAt word) (standardField word))
    {R : Site → ℤ} (hstrict : ∀ c i, auxRetained (frameAt word) (standardField word) c i → R i < R c) :
    ∀ c i, freePolicy (frameAt word) (standardField word) 1 c i →
      slipPermits (standardField word) (fun z => standardField word (z + (1 : ℤ) • (frameAt word).shortShift)) c i := by
  intro c i hci
  rw [slipPermits_iff_slip]
  unfold freePolicy at hci
  have hn3 := child_num_ge_three h
  rcases hci with ⟨hl, hE⟩ | ⟨hl, ⟨hcl, hp⟩ | ⟨hn, hs⟩⟩
  · -- black edge
    have key := black_permit_plus (F := standardField word) (σ := (frameAt word).shortShift)
      (evenSite_shortShift (frameAt word)) hW.packet.binary hW.F1_unitSlip hW.F1_noSlipSaddle hOdd hl hE
    unfold slipPermits slipIncrement at key
    dsimp only at key
    unfold ChildFrame.slip
    simp only [one_smul]
    linarith
  · -- free white: FreePresc
    obtain ⟨t, ht, hcase⟩ := hp
    rcases hcase with ⟨hH, hi⟩ | ⟨hV, hi⟩
    · exact SlipPermitH2.slip_permit_H (frameAt word) hW.packet.periods hW.packet.strips hn3 (Or.inl rfl) ht hH hi
    · have hpv : (frameAt word).slip (standardField word) 1 ((c + t) + (frameAt word).prescribedV 1 (c + t)) ≤
          (frameAt word).slip (standardField word) 1 (c + t) := freeV_permit_plus h hW hSE G hV
      exact slip_le_of_translate hW 1 ht rfl (by rw [hi]; abel) hpv
  · -- nonfree white: the forced edge
    rw [hs]
    have hf := forcedSel_spec (hex c hn hl)
    have key := forced_permitted (frameAt word) (evenSite_shortShift (frameAt word)) hW.packet.binary hW.F1_unitSlip
      hstrict hn hl hf
    unfold slipPermits slipIncrement at key
    dsimp only at key
    unfold ChildFrame.slip
    simp only [one_smul]
    linarith

/-- The sign −1 `permitted` field. Named inputs: `OddBlackNoRise`, `ForcedExists`, and the sign −1 forced permit `hforced` (the
forced edges of the sign −1 aux graph). -/
theorem permitted_minus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongEstimates word)
    (hSE : StrongEstimates (conjWord word))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hOdd : OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hex : ForcedExists (frameAt word) (standardField word))
    (hforced : ∀ c o, ¬ freeClosure (frameAt word) c → laplacian (standardField word) c = 0 →
      ForcedEdge (standardField word) (fun _ _ => False) c o →
      slipPermits (standardField word) (fun z => standardField word (z + (-1 : ℤ) • (frameAt word).shortShift)) c o) :
    ∀ c i, freePolicy (frameAt word) (standardField word) (-1) c i →
      slipPermits (standardField word) (fun z => standardField word (z + (-1 : ℤ) • (frameAt word).shortShift)) c i := by
  intro c i hci
  rw [slipPermits_iff_slip]
  unfold freePolicy at hci
  have hn3 := child_num_ge_three h
  rcases hci with ⟨hl, hE⟩ | ⟨hl, ⟨hcl, hp⟩ | ⟨hn, hs⟩⟩
  · -- black edge
    have key := black_permit_neg (F := standardField word) (σ := (frameAt word).shortShift)
      (evenSite_shortShift (frameAt word)) hW.packet.binary hW.F1_unitSlip hW.F1_noSlipSaddle hOdd
      (CanonicalPermit.standardField_reflect hW) hl hE
    unfold slipPermits slipIncrement at key
    dsimp only at key
    unfold ChildFrame.slip
    simp only [neg_one_smul] at key ⊢
    linarith
  · -- free white: FreePresc with sign −1
    obtain ⟨t, ht, hcase⟩ := hp
    rcases hcase with ⟨hH, hi⟩ | ⟨hV, hi⟩
    · exact SlipPermitH2.slip_permit_H (frameAt word) hW.packet.periods hW.packet.strips hn3 (Or.inr rfl) ht hH hi
    · have hpv : (frameAt word).slip (standardField word) (-1) ((c + t) + (frameAt word).prescribedV (-1) (c + t)) ≤
          (frameAt word).slip (standardField word) (-1) (c + t) :=
        SlipMinusPermit.slip_permit_freeV_minus h hW hSE G hV
      exact slip_le_of_translate hW (-1) ht rfl (by rw [hi]; abel) hpv
  · -- nonfree white: the sign −1 forced permit (named)
    rw [hs]
    have hf := forcedSel_spec (hex c hn hl)
    have key := hforced c (forcedSel (standardField word) c) hn hl hf
    rw [slipPermits_iff_slip] at key
    exact key

end FLatticePaper.FreePermitted
