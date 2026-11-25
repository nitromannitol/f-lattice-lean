import FLatticePaper.Plane.Induction.AuxRankSign
import FLatticePaper.Plane.Induction.FreePermitted

/-! The `permitted` field of the free-edge policy of a sign `η ∈ {±1}`, with the aux rank of that sign as the one named input.

The forced inputs come from `forcedExists_of` (from `W1Forced` and the packet), so `ForcedExists` is not a separate input. The black
edges use `OddBlackNoRise`; the free H and V edges use the proved permits (`FreePermitted.slip_le_of_translate` and the sign-η V permit). -/

namespace FLatticePaper.FreePermittedS

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreePolicy FLatticePaper.AuxRankSign FLatticePaper.FreeClosure
  FLatticePaper.AuxRank
  FLatticePaper.SquareClauses

/-- The sign-η free V permit at a free V white `c'`: `slip η (c' + prescribedV η c') ≤ slip η c'`. -/
theorem freeV_permit_S {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongEstimates word)
    (hSE : StrongEstimates (conjWord word))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    {η : ℤ} (hη : η = 1 ∨ η = -1) {c' : Site} (hc' : c' ∈ (frameAt word).freeV) :
    (frameAt word).slip (standardField word) η (c' + (frameAt word).prescribedV η c') ≤
      (frameAt word).slip (standardField word) η c' := by
  rcases hη with rfl | rfl
  · exact FreePermitted.freeV_permit_plus h hW hSE G hc'
  · exact SlipMinusPermit.slip_permit_freeV_minus h hW hSE G hc'

/-- **The `permitted` field of sign η.** Named inputs: `OddBlackNoRise` of the word's shifted field, `W1Forced` (the forced inputs
come from `forcedExists_of`), and the aux rank `R` of sign η (`hstrict`). -/
theorem permitted_S {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongEstimates word)
    (hSE : StrongEstimates (conjWord word))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hOdd : OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {η : ℤ} (hη : η = 1 ∨ η = -1) {R : Site → ℤ}
    (hstrict : ∀ c i, auxS (frameAt word) (standardField word) η c i → R i < R c) :
    ∀ c i, freePolicy (frameAt word) (standardField word) η c i →
      slipPermits (standardField word) (fun z => standardField word (z + η • (frameAt word).shortShift)) c i := by
  intro c i hci
  rw [FreePermitted.slipPermits_iff_slip]
  have hex := forcedExists_of (frameAt word) hW.packet hW1
  have hI := CanonicalPermit.standardField_reflect hW
  have hn3 := child_num_ge_three h
  have hσ := evenSite_shortShift (frameAt word)
  unfold freePolicy at hci
  rcases hci with ⟨hl, hE⟩ | ⟨hl, ⟨hcl, hp⟩ | ⟨hn, hs⟩⟩
  · -- black edge
    rcases hη with rfl | rfl
    · have key := black_permit_plus (F := standardField word) (σ := (frameAt word).shortShift) hσ hW.packet.binary
        hW.F1_unitSlip hW.F1_noSlipSaddle hOdd hl hE
      unfold slipPermits slipIncrement at key
      dsimp only at key
      unfold ChildFrame.slip
      simp only [one_smul]
      linarith
    · have key := black_permit_neg (F := standardField word) (σ := (frameAt word).shortShift) hσ hW.packet.binary
        hW.F1_unitSlip hW.F1_noSlipSaddle hOdd hI hl hE
      unfold slipPermits slipIncrement at key
      dsimp only at key
      unfold ChildFrame.slip
      simp only [neg_one_smul] at key ⊢
      linarith
  · -- free white: FreePresc of sign η
    obtain ⟨t, ht, hcase⟩ := hp
    rcases hcase with ⟨hH, hi⟩ | ⟨hV, hi⟩
    · exact SlipPermitH2.slip_permit_H (frameAt word) hW.packet.periods hW.packet.strips hn3 hη ht hH hi
    · exact FreePermitted.slip_le_of_translate hW η ht rfl (by rw [hi]; abel) (freeV_permit_S h hW hSE G hη hV)
  · -- nonfree white: the forced edge of sign η
    rw [hs]
    have key := forced_permitted_S η hη hσ hW.packet.binary hW.F1_unitSlip hI hstrict hn hl
      (forcedSel_spec (hex c hn hl))
    exact (FreePermitted.slipPermits_iff_slip η c (forcedSel (standardField word) c)).mp key

end FLatticePaper.FreePermittedS
