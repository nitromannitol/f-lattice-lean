import FLatticePaper.Plane.Induction.W1NonfreeHsqNonneg
import FLatticePaper.Plane.Induction.GenericSquare

/-! # The collar `HsqAt` from an explicit parent square with strict child corners (Q33 (3))

`PSquare G R z q0 q1 q2 o a b` is the body of `ParentSquareOut` with its witnesses explicit. `sheet_of_psquare` is the transport of
`sheet_squareOut_of_parent` with the sheet corners exposed as `lv + zTurnInv q_i`. `hsq_collar_of_psquare` gives the `HsqAt` at a strict
white centre `c` (with `Ψ c ≥ 0`) from such a square whose child corners `lv + zTurnInv q_i` are strictly interior: the sign, tie and phase
conditions are those of `square_nonneg` and `hsq_offcollar`; only the corner strictness is taken from the explicit square. -/

namespace FLatticePaper.CollarSquare

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1 FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1SheetSquare
open FLatticePaper.W1NonfreeOut FLatticePaper.W1NonfreeSheet FLatticePaper.W1NonfreeHsq FLatticePaper.W1Step
open FLatticePaper.W1Pointers FLatticePaper.W1NonfreeSquare FLatticePaper.W1CollarFrame
open FLatticePaper.W1NonfreeHsqNonneg

/-- The body of `ParentSquareOut` with its witnesses `q0 q1 q2 o a b` explicit. -/
def PSquare (G : Field) (R : Site → Site → Prop) (z q0 q1 q2 o : Site) (a b : ℤ) : Prop :=
  z ∈ squareCorners a b ∧ q0 ∈ squareCorners a b ∧ q1 ∈ squareCorners a b ∧ q2 ∈ squareCorners a b ∧
  (∀ c' ∈ squareCorners a b, c' ≠ z → c' = q0 ∨ c' = q1 ∨ c' = q2) ∧
  q0 ≠ q1 ∧ q1 ≠ q2 ∧ q0 ≠ q2 ∧ (q0 = incomingNeg z ∨ q0 = incomingPos z) ∧ ¬ R z q0 ∧
  Edge q1 q0 ∧ Edge q2 q1 ∧ Edge z q2 ∧ R q0 q1 ∧ R q1 q2 ∧ R q2 z ∧
  (o = incomingNeg z ∨ o = incomingPos z) ∧ o ∉ squareCorners a b ∧ R z o ∧
  (∀ j, R z j → j = o) ∧
  (laplacian G q0 = -1 ∨ (laplacian G q0 = 0 ∧ ∀ j, R q0 j → j = q1)) ∧
  (laplacian G q1 = -1 ∨ (laplacian G q1 = 0 ∧ ∀ j, R q1 j → j = q2)) ∧
  (laplacian G q2 = -1 ∨ (laplacian G q2 = 0 ∧ ∀ j, R q2 j → j = z))

-- The sheet transport with explicit corners (the proof of `sheet_squareOut_of_parent`, with the witnesses given).
set_option maxHeartbeats 1000000 in
theorem sheet_of_psquare {G : Field} {Q : Site → Site → Prop} {lv : Site} (hlv : EvenSite lv) (c : Site)
    {q0 q1 q2 o : Site} {qa qb : ℤ}
    (h : PSquare G Q (zTurn (c - lv)) q0 q1 q2 o qa qb) :
    ∃ p0 p1 p2 o' : Site, ∃ a' b' : ℤ,
      p0 = lv + zTurnInv q0 ∧ p1 = lv + zTurnInv q1 ∧ p2 = lv + zTurnInv q2 ∧ o' = lv + zTurnInv o ∧
      c ∈ squareCorners a' b' ∧ p0 ∈ squareCorners a' b' ∧ p1 ∈ squareCorners a' b' ∧ p2 ∈ squareCorners a' b' ∧
      (∀ c' ∈ squareCorners a' b', c' ≠ c → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
      p0 ≠ p1 ∧ p1 ≠ p2 ∧ p0 ≠ p2 ∧ (p0 = incomingNeg c ∨ p0 = incomingPos c) ∧
      ¬ sheetQ Q lv c p0 ∧ Edge p1 p0 ∧ Edge p2 p1 ∧ Edge c p2 ∧
      sheetQ Q lv p0 p1 ∧ sheetQ Q lv p1 p2 ∧ sheetQ Q lv p2 c ∧
      (o' = incomingNeg c ∨ o' = incomingPos c) ∧ o' ∉ squareCorners a' b' ∧ sheetQ Q lv c o' ∧
      (∀ j, sheetQ Q lv c j → j = o') ∧
      (laplacian G (zTurn (p0 - lv)) = -1 ∨
        (laplacian G (zTurn (p0 - lv)) = 0 ∧ ∀ j, sheetQ Q lv p0 j → j = p1)) ∧
      (laplacian G (zTurn (p1 - lv)) = -1 ∨
        (laplacian G (zTurn (p1 - lv)) = 0 ∧ ∀ j, sheetQ Q lv p1 j → j = p2)) ∧
      (laplacian G (zTurn (p2 - lv)) = -1 ∨
        (laplacian G (zTurn (p2 - lv)) = 0 ∧ ∀ j, sheetQ Q lv p2 j → j = c)) := by
  obtain ⟨hz, hq0, hq1, hq2, hcov, hne01, hne12, hne02, hin, hrej, hE1, hE2, hE3,
    hR0, hR1, hR2, ho, hout, hRo, hun, hL0, hL1, hL2⟩ := h
  have hp : ∀ q : Site, zTurn (lv + zTurnInv q - lv) = q := zTurn_sheet_point lv
  refine ⟨lv + zTurnInv q0, lv + zTurnInv q1, lv + zTurnInv q2, lv + zTurnInv o, lv.1 + qb + 1, lv.2 - qa - 1,
    rfl, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mem_square_parent lv c qa qb).2 hz
  · exact (mem_square_parent lv _ qa qb).2 (by rw [hp]; exact hq0)
  · exact (mem_square_parent lv _ qa qb).2 (by rw [hp]; exact hq1)
  · exact (mem_square_parent lv _ qa qb).2 (by rw [hp]; exact hq2)
  · intro c' hc' hne
    have h' := (mem_square_parent lv c' qa qb).1 hc'
    have hne' : zTurn (c' - lv) ≠ zTurn (c - lv) := fun e => hne (sub_left_inj.mp ((zTurn_eq_iff _ _).1 e))
    rcases hcov (zTurn (c' - lv)) h' hne' with e | e | e
    · left
      rw [← e, zTurnInv_zTurn]
      abel
    · right; left
      rw [← e, zTurnInv_zTurn]
      abel
    · right; right
      rw [← e, zTurnInv_zTurn]
      abel
  · intro e
    have h2 : zTurn ((lv + zTurnInv q0) - lv) = zTurn ((lv + zTurnInv q1) - lv) := by rw [e]
    rw [hp, hp] at h2
    exact hne01 h2
  · intro e
    have h2 : zTurn ((lv + zTurnInv q1) - lv) = zTurn ((lv + zTurnInv q2) - lv) := by rw [e]
    rw [hp, hp] at h2
    exact hne12 h2
  · intro e
    have h2 : zTurn ((lv + zTurnInv q0) - lv) = zTurn ((lv + zTurnInv q2) - lv) := by rw [e]
    rw [hp, hp] at h2
    exact hne02 h2
  · exact (input_zTurn_iff lv c _ hlv).2 (by rw [hp]; exact hin)
  · unfold sheetQ
    rw [hp]
    exact hrej
  · exact (edge_zTurn_iff lv _ _ hlv).2 (by rw [hp, hp]; exact hE1)
  · exact (edge_zTurn_iff lv _ _ hlv).2 (by rw [hp, hp]; exact hE2)
  · exact (edge_zTurn_iff lv _ _ hlv).2 (by rw [hp]; exact hE3)
  · unfold sheetQ
    rw [hp, hp]
    exact hR0
  · unfold sheetQ
    rw [hp, hp]
    exact hR1
  · unfold sheetQ
    rw [hp]
    exact hR2
  · exact (input_zTurn_iff lv c _ hlv).2 (by rw [hp]; exact ho)
  · intro hm
    have hm' := (mem_square_parent lv _ qa qb).1 hm
    rw [hp] at hm'
    exact hout hm'
  · unfold sheetQ
    rw [hp]
    exact hRo
  · intro j hj
    have hj' : Q (zTurn (c - lv)) (zTurn (j - lv)) := hj
    exact eq_sheet_of_zTurn lv j o (hun _ hj')
  · rw [hp]
    rcases hL0 with e | ⟨e, u⟩
    · exact Or.inl e
    · refine Or.inr ⟨e, fun j hj => ?_⟩
      have hj' : Q (zTurn (lv + zTurnInv q0 - lv)) (zTurn (j - lv)) := hj
      rw [hp] at hj'
      exact eq_sheet_of_zTurn lv j q1 (u _ hj')
  · rw [hp]
    rcases hL1 with e | ⟨e, u⟩
    · exact Or.inl e
    · refine Or.inr ⟨e, fun j hj => ?_⟩
      have hj' : Q (zTurn (lv + zTurnInv q1 - lv)) (zTurn (j - lv)) := hj
      rw [hp] at hj'
      exact eq_sheet_of_zTurn lv j q2 (u _ hj')
  · rw [hp]
    rcases hL2 with e | ⟨e, u⟩
    · exact Or.inl e
    · refine Or.inr ⟨e, fun j hj => ?_⟩
      have hj' : Q (zTurn (lv + zTurnInv q2 - lv)) (zTurn (j - lv)) := hj
      rw [hp] at hj'
      have hcz : c = lv + zTurnInv (zTurn (c - lv)) := by
        rw [zTurnInv_zTurn]
        abel
      rw [hcz]
      exact eq_sheet_of_zTurn lv j _ (u _ hj')



/-- **The collar `HsqAt` from an explicit parent square with strict child corners** (Q33 (3)). The sign, tie and phase conditions are
those of `square_nonneg` and `hsq_offcollar`. -/
theorem hsq_collar_of_psquare {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {c : Site} (hcS : StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hc0 : 0 ≤ sheetPsi word c) (hM : laplacian (MW word) c = 0)
    {q0 q1 q2 o : Site} {qa qb : ℤ}
    (hpsq : PSquare (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)) q0 q1 q2 o qa qb)
    (hstrict0 : StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv q0))
    (hstrict1 : StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv q1))
    (hstrict2 : StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv q2)) :
    HsqAt word P c := by
  have hlv := (frameAt word).evenSite_sheetShift
  obtain ⟨p0, p1, p2, o', a', b', ep0, ep1, ep2, eo', hc_, hq0, hq1, hq2, hcov, hne01, hne12, hne02, hin0, hnot0,
    hE1, hE2, hE3, hR0, hR1, hR2, hoin, hoout, hRo, hun, hL0, hL1, hL2⟩ := sheet_of_psquare hlv c hpsq
  have hs0 : StrictInterior (frameAt word).child.num (frameAt word).child.den p0 := by rw [ep0]; exact hstrict0
  have hs1 : StrictInterior (frameAt word).child.num (frameAt word).child.den p1 := by rw [ep1]; exact hstrict1
  have hs2 : StrictInterior (frameAt word).child.num (frameAt word).child.den p2 := by rw [ep2]; exact hstrict2
  have hbinF : ∀ x, laplacian (FqW word) x = -1 ∨ laplacian (FqW word) x = 0 :=
    fun x => quarterTurnField_binary hSE.packet.binary x
  have hPd := P.toOldPolicyWitness.toOldPolicyData
  have hTie : sheetPsi word c = 0 → sheetPsi word p0 = 0 := by
    intro h0
    have hT : (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c := by
      unfold sheetPsi at h0
      omega
    have hi := FLatticePaper.W1TieInputs.inputs_tie_of_mwhite (frameAt word) (FqW word) hbinF c hM hT p0 hin0
    unfold sheetPsi
    omega
  have hp0 : 0 ≤ sheetPsi word p0 := by
    by_cases h1 : 1 ≤ sheetPsi word c
    · exact psi_input_nonneg hw hSE (c := c) (j := p0) hin0 h1
    · have h0 : sheetPsi word c = 0 := by omega
      have := hTie h0
      omega
  have hup1 : sheetPsi word p0 ≤ sheetPsi word p1 :=
    psi_mono hw hSE P.toOldPolicyWitness.toOldPolicyData (p := p0) (q := p1) hR0
  have hup2 : sheetPsi word p1 ≤ sheetPsi word p2 :=
    psi_mono hw hSE P.toOldPolicyWitness.toOldPolicyData (p := p1) (q := p2) hR1
  have hup3 : sheetPsi word p2 ≤ sheetPsi word c :=
    psi_mono hw hSE P.toOldPolicyWitness.toOldPolicyData (p := p2) (q := c) hR2
  have hp1 : 0 ≤ sheetPsi word p1 := by omega
  have hp2 : 0 ≤ sheetPsi word p2 := by omega
  have hz : sheetPsi word c = 0 → sheetPsi word p0 = 0 ∧ sheetPsi word p1 = 0 ∧ sheetPsi word p2 = 0 := by
    intro h0
    have := hTie h0
    omega
  have k0 := corner_nonneg hw hSE P.toOldPolicyWitness.toOldPolicyData hE1 hR0 hL0 hp0
  have k1 := corner_nonneg hw hSE P.toOldPolicyWitness.toOldPolicyData hE2 hR1 hL1 hp1
  have k2 := corner_nonneg hw hSE P.toOldPolicyWitness.toOldPolicyData hE3 hR2 hL2 hp2
  have hpo := pointer_of_unique (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift) c o' hoin hRo hun
  have hpos : 0 ≤ sheetPsi word p0 ∧ 0 ≤ sheetPsi word p1 ∧ 0 ≤ sheetPsi word p2 := ⟨hp0, hp1, hp2⟩
  have t0 : Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift) p0 c :=
    Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single hR0) hR1) hR2
  have t1 : Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift) p1 c :=
    Relation.TransGen.tail (Relation.TransGen.single hR1) hR2
  have t2 : Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift) p2 c :=
    Relation.TransGen.single hR2
  unfold HsqAt
  refine ⟨a', b', hc_, ?_, ?_, ?_, ?_⟩
  · intro c' hc'
    by_cases hcc : c' = c
    · rw [hcc]
      exact hcS
    · rcases hcov c' hc' hcc with e | e | e
      · rw [e]
        exact hs0
      · rw [e]
        exact hs1
      · rw [e]
        exact hs2
  · rw [sheetOut_of_nonneg P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) hc0, hpo]
    exact hoout
  · intro c' hc' hne
    rcases hcov c' hc' hne with e | e | e
    · rw [e, sheetOut_of_nonneg P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) hpos.1]
      rcases k0 with h | ⟨h, hpt⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by rw [hpt]; exact hq1⟩
    · rw [e, sheetOut_of_nonneg P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) hpos.2.1]
      rcases k1 with h | ⟨h, hpt⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by rw [hpt]; exact hq2⟩
    · rw [e, sheetOut_of_nonneg P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) hpos.2.2]
      rcases k2 with h | ⟨h, hpt⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by rw [hpt]; exact hc_⟩
  · intro c' hc' hne _
    rcases hcov c' hc' hne with e | e | e
    · rw [e, phasePolicy_of_nonneg hc0]
      exact ⟨phaseOK_of hc0 hpos.1 (fun h0 => (hz h0).1), t0⟩
    · rw [e, phasePolicy_of_nonneg hc0]
      exact ⟨phaseOK_of hc0 hpos.2.1 (fun h0 => (hz h0).2.1), t1⟩
    · rw [e, phasePolicy_of_nonneg hc0]
      exact ⟨phaseOK_of hc0 hpos.2.2 (fun h0 => (hz h0).2.2), t2⟩

end FLatticePaper.CollarSquare
