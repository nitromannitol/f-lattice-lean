import FLatticePaper.Plane.Induction.CollarCReflect
import FLatticePaper.Plane.Induction.CollarSquare
import FLatticePaper.Plane.Induction.TieChainStep

/-! # The collar `hsq` at a tie (`Ψ c = 0`), from the reflected parent square

`hsq_C_collar` assumes `Ψ c < 0`. At a white tie `Ψ c = 0` the reflected centre `r = K − c` has `Ψ r = 0` and white, so its three
inputs are ties (`W1TieInputs.inputs_tie_of_mwhite`), and the `A`-chains of the reflected square stay on ties (`psi_mono`). The one
premise that does not come from the sheets is the tie agreement `hagree`: at a tie the `A` and `C` policies retain the same arrows
(the common arrow of a tie; Q15). With it, `sheetOut` at the tie is the `C` pointer, and the reflected `A`-chains are `A`-chains at `c`. -/

namespace FLatticePaper.CollarTie

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1 FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1SheetSquare
open FLatticePaper.W1NonfreeOut FLatticePaper.W1NonfreeSheet FLatticePaper.W1NonfreeHsq FLatticePaper.W1Step
open FLatticePaper.W1Pointers FLatticePaper.W1NonfreeSquare FLatticePaper.W1CollarFrame
open FLatticePaper.W1NonfreeHsqNonneg FLatticePaper.W1MReflect FLatticePaper.W1NonfreeHsqC
open FLatticePaper.CollarSquare FLatticePaper.CollarTop FLatticePaper.CollarCReflect

/-- A pointer depends on the relation only through its decision at `incomingNeg c`. -/
theorem pointerOf_congr_at (Q Q' : Site → Site → Prop) (c : Site) (h : ∀ y, Q c y ↔ Q' c y) :
    pointerOf Q c = pointerOf Q' c := by
  unfold pointerOf
  by_cases hn : Q c (incomingNeg c)
  · have hn' := (h _).mp hn
    simp [hn, hn']
  · have hn' : ¬ Q' c (incomingNeg c) := fun h' => hn ((h _).mpr h')
    simp [hn, hn']

/-- At a tie the sheet output is the `C` pointer, given the tie agreement at that centre. -/
theorem sheetOut_tie_eq {word : Word} {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps) {c : Site}
    (h0 : sheetPsi word c = 0)
    (hag : ∀ y, sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift c y ↔
      sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift (frameAt word).centre c y) :
    sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c =
      pointerOf (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
        (frameAt word).centre) c := by
  unfold sheetOut
  rw [if_pos (le_of_eq h0.symm)]
  exact pointerOf_congr_at _ _ c hag

/-- `Ψ` does not decrease along an `A`-chain. -/
theorem psi_mono_chain {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {a b : Site} (h : Relation.TransGen (sheetPolicyA P (frameAt word).sheetShift) a b) :
    sheetPsi word a ≤ sheetPsi word b := by
  induction h with
  | single h1 => exact psi_mono hw hSE P h1
  | tail _ h2 ih => exact le_trans ih (psi_mono hw hSE P h2)

/-- **Reflection of an `A`-chain between tie sites.** If `x` and `y` are ties, an `A`-chain from `x` to `y` reflects through the centre to
an `A`-chain from `K − x` to `K − y` (each step is at a tie, so the tie agreement applies). -/
theorem transGen_reflect_tie {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hagreeM : ∀ x, sheetPsi word x = 0 → laplacian (MW word) x = 0 → ∀ y,
      sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift x y ↔
        sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift (frameAt word).centre x y)
    (hEdgeS : ∀ c i, sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift c i →
      i = incomingNeg c ∨ i = incomingPos c)
    {x y : Site}
    (hxy : Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift) x y)
    (hx : sheetPsi word x = 0) (hy : sheetPsi word y = 0) :
    Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift)
      ((frameAt word).centre - x) ((frameAt word).centre - y) := by
  revert hy
  induction hxy with
  | single h1 =>
    intro hy
    exact Relation.TransGen.single (FLatticePaper.TieChainStep.tie_step_C hw hSE P.toOldPolicyWitness.toOldPolicyData
      (FLatticePaper.Induction.sheetExchange_of_packet hw hSE.packet) (frameAt word).evenSite_centre hEdgeS hagreeM hx hy h1)
  | tail hab hbc ih =>
    intro hy
    rename_i b z
    have hb0 : sheetPsi word b = 0 := by
      have h1 := psi_mono_chain hw hSE P.toOldPolicyWitness.toOldPolicyData hab
      have h2 := psi_mono hw hSE P.toOldPolicyWitness.toOldPolicyData hbc
      omega
    exact Relation.TransGen.tail (ih hb0) (FLatticePaper.TieChainStep.tie_step_C hw hSE P.toOldPolicyWitness.toOldPolicyData
      (FLatticePaper.Induction.sheetExchange_of_packet hw hSE.packet) (frameAt word).evenSite_centre hEdgeS hagreeM hb0 hy hbc)

/-- **The collar `hsq` at a tie (`Ψ c = 0`, `c` white)**: the reflected parent square at `K − c` gives the square at `c`, with the tie
agreement `hagree` as the named premise (the common arrow of a white tie). -/
theorem hsq_C_collar_tie {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)))
    (hagreeM : ∀ x, sheetPsi word x = 0 → laplacian (MW word) x = 0 → ∀ y,
      sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift x y ↔
        sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift (frameAt word).centre x y)
    (hEdgeS : ∀ c i, sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift c i →
      i = incomingNeg c ∨ i = incomingPos c)
    {c : Site} (hcS : StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hc0 : sheetPsi word c = 0) (hwhite : laplacian (MW word) c = 0)
    {q0 q1 q2 o : Site} {qa qb : ℤ}
    (hpsq : PSquare (standardField (conjWord word)) P.retained
      (zTurn ((frameAt word).centre - c - (frameAt word).sheetShift)) q0 q1 q2 o qa qb)
    (hstrict0 : StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv q0))
    (hstrict1 : StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv q1))
    (hstrict2 : StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv q2)) :
    HsqAt word P c := by
  have hK : ((frameAt word).centre.1 + (frameAt word).centre.2) % 2 = 0 := (frameAt word).evenSite_centre
  have hF1 : sheetPsi word ((frameAt word).centre - c) = -sheetPsi word c := psi_reflect hw hSE c
  have hr0 : sheetPsi word ((frameAt word).centre - c) = 0 := by
    rw [hF1, hc0]
    simp
  have hfreeP : ∀ c' : Site, (frameAt word).sheetC (FqW word) c' = (frameAt word).sheetA (FqW word) c' →
      laplacian (MW word) c' = 0 → ¬ Nonfree (frameAt (conjWord word)) (zTurn (c' - (frameAt word).sheetShift)) →
      ParentSquare P.retained (zTurn (c' - (frameAt word).sheetShift)) := by
    intro c' hT hM' hnf'
    have h0 : 0 ≤ sheetPsi word c' := by
      unfold sheetPsi
      omega
    exact parentSquare_of_out (hfree c' h0 hM' hnf')
  obtain ⟨p0, p1, p2, o', a, b, ep0, ep1, ep2, eo', hcS', hq0, hq1, hq2, hcov, hne01, hne12, hne02, hin0, hnot0,
    hE1, hE2, hE3, hR0, hR1, hR2, hoin, hoout, hRo, hun, hL0, hL1, hL2⟩ :=
    sheet_of_psquare (frameAt word).evenSite_sheetShift ((frameAt word).centre - c) hpsq
  have hs0 : StrictInterior (frameAt word).child.num (frameAt word).child.den p0 := by
    rw [ep0]
    exact hstrict0
  have hs1 : StrictInterior (frameAt word).child.num (frameAt word).child.den p1 := by
    rw [ep1]
    exact hstrict1
  have hs2 : StrictInterior (frameAt word).child.num (frameAt word).child.den p2 := by
    rw [ep2]
    exact hstrict2
  -- the inputs of the reflected centre are ties (white reflected centre), so `Ψ p0 = 0`
  have hbinF : ∀ x, laplacian (FqW word) x = -1 ∨ laplacian (FqW word) x = 0 :=
    fun x => quarterTurnField_binary hSE.packet.binary x
  have hp0e : sheetPsi word p0 = 0 := by
    have hMr : laplacian (MW word) ((frameAt word).centre - c) = 0 :=
      (FLatticePaper.W1NonfreeHsqC.lap_MW_reflect hw hSE c).trans hwhite
    have hTr : (frameAt word).sheetC (FqW word) ((frameAt word).centre - c) =
        (frameAt word).sheetA (FqW word) ((frameAt word).centre - c) := by
      unfold sheetPsi at hr0
      omega
    have hi := FLatticePaper.W1TieInputs.inputs_tie_of_mwhite (frameAt word) (FqW word) hbinF _ hMr hTr p0 hin0
    unfold sheetPsi
    omega
  -- along the reflected `A`-chains the sites are ties (monotone between `Ψ p0 = 0` and `Ψ r = 0`)
  have hm01 := psi_mono hw hSE P.toOldPolicyWitness.toOldPolicyData (p := p0) (q := p1) hR0
  have hm12 := psi_mono hw hSE P.toOldPolicyWitness.toOldPolicyData (p := p1) (q := p2) hR1
  have hm2r := psi_mono hw hSE P.toOldPolicyWitness.toOldPolicyData (p := p2) (q := (frameAt word).centre - c) hR2
  have hp1e : sheetPsi word p1 = 0 := by omega
  have hp2e : sheetPsi word p2 = 0 := by omega
  have hp0 : 0 ≤ sheetPsi word p0 := by omega
  have hp1 : 0 ≤ sheetPsi word p1 := by omega
  have hp2 : 0 ≤ sheetPsi word p2 := by omega
  have hcC : c ∈ squareCorners ((frameAt word).centre.1 - a - 1) ((frameAt word).centre.2 - b - 1) :=
    (square_reflect (frameAt word).centre a b c).2 hcS'
  unfold HsqAt
  refine ⟨(frameAt word).centre.1 - a - 1, (frameAt word).centre.2 - b - 1, hcC, ?_, ?_, ?_, ?_⟩
  · intro c' hc'
    have hxA := (square_reflect (frameAt word).centre a b c').1 hc'
    have hS : StrictInterior (frameAt word).child.num (frameAt word).child.den ((frameAt word).centre - c') := by
      by_cases hcc : (frameAt word).centre - c' = (frameAt word).centre - c
      · rw [hcc]
        exact (strict_reflect_centre (frameAt word) c).mpr hcS
      · rcases hcov _ hxA hcc with e | e | e
        · rw [e]
          exact hs0
        · rw [e]
          exact hs1
        · rw [e]
          exact hs2
    exact (strict_reflect_centre (frameAt word) c').mp hS
  · have hsoC : sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c =
        (frameAt word).centre - o' := by
      rw [sheetOut_tie_eq P hc0 (hagreeM c hc0 hwhite)]
      have h := pointerOf_sheetC_reflect P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
        (frameAt word).centre hK ((frameAt word).centre - c) o' hoin hRo hun
      rw [sub_sub_cancel] at h
      exact h
    rw [hsoC]
    intro h
    have h' := (square_reflect (frameAt word).centre a b ((frameAt word).centre - o')).1 h
    rw [sub_sub_cancel] at h'
    exact hoout h'
  · intro x hx hne
    have hxS : (frameAt word).centre - x ∈ squareCorners a b := (square_reflect (frameAt word).centre a b x).1 hx
    have hne' : (frameAt word).centre - x ≠ (frameAt word).centre - c := fun e => hne (sub_right_inj.mp e)
    rcases hcov ((frameAt word).centre - x) hxS hne' with e | e | e
    · have hx' : x = (frameAt word).centre - p0 := by rw [← e, sub_sub_cancel]
      rw [hx']
      exact corner_C hw hSE P hs hW1 hfreeP hp0 hE1 hR0 hL0 hq1
    · have hx' : x = (frameAt word).centre - p1 := by rw [← e, sub_sub_cancel]
      rw [hx']
      exact corner_C hw hSE P hs hW1 hfreeP hp1 hE2 hR1 hL1 hq2
    · have hx' : x = (frameAt word).centre - p2 := by rw [← e, sub_sub_cancel]
      rw [hx']
      exact corner_C hw hSE P hs hW1 hfreeP hp2 hE3 hR2 hL2 hcS'
  · intro x hx hne _
    have hxS : (frameAt word).centre - x ∈ squareCorners a b := (square_reflect (frameAt word).centre a b x).1 hx
    have hne' : (frameAt word).centre - x ≠ (frameAt word).centre - c := fun e => hne (sub_right_inj.mp e)
    have hph : phasePolicy (sheetPsi word)
        (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift)
        (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift (frameAt word).centre) c =
        sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift := by
      unfold phasePolicy
      rw [if_pos (le_of_eq hc0.symm)]
    have T0 : Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift) p0
        ((frameAt word).centre - c) :=
      Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single hR0) hR1) hR2
    have T1 : Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift) p1
        ((frameAt word).centre - c) :=
      Relation.TransGen.tail (Relation.TransGen.single hR1) hR2
    have T2 : Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift) p2
        ((frameAt word).centre - c) :=
      Relation.TransGen.single hR2
    rcases hcov ((frameAt word).centre - x) hxS hne' with e | e | e
    · have hx' : x = (frameAt word).centre - p0 := by rw [← e, sub_sub_cancel]
      have T0' := transGen_reflect_tie hw hSE P hagreeM hEdgeS T0 hp0e hr0
      rw [sub_sub_cancel] at T0'
      rw [hx', hph]
      exact ⟨⟨fun _ => by rw [psi_reflect hw hSE p0]; omega, fun h => absurd hc0 h⟩, T0'⟩
    · have hx' : x = (frameAt word).centre - p1 := by rw [← e, sub_sub_cancel]
      have T1' := transGen_reflect_tie hw hSE P hagreeM hEdgeS T1 hp1e hr0
      rw [sub_sub_cancel] at T1'
      rw [hx', hph]
      exact ⟨⟨fun _ => by rw [psi_reflect hw hSE p1]; omega, fun h => absurd hc0 h⟩, T1'⟩
    · have hx' : x = (frameAt word).centre - p2 := by rw [← e, sub_sub_cancel]
      have T2' := transGen_reflect_tie hw hSE P hagreeM hEdgeS T2 hp2e hr0
      rw [sub_sub_cancel] at T2'
      rw [hx', hph]
      exact ⟨⟨fun _ => by rw [psi_reflect hw hSE p2]; omega, fun h => absurd hc0 h⟩, T2'⟩

end FLatticePaper.CollarTie

namespace FLatticePaper.CollarTie

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1 FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1SheetSquare
open FLatticePaper.W1NonfreeOut FLatticePaper.W1NonfreeSheet FLatticePaper.W1NonfreeHsq FLatticePaper.W1Step
open FLatticePaper.W1Pointers FLatticePaper.W1NonfreeSquare FLatticePaper.W1CollarFrame
open FLatticePaper.W1NonfreeHsqNonneg FLatticePaper.W1MReflect FLatticePaper.W1NonfreeHsqC
open FLatticePaper.CollarSquare FLatticePaper.CollarTop FLatticePaper.CollarCReflect


/-- **The collar `hsq` for `Ψ c ≤ 0`**: the case split on the sign of `Ψ c`. The strict case is `hsq_C_collar`; the tie case is
`hsq_C_collar_tie`, which needs the whiteness of the tie centre and the tie agreement `hagree`. -/
theorem hsq_C_collar_le {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)))
    (hagreeM : ∀ x, sheetPsi word x = 0 → laplacian (MW word) x = 0 → ∀ y,
      sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift x y ↔
        sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift (frameAt word).centre x y)
    (hEdgeS : ∀ c i, sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift c i →
      i = incomingNeg c ∨ i = incomingPos c)
    {c : Site} (hcS : StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hc0 : sheetPsi word c ≤ 0) (hwhite : sheetPsi word c = 0 → laplacian (MW word) c = 0)
    {q0 q1 q2 o : Site} {qa qb : ℤ}
    (hpsq : PSquare (standardField (conjWord word)) P.retained
      (zTurn ((frameAt word).centre - c - (frameAt word).sheetShift)) q0 q1 q2 o qa qb)
    (hstrict0 : StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv q0))
    (hstrict1 : StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv q1))
    (hstrict2 : StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv q2)) :
    HsqAt word P c := by
  rcases lt_or_eq_of_le hc0 with h | h
  · exact hsq_C_collar hw hSE P hs hW1 hfree hcS h hpsq hstrict0 hstrict1 hstrict2
  · exact hsq_C_collar_tie hw hSE P hs hW1 hfree hagreeM hEdgeS hcS h (hwhite h) hpsq hstrict0 hstrict1 hstrict2

end FLatticePaper.CollarTie
