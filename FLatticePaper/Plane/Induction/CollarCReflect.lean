import FLatticePaper.Plane.Induction.W1NonfreeHsqC
import FLatticePaper.Plane.Induction.CollarSquare
import FLatticePaper.Plane.Induction.FreeVReflect
import FLatticePaper.Plane.Induction.CollarTop

/-! # The collar `hsq` at `Ψ c < 0`, from the explicit parent square at the reflected centre

For a `C`-centre `c` on the collar (`Ψ c < 0`), the reflected centre `K − c` is again on the collar (`collar_reflect`), and its
parent square is explicit with strictly interior child corners (`PSquare`). `hsq_C_collar` reflects that `A`-square to the `C`-square at
`c`, as `hsq_C_offcollar` does; the only change is the corner strictness, which comes from the explicit `A`-corners (`hstrict0/1/2`)
instead of from the centre's being off the collar. -/

namespace FLatticePaper.CollarCReflect

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1 FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1SheetSquare
open FLatticePaper.W1NonfreeOut FLatticePaper.W1NonfreeSheet FLatticePaper.W1NonfreeHsq FLatticePaper.W1Step
open FLatticePaper.W1Pointers FLatticePaper.W1NonfreeSquare FLatticePaper.W1CollarFrame
open FLatticePaper.W1NonfreeHsqNonneg FLatticePaper.W1MReflect FLatticePaper.W1NonfreeHsqC
open FLatticePaper.CollarSquare FLatticePaper.CollarTop

/-- The centre is `(1,−1) + transverse + kernel`. -/
theorem centre_transverse_kernel (frame : ChildFrame) :
    frame.centre = (1, -1) + frame.child.modifiedDeck.transverse + frame.child.modifiedDeck.kernel := by
  rw [centre_eq, ChildFrame.child_modifiedDeck_transverse, ChildFrame.child_modifiedDeck_kernel]
  refine Prod.ext ?_ ?_
  · simp
    ring
  · simp
    ring

/-- **The collar is preserved by the centre reflection** (`K − ·`, with the four disjuncts of `CollarFrame` exchanged). -/
theorem collar_reflect {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) {c : Site}
    (hc : CollarFrame (frameAt word) c) : CollarFrame (frameAt word) ((frameAt word).centre - c) := by
  obtain ⟨v, h1, h2, hv⟩ := hc
  have hK := centre_transverse_kernel (frameAt word)
  refine ⟨(frameAt word).centre - v, ?_, ?_, ?_⟩
  · have e : ((frameAt word).centre - v).1 - ((frameAt word).centre - c).1 = c.1 - v.1 := by
      simp only [Prod.fst_sub]
      ring
    rw [e, abs_sub_comm]
    exact h1
  · have e : ((frameAt word).centre - v).2 - ((frameAt word).centre - c).2 = c.2 - v.2 := by
      simp only [Prod.snd_sub]
      ring
    rw [e, abs_sub_comm]
    exact h2
  · rcases hv with h | h | h | h
    · right
      right
      left
      have h' := freeH_reflect (frameAt word) h
      rw [sub_sub]
      exact h'
    · right
      right
      right
      have h' := FLatticePaper.FreeVReflect.freeV_reflect_word hw h
      have e : (frameAt word).centre - v - (frameAt word).child.modifiedDeck.kernel =
          (1, -1) + (frameAt word).child.modifiedDeck.transverse - v := by
        rw [hK]
        abel
      rw [e]
      exact h'
    · left
      have h' := freeH_reflect (frameAt word) h
      rw [sub_add_cancel] at h'
      exact h'
    · right
      left
      have h' := FLatticePaper.FreeVReflect.freeV_reflect_word hw h
      have e : (1, -1) + (frameAt word).child.modifiedDeck.transverse - (v - (frameAt word).child.modifiedDeck.kernel) =
          (frameAt word).centre - v := by
        rw [hK]
        abel
      rw [e] at h'
      exact h'

/-- **The collar `hsq` at a `C`-centre (`Ψ c < 0`)**: the reflected parent square `hpsq` at `K − c` (with strictly interior corners
`hstrict0/1/2`) gives the `C`-square at `c`. -/
theorem hsq_C_collar {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)))
    {c : Site} (hcS : StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hc0 : sheetPsi word c < 0)
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
  have hcs0 : 0 ≤ sheetPsi word ((frameAt word).centre - c) := by omega
  have hpos : 1 ≤ sheetPsi word ((frameAt word).centre - c) := by omega
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
  have hp0 : 0 ≤ sheetPsi word p0 :=
    psi_input_nonneg hw hSE (c := (frameAt word).centre - c) (j := p0) hin0 hpos
  have hp1 : 0 ≤ sheetPsi word p1 := by
    have := psi_mono hw hSE P.toOldPolicyWitness.toOldPolicyData (p := p0) (q := p1) hR0
    omega
  have hp2 : 0 ≤ sheetPsi word p2 := by
    have := psi_mono hw hSE P.toOldPolicyWitness.toOldPolicyData (p := p1) (q := p2) hR1
    omega
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
      rw [sheetOut_of_neg P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) hc0]
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
      have T0' : Relation.TransGen (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
          (frameAt word).centre) ((frameAt word).centre - p0) ((frameAt word).centre - ((frameAt word).centre - c)) :=
        transGen_lift_map (fun y => (frameAt word).centre - y)
          (fun u v huv => policyC_of_A P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
            (frameAt word).centre huv) T0
      rw [sub_sub_cancel] at T0'
      rw [hx', phasePolicy_of_neg hc0]
      exact ⟨phaseOK_neg hc0 (by rw [psi_reflect hw hSE p0]; omega), T0'⟩
    · have hx' : x = (frameAt word).centre - p1 := by rw [← e, sub_sub_cancel]
      have T1' : Relation.TransGen (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
          (frameAt word).centre) ((frameAt word).centre - p1) ((frameAt word).centre - ((frameAt word).centre - c)) :=
        transGen_lift_map (fun y => (frameAt word).centre - y)
          (fun u v huv => policyC_of_A P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
            (frameAt word).centre huv) T1
      rw [sub_sub_cancel] at T1'
      rw [hx', phasePolicy_of_neg hc0]
      exact ⟨phaseOK_neg hc0 (by rw [psi_reflect hw hSE p1]; omega), T1'⟩
    · have hx' : x = (frameAt word).centre - p2 := by rw [← e, sub_sub_cancel]
      have T2' : Relation.TransGen (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
          (frameAt word).centre) ((frameAt word).centre - p2) ((frameAt word).centre - ((frameAt word).centre - c)) :=
        transGen_lift_map (fun y => (frameAt word).centre - y)
          (fun u v huv => policyC_of_A P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
            (frameAt word).centre huv) T2
      rw [sub_sub_cancel] at T2'
      rw [hx', phasePolicy_of_neg hc0]
      exact ⟨phaseOK_neg hc0 (by rw [psi_reflect hw hSE p2]; omega), T2'⟩
