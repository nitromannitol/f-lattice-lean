import FLatticePaper.Plane.Induction.WestException
import FLatticePaper.Plane.Induction.W1Bridge
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.SquareClauses
import FLatticePaper.Plane.Induction.ComparisonEmpty

/-! # The forced input of a strict white is the sheet pointer

At a strict-interior white `c` of the word's standard field, the unseeded forced input `o` equals the sheet pointer `sheetOut P c`.
Proof: `sheetOut_forcedIn` puts the sheet pointer forced in the sheet minimum `MW` (from the square data `hsq`); `agree_MW_standard`
transports that to the standard field at `c` and its inputs (`forcedEdgeIn_congr`), and `forced_sound` with the Q1 satisfiability selection
says that every forced input equals that selection, so `o` and the sheet pointer coincide. -/

namespace FLatticePaper.ForcedSheet

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1
open FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1Step FLatticePaper.W1ForcedPhase FLatticePaper.FreePolicy
open FLatticePaper.FreeClosure

/-- **The forced input is the sheet pointer.** -/
theorem forced_eq_sheetOut {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hsq : ∀ c : Site, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → ∃ a b : ℤ,
        c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, StrictInterior (frameAt word).child.num (frameAt word).child.den c') ∧
        sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c ∉ squareCorners a b ∧
        (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian (MW word) c' = -1 ∨
          (laplacian (MW word) c' = 0 ∧
            sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c' ∈ squareCorners a b)) ∧
        (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian (MW word) c' = 0 →
          PhaseOK (sheetPsi word) c c' ∧
            Relation.TransGen (phasePolicy (sheetPsi word)
              (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift)
              (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift (frameAt word).centre) c) c' c))
    (hsat : HasSatSelection (standardField word)) {c o : Site}
    (hcS : StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : laplacian (standardField word) c = 0) (hf : ForcedEdge (standardField word) (fun _ _ => False) c o) :
    o = sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c := by
  have ag := WestException.agree_MW_standard h hSE c hcS
  have hMW : laplacian (MW word) c = 0 := by
    rw [← W1Bridge.laplacian_congr ag.1.symm ag.2.1.symm ag.2.2.symm]
    exact hw
  have hI := WestException.sheetOut_forcedIn P hsq c hcS hMW
  have hS := W1Bridge.forcedEdgeIn_congr (fun c' hc' => WestException.agree_MW_standard h hSE c' hc') hI
  have hFE := FLatticePaper.W1.forcedEdgeIn_forced hS
  obtain ⟨sel, hsel, hsq'⟩ := hsat
  have e1 := SquareClauses.forced_sound (standardField word) (fun _ _ => False) sel hsel (fun _ _ hh => hh.elim) hsq' c o hf
  have e2 := SquareClauses.forced_sound (standardField word) (fun _ _ => False) sel hsel (fun _ _ hh => hh.elim) hsq' c _ hFE
  exact e1.symm.trans e2

end FLatticePaper.ForcedSheet
