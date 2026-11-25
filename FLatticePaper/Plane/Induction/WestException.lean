import FLatticePaper.Plane.Induction.W1Step
import FLatticePaper.Plane.Induction.W1Phase
import FLatticePaper.Plane.Induction.W1Bridge
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.CornerPositive
import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.ComparisonEmpty
import FLatticePaper.Plane.Induction.SheetPieces

/-! `hwest`: the prescribed west input at the exceptional vertex `v = V_p + I` when `ε = 1`.

The forced literal of the W1 step at a strict-interior white is the A-pointer of the parent policy when `Ψ ≥ 0`
(`W1Step.sheetOut`, `W1Phase.forcing_of_sheet`). At `v`, `Ψ(v) ≥ 1` (`CornerPositive.sheetDiffW_corner_ge_one`), so the forced
literal is `pointerOf (sheetPolicyA P 0) v`. It is `incomingNeg v` (west) when the parent policy retains west at `v`, which is the
named premise `hSouth` (the conjugate's retained input at `zTurn v = H'_0 − U'` is the south step `(0,−1)` of its sign `+1`
prescription; this transport needs the deck equivariance of the retained policy, which the canonical structure does not state).
The forced literal is transferred from the sheet minimum to `standardField word` (the `W1Bridge` congruence on the closed polygon),
and `forced_sound` gives its uniqueness from a satisfying selection. The named premises are `hSouth`, `hNF` (`v` is not free),
and `hSI` (`v` is strictly interior, a numerical check). -/

namespace FLatticePaper.WestException

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1
open FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1Step FLatticePaper.W1ForcedPhase FLatticePaper.FreePolicy
open FLatticePaper.FreeClosure

/-- The forced literal of the W1 step at every strict-interior white is the sheet arrow (`forcing_of_sheet`, the proof of
`W1Step.W1Forced_step`), as a derivation in the strict interior. -/
theorem sheetOut_forcedIn {word : Word} {seed : Site → Site → Prop}
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
              (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift (frameAt word).centre) c) c' c)) :
    ∀ c : Site, StrictInterior (frameAt word).child.num (frameAt word).child.den c → laplacian (MW word) c = 0 →
      ForcedEdgeIn (MW word) (StrictInterior (frameAt word).child.num (frameAt word).child.den) (fun _ _ => False) c
        (sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c) := by
  have hsq' : ∀ c : Site, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → ∃ a b : ℤ,
        c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, StrictInterior (frameAt word).child.num (frameAt word).child.den c') ∧
        sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c ∉ squareCorners a b ∧
        (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian (MW word) c' = -1 ∨
          (laplacian (MW word) c' = 0 ∧
            sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c' ∈ squareCorners a b ∧
            (sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c' = incomingNeg c' ∨
              sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c' = incomingPos c'))) ∧
        (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian (MW word) c' = 0 →
          PhaseOK (sheetPsi word) c c' ∧
            Relation.TransGen (phasePolicy (sheetPsi word)
              (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift)
              (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift (frameAt word).centre) c) c' c) := by
    intro c hc hw
    obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := hsq c hc hw
    refine ⟨a, b, h1, h2, h3, fun c' hc' hne => ?_, h5⟩
    rcases h4 c' hc' hne with hb | ⟨hw0, hpin⟩
    · exact Or.inl hb
    · exact Or.inr ⟨hw0, hpin, sheetOut_input P _ _ _ c'⟩
  exact fun z hz hw =>
    forcing_of_sheet P (frameAt word).sheetShift (frameAt word).centre (frameAt word).child.num (frameAt word).child.den
      (MW word) (sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word)) (sheetPsi word)
      (strictInterior_child_finite (frameAt word))
      (fun c _ _ => sheetOut_input P _ _ _ c) hsq' z hz hw

/-- **The forced west input at the exceptional vertex, for `MW`**: under `ε = 1`, `Ψ(v) ≥ 1` and the parent policy retains the south
image (`hSouth`), the strict-interior derivation forces the west input. -/
theorem west_forcedIn_MW {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
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
    (heps : (frameAt word).eps = 1)
    (hSI : StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1))
    (hw : laplacian (MW word) ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1) = 0)
    (hSouth : sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
      ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)
      (incomingNeg ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1))) :
    ForcedEdgeIn (MW word) (StrictInterior (frameAt word).child.num (frameAt word).child.den) (fun _ _ => False)
      ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)
      (incomingNeg ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)) := by
  set v := ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1) with hv
  have hΨ : 0 ≤ sheetPsi word v := by
    have h1 := sheetDiffW_corner_ge_one h hSE heps
    exact le_trans zero_le_one h1
  have hall := sheetOut_forcedIn P hsq v hSI hw
  have hout : sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) v = incomingNeg v := by
    unfold sheetOut
    rw [if_pos hΨ]
    unfold W1Pointers.pointerOf
    classical
    rw [if_pos hSouth]
  rw [hout] at hall
  exact hall

/-- The sheet minimum and the standard field agree on the closed polygon, so the strict-interior laplacians of `MW` and `standardField`
(and their inputs) agree. -/
theorem agree_MW_standard {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    ∀ c, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      MW word c = standardField word c ∧ MW word (incomingNeg c) = standardField word (incomingNeg c) ∧
        MW word (incomingPos c) = standardField word (incomingPos c) := by
  have hn : 1 ≤ (frameAt word).child.num := by have := (frameAt word).child_facts.1; omega
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by
    have := (frameAt word).child_facts.2.2.1; omega
  intro c hc
  have hcP : c ∈ (frameAt word).closedPolygon := by
    rw [FLatticePaper.W1.closedPolygon_eq_closedRect]
    exact FLatticePaper.W1.strictInterior_closedRect hn hnd c hc
  have hi1 : incomingNeg c ∈ (frameAt word).closedPolygon :=
    FLatticePaper.W1Exit.rectInputs (frameAt word) c ((FLatticePaper.W1Exit.openRect_iff (frameAt word) c).2 hc) _ (Or.inl rfl)
  have hi2 : incomingPos c ∈ (frameAt word).closedPolygon :=
    FLatticePaper.W1Exit.rectInputs (frameAt word) c ((FLatticePaper.W1Exit.openRect_iff (frameAt word) c).2 hc) _ (Or.inr rfl)
  exact ⟨(standardField_eq_sheetMin_of_strong h hSE hcP).symm, (standardField_eq_sheetMin_of_strong h hSE hi1).symm,
    (standardField_eq_sheetMin_of_strong h hSE hi2).symm⟩

/-- **`hwest` (forced form)**: at a white exceptional vertex `v` with `ε = 1`, `v` not free, and a satisfying selection, the west input
is the forced output of the standard field, so the free policy of the word retains it. -/
theorem hwest_freePolicy {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hWord : StrongEstimates word)
    {seed : Site → Site → Prop}
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
    (heps : (frameAt word).eps = 1)
    (hSI : StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1))
    (hSouth : sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
      ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)
      (incomingNeg ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)))
    (hNF : ¬ freeClosure (frameAt word) ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1))
    (hsat : HasSatSelection (standardField word)) (η : ℤ) :
    freePolicy (frameAt word) (standardField word) η
      ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)
      (incomingNeg ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)) := by
  set v := ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1) with hv
  have hag := agree_MW_standard h hSE v hSI
  rcases hWord.packet.binary v with hb | hw0
  · exact Or.inl ⟨hb, Or.inl rfl⟩
  · have hwMW : laplacian (MW word) v = 0 := by
      rw [FLatticePaper.W1Bridge.laplacian_congr hag.1 hag.2.1 hag.2.2]
      exact hw0
    have hMW := west_forcedIn_MW h hSE P hsq heps hSI hwMW hSouth
    have hcongr := FLatticePaper.W1Bridge.forcedEdgeIn_congr
      (fun c hc => agree_MW_standard h hSE c hc) hMW
    have hFE := forcedEdgeIn_forced hcongr
    obtain ⟨sel, hsel, hsq'⟩ := hsat
    have hfs := forcedSel_spec (F := standardField word) (c := v) ⟨incomingNeg v, hFE⟩
    have e1 := forced_sound (standardField word) (fun _ _ => False) sel hsel (fun c i hh => False.elim hh) hsq' v
      (incomingNeg v) hFE
    have e2 := forced_sound (standardField word) (fun _ _ => False) sel hsel (fun c i hh => False.elim hh) hsq' v
      (forcedSel (standardField word) v) hfs
    exact Or.inr ⟨hw0, Or.inr ⟨hNF, e1.symm.trans e2⟩⟩

end FLatticePaper.WestException
