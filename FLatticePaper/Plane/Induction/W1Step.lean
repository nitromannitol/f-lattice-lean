import FLatticePaper.Plane.Induction.W1Finite
import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.W1ForcedPhase

/-! # Task 89 (3): the W1 step at a word (`W1Forced_step`)

The sheet minimum `M = MW word = min(A, C)` of the word's frame, with `Ψ = C − A` (so `Ψ = 0` exactly on the ties). The child arrows of §5:
`A` on `Ψ ≥ 0` (where `M = A`), `C` on `Ψ < 0` (where `M = C`); at a tie `Ψ = 0` the arrow is the common arrow (`hagree_M_tie_of_inherited`
says `C` retains the `A`-pointer there). So `out c` is an input of `c` (`pointerOf` always is), and the phase is `ψ = Ψ`
(`phasePolicy`, `forcing_of_sheet`).

`W1Forced_step`: the strict-interior square data `hsq` of the sheet minimum (the named input) gives `W1Forced` of the word's child for `M`.
Finiteness of the strict interior is proved (`strictInterior_finite`). -/

namespace FLatticePaper.W1Step

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1
open FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1ForcedPhase

/-- The strict interior of the child of a frame is finite. -/
theorem strictInterior_child_finite (frame : ChildFrame) :
    {c : Site | StrictInterior frame.child.num frame.child.den c}.Finite := by
  have h1 := frame.child_facts.1
  have h2 := frame.child_facts.2.2.1
  exact FLatticePaper.W1Finite.strictInterior_finite _ _ (by omega) (by omega)

/-- The phase `Ψ = C − A` of the sheets: `0` exactly on the ties. -/
noncomputable def sheetPsi (word : Word) (c : Site) : ℤ :=
  (frameAt word).sheetC (FqW word) c - (frameAt word).sheetA (FqW word) c

/-- The child arrow of §5: `A` where `Ψ ≥ 0` (the common arrow on the ties), `C` where `Ψ < 0`. -/
noncomputable def sheetOut {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyRanked frame G seed η) (lv centre : Site) (psi : Site → ℤ) (c : Site) : Site :=
  if 0 ≤ psi c then
    FLatticePaper.W1Pointers.pointerOf (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c
  else FLatticePaper.W1Pointers.pointerOf (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData lv centre) c

/-- The child arrow is an input of its centre. -/
theorem sheetOut_input {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyRanked frame G seed η) (lv centre : Site) (psi : Site → ℤ) (c : Site) :
    sheetOut P lv centre psi c = incomingNeg c ∨ sheetOut P lv centre psi c = incomingPos c := by
  unfold sheetOut
  split_ifs
  · exact FLatticePaper.W1ForcedPhase.pointerOf_input _ c
  · exact FLatticePaper.W1ForcedPhase.pointerOf_input _ c

/-- **W1Forced_step** (task 89 (3)): from the strict-interior square data `hsq` of the sheet minimum, with the child arrows `sheetOut` and the
phase `Ψ`, the sheet minimum is forced on the strict interior of the word's child. -/
theorem W1Forced_step {seed : Site → Site → Prop} (word : Word)
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
    W1Forced (frameAt word).child.num (frameAt word).child.den (MW word) := by
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
    ⟨sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) z,
      forcing_of_sheet P (frameAt word).sheetShift (frameAt word).centre (frameAt word).child.num (frameAt word).child.den
        (MW word) (sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word)) (sheetPsi word)
        (strictInterior_child_finite (frameAt word))
        (fun c _ _ => sheetOut_input P _ _ _ c) hsq' z hz hw⟩

end FLatticePaper.W1Step
