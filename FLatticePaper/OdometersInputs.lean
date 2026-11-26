import FLatticePaper.StepHeadline
import FLatticePaper.Plane.Induction.W1StepAssembly
import FLatticePaper.Plane.Induction.FreeNamedQ1
import FLatticePaper.Plane.Induction.StrongSeedInduction

/-! # The odometers theorem from the explicit inputs of the two induction steps

The W1 step (`W1StepAssembly.w1Step_of_parts`) takes `hRow` (`hFreeIn` is discharged by `FreeInStep.hFreeIn_of_strong`). The games step (`FreeNamedQ1.gamesStep_of_noFort`) takes the same
three, the restricted no-fort `hno`, the forced permit `hforced` and the corner `hcorner`. This file assembles the two steps into the
odometers theorem `StepHeadline.odometersTheorem_of_steps`, with all inputs universal over words. The forced permit `hforced` is the
claim that `(1)` of the next task will reduce to the boundary claim Q40; until then it is an explicit input. -/

namespace FLatticePaper.OdometersInputs

open FLatticePaper.W1Phase
open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.StepHeadline FLatticePaper.FreePolicy FLatticePaper.AuxRankSign
  FLatticePaper.FreeClosure FLatticePaper.AuxRank FLatticePaper.SquareClauses FLatticePaper.FreePermittedS FLatticePaper.AuxRankQ1

/-- **The odometers theorem from the explicit inputs.** -/
theorem odometersTheorem_of_inputs
    (hno : ∀ word : Word, ∀ η : ℤ, (η = 1 ∨ η = -1) →
      RestrictedNoFort (standardField word)
        (fun z => (frameAt word).price (standardField word) z + (frameAt word).roundedSlip (standardField word) η z)
        (permitsQ1 (frameAt word) (standardField word) η))
    (hRow : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) →
      ∀ (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
        (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) (fun _ _ => False)
          (frameAt word).eps),
        P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy →
          CollarChain.RowFaceStrictHyp word (standardField (conjWord word)) P.retained)
    (hDich : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → CollarChain.WitnessDichotomy word)
    (hforced : ∀ word : Word, ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ c o : Site, ¬ freeClosure (frameAt word) c →
      laplacian (standardField word) c = 0 → ForcedEdge (standardField word) (fun _ _ => False) c o →
      slipPermits (standardField word) (fun z => standardField word (z + η • (frameAt word).shortShift)) c o)
    (hcorner : ∀ word : Word, ∀ η : ℤ, (η = 1 ∨ η = -1) → (frameAt word).eps = 1 → η = -1 →
      (frameAt word).parents.odd.num = 1 →
      FLatticePaper.W1Step.sheetPsi word (FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η))) = 0 ∧
        (frameAt word).sheetA (FLatticePaper.W1MSheet.FqW word)
          (FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η))) = 0) :
    OdometersTheorem :=
  StepHeadline.odometersTheorem_of_steps
    (fun word hproper hnot hcore hseed _ hSE hpar _ _ _ hG hW1c hW1 =>
      FreeNamedQ1.gamesStep_of_noFort (exists_ne_two_of_not_twoPow hproper hnot) hproper hcore hseed hSE hG hpar hW1c hW1
        (hno word) hRow hDich (hforced word) (hcorner word))
    (W1StepAssembly.w1Step_of_parts hRow hDich)

end FLatticePaper.OdometersInputs
