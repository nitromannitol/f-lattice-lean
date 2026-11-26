import FLatticePaper.Plane.Induction.WestException
import FLatticePaper.Plane.Induction.W1NonfreeHsqC
import FLatticePaper.Plane.Induction.WestNonfree
import FLatticePaper.Plane.Induction.SouthPolicy
import FLatticePaper.Plane.Induction.ChildNumerator

/-! # The exceptional west input of the free policy, with its four premises discharged except the collar input

`WestException.hwest_freePolicy` needs `hsq`, `hSI`, `hSouth`, `hNF` at the exceptional vertex, and `HasSatSelection`. Here:

* `hSI`: `WestNonfree.strictInterior_exc` (proved);
* `hNF`: `WestNonfree.not_freeClosure_exceptional` (proved);
* `hSouth`: `SouthPolicy.sheetPolicyA_south` (proved, from the conjugate's prescription at its free H origin and the deck invariance);
* `hsq`: `W1NonfreeHsqC.hsq_all_of_inputs`, from the route square `hfree` and the collar input `hcollar`;
* `HasSatSelection`: the Q1 rank, given.

The remaining premises are `hfree` (the route's free-root square) and `hcollar` (the collar square, which `CollarChain` derives from `hRow`). -/

namespace FLatticePaper.WestClose

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Phase FLatticePaper.SquareClauses
open FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.W1NonfreeOut FLatticePaper.W1NonfreeHsqNonneg FLatticePaper.FreePolicy

/-- **The exceptional west input of the free policy.** Given the conjugate's ranked policy `P` with the canonical game `G`, the route square
`hfree`, the collar square `hcollar`, and the Q1 satisfiability `hsat`, the free policy of sign `η` retains the west input of the
exceptional vertex. -/
theorem westAtException_of_routes {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongCore word)
    {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy)
    (heps : (frameAt word).eps = 1)
    (hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)))
    (hcollar : ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → FLatticePaper.W1CollarFrame.CollarFrame (frameAt word) c → HsqAt word P c)
    (hsat : HasSatSelection (standardField word)) (η : ℤ) :
    freePolicy (frameAt word) (standardField word) η
      ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)
      (incomingNeg ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)) :=
  WestException.hwest_freePolicy h hSE hWord P
    (fun c hcS hM => W1NonfreeHsqC.hsq_all_of_inputs h hSE P hs hW1 (FLatticePaper.Induction.child_num_ge_three h)
      hfree hcollar c hcS hM)
    heps (WestNonfree.strictInterior_exc h heps)
    (SouthPolicy.sheetPolicyA_south h hSE P G hW heps)
    (WestNonfree.not_freeClosure_exceptional h heps) hsat η

end FLatticePaper.WestClose
