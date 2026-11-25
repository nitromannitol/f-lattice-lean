import FLatticePaper.Plane.Induction.NonfreeRoot
import FLatticePaper.Plane.Induction.ConjFreeRoot
import FLatticePaper.Plane.Induction.MatchedPolicy

/-! # W4 (Q34): the drop cases of `hnofall_forced`, wired to the existing lemmas

A drop `a(x) = 1 → a(x') = 0` along a retained parent edge `parentPolicy P x x'` (with `x = c − l_v`, `x' = i − l_v`) is excluded
in each case of the old-root split:

* (i) nonfree or strictly interior old root: `nonfree_root_forced` gives the root condition of `nonfree_drop_excluded`
  (black or the forced retained edge), which excludes the drop (`excluded_of_nonfree_root`);
* (ii) an H-web translate with the target band: `H_translate_drop_excluded` excludes the drop (`excluded_of_H_translate`).

The residual cases (a conjugate freeH translate outside the H web, and the exceptional V root) are not in this file. -/

namespace FLatticePaper.W4Cases

open Farey FLatticePaper FLatticePaper.Induction

/-- **Case (i): the drop is excluded at a strictly interior old root.** The root condition comes from the W1 forcing of the
conjugate field (`hW1`, the named framework input of `nonfree_root_forced`). -/
theorem excluded_of_nonfree_root {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    {x x' : Site}
    (hSI : FLatticePaper.W1.StrictInterior (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den (zTurn x))
    (hpol : parentPolicy P x x')
    (h1 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1)
    (h0 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x' = 0) : False :=
  nonfree_drop_excluded h hSE P hpol h1 h0
    (nonfree_root_forced P hSE.packet.binary hW1 hSI hpol)

/-- **Case (ii): the drop is excluded at an H-web translate of the old root**, with the target band `hsy`. -/
theorem excluded_of_H_translate {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {x y : Site} {i : ℤ}
    (hx : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1)
    (hy : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) y = 0)
    (hwx : HRootWeb (frameAt word).parents.odd.num (frameAt word).parents.odd.den
      ((frameAt word).parentTGrade x + i * oddParentPeriod (frameAt word)))
    (hsy : 1 - (frameAt word).parents.odd.den ≤ (frameAt word).parentTGrade y + i * oddParentPeriod (frameAt word) ∧
      (frameAt word).parentTGrade y + i * oddParentPeriod (frameAt word) + 1 ≤
        (frameAt word).parents.odd.num + 2 * (frameAt word).parents.odd.den - 1) : False :=
  H_translate_drop_excluded h hSE hx hy hwx hsy

/-- **Class (i) of the rise exclusion: a conjugate-nonfree old root.** A drop `a(x) = 1 → a(x') = 0` along a retained parent edge
is impossible when the old root `zTurn x` is nonfree in the conjugate frame: `nonfree_root_forced_nonfree` gives black or the
forced retained edge, and `nonfree_drop_excluded` excludes the drop. The W1 forcing of the conjugate field `hW1` is the headline
input (the same as in `W1Forced_chain`), not a new one. -/
theorem rise_excluded_of_nonfree_root {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    {x x' : Site}
    (hnf : FLatticePaper.Induction.Nonfree (frameAt (conjWord word)) (zTurn x))
    (hpol : parentPolicy P x x')
    (h1 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1)
    (h0 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x' = 0) : False :=
  nonfree_drop_excluded h hSE P hpol h1 h0
    (nonfree_root_forced_nonfree P hSE.packet hW1 hnf hpol)

end FLatticePaper.W4Cases
