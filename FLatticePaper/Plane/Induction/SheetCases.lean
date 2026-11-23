import FLatticePaper.Plane.Induction.MatchedPolicy
import FLatticePaper.Plane.Induction.NoBlackPair

/-! Task 63: `NoBlackPairRise` for the word field, with the leaves wired to the proved drop lemmas of `MatchedPolicy`.

The leaves that are closed here (no hypothesis beyond the strong estimates and the policy):
* `nonfree_drop_excluded`: a drop `a = 1 → 0` along a transported policy edge (nonfree root);
* `H_drop_excluded`: a drop from an old H root, with the H-web condition `hweb` supplied in the cover (open, paragraph 8);
* `ChildFrame.not_rising_of_blockPair`: the free V block pair (paragraph 10);
* `exceptional_drop_excluded`: the exceptional vertex, with the named `V_p`-step `hT` (paragraph 10).

Named (not closed here): the cover `hcover` (the sheet choice and the chart classification of a rising black pair), and the
first-common-chart, adjacent-chart and exit leaves `hfirst`, `hadj`, `hexit`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The exceptional vertex `V_p + I = (N − D + 1, D + N − 1)` of the parent (paragraph 10, `W = 1`). -/
def excVertex (frame : ChildFrame) : Site :=
  (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1)

theorem noBlackPairRise_of_sheet_cases {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (firstCommon adjacentPositive exitSameSlip : Site → Site → Prop)
    (hcover : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      firstCommon c i ∨ adjacentPositive c i ∨ exitSameSlip c i ∨
      (∃ x x', parentPolicy P x x' ∧
        jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1 ∧
        jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x' = 0) ∨
      (∃ x, HRootWeb (frameAt word).parents.odd.num (frameAt word).parents.odd.den
          ((frameAt word).parentTGrade x) ∧
        jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1) ∨
      ChildFrame.BlockPairAt (frameAt word) c ∨
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (excVertex (frameAt word) - (1, 0)) = 0)
    (hfirst : ∀ c i, firstCommon c i → ¬ RisingBlackPair (standardField word) (frameAt word).shortShift c i)
    (hadj : ∀ c i, adjacentPositive c i → ¬ RisingBlackPair (standardField word) (frameAt word).shortShift c i)
    (hexit : ∀ c i, exitSameSlip c i → ¬ RisingBlackPair (standardField word) (frameAt word).shortShift c i)
    (hT : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (excVertex (frameAt word) - (1, 0)) =
      pJump (frameAt word) (quarterTurnField (standardField (conjWord word))) (1, 0) + 1) :
    NoBlackPairRise (standardField word) (frameAt word).shortShift := by
  intro c hc hpar hbs i hi hone
  have hr : RisingBlackPair (standardField word) (frameAt word).shortShift c i := ⟨hi, hc, hpar, hbs, hone⟩
  rcases hcover c i hr with h1 | h1 | h1 | ⟨x, x', hpol, j1, j0⟩ | ⟨x, hw, j1⟩ | hblk | j0
  · exact hfirst c i h1 hr
  · exact hadj c i h1 hr
  · exact hexit c i h1 hr
  · exact nonfree_drop_excluded h hSE P hpol j1 j0
  · exact H_drop_excluded h hSE x hw j1
  · exact (frameAt word).not_rising_of_blockPair hpk hc hbs hblk
  · exact exceptional_drop_excluded h hSE _ hT j0

end FLatticePaper.Induction
