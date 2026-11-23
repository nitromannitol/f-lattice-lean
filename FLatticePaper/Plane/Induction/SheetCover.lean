import FLatticePaper.Plane.Induction.SheetCharts
import FLatticePaper.Plane.Induction.ExitSlip
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.PolygonGeometry

/-! Task 65: the cover of a rising black pair by the cases, with the exit case closed.

* `noBlackPairRise_of_cover`: `NoBlackPairRise` for the word field. The cover `hcover` is the chart split of the shifted
  edge: the first common chart (`FirstChartEdge`), the adjacent chart (`AdjacentChartEdge`), the centre exit
  (`CentreLowerExit`, closed by `not_rising_of_centre_exit`), the input exit (named), the nonfree, H and V-block drops and the
  exceptional vertex (closed in `SheetCases`/`SheetCharts`). The bounds `3 ≤ n` and `n + 2 ≤ d` come from the proper word
  (`child_num_ge_three`, `child_facts`), not as hypotheses.
* `HRootWeb_iff_bounds`: the H-web condition `hweb` of paragraph 8 is equivalent to `0 ≤ t_p ≤ N + D`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem HRootWeb_iff_bounds {N D t : ℤ} (hN : 1 ≤ N) (hND : N + 1 ≤ D) :
    HRootWeb N D t ↔ 0 ≤ t ∧ t ≤ N + D := by
  unfold HRootWeb
  constructor <;> intro h <;> omega

theorem noBlackPairRise_of_cover {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (inputExit : Site → Site → Prop)
    (hcover : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      FirstChartEdge P c i ∨ AdjacentChartEdge P c i ∨ CentreLowerExit (frameAt word) c i ∨ inputExit c i ∨
      (∃ x x', parentPolicy P x x' ∧
        jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1 ∧
        jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x' = 0) ∨
      (∃ x, HRootWeb (frameAt word).parents.odd.num (frameAt word).parents.odd.den
          ((frameAt word).parentTGrade x) ∧
        jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1) ∨
      ChildFrame.BlockPairAt (frameAt word) c ∨
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (excVertex (frameAt word) - (1, 0)) = 0)
    (hinputExit : ∀ c i, inputExit c i → ¬ RisingBlackPair (standardField word) (frameAt word).shortShift c i) :
    NoBlackPairRise (standardField word) (frameAt word).shortShift := by
  have hn : 3 ≤ (frameAt word).child.num := child_num_ge_three hw
  have hfacts := (frameAt word).child_facts
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by
    have := hfacts.2.2.1
    omega
  intro c hc hpar hbs i hi hone
  have hr : RisingBlackPair (standardField word) (frameAt word).shortShift c i := ⟨hi, hc, hpar, hbs, hone⟩
  rcases hcover c i hr with h1 | h1 | h1 | h1 | ⟨x, x', hpol, j1, j0⟩ | ⟨x, hw', j1⟩ | hblk | j0
  · exact first_chart_excluded hw hSE P h1 hr
  · exact adjacent_chart_excluded hw hSE P h1 hr
  · exact (frameAt word).not_rising_of_centre_exit hpk hn hnd h1 hr
  · exact hinputExit c i h1 hr
  · exact nonfree_drop_excluded hw hSE P hpol j1 j0
  · exact H_drop_excluded hw hSE x hw' j1
  · exact (frameAt word).not_rising_of_blockPair hpk hc hbs hblk
  · exact exceptional_drop_excluded hw hSE _ (exceptional_hT_proved hw hSE) j0

end FLatticePaper.Induction
