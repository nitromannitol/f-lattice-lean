import FLatticePaper.Plane.Induction.ParentStrip
import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.CutRowsAll
import FLatticePaper.Plane.Induction.StrongEstimates

/-! The h0 equality at free V whites: `F(w) = F_p(w)`, both equal to the harmonic grid. The child strip gives `F(w)` from the
free V window (`freeV_even_window`, `freeV_odd_window`), and the parent strip gives `F_p(w)` from `ParentStrip.even_strip` (at the
ordinate bounds of `freeV_even_ordinate`), `even_strip_vLast` at the final vertex, and `odd_strip`. -/

namespace FLatticePaper.FreeVH0

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet

theorem standardField_eq_harmonic_of_freeV {word : Word} (hW : StrongEstimates word) {w : Site}
    (hw : w ∈ (frameAt word).freeV) : standardField word w = harmonicGrid w := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := (frameAt word).child_facts
  by_cases he : EvenSite w
  · have hwin := FreeVWindow.freeV_even_window (frameAt word) hw he
    exact hW.packet.strips.2 w (by omega) (by omega)
  · have hwin := FreeVWindow.freeV_odd_window (frameAt word) hw he
    exact hW.packet.strips.2 w (by omega) (by omega)

theorem FqW_eq_harmonic_of_freeV {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {w : Site} (hw : w ∈ (frameAt word).freeV) :
    FqW word w = harmonicGrid w := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := (frameAt word).child_facts
  by_cases he : EvenSite w
  · by_cases hv : w = (frameAt word).vLast
    · subst hv
      exact (ParentStrip.even_strip_vLast h hSE).1
    · obtain ⟨o0, o1, o2⟩ := FreeVOrdinate.freeV_even_ordinate (frameAt word) hw he
      have hwin := FreeVWindow.freeV_even_window (frameAt word) hw he
      exact (ParentStrip.even_strip h hSE w he o0 (o2 hv) hwin.1 hwin.2).1
  · obtain ⟨o0, o1⟩ := FreeVOrdinate.freeV_odd_ordinate (frameAt word) (CutRowsAll.cut_one_per_ordinate_all (frameAt word)) hw he
    have hwin := FreeVWindow.freeV_odd_window (frameAt word) hw he
    exact (ParentStrip.odd_strip h hSE w he o0 (by omega) hwin.1 hwin.2).1

theorem h0_eq_of_freeV {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongEstimates word)
    (hSE : StrongEstimates (conjWord word)) {w : Site} (hw : w ∈ (frameAt word).freeV) :
    standardField word w = FqW word w :=
  (standardField_eq_harmonic_of_freeV hW hw).trans (FqW_eq_harmonic_of_freeV h hSE hw).symm

end FLatticePaper.FreeVH0
