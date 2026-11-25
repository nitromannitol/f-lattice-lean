import FLatticePaper.Plane.Induction.ClippedIdentity
import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.ParentStrip
import FLatticePaper.Plane.Induction.CutOnePerProper

/-! Task 72 / Q31 step 2: the clipped identity from `freeV` alone.

The windows (`FreeVWindow`), the ordinate bounds (`FreeVOrdinate`, with `CutOnePerProper` for the odd points), and the parent strip
(`ParentStrip`, with the separate `vLast` case) supply every hypothesis of `ClippedIdentity.clipped_identity`. The only inputs are
the proper word, the packet of its field, and `z ∈ freeV`. -/

namespace FLatticePaper.ClippedFreeV

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet

/-- **The clipped identity for a native V point.** -/
theorem clipped_identity_freeV {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hpk : (frameAt word).Packet (standardField word)) {z : Site}
    (hz : z ∈ (frameAt word).freeV) :
    standardField word z - standardField word (z - (frameAt word).shortShift) =
      -min (FqW word (z + ((frameAt word).eps * (frameAt word).parents.even.den,
          (frameAt word).eps * (frameAt word).parents.even.num)) - FqW word z) 2 := by
  have hcut := CutOnePerProper.cutOnePerOrdinate_of_proper h
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := (frameAt word).child_facts
  have hwin : 2 - ((frameAt word).child.den - (frameAt word).child.num) ≤ (frameAt word).sGrade z ∧
      (frameAt word).sGrade z ≤ (frameAt word).child.den + (frameAt word).child.num - 2 := by
    by_cases he : EvenSite z
    · obtain ⟨a, b⟩ := FreeVWindow.freeV_even_window (frameAt word) hz he
      constructor <;> omega
    · exact FreeVWindow.freeV_odd_window (frameAt word) hz he
  have hstrip : FqW word z = harmonicGrid z ∧
      FqW word (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) =
        harmonicGrid (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) := by
    by_cases hv : z = (frameAt word).vLast
    · subst hv
      exact ParentStrip.even_strip_vLast h hSE
    · by_cases he : EvenSite z
      · obtain ⟨a, b, c⟩ := FreeVOrdinate.freeV_even_ordinate (frameAt word) hz he
        obtain ⟨a', b'⟩ := FreeVWindow.freeV_even_window (frameAt word) hz he
        exact ParentStrip.even_strip h hSE z he a (c hv) a' b'
      · obtain ⟨a, b⟩ := FreeVOrdinate.freeV_odd_ordinate (frameAt word) hcut hz he
        exact ParentStrip.odd_strip h hSE z he a b hwin.1 hwin.2
  exact ClippedIdentity.clipped_identity h hSE hpk hz hwin.1 hwin.2 hstrip

end FLatticePaper.ClippedFreeV
