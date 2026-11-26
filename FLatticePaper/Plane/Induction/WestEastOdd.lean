import FLatticePaper.Plane.Induction.WestEast
import FLatticePaper.Plane.Induction.VStrict
import FLatticePaper.Plane.Induction.VLattice
import FLatticePaper.Plane.Induction.CentralForced

/-! # The central reflection of an odd free V root is an odd free V root

With `A = I + tr = (n − d + 1, n + d − 1)`, the reflection `y ↦ A − y` preserves parity (`A` is even). For an odd free V root `z`:
`t(A − z) = n + d − T − t(z)` and `s(A − z) = 2n − s(z)` (`WestEast.tGrade_cref`, `sGrade_cref`). The closed odd bounds of `z`
and the `s`-spectrum `2 − d + n ≤ s ≤ d + n − 2` (`VLattice.s_range`) give the closed bounds of `A − z`, and its `s`-value stays in the
spectrum. Its west neighbour `A − z − (1, 0)` is even with `s = n − d − s(z) ≤ −2 < 0`, so it is not closed. -/

namespace FLatticePaper.WestEastOdd


open FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.CentralForced

theorem cref_freeV_odd (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    cref (reflectionI + frame.child.modifiedDeck.transverse) z ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnd2 : frame.child.num + 2 ≤ frame.child.den := by omega
  have hT0 : 0 < frame.child.periodDenominator := frame.T_pos
  obtain ⟨h1, h2, h3, h4, hvs⟩ := FLatticePaper.VStrict.odd_free_V_facts hz hodd
  obtain ⟨hs_lo, hs_hi⟩ := FLatticePaper.VLattice.s_range hnd2 hvs
  have hsE : frame.sGrade z % 2 = 0 := by
    have hvz := hz.2.2
    unfold ChildFrame.vSpectrum at hvz
    exact hvz.1
  have hw_odd : ¬ EvenSite (cref (reflectionI + frame.child.modifiedDeck.transverse) z) := by
    intro h
    exact hodd ((evenSite_cref (centre_even frame) z).mp h)
  refine ⟨?_, ?_, ?_⟩
  · refine (frame.mem_closedPolygon_iff _).mpr (Or.inr ⟨hw_odd, ?_, ?_, ?_, ?_⟩)
    · rw [tGrade_cref]; omega
    · rw [tGrade_cref]; omega
    · rw [sGrade_cref]; omega
    · rw [sGrade_cref]; omega
  · intro hc
    rcases (frame.mem_closedPolygon_iff _).mp hc with h | h
    · have h' := h.2.2.2.1
      rw [frame.sGrade_sub_x, sGrade_cref] at h'
      omega
    · exfalso
      have hev2 := h.1
      unfold EvenSite at hev2 hw_odd
      omega
  · unfold ChildFrame.vSpectrum
    rw [sGrade_cref]
    refine ⟨by omega, ?_⟩
    rcases hvs with h | h
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩

end FLatticePaper.WestEastOdd
