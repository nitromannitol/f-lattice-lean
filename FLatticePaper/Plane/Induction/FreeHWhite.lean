import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.StarClassify

/-!
# The free H sites are white (the mirror of `laplacian_eq_zero_of_freeV`)

A site of the H cut `freeH` (`z ∈ E`, `(z.1, z.2 − 1) ∉ E`, `t(z)` in the H spectrum) has the star of its t-grades inside the zero strip
`1 − d ≤ t ≤ n + 2d − 1` of the packet, where `F = 0`. Hence its Laplacian vanishes. Consequently a black site (Laplacian `−1`) is never a
free H site of its frame, and the same holds for the V cut by `laplacian_eq_zero_of_freeV`.
-/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **A free H site is white.** Under the packet strips, the Laplacian of `F` vanishes at every site of `freeH`. -/
theorem laplacian_eq_zero_of_freeH (frame : ChildFrame) {F : Field} (hstrips : frame.HasStrips F) {w : Site}
    (hw : w ∈ frame.freeH) : laplacian F w = 0 := by
  obtain ⟨a, b, ha, hb⟩ := FLatticePaper.PriceDeck.child_odd_witness frame
  obtain ⟨hn0, hnd, -, hd3, -⟩ := frame.child_facts
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hw
  obtain ⟨-, -, hts⟩ := hw
  unfold ChildFrame.hSpectrum at hts
  have hz := hstrips.1
  have hEv := FLatticePaper.StrongUnitPrice.even_iff_tGrade frame a b ha hb w
  unfold laplacian
  by_cases he : EvenSite w
  · have ht := hEv.1 he
    have hN := FLatticePaper.StrongUnitPrice.tGrade_incomingNeg_even frame w he
    have hP := FLatticePaper.StrongUnitPrice.tGrade_incomingPos_even frame w he
    have h0 : F w = 0 := hz w (by omega) (by omega)
    have h1 : F (FLatticePaper.incomingNeg w) = 0 :=
      hz _ (by rw [hN]; omega) (by rw [hN]; omega)
    have h2 : F (FLatticePaper.incomingPos w) = 0 :=
      hz _ (by rw [hP]; omega) (by rw [hP]; omega)
    rw [h1, h2, h0]
    ring
  · have ht : frame.tGrade w % 2 = 1 := by
      have := mt hEv.2 he
      omega
    have hN := FLatticePaper.StrongUnitPrice.tGrade_incomingNeg_odd frame w he
    have hP := FLatticePaper.StrongUnitPrice.tGrade_incomingPos_odd frame w he
    have h0 : F w = 0 := hz w (by omega) (by omega)
    have h1 : F (FLatticePaper.incomingNeg w) = 0 :=
      hz _ (by rw [hN]; omega) (by rw [hN]; omega)
    have h2 : F (FLatticePaper.incomingPos w) = 0 :=
      hz _ (by rw [hP]; omega) (by rw [hP]; omega)
    rw [h1, h2, h0]
    ring

end FLatticePaper.Induction
