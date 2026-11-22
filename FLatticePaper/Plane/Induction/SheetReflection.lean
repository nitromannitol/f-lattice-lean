import FLatticePaper.Plane.Induction.Bands
import FLatticePaper.Plane.Induction.Coherence
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.WordInduction

/-! Task 25, the eps = -1 branch of (I2) by the reflection.

The archive treats the branch eps = -1 (C = h0 on the harmonic band, A >= h0) "by reflection". The reflection is the
centre `c` of the closed polygon (`ChildFrame.centre`, Bands.lean). It exchanges the two sheets, with the t-correction
and the symmetry constant (`ChildFrame.symmetryConstant`):

  A(c - z) = C(z) - t(z) + kappa,     C(c - z) = A(z) - t(z) + kappa,     kappa = symmetryConstant.

This exchange is the stated reflection (the input `SheetExchange`); it is verified numerically on the 116 proper words
(scripts/reflection_exchange.py), with kappa equal to (d + n - T)/2 on every word.
From the exchange the difference is antisymmetric, `Psi(c - z) = -Psi(z)`, which is proved below. The transfer of the
eps = -1 claim `Psi <= 0` on the harmonic band to the reflected band `Psi >= 0` is then exact. What remains open is the
exchange itself (not in Lean: only the minimum reflection `hrefl` of `packet_of_sheets` is) and the positivity on the
reflected band, which is not a written statement of the archive. -/

namespace FLatticePaper.Induction
open Farey FLatticePaper

/-- The stated reflection of the sheets through the centre of the closed polygon. -/
def ChildFrame.SheetExchange (frame : ChildFrame) (Fp : Field) : Prop :=
  (∀ z : Site, frame.sheetA Fp (frame.centre - z) =
      frame.sheetC Fp z - frame.tGrade z + frame.symmetryConstant) ∧
    (∀ z : Site, frame.sheetC Fp (frame.centre - z) =
      frame.sheetA Fp z - frame.tGrade z + frame.symmetryConstant)

/-- The sheet difference `Psi = C - A` is antisymmetric under the centre reflection. -/
theorem sheetDiff_antisymm_of_exchange (frame : ChildFrame) (Fp : Field) (hX : frame.SheetExchange Fp)
    (z : Site) :
    frame.sheetC Fp (frame.centre - z) - frame.sheetA Fp (frame.centre - z) =
      -(frame.sheetC Fp z - frame.sheetA Fp z) := by
  obtain ⟨h1, h2⟩ := hX
  rw [h1 z, h2 z]
  ring

/-- (I2), eps = -1, by the reflection. Named inputs: the stated sheet exchange `hX`, and the positivity `hpos` of the
difference on the reflected harmonic band `c - H`, where `H = E cap {s <= 2L - 1}`. Then the difference is nonpositive
on the harmonic band.

Uncovered region: `hpos` is not established. The reflected band `c - H` is inside `E` (E is invariant), but it meets
`{t < 1 - d}`, which is outside the I1 zone `E cap {t >= 1 - d}`, the only region where `Psi >= 0` is a premise
(numerically 6088 of the 6262 reflected points, over the 58 eps = -1 words). On that part `Psi >= 0` is not written in
the archive. -/
theorem i2_neg_of_reflection (frame : ChildFrame) (Fp : Field) (hX : frame.SheetExchange Fp)
    (hpos : ∀ z ∈ frame.closedPolygon,
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 →
        0 ≤ frame.sheetC Fp (frame.centre - z) - frame.sheetA Fp (frame.centre - z)) :
    ∀ z ∈ frame.closedPolygon,
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 →
        frame.sheetC Fp z - frame.sheetA Fp z ≤ 0 := by
  intro z hz hs
  have h := sheetDiff_antisymm_of_exchange frame Fp hX z
  have hp := hpos z hz hs
  linarith

/-- The sheet exchange of the eps = -1 branch, from the conjugate packet. The reflection and the periods of the
conjugate standard field, with the child identity of the conjugate, transport through the quarter turn to the two
sheets (`ChildFrame.sheet_swap`, SheetSwap.lean). -/
theorem sheetExchange_of_packet {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word))) :
    (frameAt word).SheetExchange (quarterTurnField (standardField (conjWord word))) := by
  have hc := frameAt_conj_child h
  have hs := (frameAt word).sheet_swap (frameAt (conjWord word)) hc hG.reflection hG.periods
  exact ⟨fun z => (hs z).1, fun z => (hs z).2⟩

end FLatticePaper.Induction
