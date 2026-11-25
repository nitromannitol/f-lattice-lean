import FLatticePaper.Plane.Induction.SlipPermitH
import FLatticePaper.Plane.Induction.FreeChain
import FLatticePaper.Plane.Induction.DeckSelection

/-! The H-branch slip permit by translation. The slip `D_η = ChildFrame.slip F η` drifts under the generators: `D(z + kernel) = D z`
and `D(z + transverse) = D z + 2η` (the transverse grade of `η s` is `2η`). So `D(z + combine i j) = D z + 2ηj` for every `z`, and the slip
increment `D(i) − D(c)` is invariant when `c` and `i` are both translated by the same span element. -/

namespace FLatticePaper.SlipPermitH2

open Farey FLatticePaper FLatticePaper.Induction

theorem slip_drift (frame : ChildFrame) {F : Field} {cU cV : ℤ} (hF : HasGeneratorPeriods frame.child F cU cV) (η : ℤ)
    (z : Site) :
    frame.slip F η (z + frame.child.modifiedDeck.kernel) = frame.slip F η z ∧
      frame.slip F η (z + frame.child.modifiedDeck.transverse) = frame.slip F η z + 2 * η := by
  have a0 := hF.1 z
  have a1 : F (z + frame.child.modifiedDeck.kernel + η • frame.shortShift) =
      F (z + η • frame.shortShift) + cU := by
    rw [show z + frame.child.modifiedDeck.kernel + η • frame.shortShift =
      (z + η • frame.shortShift) + frame.child.modifiedDeck.kernel by abel]
    exact hF.1 _
  have b0 := hF.2 z
  have b1 : F (z + frame.child.modifiedDeck.transverse + η • frame.shortShift) =
      F (z + η • frame.shortShift) - frame.child.transverseGrade (z + η • frame.shortShift) + cV := by
    rw [show z + frame.child.modifiedDeck.transverse + η • frame.shortShift =
      (z + η • frame.shortShift) + frame.child.modifiedDeck.transverse by abel]
    exact hF.2 _
  have tw := FLatticePaper.FreeChain.transverse_grade_add_smul frame η z
  unfold ChildFrame.slip
  constructor
  · linarith
  · linarith

theorem slip_combine (frame : ChildFrame) {F : Field} {cU cV : ℤ} (hF : HasGeneratorPeriods frame.child F cU cV) (η : ℤ)
    (i j : ℤ) (z : Site) :
    frame.slip F η (z + frame.child.modifiedDeck.combine i j) = frame.slip F η z + 2 * η * j := by
  have hU : ∀ x, frame.slip F η (x + frame.child.modifiedDeck.kernel) = frame.slip F η x + 0 := fun x => by
    rw [(slip_drift frame hF η x).1]
    ring
  have hV : ∀ x, frame.slip F η (x + frame.child.modifiedDeck.transverse) = frame.slip F η x + 2 * η := fun x =>
    (slip_drift frame hF η x).2
  have hUi := FLatticePaper.FreeChain.iter_add (G := frame.slip F η) (v := frame.child.modifiedDeck.kernel) (c := 0) hU i
  have hVj := FLatticePaper.FreeChain.iter_add (G := frame.slip F η) (v := frame.child.modifiedDeck.transverse)
    (c := 2 * η) hV j
  rw [DeckSelection.combine_eq frame i j, show z + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse) =
    (z + j • frame.child.modifiedDeck.transverse) + i • frame.child.modifiedDeck.kernel by abel, hUi (z + j • frame.child.modifiedDeck.transverse), hVj z]
  ring

/-- **The H-branch slip permit.** For a free-presc H input `i = c + prescribedH η (c + t)` with `c + t` a free H root, the slip increment
from `c` to `i` is `0`, hence `≤ 0`. -/
theorem slip_permit_H (frame : ChildFrame) {F : Field} {cU cV : ℤ} (hF : HasGeneratorPeriods frame.child F cU cV)
    (hS : frame.HasStrips F) (hn3 : 3 ≤ frame.child.num) {η : ℤ} (hη : η = 1 ∨ η = -1) {c i t : Site}
    (ht : t ∈ frame.child.modifiedDeck.span) (hx : c + t ∈ frame.freeH)
    (hi : i = c + frame.prescribedH η (c + t)) :
    frame.slip F η i ≤ frame.slip F η c := by
  obtain ⟨a, b, rfl⟩ := ht
  have hroot := SlipPermitH.slip_zero_root frame hS hx hn3 hη
  have h1 := slip_combine frame hF η a b c
  have h2 := slip_combine frame hF η a b i
  have e : i + frame.child.modifiedDeck.combine a b =
      (c + frame.child.modifiedDeck.combine a b) +
        frame.prescribedH η (c + frame.child.modifiedDeck.combine a b) := by
    rw [hi]
    abel
  rw [e] at h2
  rw [hroot.1] at h1
  rw [hroot.2] at h2
  linarith

end FLatticePaper.SlipPermitH2
