import FLatticePaper.Plane.Induction.SlipReflect
import FLatticePaper.Plane.Induction.SlipPermitH2
import FLatticePaper.Plane.Induction.FreePolicy

/-! The sign −1 V permit from the sign +1 one, by the reflection `R z = I + V − z` (`I = (1,−1)`, `V` the transverse vector).

* `slip_minus_reflect`: `D₋(z) = D₊(R z) − 2`, from the packet reflection `slip_reflect` (centre − R z = z + kernel) and the kernel invariance of the slip.
* `step_match`: for `w ≠ vFirst`, the sign −1 prescribed V input of `w` is mapped by `R` to the sign +1 prescribed V input of `R w`,
  since `R` preserves parity and `−prescribedV(−1) w = prescribedV(+1) (R w)` (the origin is the only exception).
* `minus_increment_eq_plus`: the sign −1 slip increment at `(w, w + prescribedV(−1) w)` equals the sign +1 slip increment at `(R w, R w + prescribedV(+1)(R w))`. -/

namespace FLatticePaper.SlipReflectMinus

open Farey FLatticePaper FLatticePaper.Induction

theorem slip_minus_reflect (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (z : Site) :
    frame.slip F (-1) z = frame.slip F 1 ((1, -1) + frame.child.modifiedDeck.transverse - z) - 2 := by
  have h1 := ChildFrame.slip_reflect frame hP ((1, -1) + frame.child.modifiedDeck.transverse - z)
  have hc : frame.centre - ((1, -1) + frame.child.modifiedDeck.transverse - z) =
      z + frame.child.modifiedDeck.kernel := by
    unfold ChildFrame.centre
    ext <;> simp <;> ring
  rw [hc] at h1
  have hk := (SlipPermitH2.slip_drift frame hP.periods (-1) z).1
  unfold ChildFrame.slip at hk ⊢
  simp only [neg_one_smul, one_smul] at hk h1 ⊢
  linarith

theorem step_match (frame : ChildFrame) {w : Site} (hw : w ≠ FLatticePaper.Induction.vFirst) :
    (1, -1) + frame.child.modifiedDeck.transverse - (w + frame.prescribedV (-1) w) =
      ((1, -1) + frame.child.modifiedDeck.transverse - w) + frame.prescribedV 1 ((1, -1) + frame.child.modifiedDeck.transverse - w) := by
  have hpar : EvenSite ((1, -1) + frame.child.modifiedDeck.transverse - w) ↔ EvenSite w := by
    unfold EvenSite
    have hV : frame.child.modifiedDeck.transverse = (frame.child.num - frame.child.den, frame.child.num + frame.child.den) :=
      ChildFrame.child_modifiedDeck_transverse frame
    rw [hV]
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    omega
  by_cases he : EvenSite w
  · have hR : EvenSite ((1, -1) + frame.child.modifiedDeck.transverse - w) := hpar.2 he
    rw [FLatticePaper.FreePolicy.pV_even frame (-1) he, if_neg hw,
      FLatticePaper.FreePolicy.pV_even frame 1 hR]
    split_ifs
    · simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
      constructor <;> ring
    · simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
      constructor <;> ring
  · have ho : ¬ EvenSite ((1, -1) + frame.child.modifiedDeck.transverse - w) := fun h => he (hpar.1 h)
    rw [FLatticePaper.FreePolicy.pV_odd frame (-1) he, FLatticePaper.FreePolicy.pV_odd frame 1 ho]
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    constructor <;> ring

/-- The sign −1 slip increment along the prescribed V step equals the sign +1 increment at the reflected pair. -/
theorem minus_increment_eq_plus (frame : ChildFrame) {F : Field} (hP : frame.Packet F) {w : Site}
    (hw : w ≠ FLatticePaper.Induction.vFirst) :
    frame.slip F (-1) (w + frame.prescribedV (-1) w) - frame.slip F (-1) w =
      frame.slip F 1 (((1, -1) + frame.child.modifiedDeck.transverse - w) +
          frame.prescribedV 1 ((1, -1) + frame.child.modifiedDeck.transverse - w)) -
        frame.slip F 1 ((1, -1) + frame.child.modifiedDeck.transverse - w) := by
  have hu := slip_minus_reflect frame hP (w + frame.prescribedV (-1) w)
  have hw' := slip_minus_reflect frame hP w
  rw [step_match frame hw] at hu
  linarith

end FLatticePaper.SlipReflectMinus
