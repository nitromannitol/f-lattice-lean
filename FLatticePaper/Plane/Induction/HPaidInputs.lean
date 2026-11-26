import FLatticePaper.Plane.Induction.HPaidSet
import FLatticePaper.Plane.Induction.W4NativeSlip
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.SlipPermitH2
import FLatticePaper.Plane.Induction.Potentials

/-! # The named inputs of `first_exit_pair`, discharged at the child frame of a word

For the frame `C = frameAt (conjWord word)` with field `F = standardField (conjWord word)`:
* `P = C.price F` drifts by `−1` along `U = (d, n)` and by `0` along `V = (n − d, n + d)` (`price_kernel`, `price_transverse`);
* `J = C.roundedSlip F η` is unchanged by `U` and rises by `η` along `V` (`slip_drift`);
* `J = 0` on the free H sites for `η = ±1` (the native zero strip, `W4NativeSlip.conj_slip_zero_native_H`);
* `P = c₀` on the free V sites (`PriceDeck.price_on_freeV`). -/

namespace FLatticePaper.HPaidInputs

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

variable {word : Word}

theorem price_U (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (z : Site) :
    frame.price F (z + ((frame.child.den, frame.child.num) : Site)) = frame.price F z - 1 := by
  have h := frame.price_kernel F hP.periods z
  rw [frame.child_modifiedDeck_kernel] at h
  exact h

theorem price_V (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (z : Site) :
    frame.price F (z + ((frame.child.num - frame.child.den, frame.child.num + frame.child.den) : Site)) =
      frame.price F z := by
  have h := frame.price_transverse F hP.periods z
  rw [frame.child_modifiedDeck_transverse] at h
  exact h

theorem roundedSlip_U (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (η : ℤ) (z : Site) :
    frame.roundedSlip F η (z + ((frame.child.den, frame.child.num) : Site)) = frame.roundedSlip F η z := by
  have h := (SlipPermitH2.slip_drift frame hP.periods η z).1
  rw [frame.child_modifiedDeck_kernel] at h
  unfold ChildFrame.roundedSlip
  rw [h]

theorem roundedSlip_V (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (η : ℤ) (z : Site) :
    frame.roundedSlip F η (z + ((frame.child.num - frame.child.den, frame.child.num + frame.child.den) : Site)) =
      frame.roundedSlip F η z + η := by
  have h := (SlipPermitH2.slip_drift frame hP.periods η z).2
  rw [frame.child_modifiedDeck_transverse] at h
  unfold ChildFrame.roundedSlip
  rw [h]
  omega

/-- The rounded slip vanishes on the free H sites of `C = frameAt (conjWord word)` for `η = ±1`. -/
theorem roundedSlip_freeH (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word))) {η : ℤ} (hη : η = 1 ∨ η = -1) {z : Site}
    (hz : z ∈ (frameAt (conjWord word)).freeH) :
    (frameAt (conjWord word)).roundedSlip (standardField (conjWord word)) η z = 0 := by
  have h := W4NativeSlip.conj_slip_zero_native_H hX hSE' hz hη
  unfold ChildFrame.roundedSlip
  rw [h]
  omega

/-- **The named inputs at the child frame, and the first exit.** For a word, the first exit `u` of a strict site of
`C = frameAt (conjWord word)`, translated to pair `(c₀, 0)`, is own-deck free. -/
theorem first_exit_pair_word (hX : ∃ x ∈ conjWord word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hSE' : StrongEstimates (conjWord (conjWord word))) {η : ℤ} (hη : η = 1 ∨ η = -1) {z u : Site}
    (hz : StrictInterior (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den z)
    (hE : Edge u z)
    (hnot : ¬ StrictInterior (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den u) :
    ∃ k l : ℤ,
      (frameAt (conjWord word)).price (standardField (conjWord word))
          (u + k • ((frameAt (conjWord word)).child.den, (frameAt (conjWord word)).child.num) +
            l • ((frameAt (conjWord word)).child.num - (frameAt (conjWord word)).child.den,
              (frameAt (conjWord word)).child.num + (frameAt (conjWord word)).child.den)) =
        (frameAt (conjWord word)).cutPrice ∧
      (frameAt (conjWord word)).roundedSlip (standardField (conjWord word)) η
          (u + k • ((frameAt (conjWord word)).child.den, (frameAt (conjWord word)).child.num) +
            l • ((frameAt (conjWord word)).child.num - (frameAt (conjWord word)).child.den,
              (frameAt (conjWord word)).child.num + (frameAt (conjWord word)).child.den)) = 0 ∧
      ((∃ m : ℤ, u + k • ((frameAt (conjWord word)).child.den, (frameAt (conjWord word)).child.num) +
          l • ((frameAt (conjWord word)).child.num - (frameAt (conjWord word)).child.den,
            (frameAt (conjWord word)).child.num + (frameAt (conjWord word)).child.den) -
          m • ((frameAt (conjWord word)).child.den, (frameAt (conjWord word)).child.num) ∈
            (frameAt (conjWord word)).freeH) ∨
       (∃ m : ℤ, u + k • ((frameAt (conjWord word)).child.den, (frameAt (conjWord word)).child.num) +
          l • ((frameAt (conjWord word)).child.num - (frameAt (conjWord word)).child.den,
            (frameAt (conjWord word)).child.num + (frameAt (conjWord word)).child.den) -
          m • ((frameAt (conjWord word)).child.num - (frameAt (conjWord word)).child.den,
            (frameAt (conjWord word)).child.num + (frameAt (conjWord word)).child.den) ∈
            (frameAt (conjWord word)).freeV)) := by
  have hη2 : η * η = 1 := by rcases hη with rfl | rfl <;> norm_num
  exact FLatticePaper.HPaidSet.first_exit_pair (frameAt (conjWord word)) ((frameAt (conjWord word)).price (standardField (conjWord word)))
    ((frameAt (conjWord word)).roundedSlip (standardField (conjWord word)) η)
    η ((frameAt (conjWord word)).cutPrice) hη2
    (fun z => price_U _ _ hSE.packet z) (fun z => price_V _ _ hSE.packet z)
    (fun z => roundedSlip_U _ _ hSE.packet η z) (fun z => roundedSlip_V _ _ hSE.packet η z)
    (fun v hv => roundedSlip_freeH hX hSE' hη hv)
    (fun v hv => PriceDeck.price_on_freeV _ _ hSE.packet.strips hv) hz hE hnot

end FLatticePaper.HPaidInputs
