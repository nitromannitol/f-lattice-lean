import FLatticePaper.Plane.Induction.Binary
import FLatticePaper.Plane.Induction.ChildFrame
import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.Induction.Reflection
import FLatticePaper.Plane.Induction.Strips

/-! Task 67, STRONG_PRICE §3 (the H full stars): the short slip `D_η` vanishes on an H full star by the ordinary zero strip.

The zero strip (`ChildFrame.HasStrips`, the first clause) gives `F = 0` on `t ∈ [1 − d, n + 2d − 1]` at both parities. The short shift
`σ` has `t(σ) = −2`, so for `t(z) ∈ [3 − d, n + 2d − 3]` both `z` and `z + η σ` (η = ±1) lie in the strip, and `D_η z = 0`
(`slip_eq_zero_of_tBand`).

The native even H endpoints `(2l − b, b)`, `b = ⌊2nl/L⌋`, have `t = (2nl) mod L ∈ [0, L − 1]` (`tGrade_even_endpoint`). The two physical
inputs of an even root shift `t` by `∓n`, which stays in the band when `d − n ≥ 4` (`star_tBand_of_even_root`). So the full star of every
native even H endpoint has `D_± = 0` (`slip_zero_on_even_star`). The odd H roots are a named geometric input (the odd native vertices). -/

namespace FLatticePaper.StrongHStrip

open Farey FLatticePaper FLatticePaper.Induction

/-- The zero band of the short slip: `D_η = 0` where `t ∈ [3 − d, n + 2d − 3]`, for `η = ±1`. -/
theorem slip_eq_zero_of_tBand (frame : ChildFrame) (F : Field) (hS : frame.HasStrips F) {η : ℤ} (hη : η = 1 ∨ η = -1)
    (z : Site) (ht1 : 3 - frame.child.den ≤ frame.tGrade z)
    (ht2 : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 3) :
    frame.slip F η z = 0 := by
  obtain ⟨hz, -⟩ := hS
  have hshift : frame.tGrade (z + η • frame.shortShift) = frame.tGrade z - 2 * η := by
    rw [frame.tGrade_add_pt, frame.tGrade_smul, frame.tGrade_shortShift]
    ring
  have h0 := hz z (by omega) (by omega)
  have h1 := hz (z + η • frame.shortShift)
    (by rw [hshift]; rcases hη with rfl | rfl <;> omega)
    (by rw [hshift]; rcases hη with rfl | rfl <;> omega)
  unfold ChildFrame.slip
  rw [h0, h1]
  ring

/-- The native even H endpoint `(2l − b, b)`, `b = ⌊2nl/L⌋`, has `t = (2nl) mod L`. -/
theorem tGrade_even_endpoint (frame : ChildFrame) (l b : ℤ)
    (hb : b = (2 * frame.child.num * l) / (frame.child.den + frame.child.num)) :
    frame.tGrade (2 * l - b, b) = (2 * frame.child.num * l) % (frame.child.den + frame.child.num) := by
  unfold ChildFrame.tGrade
  rw [Int.emod_def, hb]
  ring

/-- The inputs of an even site are its horizontal neighbours: their `t`-grades are `t ∓ n`. -/
theorem even_inputs_tGrade (frame : ChildFrame) (z : Site) (he : EvenSite z) :
    frame.tGrade (FLatticePaper.incomingNeg z) = frame.tGrade z - frame.child.num ∧
      frame.tGrade (FLatticePaper.incomingPos z) = frame.tGrade z + frame.child.num := by
  have hneg : FLatticePaper.incomingNeg z = (z.1 - 1, z.2) := by
    unfold FLatticePaper.incomingNeg
    rw [if_pos he]
  have hpos : FLatticePaper.incomingPos z = (z.1 + 1, z.2) := by
    unfold FLatticePaper.incomingPos
    rw [if_pos he]
  rw [hneg, hpos]
  unfold ChildFrame.tGrade
  constructor <;> ring

/-- An even root with `t(z) ∈ [0, L − 1]` (`L = d + n`) and its two inputs lie in the zero band, when `d − n ≥ 4`. -/
theorem star_tBand_of_even_root (frame : ChildFrame) (hdn : frame.child.num + 4 ≤ frame.child.den) (z : Site)
    (he : EvenSite z) (ht1 : 0 ≤ frame.tGrade z)
    (ht2 : frame.tGrade z ≤ frame.child.den + frame.child.num - 1) :
    (3 - frame.child.den ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 3) ∧
      (3 - frame.child.den ≤ frame.tGrade (FLatticePaper.incomingNeg z) ∧
        frame.tGrade (FLatticePaper.incomingNeg z) ≤ frame.child.num + 2 * frame.child.den - 3) ∧
      (3 - frame.child.den ≤ frame.tGrade (FLatticePaper.incomingPos z) ∧
        frame.tGrade (FLatticePaper.incomingPos z) ≤ frame.child.num + 2 * frame.child.den - 3) := by
  obtain ⟨hn0, -, -, -, -⟩ := frame.child_facts
  obtain ⟨hN, hP⟩ := even_inputs_tGrade frame z he
  rw [hN, hP]
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- **The full star of an even root.** If `t(z) ∈ [0, L − 1]` and `d − n ≥ 4`, the short slip vanishes (for `η = ±1`) on the root and on
both of its physical inputs: the H full star of such a root has `D_± = 0`. -/
theorem slip_zero_on_even_star (frame : ChildFrame) (F : Field) (hS : frame.HasStrips F)
    (hdn : frame.child.num + 4 ≤ frame.child.den) {η : ℤ} (hη : η = 1 ∨ η = -1) (z : Site) (he : EvenSite z)
    (ht1 : 0 ≤ frame.tGrade z) (ht2 : frame.tGrade z ≤ frame.child.den + frame.child.num - 1) :
    frame.slip F η z = 0 ∧ frame.slip F η (FLatticePaper.incomingNeg z) = 0 ∧
      frame.slip F η (FLatticePaper.incomingPos z) = 0 := by
  obtain ⟨h0, h1, h2⟩ := star_tBand_of_even_root frame hdn z he ht1 ht2
  exact ⟨slip_eq_zero_of_tBand frame F hS hη z h0.1 h0.2,
    slip_eq_zero_of_tBand frame F hS hη _ h1.1 h1.2,
    slip_eq_zero_of_tBand frame F hS hη _ h2.1 h2.2⟩

/-- **The native even H endpoints.** For `b = ⌊2nl/L⌋` the endpoint `(2l − b, b)` is even with `t ∈ [0, L − 1]`, so its full star has
`D_± = 0` (with `d − n ≥ 4`). -/
theorem slip_zero_on_native_even_endpoint (frame : ChildFrame) (F : Field) (hS : frame.HasStrips F)
    (hdn : frame.child.num + 4 ≤ frame.child.den) {η : ℤ} (hη : η = 1 ∨ η = -1) (l b : ℤ)
    (hb : b = (2 * frame.child.num * l) / (frame.child.den + frame.child.num)) :
    frame.slip F η (2 * l - b, b) = 0 ∧ frame.slip F η (FLatticePaper.incomingNeg (2 * l - b, b)) = 0 ∧
      frame.slip F η (FLatticePaper.incomingPos (2 * l - b, b)) = 0 := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  have hL : 0 < frame.child.den + frame.child.num := by omega
  have he : EvenSite (2 * l - b, b) := by
    unfold EvenSite
    show (2 * l - b + b) % 2 = 0
    omega
  have ht := tGrade_even_endpoint frame l b hb
  have h0 := Int.emod_nonneg (2 * frame.child.num * l) hL.ne'
  have h1 := Int.emod_lt_of_pos (2 * frame.child.num * l) hL
  exact slip_zero_on_even_star frame F hS hdn hη (2 * l - b, b) he (by rw [ht]; exact h0)
    (by rw [ht]; omega)

end FLatticePaper.StrongHStrip
