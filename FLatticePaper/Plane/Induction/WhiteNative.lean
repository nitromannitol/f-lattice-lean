import FLatticePaper.Plane.Induction.WhiteSheetPlus
import FLatticePaper.Plane.Induction.Sec3Monotone
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! # W2 of the white case of Q34: the native chart at a forced white (`ε = +1`, sign `+1`)

At a white `z` with `F z = FqW z` (an `A`-root) and a forced input `u`, the input `u` is an `A`-root (`WhiteSheetPlus.inputs_aroot_plus`),
and the native chart gives `D₊(u) ≤ D₊(z)` as soon as the forced edge is a retained edge of the parent at the chart points
(`Sec3Monotone.slip_le_of_retained`). The retained edge is the W1 identification: the forced input is the sheet pointer, and the
pointer is retained (`W1HagreeNonfree.sheetPolicyA_pointer_retained`). That identification is the named premise `hid` here; it is
the output of `WestException.sheetOut_forcedIn` with the square data `hsq` (the W1 assembly), in chart coordinates. -/

namespace FLatticePaper.WhiteNative

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet FLatticePaper.Sec3Shift

/-- **W2 (native chart, sign `+1`, `ε = +1`).** -/
theorem forced_native_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongCore word) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hε : (frameAt word).eps = 1) {z u : Site}
    (hF : laplacian (standardField word) z = 0) (hA : standardField word z = FqW word z)
    (hi : ∀ i : Site, (i = incomingNeg z ∨ i = incomingPos z) → i ∈ (frameAt word).closedPolygon)
    (hu : u = incomingNeg z ∨ u = incomingPos z)
    (hsw : z + sec3X word ∈ (frameAt word).closedPolygon)
    (hsu : u + sec3X word ∈ (frameAt word).closedPolygon)
    (hid : P.retained (zTurn (z + sec3X word - (frameAt word).sheetShift))
      (zTurn (u + sec3X word - (frameAt word).sheetShift))) :
    (frameAt word).slip (standardField word) 1 u ≤ (frameAt word).slip (standardField word) 1 z := by
  have hu' := WhiteSheetPlus.inputs_aroot_plus h hSE hε hF hA hi u hu
  exact FLatticePaper.Sec3Monotone.slip_le_of_retained h hW hSE P hA hu'.1 hsw hsu hid

end FLatticePaper.WhiteNative
