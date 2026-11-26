import FLatticePaper.Plane.Induction.NativeMinus
import FLatticePaper.Plane.Induction.NativeQ34
import FLatticePaper.Plane.Induction.FreePermitted

/-! # The native chart of the forced permit, in the `slipPermits` form

Sign −1 at a centre with `Ψ ≥ 0` needs only the native memberships (`z − σ`, `u − σ` in the polygon); sign +1 at any centre needs the
sheet pointer identity `sheetOut P z = u` and the native memberships `z + σ`, `u + σ`. These are the two native charts of the forced permit. -/

namespace FLatticePaper.PermitNative

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreePermitted

/-- **The native sign −1 permit at a nonnegative centre.** -/
theorem permit_minus_native {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {z u : Site}
    (hz : z ∈ (frameAt word).closedPolygon) (hzs : z - (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hu : u ∈ (frameAt word).closedPolygon) (hus : u - (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hΨ : 0 ≤ FLatticePaper.W1Step.sheetPsi word z) :
    slipPermits (standardField word) (fun x => standardField word (x + (-1 : ℤ) • (frameAt word).shortShift)) z u :=
  (slipPermits_iff_slip (-1) z u).mpr (NativeMinus.native_sign_minus_of_nonneg h hSE hz hzs hu hus hΨ)

/-- **The native sign +1 permit under the sheet pointer identity.** -/
theorem permit_plus_native {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps)
    {z u : Site}
    (hz : z ∈ (frameAt word).closedPolygon) (hzs : z + (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hu : u ∈ (frameAt word).closedPolygon) (hus : u + (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hout : FLatticePaper.W1Step.sheetOut P (frameAt word).sheetShift (frameAt word).centre
      (FLatticePaper.W1Step.sheetPsi word) z = u) :
    slipPermits (standardField word) (fun x => standardField word (x + (1 : ℤ) • (frameAt word).shortShift)) z u :=
  (slipPermits_iff_slip 1 z u).mpr (NativeQ34.native_sign_plus_of_sheetOut h hSE P hz hzs hu hus hout)

end FLatticePaper.PermitNative
