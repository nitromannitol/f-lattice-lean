import FLatticePaper.Plane.Induction.NegChart
import FLatticePaper.Plane.Induction.W1NonfreeHsq
import FLatticePaper.Plane.Induction.W1HagreeNonfree
import FLatticePaper.Plane.Induction.SheetPieces

/-! # The native chart of Q34, in the form of the note (sign `+1`, both phases)

Q34: at the `A`-contacts, `S(v) = F(v + σ) − A(v)` and `S = min(0, Ψ − 2)` in the native chart, since `A` is `σ`-periodic and
`C(v + σ) = C(v) − 2`. So with `v` and `v + σ` in the closed polygon, and `F = min(A, C)` there (`standardField_eq_sheetMin_of_strong`),

  `D₊(v) = F(v) − F(v + σ) = min(0, Ψ v) − min(0, Ψ v − 2)`,  with `Ψ = C − A`.

The map `Ψ ↦ min(0, Ψ) − min(0, Ψ − 2)` is at most `2` and nonincreasing, so `D₊(u) ≤ D₊(z)` when `Ψ z ≤ Ψ u`, and trivially when
`Ψ z ≤ 0` (then `D₊(z) = 2`). The monotonicity `Ψ z ≤ Ψ u` along a sheet-`A` edge is `W1NonfreeHsq.psi_mono` in standard coordinates,
so no reconciliation with the chart shift is needed (both phases). -/

namespace FLatticePaper.NativeQ34

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet FLatticePaper.W1Step

/-- `A` is `σ`-periodic and `C(x + σ) = C x − 2` (from `sheetA_sub_shortShift`, `sheetC_sub_shortShift`). -/
theorem sheet_add_shortShift {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    (frameAt word).sheetA (FqW word) ((x + (frameAt word).shortShift)) = (frameAt word).sheetA (FqW word) x ∧
      (frameAt word).sheetC (FqW word) ((x + (frameAt word).shortShift)) = (frameAt word).sheetC (FqW word) x - 2 := by
  have hA := sheetA_sub_shortShift h hSE (x + (frameAt word).shortShift)
  have hC := sheetC_sub_shortShift h hSE (x + (frameAt word).shortShift)
  rw [add_sub_cancel_right] at hA hC
  simp only [FqW]
  exact ⟨hA.symm, by omega⟩

/-- **The native identity.** -/
theorem slip_native_identity {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {z : Site}
    (hz : z ∈ (frameAt word).closedPolygon) (hzs : z + (frameAt word).shortShift ∈ (frameAt word).closedPolygon) :
    (frameAt word).slip (standardField word) 1 z =
      min 0 (sheetPsi word z) - min 0 (sheetPsi word z - 2) := by
  unfold ChildFrame.slip
  rw [one_smul, standardField_eq_sheetMin_of_strong h hSE hz,
    standardField_eq_sheetMin_of_strong h hSE hzs]
  unfold ChildFrame.sheetMin sheetPsi
  obtain ⟨hA, hC⟩ := sheet_add_shortShift h hSE z
  simp only [FqW] at *
  rw [hA, hC]
  omega

/-- **The native step, sign `+1`:** if `Ψ z ≤ Ψ u` (a sheet-`A` edge), then `D₊(u) ≤ D₊(z)`. -/
theorem slip_native_le {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {z u : Site}
    (hz : z ∈ (frameAt word).closedPolygon) (hzs : z + (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hu : u ∈ (frameAt word).closedPolygon) (hus : u + (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hΨ : sheetPsi word z ≤ sheetPsi word u) :
    (frameAt word).slip (standardField word) 1 u ≤ (frameAt word).slip (standardField word) 1 z := by
  rw [slip_native_identity h hSE hu hus, slip_native_identity h hSE hz hzs]
  omega

/-- **The native step, sign `+1`, when `Ψ z ≤ 0`:** `D₊(z) = 2`, the maximum, so the claim is trivial. -/
theorem slip_native_le_of_nonpos {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {z u : Site}
    (hz : z ∈ (frameAt word).closedPolygon) (hzs : z + (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hu : u ∈ (frameAt word).closedPolygon) (hus : u + (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hΨz : sheetPsi word z ≤ 0) :
    (frameAt word).slip (standardField word) 1 u ≤ (frameAt word).slip (standardField word) 1 z := by
  rw [slip_native_identity h hSE hu hus, slip_native_identity h hSE hz hzs]
  omega


/-- **The native white at a forced edge, sign `+1`, with the W1 identification in its `sheetOut` form.** The forced input `u` of
`z` is the sheet arrow `sheetOut P lv centre (sheetPsi word) z` (`WestException.sheetOut_forcedIn`). If `Ψ z ≤ 0` the claim is
trivial; if `Ψ z ≥ 0` the arrow is the `A`-pointer, which is a sheet-`A` edge, and `psi_mono` gives `Ψ z ≤ Ψ u`. No chart shift
enters: both endpoints are evaluated in standard coordinates. -/
theorem native_sign_plus_of_sheetOut {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {z u : Site}
    (hz : z ∈ (frameAt word).closedPolygon) (hzs : z + (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hu : u ∈ (frameAt word).closedPolygon) (hus : u + (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hout : sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) z = u) :
    (frameAt word).slip (standardField word) 1 u ≤ (frameAt word).slip (standardField word) 1 z := by
  by_cases hΨ : sheetPsi word z ≤ 0
  · exact slip_native_le_of_nonpos h hSE hz hzs hu hus hΨ
  · have hpos : 0 ≤ sheetPsi word z := by omega
    have hbin : ∀ x, laplacian (standardField (conjWord word)) x = -1 ∨ laplacian (standardField (conjWord word)) x = 0 :=
      fun x => hSE.packet.binary x
    have hlv : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
    have hA : sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) z =
        FLatticePaper.W1Pointers.pointerOf (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift) z := by
      unfold sheetOut
      rw [if_pos hpos]
    have hp := FLatticePaper.W1HagreeNonfree.sheetPolicyA_pointer_retained P.toOldPolicyWitness.toOldPolicyData hbin
      (frameAt word).sheetShift hlv z
    rw [← hA, hout] at hp
    have hmono := FLatticePaper.W1NonfreeHsq.psi_mono h hSE P.toOldPolicyWitness.toOldPolicyData hp
    exact slip_native_le h hSE hz hzs hu hus hmono

end FLatticePaper.NativeQ34
