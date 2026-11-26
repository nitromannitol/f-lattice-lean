import FLatticePaper.Plane.Induction.W4NativeSlip
import FLatticePaper.Plane.Induction.StripsM
import FLatticePaper.Plane.Induction.TraceFromPsi
import FLatticePaper.Plane.Induction.BoundaryPair

/-! # The boundary set at the game's own word

The frame is `frameAt word` with the field `standardField word` (the game's pair, as in `TraceFromPsi.TraceAt word`).
* `standardField_zero_strip_word`: the zero strip of the word's own standard field (from `StripsM.stripInputs_M` at the game's `hSE`);
* `roundedSlip_freeH_word`: `J = 0` on the free H sites of `frameAt word` (the native zero, as `W4NativeSlip.conj_slip_zero_native_H`,
  transcribed to the word);
* `hPH_of_trace`: `P ≤ c₀` on free H with equality only at `H_0`, from `TraceAt word`;
* `minus_boundary_word`, `plus_boundary_word`: the boundary sets with only the V pattern named. -/

namespace FLatticePaper.WordBoundary

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem standardField_zero_strip_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {z : Site}
    (hlo : 1 - (frameAt word).child.den ≤ (frameAt word).tGrade z)
    (hhi : (frameAt word).tGrade z ≤ (frameAt word).child.num + 2 * (frameAt word).child.den - 1) :
    standardField word z = 0 :=
  (frameAt word).zero_strip (StripsM.stripInputs_M hw hSE)
    (fun _ hy => standardField_eq_sheetMin_of_strong hw hSE hy) (StripsM.hper_word hw hSE) z hlo hhi

/-- `J = 0` on the free H sites of the word's own frame, for `η = ±1`. -/
theorem roundedSlip_freeH_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {η : ℤ} (hη : η = 1 ∨ η = -1) {z : Site}
    (hz : z ∈ (frameAt word).freeH) :
    (frameAt word).roundedSlip (standardField word) η z = 0 := by
  obtain ⟨hA, hB⟩ := W4NativeSlip.freeH_strip_margin (frameAt word) hz
  have hz0 : standardField word z = 0 :=
    standardField_zero_strip_word hw hSE (by omega) (by omega)
  have hy : standardField word (z + η • (frameAt word).shortShift) = 0 := by
    refine standardField_zero_strip_word hw hSE ?_ ?_
    · rw [W4NativeSlip.tGrade_add_smul_shortShift]
      rcases hη with rfl | rfl <;> omega
    · rw [W4NativeSlip.tGrade_add_smul_shortShift]
      rcases hη with rfl | rfl <;> omega
  unfold ChildFrame.roundedSlip ChildFrame.slip
  rw [hz0, hy]
  norm_num

/-- `P ≤ c₀` on the free H sites, with equality only at `H_0`, from the trace of the word. -/
theorem hPH_of_trace {word : Word} (hTr : TraceFromPsi.TraceAt word) :
    ∀ h : Site, (frameAt word).freeH h → (frameAt word).price (standardField word) h ≤ (frameAt word).cutPrice ∧
      ((frameAt word).price (standardField word) h = (frameAt word).cutPrice →
        h = FLatticePaper.Induction.hFirst) := by
  intro h hh
  have ht := hTr h hh
  rw [ht]
  by_cases hH : h = ((1 : ℤ), (0 : ℤ))
  · rw [if_pos hH]
    exact ⟨by norm_num, fun _ => hH⟩
  · rw [if_neg hH]
    exact ⟨by omega, fun heq => absurd heq (by omega)⟩

/-- **The minus boundary set at the game's word.** Only the V pattern `hpat` is named. -/
theorem minus_boundary_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW : StrongEstimates word) (hTr : TraceFromPsi.TraceAt word)
    (r : ℤ)
    (hpat : ∀ k : ℕ, (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num →
      (frameAt word).roundedSlip (standardField word) (-1) (VChain.vpath (frameAt word) k) =
        if (k : ℤ) ≤ r then 0 else -1)
    (z : Site) (hz : z ∈ (frameAt word).closedPolygon) (hnot : ¬ (frameAt word).openRect z)
    (hK : (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
      (frameAt word).roundedSlip (standardField word) (-1) z) :
    z = FLatticePaper.Induction.hFirst ∨
      ∃ k : ℕ, (k : ℤ) ≤ r ∧ (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num ∧
        z = VChain.vpath (frameAt word) k :=
  BoundaryPair.minus_boundary_K (frameAt word) (standardField word) hW.packet r (hPH_of_trace hTr)
    (fun h hh => roundedSlip_freeH_word hw hSE (η := -1) (by norm_num) hh) hpat z hz hnot hK

/-- **The plus boundary set at the game's word.** Only the V pattern `hpat` is named. -/
theorem plus_boundary_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW : StrongEstimates word) (hTr : TraceFromPsi.TraceAt word)
    (r : ℤ)
    (hpat : ∀ k : ℕ, (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num →
      (frameAt word).roundedSlip (standardField word) 1 (VChain.vpath (frameAt word) k) =
        if (k : ℤ) ≤ (frameAt word).child.den + (frameAt word).child.num - r - 2 then 0 else 1)
    (z : Site)
    (hw' : (z.1 + ((frameAt word).child.num - (frameAt word).child.den),
        z.2 + ((frameAt word).child.num + (frameAt word).child.den)) ∈ (frameAt word).closedPolygon)
    (hnot : ¬ (frameAt word).openRect (z.1 + ((frameAt word).child.num - (frameAt word).child.den),
        z.2 + ((frameAt word).child.num + (frameAt word).child.den)))
    (hK : (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
      (frameAt word).roundedSlip (standardField word) 1 z) :
    z = FLatticePaper.Induction.hFirst ∨
      ∃ j : ℤ, -r - 1 ≤ j ∧ j ≤ -1 ∧ z = RowAt.vAt (frameAt word) j :=
  BoundaryPair.plus_boundary_K (frameAt word) (standardField word) hW.packet r (hPH_of_trace hTr)
    (fun h hh => roundedSlip_freeH_word hw hSE (η := 1) (by norm_num) hh) hpat z hw' hnot hK

end FLatticePaper.WordBoundary
