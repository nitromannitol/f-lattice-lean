import FLatticePaper.Plane.Induction.HarmWrap
import FLatticePaper.Plane.Induction.ParentStepDischarge
import FLatticePaper.Plane.Induction.StrongInduction

/-! Task 50, part 1: the strong induction without star-zone inputs or arc inputs as hypotheses.

The open inputs `OpenInputs word` of a proper word are the I1 zone cover (`I1_of_strong`), the I2 harmonic band
(`I2_of_strong`) and the I3 binarity (`i3_binary_of_local_inputs` on `i3_sheetLocalInputs_of_strong`), all from the strong
estimates of the conjugate word alone. The V arc inputs of the word come from the same data (`vArcInputs_of_strong_discharged`),
and the slip fields and the star estimates follow. So the induction step needs only `StrongEstimates (conjWord word)` and the
residual `StrongResidual word`.

The existing chain through `StarZoneInputs` (`strongEstimates_step`) is kept unchanged. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **The open inputs of a proper word from the strong estimates of its conjugate**: I1, I2 and the I3 binarity. -/
theorem openInputs_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) : OpenInputs word := by
  have hsheet := i3_sheetLocalInputs_of_strong h hS
  have hI3 := i3_binary_of_local_inputs h hS.packet hsheet.unit hsheet.permitA hsheet.noA hsheet.permitC hsheet.noC
  unfold OpenInputs
  refine ⟨fun z hz ht => ZoneI1.I1_of_strong h hS z hz ht, fun z hz hs => ?_, hI3.1⟩
  by_cases he : (frameAt word).eps = 1
  · rw [if_pos he]
    exact (HarmWrap.I2_of_strong h hS z hz hs).1 he
  · rw [if_neg he]
    exact (HarmWrap.I2_of_strong h hS z hz hs).2 ((frameAt word).eps_unit.resolve_left he)

/-- **The arc inputs of a proper word from the strong estimates of its conjugate**: the sheet minimum has the strip and height
inputs, the standard field is its sewing, and the V arc range follows (`vArcInputs_of_strong_discharged`). -/
theorem arcInputs_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) : VArcInputs (frameAt word) (standardField word) := by
  have hO := openInputs_of_strong h hS
  obtain ⟨hA0, hEq, hrefl, -⟩ := sheetFacts_of_conjPacket h hS.packet
  obtain ⟨hC0, hGe, -⟩ := hO
  have hSt := (frameAt word).stripInputs_sheetMin hA0 hC0 hEq hGe hrefl
  have hH := hSt.heightInputs
  obtain ⟨hagree, hper⟩ :=
    (frameAt word).sewnField_spec ((frameAt word).respectsPeriodsOn_of_heightInputs hH)
  have h0 := (frameAt word).coherentConstantU_eq_zero
  rw [standardField_proper h]
  refine vArcInputs_of_strong_discharged h hS hSt hH hagree ?_
  have hper' := hper
  rw [h0] at hper' ⊢
  exact hper'

/-- **The slip fields of a proper word from the strong estimates of its conjugate and the arc inputs**: the unit slip, the
no-even-saddle condition and the slip range, as `StrongEstimates` states them. -/
theorem slipFields_of_strong {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (h : StrongEstimates (conjWord word))
    (arcs : VArcInputs (frameAt word) (standardField word)) :
    HasUnitSlip (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) ∧
      NoEvenSlipSaddle (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) ∧
      ∀ z ∈ (frameAt word).closedPolygon,
        0 ≤ (frameAt word).slip (standardField word) 1 z ∧ (frameAt word).slip (standardField word) 1 z ≤ 2 := by
  have hsheet := i3_sheetLocalInputs_of_strong hw h
  obtain ⟨h1, h2, h3⟩ := S1S2_of_openInputs word hw h.packet (openInputs_of_strong hw h) hsheet.unit
    (i3_constrainedRank_A h) (i3_constrainedRank_C hw h) arcs
  refine ⟨h1, h2, fun z hz => ?_⟩
  have hs : (frameAt word).slip (standardField word) 1 z =
      starDiff (standardField word) (frameAt word).shortShift z := by
    unfold ChildFrame.slip starDiff
    rw [one_smul]
  rw [hs]
  exact h3 z hz

/-- **The strong estimates of a proper word from those of its conjugate and its residual**: no star-zone or arc inputs. -/
theorem strongEstimates_step_strong {word : Word} (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (h : StrongEstimates (conjWord word)) (R : StrongResidual word) : StrongEstimates word :=
  { packet := packet_of_openInputs_step hproper h.packet (openInputs_of_strong hproper h)
    slipRange := (slipFields_of_strong hproper h (arcInputs_of_strong hproper h)).2.2
    priceRange := R.priceRange
    priceDrift := R.priceDrift
    slipDrift := R.slipDrift
    zeroStripInterval := R.zeroStripInterval
    zeroEvenLine := R.zeroEvenLine
    F1_unitSlip := (slipFields_of_strong hproper h (arcInputs_of_strong hproper h)).1
    F1_noSlipSaddle := (slipFields_of_strong hproper h (arcInputs_of_strong hproper h)).2.1
    F1_unitPrice := R.F1_unitPrice
    F1_noPriceSaddle := R.F1_noPriceSaddle
    F2F3_policy := R.F2F3_policy }

/-- **The strong estimates of every word from the pure words, the two-powers and the residuals**, by the word induction. -/
theorem strongEstimates_of_residual_all
    (hpure : ∀ k : ℕ, StrongEstimates (List.replicate k Digit.three))
    (htwo : ∀ k : ℕ, StrongEstimates (List.replicate (k + 1) Digit.two))
    (hres : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → StrongResidual word) :
    ∀ word : Word, StrongEstimates word := by
  refine word_induction (P := fun word => StrongEstimates word) hpure ?_
  intro word hproper ih
  by_cases hI : IsTwoPow word
  · obtain ⟨k, rfl⟩ := hI
    exact htwo k
  · exact strongEstimates_step_strong hproper ih (hres word hproper hI)

end FLatticePaper.Induction
