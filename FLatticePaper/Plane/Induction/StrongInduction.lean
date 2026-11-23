import FLatticePaper.Plane.Induction.StrongResidual
import FLatticePaper.Plane.Induction.WordInduction
import FLatticePaper.Plane.Induction.TwosInduction

/-! Task 40, step 3–4: the strong estimates of every word, by the word induction.

The step at a proper word `w` (not a two-power) takes the strong estimates of the conjugate word, the star-zone inputs and the arc
inputs of `w`, and the residual of `w`: the packet of `w` comes from the conjugate packet and the open inputs of `w`
(`packet_of_openInputs_step`), and `StrongEstimates.of_residual` assembles the rest. The two-powers and the pure words are the
base cases, given explicitly. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The packet of a word from the conjugate packet and the open inputs of the word (the step of `packet_standardField`). -/
theorem packet_of_openInputs_step {word : Word} (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word))) (hO : OpenInputs word) :
    (frameAt word).Packet (standardField word) := by
  obtain ⟨hA0, hEq, hrefl, -⟩ := sheetFacts_of_conjPacket hproper hG
  obtain ⟨hC0, hGe, hbin⟩ := hO
  have hP := (frameAt word).packet_of_sheets (Fp := quarterTurnField (standardField (conjWord word)))
    hA0 hC0 hEq hGe hrefl hbin
  rw [standardField_proper hproper]
  exact hP

/-- **The strong estimates of a proper word from those of its conjugate**, the star-zone and arc inputs of the word and its
residual. -/
theorem strongEstimates_step {word : Word} (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hstar : StarZoneInputs word) (harc : VArcInputs (frameAt word) (standardField word))
    (h : StrongEstimates (conjWord word)) (R : StrongResidual word) : StrongEstimates word := by
  have hsheet := i3_sheetLocalInputs_of_strong hproper h
  have hO := openInputs_of_inputs hproper h.packet hstar hsheet
  exact StrongEstimates.of_residual hproper (packet_of_openInputs_step hproper h.packet hO) hstar harc h R

/-- **The strong estimates of every word**, by the word induction from the pure words and the two-powers. -/
theorem strongEstimates_of_all
    (hpure : ∀ k : ℕ, StrongEstimates (List.replicate k Digit.three))
    (htwo : ∀ k : ℕ, StrongEstimates (List.replicate (k + 1) Digit.two))
    (hres : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → StrongResidual word)
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → StarZoneInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      VArcInputs (frameAt word) (standardField word)) :
    ∀ word : Word, StrongEstimates word := by
  refine word_induction (P := fun word => StrongEstimates word) hpure ?_
  intro word hproper ih
  by_cases hI : IsTwoPow word
  · obtain ⟨k, rfl⟩ := hI
    exact htwo k
  · exact strongEstimates_step hproper (hstar word hproper hI) (harc word hproper hI) ih (hres word hproper hI)

end FLatticePaper.Induction
