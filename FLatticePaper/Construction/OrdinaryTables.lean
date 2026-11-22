import FLatticePaper.Construction.OrdinaryComparisons

/-! The written case tables of the ordinary standard (task 41, supplement Part II section II and
ALL_PROPER_UNC_STANDARD_NOMINAL_PRICES section 1).

The insertion order of the six copies (Part II, the table of the actual positioned insertion order), and the origins
and slopes of the odd standard placements in phase 0 and phase 1. The 1-based slot numbers of the paper are the
0-based `Fin 6` slots here. -/

namespace FLatticePaper.Construction

open Farey

/-- Part II table: an odd standard is inserted in the order `1,2,5,6,3,4` (here `0,1,4,5,2,3`). -/
theorem insertion_order_odd_standard : (0 :: afterFirstStandard .odd) = [0, 1, 4, 5, 2, 3] := rfl

/-- Part II table: an even standard is inserted in the order `1,3,4,2,5,6` (here `0,2,3,1,4,5`). -/
theorem insertion_order_even_standard : (0 :: afterFirstStandard .even) = [0, 2, 3, 1, 4, 5] := rfl

/-- The odd standard placements in phase 0 (ALL_PROPER_UNC_STANDARD_NOMINAL_PRICES section 1, the W0 row):
origins `0, Z, 2C+V_C, 2C+V_C+Z, 2Z, V_Z` and slopes `0, 0, b_C, b_C, 0, b_Z`, where `Z` is the even parent's kernel,
`C` the odd parent's kernel, and `V_C`, `V_Z` the transverse jets. -/
theorem standardJets_odd_phase0 (word : Word) (h : phase word = 0) :
    standardJets word .odd 0 = (0, 0) ∧
    standardJets word .odd 1 = kernelJet (parentsAt word).even ∧
    standardJets word .odd 2 = 2 • kernelJet (parentsAt word).odd + transverseJet (parentsAt word).odd ∧
    standardJets word .odd 3 =
      (2 • kernelJet (parentsAt word).odd + transverseJet (parentsAt word).odd) + kernelJet (parentsAt word).even ∧
    standardJets word .odd 4 = 2 • kernelJet (parentsAt word).even ∧
    standardJets word .odd 5 = transverseJet (parentsAt word).even := by
  simp [standardJets, doubleFirst, h, Prod.ext_iff]

/-- The odd standard placements in phase 1 (the W1 row): origins `2C, 2C+Z, V_C, V_C+Z, 0, 2Z+V_Z`. -/
theorem standardJets_odd_phase1 (word : Word) (h : phase word ≠ 0) :
    standardJets word .odd 0 = 2 • kernelJet (parentsAt word).odd ∧
    standardJets word .odd 1 = 2 • kernelJet (parentsAt word).odd + kernelJet (parentsAt word).even ∧
    standardJets word .odd 2 = transverseJet (parentsAt word).odd ∧
    standardJets word .odd 3 = transverseJet (parentsAt word).odd + kernelJet (parentsAt word).even ∧
    standardJets word .odd 4 = 0 ∧
    standardJets word .odd 5 = 2 • kernelJet (parentsAt word).even + transverseJet (parentsAt word).even := by
  simp [standardJets, doubleFirst, h]

end FLatticePaper.Construction
