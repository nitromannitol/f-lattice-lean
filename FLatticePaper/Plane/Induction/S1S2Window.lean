import FLatticePaper.Plane.Induction.BaseHalo
import FLatticePaper.Plane.Induction.BaseRecurrent
import FLatticePaper.Plane.Induction.LocalPremises
import FLatticePaper.Plane.Induction.ChildNumerator

/-! S1 and S2 for the standard field of a proper word (task 37, item 4).

The chain is: the sheet facts and the open inputs of the word come from the conjugate packet and the local premises
(`sheetFacts_of_conjPacket`, `openInputs_of_localPremises`); the sheet minimum `M` has its zero strip, binarity and
recurrence in the fort form (`stripInputs_sheetMin`, `sheetMin_binary_recurrent_of_chain`,
`sheetMin_recurrentField_of_chain`); the sewn field `F` has its periods, reflection and binarity from `M`
(`sewnField_spec`, `reflection_of_heightInputs`, `binary_of_strips`). Then `base_range_of_inputs` gives `D ∈ [0, 2]` on
`E`, and `S1S2_of_base` gives the halo range and S1, S2.

The signature shows what remains open:
* `hLP` — the local premises of the word, used for the open inputs `I1, I2` and the ranks `I3` only; their S1 and S2
  clauses are not used (they are now derived);
* `arcs` — the range `D ∈ {0, 1, 2}` on the V arcs, the one step not formalized (archive: ANCESTRAL_PSI_V_CUT_PROOF). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The periods with constant `0` in the `U` direction, from the periods with a constant `cU = 0`. -/
theorem hasGeneratorPeriods_zero_u {fraction : Fraction} {F : Field} {cU cV : ℤ}
    (h : HasGeneratorPeriods fraction F cU cV) (hU : cU = 0) : HasGeneratorPeriods fraction F 0 cV :=
  ⟨fun site => by rw [h.1 site, hU], h.2⟩

theorem S1S2_standardField (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hLP : LocalPremises word)
    (arcs : VArcInputs (frameAt word) (standardField word)) :
    HasUnitSlip (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) ∧
      NoEvenSlipSaddle (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) := by
  obtain ⟨hA0, hEq, hrefl, -⟩ := sheetFacts_of_conjPacket hproper hG
  obtain ⟨hC0, hGe, hbin⟩ := openInputs_of_localPremises hproper hG hLP
  dsimp only [LocalPremises] at hLP
  obtain ⟨-, -, hunit, ⟨rankA, hrankA⟩, ⟨rankC, hrankC⟩, -, -, -, -, -⟩ := hLP
  have hsewn := standardField_proper hproper
  have hS := (frameAt word).stripInputs_sheetMin hA0 hC0 hEq hGe hrefl
  have hH := hS.heightInputs
  obtain ⟨hagree, hper⟩ := (frameAt word).sewnField_spec ((frameAt word).respectsPeriodsOn_of_heightInputs hH)
  have hstrips := (frameAt word).hasStrips_of_stripInputs hS hagree hper
  have hreflF := (frameAt word).reflection_of_heightInputs hH hagree hper
  have hbinF := (frameAt word).binary_of_strips hper hagree hbin hstrips hreflF
  have hper0 := hasGeneratorPeriods_zero_u hper ((frameAt word).coherentConstantU_eq_zero)
  have hrecM := sheetMin_recurrentField_of_chain hproper hG hunit rankA rankC hrankA hrankC
  have hbinM := (sheetMin_binary_recurrent_of_chain hproper hG hunit rankA rankC hrankA hrankC).1
  rw [hsewn] at arcs ⊢
  have base := base_range_of_inputs (frameAt word) hS hagree hper0 hper hreflF hbinF hbinM hrecM arcs
  exact S1S2_of_base (frameAt word) (child_num_ge_three hproper) hS hagree hper0 hper hreflF hbinF base

end FLatticePaper.Induction
