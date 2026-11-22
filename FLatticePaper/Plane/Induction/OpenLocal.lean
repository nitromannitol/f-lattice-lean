import FLatticePaper.Plane.Induction.S1S2Window
import FLatticePaper.Plane.Induction.OpenInputsProof
import FLatticePaper.Plane.Induction.S3NoFort
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.RestrictedBellmanRank
import FLatticePaper.Plane.Induction.SlipPermits

/-! The open inputs of the induction, as named structures (task 38, item 3).

Everything else in the odometers theorem is proved inside: the conjugate packet is the induction hypothesis, the open
inputs `OpenInputs` and the packet follow from the three structures below, the S1 and S2 window follows from the base
range, the halo and the V arcs, and the S3 rank follows from the S3 no-fort inputs and the slip permits.

* `StarZoneInputs word`: the named inputs I1 and I2 of the star step (witnesses of the zone covering by roots and
  calibrated points, and the mirror branch `ε = −1` of I2, which the archive does not write out).
* `SheetLocalInputs word`: the named inputs I3 of the two sheets `A`, `C` of the conjugate (unit increments of the chain
  potential, and the variant local permits and restricted no-fort conditions). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The star-zone inputs I1 and I2 at a proper word: witnesses `R` (roots, with `Ψ ≥ 1`) and `G` (calibrated sites, with
`Ψ ≥ 0`) covering the two zones, and the mirror branch `ε = −1` of I2. -/
def StarZoneInputs (word : Word) : Prop :=
  ∃ R G : Site → Prop,
    (∀ c, R c → 1 ≤ sheetDiff word c) ∧ (∀ z, G z → 0 ≤ sheetDiff word z) ∧
    (∀ z ∈ (frameAt word).closedPolygon, 1 - (frameAt word).child.den ≤ (frameAt word).tGrade z →
      R z ∨ (∃ c, R c ∧ FLatticePaper.Edge z c) ∨ G z) ∧
    (∀ z ∈ (frameAt word).closedPolygon,
      (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 →
        R z ∨ (∃ c, R c ∧ FLatticePaper.Edge z c) ∨ G z) ∧
    ((frameAt word).eps = -1 → ∀ z ∈ (frameAt word).closedPolygon,
      (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 →
        (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z -
          (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z ≤ 0)

/-- The sheet inputs I3 at a proper word: unit increments of the chain potential `Ξ`, and the local permits and restricted
no-fort conditions of the sheets `A` and `C` of the conjugate standard field (the variant). -/
structure SheetLocalInputs (word : Word) : Prop where
  unit : ∀ c i : Site, FLatticePaper.Edge i c →
    -1 ≤ sheetChainPotential word (standardField (conjWord word)) i -
        sheetChainPotential word (standardField (conjWord word)) c ∧
      sheetChainPotential word (standardField (conjWord word)) i -
        sheetChainPotential word (standardField (conjWord word)) c ≤ 1
  permitA : PermitLocal (quarterTurnField (standardField (conjWord word)))
    (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
      sheetChainPotential word (standardField (conjWord word)) c)
  noA : RestrictedNoFort (quarterTurnField (standardField (conjWord word))) (i3aGrade word)
    (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
      sheetChainPotential word (standardField (conjWord word)) c)
  permitC : PermitLocal (quarterTurnField (standardField (conjWord word)))
    (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
      sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset))
  noC : RestrictedNoFort (quarterTurnField (standardField (conjWord word))) (frameAt word).tGrade
    (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
      sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset))

/-- `OpenInputs` at a proper word, from the star-zone inputs, the sheet inputs and the conjugate packet. -/
theorem openInputs_of_inputs {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hstar : StarZoneInputs word) (hsheet : SheetLocalInputs word) : OpenInputs word := by
  obtain ⟨K, hK⟩ := sheetDifference_identifies h hG
  obtain ⟨R, G, hR, hGd, cover1, cover2, mirror⟩ := hstar
  have hI1 := i1_of_root_stars h hG hsheet.unit hR hGd cover1
  have hI2 := i2_pos_of_root_stars h hG hsheet.unit hR hGd cover2
  have hI1' := openInput_one_of_chainBound h hG hK (fun z hz ht => by linarith [hK z, hI1 z hz ht])
  have hI2' := openInput_two_of_chainBound h hG hK (fun z hz hs =>
    ⟨fun he => by linarith [hK z, hI2 he z hz hs], fun he => by linarith [hK z, mirror he z hz hs]⟩)
  have hI3 := i3_binary_of_local_inputs h hG hsheet.unit hsheet.permitA hsheet.noA hsheet.permitC hsheet.noC
  unfold OpenInputs
  exact ⟨hI1', hI2', hI3.1⟩

/-- The packet of every standard field, by induction over words, from the star-zone and sheet inputs at the proper words. -/
theorem packet_standardField_of_inputs
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → SheetLocalInputs word) :
    ∀ word, (frameAt word).Packet (standardField word) := by
  refine word_induction (P := fun word => (frameAt word).Packet (standardField word)) ?_ ?_
  · intro k
    exact reciprocal_packet k
  · intro word hproper hIH
    have hop := openInputs_of_inputs hproper hIH (hstar word hproper) (hsheet word hproper)
    obtain ⟨hA0, hEq, hrefl, -⟩ := sheetFacts_of_conjPacket hproper hIH
    obtain ⟨hC0, hGe, hbin⟩ := hop
    have hP := (frameAt word).packet_of_sheets (Fp := quarterTurnField (standardField (conjWord word)))
      hA0 hC0 hEq hGe hrefl hbin
    rw [standardField_proper hproper]
    exact hP

/-- S1 and S2 at a proper word, from the star-zone and sheet inputs, the conjugate packet and the V arc inputs. -/
theorem S1S2_of_sheet_inputs (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hstar : StarZoneInputs word) (hsheet : SheetLocalInputs word)
    (arcs : VArcInputs (frameAt word) (standardField word)) :
    HasUnitSlip (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) ∧
      NoEvenSlipSaddle (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) := by
  have hop := openInputs_of_inputs hproper hG hstar hsheet
  obtain ⟨hA0, hEq, hrefl, -⟩ := sheetFacts_of_conjPacket hproper hG
  obtain ⟨hC0, hGe, hbin⟩ := hop
  obtain ⟨rankA, hrankA⟩ := constrainedRank_of_variant hproper hG (i3aGrade_deck hproper hG)
    (permitA_invariant hproper hG) hsheet.permitA hsheet.noA
  obtain ⟨rankC, hrankC⟩ := constrainedRank_of_variant hproper hG (tGrade_add_odd_deck word)
    (permitC_invariant hproper hG) hsheet.permitC hsheet.noC
  have hsewn := standardField_proper hproper
  have hS := (frameAt word).stripInputs_sheetMin hA0 hC0 hEq hGe hrefl
  have hH := hS.heightInputs
  obtain ⟨hagree, hper⟩ := (frameAt word).sewnField_spec ((frameAt word).respectsPeriodsOn_of_heightInputs hH)
  have hstrips := (frameAt word).hasStrips_of_stripInputs hS hagree hper
  have hreflF := (frameAt word).reflection_of_heightInputs hH hagree hper
  have hbinF := (frameAt word).binary_of_strips hper hagree hbin hstrips hreflF
  have hper0 := hasGeneratorPeriods_zero_u hper ((frameAt word).coherentConstantU_eq_zero)
  have hrecM := sheetMin_recurrentField_of_chain hproper hG hsheet.unit rankA rankC hrankA hrankC
  have hbinM := (sheetMin_binary_recurrent_of_chain hproper hG hsheet.unit rankA rankC hrankA hrankC).1
  rw [hsewn] at arcs ⊢
  have base := base_range_of_inputs (frameAt word) hS hagree hper0 hper hreflF hbinF hbinM hrecM arcs
  exact S1S2_of_base (frameAt word) (child_num_ge_three hproper) hS hagree hper0 hper hreflF hbinF base

/-- The three star estimates of a proper word: S1, S2, and the constrained rank. The slip permits are derived from S1, S2
and the binarity, up to the premise `OddBlackNoRise` (the one case of `PermitLocal` the local data do not exclude). -/
theorem starEstimates_of_inputs (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hpk : (frameAt word).Packet (standardField word))
    (hstar : StarZoneInputs word) (hsheet : SheetLocalInputs word)
    (arcs : VArcInputs (frameAt word) (standardField word))
    (hodd : OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hS3n : S3NoFortInputs (frameAt word) (standardField word)) :
    HasUnitSlip (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) ∧
      NoEvenSlipSaddle (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) ∧
      ∃ rank : Site → ℤ, IsConstrainedBurningRank (standardField word) rank
        (slipPermits (standardField word) (fun z => standardField word (z + (frameAt word).shortShift))) := by
  obtain ⟨hU, hNS⟩ := S1S2_of_sheet_inputs word hproper hG hstar hsheet arcs
  have hS3p := permitLocal_of_star_data (evenSite_shortShift (frameAt word)) hpk.binary hU hNS hodd
  have hno := restrictedNoFort_S3_of_inputs (frameAt word) hpk.periods hpk.binary hS3p hS3n
  obtain ⟨rank, hrank⟩ := S3_of_packet_restrictedNoFort word hpk hS3p hno
  exact ⟨hU, hNS, rank, hrank⟩

end FLatticePaper.Induction
