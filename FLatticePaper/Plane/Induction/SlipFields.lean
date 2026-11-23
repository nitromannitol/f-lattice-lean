import FLatticePaper.Plane.Induction.S1S2Window
import FLatticePaper.Plane.Induction.I3CSheet

/-! Task 40, step 1: the slip fields of `StrongEstimates u` from its own inputs.

`S1S2_standardField` takes `LocalPremises` only through its open inputs `I1, I2` (the `OpenInputs` triple), the unit increments
`I3` and the two constrained ranks `I3`; its S1 and S2 clauses are not used. Here these are supplied directly: `OpenInputs u`
from the star-zone and sheet inputs, the sheet unit increments and the two constrained ranks from the strong data of the
conjugate word. The result is the unit slip, the no-even-saddle condition and the slip range `0 ≤ D ≤ 2` on the closed polygon. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The `A`-sheet constrained rank of the word, from the strong data of the conjugate word (the policy of phase `eps(word)`). -/
theorem i3_constrainedRank_A {word : Word} (h : StrongEstimates (conjWord word)) :
    ∃ rank : Site → ℤ, IsConstrainedBurningRank (quarterTurnField (standardField (conjWord word))) rank
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c) := by
  have hη := (frameAt word).eps_unit
  obtain ⟨policy, hq, hmono, hrank⟩ := h.F2F3_policy (frameAt word).eps hη
  obtain ⟨rk, lam, hlam, hstrict, -, -⟩ := hrank 1 1 zero_lt_one zero_lt_one
  have hbin : ∀ c, laplacian (quarterTurnField (standardField (conjWord word))) c = -1 ∨
      laplacian (quarterTurnField (standardField (conjWord word))) c = 0 :=
    fun c => quarterTurnField_binary h.packet.binary c
  have hT := i3_retainQuota_quarterTurn _ policy hq
  have hcon_T := isConstrainedBurningRank_of_strict_quota (rank := fun x => rk (i3Z x)) hbin hT
    (fun c i _ hp => hstrict _ _ hp)
  have hle : ∀ c i, (fun c i => policy (i3Z c) (i3Z i)) c i →
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c) c i := by
    intro c i hp
    show sheetChainPotential word (standardField (conjWord word)) i ≤
      sheetChainPotential word (standardField (conjWord word)) c
    rw [i3_sheet_eq_chainPotential, i3_sheet_eq_chainPotential]
    exact hmono (i3Z c) (i3Z i) hp
  exact ⟨fun x => rk (i3Z x), IsConstrainedBurningRank.mono hcon_T hle⟩

/-- The `C`-sheet constrained rank of the word, from the reflected chain rank of the conjugate word's strong data. -/
theorem i3_constrainedRank_C {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (h : StrongEstimates (conjWord word)) :
    ∃ rank : Site → ℤ, IsConstrainedBurningRank (quarterTurnField (standardField (conjWord word))) rank
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset)) := by
  have hη := (frameAt word).eps_unit
  obtain ⟨cp, hmH, hqH, hrank⟩ := h.chain_data (frameAt word).eps hη
  obtain ⟨K', hid⟩ := i3_chainSheet_identity hw h.packet
  have he := i3_evenSite_sheetOffset word
  have hsl : ∀ c, laplacian (fun x => (frameAt word).siblingSlope (x + (frameAt word).sheetOffset)) c = 0 :=
    fun c => i3_laplacian_siblingSlope_shift (frameAt word) _ c
  have hlap := fun c => i3_laplacian_shift_of_identity he hsl hid c
  have hT := i3_retainQuota_shift_Z (R := ReflectedPolicy (frameAt (conjWord word)).centre
    ((frameAt word).eps • (frameAt (conjWord word)).shortShift - (frameAt (conjWord word)).parentShift) cp) he hlap hqH
  obtain ⟨rk, lam, hlam, hstrict, -, -⟩ := hrank 1 1 zero_lt_one zero_lt_one
  have hbin : ∀ c, laplacian (quarterTurnField (standardField (conjWord word))) c = -1 ∨
      laplacian (quarterTurnField (standardField (conjWord word))) c = 0 :=
    fun c => quarterTurnField_binary h.packet.binary c
  have hcon_T := isConstrainedBurningRank_of_strict_quota
    (rank := fun x => rk (i3Z (x + (frameAt word).sheetOffset))) hbin hT (fun c i _ hp => hstrict _ _ hp)
  have hle : ∀ c i, (fun c i => ReflectedPolicy (frameAt (conjWord word)).centre
      ((frameAt word).eps • (frameAt (conjWord word)).shortShift - (frameAt (conjWord word)).parentShift) cp
      (i3Z (c + (frameAt word).sheetOffset)) (i3Z (i + (frameAt word).sheetOffset))) c i →
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset)) c i := by
    intro c i hp
    show sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
      sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset)
    rw [i3_sheet_eq_chainPotential, i3_sheet_eq_chainPotential]
    exact hmH (i3Z (c + (frameAt word).sheetOffset)) (i3Z (i + (frameAt word).sheetOffset)) hp
  exact ⟨fun x => rk (i3Z (x + (frameAt word).sheetOffset)), IsConstrainedBurningRank.mono hcon_T hle⟩

/-- **The slip fields from the open inputs**: the S1S2 argument of `S1S2_standardField`, with the inputs given directly. -/
theorem S1S2_of_openInputs (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hOpen : OpenInputs word)
    (hunit : ∀ c i : Site, FLatticePaper.Edge i c →
      -1 ≤ sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ∧
        sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ≤ 1)
    (hA : ∃ rankA : Site → ℤ, IsConstrainedBurningRank (quarterTurnField (standardField (conjWord word))) rankA
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c))
    (hC : ∃ rankC : Site → ℤ, IsConstrainedBurningRank (quarterTurnField (standardField (conjWord word))) rankC
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset)))
    (arcs : VArcInputs (frameAt word) (standardField word)) :
    HasUnitSlip (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) ∧
      NoEvenSlipSaddle (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) ∧
      ∀ z ∈ (frameAt word).closedPolygon,
        0 ≤ starDiff (standardField word) (frameAt word).shortShift z ∧
          starDiff (standardField word) (frameAt word).shortShift z ≤ 2 := by
  obtain ⟨hA0, hEq, hrefl, -⟩ := sheetFacts_of_conjPacket hproper hG
  obtain ⟨hC0, hGe, hbin⟩ := hOpen
  obtain ⟨rankA, hrankA⟩ := hA
  obtain ⟨rankC, hrankC⟩ := hC
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
  have h := S1S2_of_base (frameAt word) (child_num_ge_three hproper) hS hagree hper0 hper hreflF hbinF base
  exact ⟨h.1, h.2, base⟩

/-- **The slip fields of the strong estimates of a word**, from the star-zone inputs of the word, the strong data of the conjugate
word and the arc inputs: the unit slip, the no-even-saddle condition and the slip range in the form of `StrongEstimates`. -/
theorem i3_slipFields_of_strong {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (h : StrongEstimates (conjWord word)) (hstar : StarZoneInputs word)
    (arcs : VArcInputs (frameAt word) (standardField word)) :
    HasUnitSlip (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) ∧
      NoEvenSlipSaddle (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) ∧
      ∀ z ∈ (frameAt word).closedPolygon,
        0 ≤ (frameAt word).slip (standardField word) 1 z ∧ (frameAt word).slip (standardField word) 1 z ≤ 2 := by
  have hsheet := i3_sheetLocalInputs_of_strong hw h
  obtain ⟨h1, h2, h3⟩ := S1S2_of_openInputs word hw h.packet (openInputs_of_inputs hw h.packet hstar hsheet)
    hsheet.unit (i3_constrainedRank_A h) (i3_constrainedRank_C hw h) arcs
  refine ⟨h1, h2, fun z hz => ?_⟩
  have hs : (frameAt word).slip (standardField word) 1 z =
      starDiff (standardField word) (frameAt word).shortShift z := by
    unfold ChildFrame.slip starDiff
    rw [one_smul]
  rw [hs]
  exact h3 z hz

end FLatticePaper.Induction
