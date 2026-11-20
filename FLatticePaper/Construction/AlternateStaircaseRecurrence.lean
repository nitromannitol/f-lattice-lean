import FLatticePaper.Construction.AlternateStaircaseRank
import FLatticePaper.Construction.AlternateStaircaseRotation

namespace FLatticePaper.Construction

open Farey

/-- The centered B4 mask is recurrent after the physical harmonic quarter-turn. -/
theorem stairOddAlt_exists_recurrent_extension {den : ℤ} (hden : BaseMask.stairOddAlt.Valid den) :
    ∃ field : Field,
      ((BaseMask.stairOddAlt.tile den hden).llCenter (BaseMask.stairOddAlt.tile_nonempty den hden)).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den).rotate field (-1) (stairOddConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).rotate.matrix ∧ Superharmonic field ∧ Recurrent field := by
  obtain ⟨field, hagree, hperiod, _, hsuper, hrec⟩ := stairEvenAlt_exists_recurrent_extension hden
  have hrot := rotateStaircaseField_periods hden.2 hperiod
  rw [show den + (stairEvenConstantV den - 1) + chooseTwo (den + 1) = -1 by
    unfold stairEvenConstantV; omega, centeredQuarterTurnCorrection_nearOne_transverse, sub_zero] at hrot
  exact ⟨rotateStaircaseField den field, BaseMask.stairOddAlt_agrees_rotateStaircaseField hden hagree,
    hrot, generator_periods_growth (staircase_rotate_inUnitInterval hden.1 hden.2) hrot,
    rotateStaircaseField_recurrent hden.2 hrec hsuper⟩

/-- The root's even alternate has a recurrent extension in the restored physical chart. -/
theorem evaluateNative_empty_even_alternate_recurrent :
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative [] = .ok registers ∧
      registers.alternate.currentEven.val.Agrees (fun site => field (site + (-2, -1))) 0 ∧
      HasGeneratorPeriods ((parentsAt []).current .even) field 0 (stairEvenConstantV 3 - 1) ∧
      HasQuadraticGrowth field ((parentsAt []).current .even).matrix ∧ Superharmonic field ∧ Recurrent field := by
  have hvalid : BaseMask.stairEvenAlt.Valid 3 := by simp [BaseMask.Valid]
  obtain ⟨field, hagree, hperiod, hgrowth, hsuper, hrec⟩ := stairEvenAlt_exists_recurrent_extension hvalid
  exact ⟨BaseRun.empty.registers.llCenter, field, evaluateNative_base .empty,
    BaseMask.stairEvenAlt_llCenter_agrees hvalid hagree, hperiod, hgrowth, hsuper, hrec⟩

theorem evaluateNative_threes_even_alternate_recurrent (extra : ℕ) :
    let word := (BaseRun.threes extra).word
    let den : ℤ := 2 * (extra : ℤ) + 3 + 2
    let fraction := (parentsAt word).current .even
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧
      registers.alternate.currentEven.val.Agrees (fun site => field (site + (1 - den, -1))) 0 ∧
      HasGeneratorPeriods fraction field 0 (stairEvenConstantV den - 1) ∧
      HasQuadraticGrowth field fraction.matrix ∧ Superharmonic field ∧ Recurrent field := by
  dsimp only
  rw [threes_current_even]
  have hvalid : BaseMask.stairEvenAlt.Valid (2 * (extra : ℤ) + 3 + 2) := by
    change 3 ≤ 2 * (extra : ℤ) + 3 + 2 ∧ (2 * (extra : ℤ) + 3 + 2) % 2 = 1
    omega
  obtain ⟨field, hagree, hperiod, hgrowth, hsuper, hrec⟩ := stairEvenAlt_exists_recurrent_extension hvalid
  exact ⟨(BaseRun.threes extra).registers.llCenter, field, evaluateNative_base _,
    BaseMask.stairEvenAlt_llCenter_agrees hvalid hagree, hperiod, hgrowth, hsuper, hrec⟩

/-- The centered odd alternate at the root has a recurrent physical plane extension. -/
theorem evaluateNative_empty_odd_alternate_recurrent :
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative [] = .ok registers ∧ registers.alternate.currentOdd.val.Agrees field 0 ∧
      HasGeneratorPeriods ((parentsAt []).current .odd) field (-1) (stairOddConstantV 3) ∧
      HasQuadraticGrowth field ((parentsAt []).current .odd).matrix ∧ Superharmonic field ∧ Recurrent field := by
  have hvalid : BaseMask.stairOddAlt.Valid 3 := by simp [BaseMask.Valid]
  obtain ⟨field, hagree, hperiod, hgrowth, hsuper, hrec⟩ := stairOddAlt_exists_recurrent_extension hvalid
  exact ⟨BaseRun.empty.registers.llCenter, field, evaluateNative_base .empty, hagree, hperiod, hgrowth, hsuper, hrec⟩

theorem evaluateNative_twos_odd_alternate_recurrent (extra : ℕ) :
    let word := (BaseRun.twos extra).word
    let fraction := (parentsAt word).current .odd
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.alternate.currentOdd.val.Agrees field 0 ∧
      HasGeneratorPeriods fraction field (-1) (stairOddConstantV (2 * (extra : ℤ) + 3 + 2)) ∧
      HasQuadraticGrowth field fraction.matrix ∧ Superharmonic field ∧ Recurrent field := by
  dsimp only
  rw [twos_current_odd]
  have hvalid : BaseMask.stairOddAlt.Valid (2 * (extra : ℤ) + 3 + 2) := by
    change 3 ≤ 2 * (extra : ℤ) + 3 + 2 ∧ (2 * (extra : ℤ) + 3 + 2) % 2 = 1
    omega
  obtain ⟨field, hagree, hperiod, hgrowth, hsuper, hrec⟩ := stairOddAlt_exists_recurrent_extension hvalid
  exact ⟨(BaseRun.twos extra).registers.llCenter, field, evaluateNative_base _, hagree, hperiod, hgrowth, hsuper, hrec⟩

end FLatticePaper.Construction
