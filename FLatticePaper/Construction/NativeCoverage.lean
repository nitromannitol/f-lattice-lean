import FLatticePaper.Construction.Native
import FLatticePaper.Farey.PeriodDeck

namespace FLatticePaper.Construction

open Farey

/-- Coverage is of the actual occupied sites in each of the eight native registers. -/
structure TileRegisters.Covers (registers : TileRegisters) (parents : Parents) : Prop where
  standardOdd : (parents.current .odd).modifiedDeck.Covers registers.standard.currentOdd.val.sites
  standardEven : (parents.current .even).modifiedDeck.Covers registers.standard.currentEven.val.sites
  alternateOdd : (parents.current .odd).modifiedDeck.Covers registers.alternate.currentOdd.val.sites
  alternateEven : (parents.current .even).modifiedDeck.Covers registers.alternate.currentEven.val.sites
  standardRetainedOdd : parents.odd.modifiedDeck.Covers registers.standard.retainedOdd.val.sites
  standardRetainedEven : parents.even.modifiedDeck.Covers registers.standard.retainedEven.val.sites
  alternateRetainedOdd : parents.odd.modifiedDeck.Covers registers.alternate.retainedOdd.val.sites
  alternateRetainedEven : parents.even.modifiedDeck.Covers registers.alternate.retainedEven.val.sites

/-- At the empty word, check both native child parities and both families
against the complete quotient test, including their literal retained atoms. -/
theorem empty_registers_cover : BaseRun.empty.registers.llCenter.Covers (parentsAt []) := by
  constructor <;> apply (PeriodDeck.covers_iff_square_codes_subset _ (by decide) _).mpr <;> decide +kernel

theorem evaluateNative_empty_covers :
    ∃ registers, evaluateNative [] = .ok registers ∧ registers.Covers (parentsAt []) :=
  ⟨BaseRun.empty.registers.llCenter, evaluateNative_base .empty, empty_registers_cover⟩

end FLatticePaper.Construction
