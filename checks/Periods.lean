import FLatticePaper.Construction.LadderExtension
import FLatticePaper.Construction.LadderReflection
import FLatticePaper.Construction.LadderRotation
import FLatticePaper.Construction.NativeCoverage
import FLatticePaper.Plane.EndpointGrowth
import FLatticePaper.Farey.Birth

namespace FLatticePaper.Checks

open Farey Construction

theorem birth_periods_eq_integral_even (birth : Birth) (period : Site) :
    period ∈ birth.fraction.modifiedDeck.span ↔
      period ∈ birth.fraction.integralLattice ∧ EvenSite period :=
  Fraction.mem_modifiedDeck_iff_integral_even birth.interior.inUnitInterval birth.reduced period

theorem recognizable_root_has_its_matrix_growth
    {field : Field} {constantU constantV : ℤ}
    (hperiod : HasGeneratorPeriods ((parentsAt []).current .even) field constantU constantV) :
    HasQuadraticGrowth field ((parentsAt []).current .even).matrix :=
  generator_periods_growth ((parentsAt_valid []).current_interior .even).inUnitInterval hperiod

theorem long_pure_runs_cover_all_registers :
    (∃ registers, evaluateNative (List.replicate 200 .two) = .ok registers ∧
      registers.Covers (parentsAt (List.replicate 200 .two))) ∧
    (∃ registers, evaluateNative (List.replicate 200 .three) = .ok registers ∧
      registers.Covers (parentsAt (List.replicate 200 .three))) :=
  ⟨evaluateNative_base_covers (.twos 199), evaluateNative_base_covers (.threes 199)⟩

theorem long_pure_three_has_standard_ladder_extension :
    let word := List.replicate 200 .three
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.standard.currentOdd.val.Agrees field 0 ∧
      HasGeneratorPeriods ((parentsAt word).current .odd) field 0 (stairEvenConstantV 402) ∧
      HasQuadraticGrowth field ((parentsAt word).current .odd).matrix := by
  exact evaluateNative_threes_odd_standard_extension 199

theorem long_pure_two_has_standard_ladder_extension :
    let word := List.replicate 200 .two
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.standard.currentEven.val.Agrees field 0 ∧
      HasGeneratorPeriods ((parentsAt word).current .even) field 0 (ladderEvenConstantV 402) ∧
      HasQuadraticGrowth field ((parentsAt word).current .even).matrix := by
  exact evaluateNative_twos_even_standard_extension 199

theorem reciprocal_ladder_four_laplacian_reflection :
    ∃ field : Field, (BaseMask.ladderOdd.raw 4).Agrees field 0 ∧
      ∀ point, laplacian field ((6, 6) - point) = laplacian field point := by
  have hvalid : BaseMask.ladderOdd.Valid 4 := by simp [BaseMask.Valid]
  obtain ⟨field, hagree, hperiod, _⟩ := ladderOdd_exists_extension hvalid
  exact ⟨field, hagree, laplacian_ladderOddField_reflection hvalid hagree hperiod⟩

#print axioms Fraction.integralLattice_eq_span
#print axioms Fraction.mem_modifiedDeck_iff_integral_even
#print axioms evaluateNative_empty_covers
#print axioms ladderOdd_cover
#print axioms ladderOddAlt_cover
#print axioms ladderEven_cover
#print axioms ladderEvenAlt_cover
#print axioms evaluateNative_base_covers
#print axioms long_pure_runs_cover_all_registers
#print axioms generator_period_formula
#print axioms generator_periods_affine
#print axioms eq_of_covered_generator_periods
#print axioms generator_periods_growth
#print axioms checkerboard_endpoints
#print axioms birth_periods_eq_integral_even
#print axioms recognizable_root_has_its_matrix_growth
#print axioms BaseMask.ladderOdd_raw_height
#print axioms ladderOdd_overlap_indices
#print axioms ladderOdd_respectsPeriods
#print axioms evaluateNative_threes_odd_standard_extension
#print axioms long_pure_three_has_standard_ladder_extension
#print axioms BaseMask.ladderEven_raw_height
#print axioms rotateLadderField_periods
#print axioms ladderEvenConstantV_eq
#print axioms evaluateNative_twos_even_standard_extension
#print axioms long_pure_two_has_standard_ladder_extension
#print axioms ladderOddField_reflection
#print axioms laplacian_ladderOddField_reflection
#print axioms reciprocal_ladder_four_laplacian_reflection

end FLatticePaper.Checks
