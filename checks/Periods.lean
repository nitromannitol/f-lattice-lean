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

end FLatticePaper.Checks
