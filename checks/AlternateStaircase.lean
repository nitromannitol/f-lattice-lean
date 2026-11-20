import FLatticePaper.Construction.AlternateStaircaseLaplacian
import FLatticePaper.Construction.AlternateStaircaseRankCorrection
import FLatticePaper.Construction.AlternateStaircaseRecurrence
import FLatticePaper.Construction.AlternateStaircaseRotation
import FLatticePaper.Construction.AlternateStaircaseSeams

namespace FLatticePaper.Checks

open Construction Farey

theorem long_pure_three_has_recurrent_alternate_in_physical_chart :
    let word := List.replicate 200 .three
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧
      registers.alternate.currentEven.val.Agrees (fun site => field (site + (-402, -1))) 0 ∧
      HasQuadraticGrowth field ((parentsAt word).current .even).matrix ∧ Recurrent field := by
  obtain ⟨registers, field, heval, hagree, _, hgrowth, _, hrec⟩ := evaluateNative_threes_even_alternate_recurrent 199
  exact ⟨registers, field, heval, hagree, hgrowth, hrec⟩

theorem long_pure_two_has_recurrent_alternate :
    let word := List.replicate 200 .two
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.alternate.currentOdd.val.Agrees field 0 ∧
      HasQuadraticGrowth field ((parentsAt word).current .odd).matrix ∧ Recurrent field := by
  obtain ⟨registers, field, heval, hagree, _, hgrowth, _, hrec⟩ := evaluateNative_twos_odd_alternate_recurrent 199
  exact ⟨registers, field, heval, hagree, hgrowth, hrec⟩

theorem native_root_even_alternate_finiteComparison :
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative [] = .ok registers ∧
      registers.alternate.currentEven.val.Agrees (fun site => field (site + (-2, -1))) 0 ∧
      ∀ competitor : Field, Superharmonic competitor →
        ∀ (sites : Finset Site), StronglyConnected sites → ∀ bound : ℤ,
          (∀ point ∈ incomingBoundary sites, field point - competitor point ≤ bound) →
          ∀ point ∈ sites, field point - competitor point ≤ bound := by
  obtain ⟨registers, field, heval, hagree, _, _, _, hrec⟩ := evaluateNative_empty_even_alternate_recurrent
  exact ⟨registers, field, heval, hagree, fun _ => hrec.finiteComparison⟩

theorem root_odd_staircases_have_distinct_plane_extensions :
    ∃ registers : TileRegisters, ∃ standard alternate : Field,
      evaluateNative [] = .ok registers ∧ registers.standard.currentOdd.val.Agrees standard 0 ∧
      registers.alternate.currentOdd.val.Agrees alternate 0 ∧
      ¬ IntegerAffine (fun site => alternate site - standard site) := by
  obtain ⟨first, standard, hf, hstandard, hperiod, _⟩ := evaluateNative_empty_odd_standard_recurrent
  obtain ⟨second, alternate, hs, halternate, hperiod', _, _, _⟩ := evaluateNative_empty_odd_alternate_recurrent
  have heq : first = second := Except.ok.inj (hf.symm.trans hs)
  subst second
  exact ⟨first, standard, alternate, hf, hstandard, halternate,
    stairOddAlt_sub_standard_not_integerAffine (den := 3) (by decide) hperiod hperiod'⟩

theorem reciprocal_alternate_left_corner_has_physical_laplacian_neg_one :
    ∃ field : Field, (BaseMask.stairEvenAlt.raw 3).Agrees field 0 ∧ laplacian field (-2, 0) = -1 := by
  have hvalid : BaseMask.stairEvenAlt.Valid 3 := by simp [BaseMask.Valid]
  obtain ⟨standard, hagree, hperiod, _⟩ := stairEven_exists_extension hvalid
  refine ⟨stairEvenAltField 3 standard, stairEvenAltField_agrees hvalid hagree hperiod, ?_⟩
  have hsite : ((-2, 0) : Site) ∈ (BaseMask.stairEvenAlt.raw 3).sites := by decide +kernel
  rw [stairEvenAlt_laplacian_on_raw hvalid hagree hperiod _ hsite]
  decide

theorem reciprocal_alternate_five_has_binary_plane_laplacian :
    ∃ field : Field, (BaseMask.stairEvenAlt.raw 5).Agrees field 0 ∧
      ∀ site, laplacian field site = -1 ∨ laplacian field site = 0 := by
  have hvalid : BaseMask.stairEvenAlt.Valid 5 := by simp [BaseMask.Valid]
  obtain ⟨standard, hagree, hperiod, _⟩ := stairEven_exists_extension hvalid
  exact ⟨stairEvenAltField 5 standard, stairEvenAltField_agrees hvalid hagree hperiod,
    stairEvenAlt_binary_laplacian hvalid hagree hperiod⟩

theorem reciprocal_alternate_corner_and_diagonal_share_periodic_rank_correction :
    ∃ correction : Field, correction (-2, 0) = 24 ∧ correction (1, 1) = 24 ∧
      Function.Periodic correction (3, 1) := by
  have hvalid : BaseMask.stairEvenAlt.Valid 3 := by simp [BaseMask.Valid]
  obtain ⟨correction, hagree, hperiodic⟩ := stairEvenAlt_exists_periodic_rankCorrection hvalid
  have hcorner : ((-2, 0) : Site) ∈ (BaseMask.stairEvenAlt.raw 3).sites := by decide +kernel
  have hdiag : ((1, 1) : Site) ∈ (BaseMask.stairEvenAlt.raw 3).sites := by decide +kernel
  have hstep : ((3, 1) : Site) ∈ (reciprocalEvenDeck 3).span := ⟨1, 0, rfl⟩
  exact ⟨correction, (hagree _ hcorner).trans (by decide), (hagree _ hdiag).trans (by decide),
    hperiodic _ hstep⟩

/-- The stored root alternate needs its physical chart. Its centered
coordinates alone give a positive Laplacian at `(2,2)`. -/
theorem centered_root_alternate_has_no_unshifted_superharmonic_extension :
    ¬ ∃ field : Field, BaseRun.empty.registers.llCenter.alternate.currentEven.val.Agrees field 0 ∧
      Superharmonic field := by
  let tile := BaseRun.empty.registers.llCenter.alternate.currentEven.val
  rintro ⟨field, hagree, hsuper⟩
  change tile.Agrees field 0 at hagree
  let left : tile.sites := ⟨(1, 2), by decide +kernel⟩
  let center : tile.sites := ⟨(2, 2), by decide +kernel⟩
  let right : tile.sites := ⟨(3, 2), by decide +kernel⟩
  have hleft : tile.height left = -1 := by decide +kernel
  have hcenter : tile.height center = -1 := by decide +kernel
  have hright : tile.height right = 0 := by decide +kernel
  have hleft' := hagree left
  have hcenter' := hagree center
  have hright' := hagree right
  rw [hleft, add_zero] at hleft'
  rw [hcenter, add_zero] at hcenter'
  rw [hright, add_zero] at hright'
  change -1 = field (1, 2) at hleft'
  change -1 = field (2, 2) at hcenter'
  change 0 = field (3, 2) at hright'
  have hstar := hsuper (2, 2)
  change (field (1, 2) - field (2, 2)) + (field (3, 2) - field (2, 2)) ≤ 0 at hstar
  omega

#print axioms stairEvenAltMarker_periodic
#print axioms stairEvenAltField_reflection
#print axioms stairEvenAltField_residual_reflection
#print axioms laplacian_stairEvenAltField_reflection
#print axioms laplacian_stairEvenAltBackground
#print axioms stairEvenAlt_incomingNeg_notMem_iff
#print axioms stairEvenAltResidual_incomingNeg_of_notMem
#print axioms stairEvenAltResidual_incomingNeg_even
#print axioms stairEvenAltResidual_incomingNeg_odd
#print axioms stairEvenAltResidual_incomingPos_reflect
#print axioms stairEvenAlt_laplacian_on_raw
#print axioms stairEvenAlt_binary_laplacian
#print axioms reciprocal_alternate_left_corner_has_physical_laplacian_neg_one
#print axioms reciprocal_alternate_five_has_binary_plane_laplacian
#print axioms stairEvenAlt_rankCorrection_class_constant
#print axioms stairEvenAlt_exists_periodic_rankCorrection
#print axioms reciprocal_alternate_corner_and_diagonal_share_periodic_rank_correction
#print axioms stairEvenAltField_agrees
#print axioms stairEvenAlt_exists_extension
#print axioms evaluateNative_empty_even_alternate_extension
#print axioms stairEvenAlt_exists_burningRank
#print axioms stairEvenAlt_exists_recurrent_extension
#print axioms evaluateNative_empty_even_alternate_recurrent
#print axioms evaluateNative_threes_even_alternate_recurrent
#print axioms long_pure_three_has_recurrent_alternate_in_physical_chart
#print axioms native_root_even_alternate_finiteComparison
#print axioms stairOddAlt_exists_extension
#print axioms stairOddAlt_exists_recurrent_extension
#print axioms evaluateNative_empty_odd_alternate_recurrent
#print axioms evaluateNative_twos_odd_alternate_recurrent
#print axioms stairEvenAltField_sub_standard_not_integerAffine
#print axioms stairOddAlt_sub_standard_not_integerAffine
#print axioms long_pure_two_has_recurrent_alternate
#print axioms root_odd_staircases_have_distinct_plane_extensions
#print axioms centered_root_alternate_has_no_unshifted_superharmonic_extension

end FLatticePaper.Checks
