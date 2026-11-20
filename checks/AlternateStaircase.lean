import FLatticePaper.Construction.AlternateStaircaseReflection

namespace FLatticePaper.Checks

open Construction Farey

theorem long_pure_three_has_alternate_extension_in_physical_chart :
    let word := List.replicate 200 .three
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧
      registers.alternate.currentEven.val.Agrees (fun site => field (site + (-402, -1))) 0 ∧
      HasQuadraticGrowth field ((parentsAt word).current .even).matrix := by
  obtain ⟨registers, field, heval, hagree, _, hgrowth⟩ := evaluateNative_threes_even_alternate_extension 199
  exact ⟨registers, field, heval, hagree, hgrowth⟩

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
#print axioms stairEvenAltField_agrees
#print axioms stairEvenAlt_exists_extension
#print axioms evaluateNative_empty_even_alternate_extension
#print axioms long_pure_three_has_alternate_extension_in_physical_chart
#print axioms centered_root_alternate_has_no_unshifted_superharmonic_extension

end FLatticePaper.Checks
