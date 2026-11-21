import FLatticePaper.Plane.ClassificationReduction
import FLatticePaper.Plane.RecurrentBoundary
import FLatticePaper.Plane.CirclePacking
import FLatticePaper.Construction.EndpointAtoms

namespace FLatticePaper.Checks

theorem circle_origin_cone_admits_irrational_singular_matrix :
    circleMatrix 1 1 (-Real.sqrt 2) ∈ integerSuperharmonicMatrices := by
  apply mem_integerSuperharmonicMatrices_of_peak_sub_posSemidef 0 0
  have heq : harmonicPeak 0 0 - circleMatrix 1 1 (-Real.sqrt 2) = circleMatrix (-1) (-1) (Real.sqrt 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [harmonicPeak, circleMatrix, GeneralK.symmetricMatrix] <;> ring
  rw [heq, circleMatrix_posSemidef_iff]
  norm_num

theorem nonzero_harmonic_apex_is_on_the_physical_frontier :
    symmetricCircleMatrix 1 3 0 ∈ frontier symmetricGrowthSet := by
  have h := harmonicPeak_mem_frontier 2 1
  norm_num at h
  exact h

theorem retained_endpoint_atoms_are_on_the_physical_frontier (atom : Construction.EndpointAtom) :
    ∃ h : atom.fraction.matrix.IsSymm, (⟨atom.fraction.matrix, h⟩ : SymmetricMatrix) ∈ frontier symmetricGrowthSet := by
  have hs : atom.fraction.matrix.IsSymm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨hsuper, hrec, hgrowth⟩ := atom.planeField_recurrent
  exact ⟨hs, hrec.mem_frontier_of_quadraticGrowth hsuper ⟨_, hs⟩ hgrowth⟩

theorem negative_identity_lies_in_physical_interior : symmetricCircleMatrix 0 0 (-2) ∈ interior symmetricGrowthSet := by
  have h := harmonicPeak_mem_integerSuperharmonicMatrices 0 0
  norm_num [harmonicPeak] at h
  exact symmetricCircleMatrix_mem_interior_of_lt h (by norm_num)

#print axioms negative_identity_lies_in_physical_interior
#print axioms circlePacking_of_hyperbolaBoundary
#print axioms circle_origin_cone_admits_irrational_singular_matrix
#print axioms nonzero_harmonic_apex_is_on_the_physical_frontier
#print axioms circleMatrix_posSemidef_iff
#print axioms Recurrent.mem_frontier_of_quadraticGrowth
#print axioms retained_endpoint_atoms_are_on_the_physical_frontier

end FLatticePaper.Checks
