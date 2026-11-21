import FLatticePaper.Plane.ClassificationReduction

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

#print axioms circle_origin_cone_admits_irrational_singular_matrix
#print axioms nonzero_harmonic_apex_is_on_the_physical_frontier
#print axioms circleMatrix_posSemidef_iff

end FLatticePaper.Checks
