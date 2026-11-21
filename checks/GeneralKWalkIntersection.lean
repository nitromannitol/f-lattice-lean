import FLatticePaper.GeneralK.WalkIntersection

namespace FLatticePaper.GeneralK.Checks

theorem transverse_three_step_loops_meet :
    ∃ x ∈ walkVertices (0, 1) [.right, .right, .right],
      ∃ y ∈ walkVertices (2, 0) [.up, .up, .up], residueVertex 3 x = residueVertex 3 y := by
  by_contra! h
  have hdet := determinant_eq_zero_of_disjoint_squareWalks (n := 3) (0, 1) (2, 0)
    [.right, .right, .right] [.up, .up, .up] 1 0 0 1 (by decide) (by decide) h
  omega

#print axioms walkCount_divergence_eq_zero
#print axioms axisPotential_shift
#print axioms determinant_eq_zero_of_disjoint_squareWalks
#print axioms transverse_three_step_loops_meet

end FLatticePaper.GeneralK.Checks
