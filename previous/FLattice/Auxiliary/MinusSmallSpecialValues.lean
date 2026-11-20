import FLattice.Auxiliary.MinusSmallCoordinates
import FLattice.Auxiliary.MinusSmallDeficit

/-! # Exact source pin and root values for the smallest-minus profiles -/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusSmallProfile

/-- The source cost is integer at every signed pair of indices. -/
def cost (a b : ℤ) : ℤ := 3 * a ^ 2 + 2 * a * b + b ^ 2 - 2 * a - b

/-- The complete signed prescribed coset has the exact source height. -/
theorem profile_prescribed_coset (ε : Fin 2) (a b : ℤ) :
    profile ε (prescribedX ε - 6 * a - 2 * b)
      (prescribedY ε - 2 * a - 2 * b) = 1 - cost a b := by
  fin_cases ε
  · have h := profile_at_lifted_cell 0 0 1 (-a - b) (1 - a)
    norm_num [representativeHeight, periodConstant, prescribedX, prescribedY,
      cost, Fin.ext_iff] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := profile_at_lifted_cell 1 3 0 (-a - b) (-a - 1)
    norm_num [representativeHeight, periodConstant, prescribedX, prescribedY,
      cost, Fin.ext_iff] at h ⊢
    ring_nf at h ⊢
    exact h

/-- Both source base points have height one. -/
theorem profile_prescribed_point (ε : Fin 2) :
    profile ε (prescribedX ε) (prescribedY ε) = 1 := by
  simpa [cost] using profile_prescribed_coset ε 0 0

/-- The four source root values, evaluated from the literal global functions. -/
theorem even_origin : profile 0 0 0 = 1 := by decide

theorem odd_origin : profile 1 0 0 = 0 := by decide

theorem even_twice_prescribed : profile 0 8 2 = -2 := by decide

theorem odd_twice_prescribed : profile 1 (-2) 0 = 1 := by decide

end FLattice.Auxiliary.MinusSmallProfile
