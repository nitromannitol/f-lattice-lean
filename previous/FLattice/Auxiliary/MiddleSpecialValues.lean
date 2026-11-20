import FLattice.Auxiliary.MiddleCoordinates
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Origin and prescribed-coset values for the two smallest-branch profiles

Both identities evaluate the literal global profiles. The prescribed-coset
proof uses explicit signed coordinate lifts and the common integer cost
`3*a^2+2*a*b+b^2+a`. No periodicity of a comparison function is involved.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MiddleProfile

/-- Both literal comparison profiles vanish at the physical origin. -/
theorem profile_origin (ε : Fin 2) : profile ε 0 0 = 0 := by
  have h := profile_at_cell ε 0 0
  fin_cases ε <;> simpa [representativeHeight, Fin.ext_iff] using h

/-- The entire prescribed coset has its stated height, for arbitrary signed indices. -/
theorem profile_prescribed_coset (ε : Fin 2) (a b : ℤ) :
    profile ε (-2 + (ε.val : ℤ) - 6 * a - 2 * b)
      (-1 + (ε.val : ℤ) - 2 * a - 2 * b) =
      1 - (3 * a ^ 2 + 2 * a * b + b ^ 2 + a) := by
  fin_cases ε
  · have h := profile_at_lifted_cell 0 0 1 (-a - b - 1) (-a)
    norm_num [representativeHeight, Fin.ext_iff] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := profile_at_lifted_cell 1 3 0 (-a - b) (-a - 1)
    norm_num [representativeHeight, Fin.ext_iff] at h ⊢
    ring_nf at h ⊢
    exact h

/-- Each prescribed base point `Dε` has height one. -/
theorem profile_prescribed_point (ε : Fin 2) :
    profile ε (-2 + (ε.val : ℤ)) (-1 + (ε.val : ℤ)) = 1 := by
  simpa using profile_prescribed_coset ε 0 0

end FLattice.Auxiliary.MiddleProfile
