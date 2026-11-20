import FLattice.Auxiliary.PlusEvenDeficit
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Ring.Periodic

/-!
# All signed period translations of the even-plus deficit

The two proved primitive periods generate the displayed translation identity.
Integer scalar multiples include negative as well as positive translations.
No bound on the deficit or additional physical-profile property is assumed.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- The literal incoming deficit is invariant under every signed combination
of its diagonal and horizontal periods. -/
theorem incomingDeficit_add_periods (m : Parameter) (x y k q : ℤ) :
    incomingDeficit m (x + 2 * m.val * k + 2 * halfPeriod m * q) (y + 2 * k) =
      incomingDeficit m x y := by
  have hDiagonal : Function.Periodic
      (fun z : ℤ × ℤ => incomingDeficit m z.1 z.2) (2 * m.val, 2) := by
    intro z
    exact incomingDeficit_add_diagonal_period m z.1 z.2
  have hHorizontal : Function.Periodic
      (fun z : ℤ × ℤ => incomingDeficit m z.1 z.2) (2 * halfPeriod m, 0) := by
    intro z
    change incomingDeficit m (z.1 + 2 * halfPeriod m) (z.2 + 0) =
      incomingDeficit m z.1 z.2
    simpa only [add_zero] using incomingDeficit_add_horizontal_period m z.1 z.2
  have h := ((hDiagonal.zsmul k).add_period (hHorizontal.zsmul q)) (x, y)
  change incomingDeficit m
      (x + (k • (2 * m.val) + q • (2 * halfPeriod m)))
      (y + (k • (2 : ℤ) + q • (0 : ℤ))) = incomingDeficit m x y at h
  simp only [zsmul_eq_mul, Int.cast_id, mul_zero, add_zero] at h
  ring_nf at h ⊢
  exact h

end FLattice.Auxiliary.PlusEvenProfile
