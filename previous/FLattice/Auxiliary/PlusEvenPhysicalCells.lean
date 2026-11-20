import FLattice.Auxiliary.PlusEvenCoordinates
import FLattice.Auxiliary.PlusEvenDeficit

/-!
# Physical representatives and their incoming stars

The equalities use the literal global profile and the actual parity-dependent
incoming deficit. Valid representative bounds are exposed at every evaluation.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- The global profile at a valid representative has exactly its table value. -/
theorem profile_at_cell (m : Parameter) (r s : ℤ) (e v : Fin 2)
    (hr0 : 0 ≤ r) (hrm : r ≤ m.val + 1)
    (hs0 : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1)) :
    profile m (2 * m.val * r + 2 * s + (v.val : ℤ)) (e.val : ℤ) =
      representativeHeight e v r s := by
  simpa only [mul_zero, add_zero, zero_add, zero_mul, zero_pow (by decide : 2 ≠ 0), sub_zero]
    using profile_at_lifted_cell m r s 0 0 e v hr0 hrm hs0 hsm hMissing

/-- A physical `00` center has horizontal incoming neighbors. -/
theorem incomingDeficit_00 (m : Parameter) (r s : ℤ) :
    incomingDeficit m (2 * m.val * r + 2 * s) 0 =
      2 * profile m (2 * m.val * r + 2 * s) 0 -
        profile m (2 * m.val * r + 2 * s - 1) 0 -
        profile m (2 * m.val * r + 2 * s + 1) 0 := by
  have hParity : (2 * m.val * r + 2 * s + 0) % 2 = 0 := by
    rw [show 2 * m.val * r = 2 * (m.val * r) by ring]
    omega
  rw [incomingDeficit, if_pos hParity]

/-- A physical `01` center has vertical incoming neighbors. -/
theorem incomingDeficit_01 (m : Parameter) (r s : ℤ) :
    incomingDeficit m (2 * m.val * r + 2 * s + 1) 0 =
      2 * profile m (2 * m.val * r + 2 * s + 1) 0 -
        profile m (2 * m.val * r + 2 * s + 1) (-1) -
        profile m (2 * m.val * r + 2 * s + 1) 1 := by
  have hParity : (2 * m.val * r + 2 * s + 1 + 0) % 2 ≠ 0 := by
    rw [show 2 * m.val * r = 2 * (m.val * r) by ring]
    omega
  rw [incomingDeficit, if_neg hParity]
  rfl

/-- A physical `10` center has vertical incoming neighbors. -/
theorem incomingDeficit_10 (m : Parameter) (r s : ℤ) :
    incomingDeficit m (2 * m.val * r + 2 * s) 1 =
      2 * profile m (2 * m.val * r + 2 * s) 1 -
        profile m (2 * m.val * r + 2 * s) 0 -
        profile m (2 * m.val * r + 2 * s) 2 := by
  have hParity : (2 * m.val * r + 2 * s + 1) % 2 ≠ 0 := by
    rw [show 2 * m.val * r = 2 * (m.val * r) by ring]
    omega
  rw [incomingDeficit, if_neg hParity]
  rfl

/-- A physical `11` center has horizontal incoming neighbors. -/
theorem incomingDeficit_11 (m : Parameter) (r s : ℤ) :
    incomingDeficit m (2 * m.val * r + 2 * s + 1) 1 =
      2 * profile m (2 * m.val * r + 2 * s + 1) 1 -
        profile m (2 * m.val * r + 2 * s) 1 -
        profile m (2 * m.val * r + 2 * s + 2) 1 := by
  have hParity : (2 * m.val * r + 2 * s + 1 + 1) % 2 = 0 := by
    rw [show 2 * m.val * r = 2 * (m.val * r) by ring]
    omega
  rw [incomingDeficit, if_pos hParity]
  rw [show 2 * m.val * r + 2 * s + 1 - 1 = 2 * m.val * r + 2 * s by omega,
    show 2 * m.val * r + 2 * s + 1 + 1 = 2 * m.val * r + 2 * s + 2 by omega]

end FLattice.Auxiliary.PlusEvenProfile
