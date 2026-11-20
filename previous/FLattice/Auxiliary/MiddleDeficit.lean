import FLattice.Auxiliary.MiddlePeriods
import FLattice.Auxiliary.MiddleCoordinates
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Actual native deficits of the two smallest-branch profiles

The native graph uses horizontal incoming neighbors when `x+y+ε` is even.
The eight representative stars are evaluated from the literal global profile.
Affine periods then give the full physical table and identify its unique
value-two class with the prescribed signed coset. No table identity is
assumed as a hypothesis.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MiddleProfile

/-- Twice the profile minus its two actual parity-dependent incoming values. -/
def incomingDeficit (ε : Fin 2) (x y : ℤ) : ℤ :=
  if (x + y + (ε.val : ℤ)) % 2 = 0 then
    2 * profile ε x y - profile ε (x - 1) y - profile ε (x + 1) y
  else
    2 * profile ε x y - profile ε x (y - 1) - profile ε x (y + 1)

/-- The literal eight-entry deficit table for each native parity. -/
def representativeDeficit (ε : Fin 2) (X : Fin 4) (e : Fin 2) : ℤ :=
  if ε = 0 then
    if e = 0 then (if X = 2 then 1 else 0)
    else if X = 0 then 2 else if X = 1 then 1 else 0
  else if e = 0 then (if X = 2 then 1 else if X = 3 then 2 else 0)
  else if X = 3 then 1 else 0

/-- The prescribed set is exactly `Dε-C(a,b)` with arbitrary signed indices. -/
def prescribedCoset (ε : Fin 2) (x y : ℤ) : Prop :=
  ∃ a b : ℤ, x = -2 + (ε.val : ℤ) - 6 * a - 2 * b ∧
    y = -1 + (ε.val : ℤ) - 2 * a - 2 * b

/-- The diagonal affine period preserves the actual native deficit. -/
theorem incomingDeficit_add_diagonal_period (ε : Fin 2) (x y : ℤ) :
    incomingDeficit ε (x + 2) (y + 2) = incomingDeficit ε x y := by
  have hParity : (x + 2 + (y + 2) + (ε.val : ℤ)) % 2 =
      (x + y + (ε.val : ℤ)) % 2 := by omega
  unfold incomingDeficit
  rw [hParity]
  have hCenter := profile_add_diagonal_period ε x y
  split_ifs
  · have hLeft := profile_add_diagonal_period ε (x - 1) y
    have hRight := profile_add_diagonal_period ε (x + 1) y
    rw [show x + 2 - 1 = (x - 1) + 2 by omega,
      show x + 2 + 1 = (x + 1) + 2 by omega]
    omega
  · have hDown := profile_add_diagonal_period ε x (y - 1)
    have hUp := profile_add_diagonal_period ε x (y + 1)
    rw [show y + 2 - 1 = (y - 1) + 2 by omega,
      show y + 2 + 1 = (y + 1) + 2 by omega]
    omega

/-- The horizontal affine period preserves the actual native deficit. -/
theorem incomingDeficit_add_horizontal_period (ε : Fin 2) (x y : ℤ) :
    incomingDeficit ε (x + 4) y = incomingDeficit ε x y := by
  have hParity : (x + 4 + y + (ε.val : ℤ)) % 2 =
      (x + y + (ε.val : ℤ)) % 2 := by omega
  unfold incomingDeficit
  rw [hParity]
  have hCenter := profile_add_horizontal_period ε x y
  split_ifs
  · have hLeft := profile_add_horizontal_period ε (x - 1) y
    have hRight := profile_add_horizontal_period ε (x + 1) y
    rw [show x + 4 - 1 = (x - 1) + 4 by omega,
      show x + 4 + 1 = (x + 1) + 4 by omega]
    omega
  · have hDown := profile_add_horizontal_period ε x (y - 1)
    have hUp := profile_add_horizontal_period ε x (y + 1)
    omega

/-- Every signed combination of the two primitive periods preserves the deficit. -/
theorem incomingDeficit_add_periods (ε : Fin 2) (x y k q : ℤ) :
    incomingDeficit ε (x + 2 * k + 4 * q) (y + 2 * k) =
      incomingDeficit ε x y := by
  have hDiagonal : Function.Periodic
      (fun z : ℤ × ℤ => incomingDeficit ε z.1 z.2) (2, 2) := by
    intro z
    exact incomingDeficit_add_diagonal_period ε z.1 z.2
  have hHorizontal : Function.Periodic
      (fun z : ℤ × ℤ => incomingDeficit ε z.1 z.2) (4, 0) := by
    intro z
    change incomingDeficit ε (z.1 + 4) (z.2 + 0) = incomingDeficit ε z.1 z.2
    simpa only [add_zero] using incomingDeficit_add_horizontal_period ε z.1 z.2
  have h := ((hDiagonal.zsmul k).add_period (hHorizontal.zsmul q)) (x, y)
  change incomingDeficit ε (x + (k • (2 : ℤ) + q • (4 : ℤ)))
      (y + (k • (2 : ℤ) + q • (0 : ℤ))) = incomingDeficit ε x y at h
  simp only [zsmul_eq_mul, Int.cast_id, mul_zero, add_zero] at h
  ring_nf at h ⊢
  exact h

/-- Direct evaluation of all eight actual representative stars for both native parities. -/
theorem incomingDeficit_at_cell (ε : Fin 2) (X : Fin 4) (e : Fin 2) :
    incomingDeficit ε (X.val : ℤ) (e.val : ℤ) = representativeDeficit ε X e := by
  fin_cases ε <;> fin_cases X <;> fin_cases e <;> decide

/-- The exact representative table holds on every signed physical lift. -/
theorem incomingDeficit_at_lifted_cell (ε : Fin 2) (X : Fin 4) (e : Fin 2)
    (k q : ℤ) :
    incomingDeficit ε ((X.val : ℤ) + 2 * k + 4 * q) (2 * k + (e.val : ℤ)) =
      representativeDeficit ε X e := by
  rw [add_comm (2 * k) (e.val : ℤ), incomingDeficit_add_periods]
  exact incomingDeficit_at_cell ε X e

/-- The displayed value two occurs at exactly one representative for each parity. -/
theorem representativeDeficit_eq_two_iff (ε : Fin 2) (X : Fin 4) (e : Fin 2) :
    representativeDeficit ε X e = 2 ↔
      (ε = 0 ∧ X = 0 ∧ e = 1) ∨ (ε = 1 ∧ X = 3 ∧ e = 0) := by
  fin_cases ε <;> fin_cases X <;> fin_cases e <;> norm_num [representativeDeficit, Fin.ext_iff]

/-- Every signed prescribed-coset point has actual deficit two. -/
theorem incomingDeficit_prescribed_coset (ε : Fin 2) (a b : ℤ) :
    incomingDeficit ε (-2 + (ε.val : ℤ) - 6 * a - 2 * b)
      (-1 + (ε.val : ℤ) - 2 * a - 2 * b) = 2 := by
  fin_cases ε
  · have h := incomingDeficit_at_lifted_cell 0 0 1 (-a - b - 1) (-a)
    norm_num [representativeDeficit, Fin.ext_iff] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := incomingDeficit_at_lifted_cell 1 3 0 (-a - b) (-a - 1)
    norm_num [representativeDeficit, Fin.ext_iff] at h ⊢
    ring_nf at h ⊢
    exact h

/-- The actual deficit equals two precisely on the prescribed signed coset. -/
theorem incomingDeficit_eq_two_iff (ε : Fin 2) (x y : ℤ) :
    incomingDeficit ε x y = 2 ↔ prescribedCoset ε x y := by
  constructor
  · intro hTwo
    obtain ⟨X, e, k, q, hx, hy⟩ := exists_lifted_cell x y
    have ht := incomingDeficit_at_lifted_cell ε X e k q
    rw [← hx, ← hy, hTwo] at ht
    rcases (representativeDeficit_eq_two_iff ε X e).mp ht.symm with hEven | hOdd
    · rcases hEven with ⟨hε, hX, he⟩
      refine ⟨-q, q - k - 1, ?_, ?_⟩
      · rw [hx, hX, hε]
        norm_num
        ring
      · rw [hy, he, hε]
        norm_num
        ring
    · rcases hOdd with ⟨hε, hX, he⟩
      refine ⟨-q - 1, q + 1 - k, ?_, ?_⟩
      · rw [hx, hX, hε]
        norm_num
        ring
      · rw [hy, he, hε]
        norm_num
        ring
  · rintro ⟨a, b, hx, hy⟩
    rw [hx, hy]
    exact incomingDeficit_prescribed_coset ε a b

/-- Away from the prescribed coset, the actual deficit is zero or one. -/
theorem incomingDeficit_zero_or_one (ε : Fin 2) (x y : ℤ)
    (hNotPrescribed : ¬prescribedCoset ε x y) :
    incomingDeficit ε x y = 0 ∨ incomingDeficit ε x y = 1 := by
  have hNotTwo : incomingDeficit ε x y ≠ 2 := by
    intro h
    exact hNotPrescribed ((incomingDeficit_eq_two_iff ε x y).mp h)
  obtain ⟨X, e, k, q, hx, hy⟩ := exists_lifted_cell x y
  have ht := incomingDeficit_at_lifted_cell ε X e k q
  rw [← hx, ← hy] at ht
  rw [ht] at hNotTwo ⊢
  fin_cases ε <;> fin_cases X <;> fin_cases e <;>
    simp_all [representativeDeficit, Fin.ext_iff]

private theorem representativeDeficit_eq_one_even (ε : Fin 2) (X : Fin 4) (e : Fin 2) :
    representativeDeficit ε X e = 1 → ((X.val : ℤ) + (e.val : ℤ)) % 2 = 0 := by
  fin_cases ε <;> fin_cases X <;> fin_cases e <;> decide

/-- Every actual deficit-one point has even coordinate sum, for both native parities. -/
theorem even_sum_of_incomingDeficit_eq_one (ε : Fin 2) (x y : ℤ)
    (hOne : incomingDeficit ε x y = 1) : (x + y) % 2 = 0 := by
  obtain ⟨X, e, k, q, hx, hy⟩ := exists_lifted_cell x y
  have ht := incomingDeficit_at_lifted_cell ε X e k q
  rw [← hx, ← hy, hOne] at ht
  have hp := representativeDeficit_eq_one_even ε X e ht.symm
  omega

end FLattice.Auxiliary.MiddleProfile
