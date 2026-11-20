import FLattice.Auxiliary.MinusSmallPeriods
import FLattice.Auxiliary.MinusSmallCoordinates
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Actual native deficits of the two smallest-branch profiles

The native graph uses horizontal incoming neighbors when `x+y+ε` is even.
The eight representative stars are evaluated from the literal global profile.
Affine periods then give the full physical table and identify its unique
prescribed class with its full signed coset. No table identity is
assumed as a hypothesis.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusSmallProfile

/-- Twice the profile minus its two actual parity-dependent incoming values. -/
def incomingDeficit (ε : Fin 2) (x y : ℤ) : ℤ :=
  if (x + y + (ε.val : ℤ)) % 2 = 0 then
    2 * profile ε x y - profile ε (x - 1) y - profile ε (x + 1) y
  else
    2 * profile ε x y - profile ε x (y - 1) - profile ε x (y + 1)

/-- The literal smallest-minus deficit tables, in representative coordinates. -/
def representativeDeficit (ε : Fin 2) (X : Fin 4) (e : Fin 2) : ℤ :=
  if ε = 0 then
    if e = 0 then (if X = 0 then 1 else 0)
    else if X = 3 then 0 else 1
  else if e = 0 then (if X = 1 ∨ X = 2 ∨ X = 3 then 1 else 0)
  else if X = 1 then 1 else 0

/-- The source's two prescribed base coordinates. -/
def prescribedX (ε : Fin 2) : ℤ := if ε = 0 then 4 else -1

def prescribedY (ε : Fin 2) : ℤ := if ε = 0 then 1 else 0

/-- The signed prescribed coset, with no nonnegative-index restriction. -/
def prescribedCoset (ε : Fin 2) (x y : ℤ) : Prop :=
  ∃ a b : ℤ, x = prescribedX ε - 6 * a - 2 * b ∧
    y = prescribedY ε - 2 * a - 2 * b

/-- The prescribed representative for each native parity. -/
def representativePrescribed (ε : Fin 2) (X : Fin 4) (e : Fin 2) : Prop :=
  (ε = 0 ∧ X = 0 ∧ e = 1) ∨ (ε = 1 ∧ X = 3 ∧ e = 0)

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

/-- The actual deficit is zero or one at every physical point, including pins. -/
theorem incomingDeficit_zero_or_one (ε : Fin 2) (x y : ℤ) :
    incomingDeficit ε x y = 0 ∨ incomingDeficit ε x y = 1 := by
  obtain ⟨X, e, k, q, rfl, rfl⟩ := exists_lifted_cell x y
  rw [incomingDeficit_at_lifted_cell]
  fin_cases ε <;> fin_cases X <;> fin_cases e <;> decide

/-- The two prescribed representative classes are exactly the full signed cosets. -/
theorem prescribedCoset_at_lifted_cell (ε : Fin 2) (X : Fin 4) (e : Fin 2)
    (k q : ℤ) :
    prescribedCoset ε ((X.val : ℤ) + 2 * k + 4 * q) (2 * k + (e.val : ℤ)) ↔
      representativePrescribed ε X e := by
  constructor
  · rintro ⟨a, b, hx, hy⟩
    have hX := X.isLt
    have he := e.isLt
    fin_cases ε
    · norm_num [prescribedX, prescribedY] at hx hy
      exact Or.inl ⟨rfl, Fin.ext (by omega), Fin.ext (by omega)⟩
    · norm_num [prescribedX, prescribedY] at hx hy
      exact Or.inr ⟨rfl, Fin.ext (by omega), Fin.ext (by omega)⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · refine ⟨1 - q, q - k - 1, ?_, ?_⟩ <;>
        norm_num [prescribedX, prescribedY] <;> ring
    · refine ⟨-q - 1, q + 1 - k, ?_, ?_⟩ <;>
        norm_num [prescribedX, prescribedY] <;> ring

end FLattice.Auxiliary.MinusSmallProfile
