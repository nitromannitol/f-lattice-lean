import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The two literal eight-class smallest-minus comparison profiles

Both parity parameters and both representative coordinates have the exact
finite carriers in the source. The global function uses signed Euclidean
division with periods `(2,2)` and `(4,0)`. It is independent of the parameter
range and definitions used by the larger plus profiles.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusSmallProfile

/-- The binary residue of a signed integer. -/
def binaryState (z : ℤ) : Fin 2 := ⟨(z % 2).toNat, by omega⟩

/-- The residue modulo four of a signed integer. -/
def horizontalState (z : ℤ) : Fin 4 := ⟨(z % 4).toNat, by omega⟩

@[simp] theorem binaryState_val (z : ℤ) :
    ((binaryState z).val : ℤ) = z % 2 := by
  unfold binaryState
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))

@[simp] theorem horizontalState_val (z : ℤ) :
    ((horizontalState z).val : ℤ) = z % 4 := by
  unfold horizontalState
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))

@[simp] theorem binaryState_of_bit (e : Fin 2) :
    binaryState (e.val : ℤ) = e := by
  apply Fin.ext
  have he := e.isLt
  have h := binaryState_val (e.val : ℤ)
  omega

@[simp] theorem horizontalState_of_coordinate (X : Fin 4) :
    horizontalState (X.val : ℤ) = X := by
  apply Fin.ext
  have hX := X.isLt
  have h := horizontalState_val (X.val : ℤ)
  omega

/-- The source's two complete eight-class tables: even `(1,0,1,1,1,1,1,1)`
and odd `(0,0,0,0,-1,-1,-2,-2)`, indexed by `2 * X + e`. -/
def representativeHeight (ε : Fin 2) (X : Fin 4) (e : Fin 2) : ℤ :=
  if ε = 0 then (if X = 0 ∧ e = 1 then 0 else 1)
  else if X = 0 ∨ X = 1 then 0 else if X = 2 then -1 else -2

/-- The horizontal affine constant in the smallest-minus source. -/
def periodConstant (ε : Fin 2) : ℤ := if ε = 0 then 2 else -2

/-- The exact affine extension of the eight-class table on the whole plane. -/
def profile (ε : Fin 2) (x y : ℤ) : ℤ :=
  let k := y / 2
  let e := y % 2
  let q := (x - 2 * k) / 4
  let X := (x - 2 * k) % 4
  representativeHeight ε (horizontalState (x - 2 * k)) (binaryState y) -
    q * X + q * e - 2 * q ^ 2 + periodConstant ε * q -
      k * e - k ^ 2 - (ε.val : ℤ) * k

end FLattice.Auxiliary.MinusSmallProfile
