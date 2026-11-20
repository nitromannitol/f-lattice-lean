import FLattice.Auxiliary.PlusEvenBulk
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith

/-!
# The literal global even-plus comparison function

The parameter is restricted to the manuscript range. Euclidean division
reduces every signed physical coordinate to the two-row strip, then to
its representative cell. Both exceptional heights are included before
the affine extension is applied.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- The allowed integer parameters of the even-plus comparison. -/
abbrev Parameter := {m : ℤ // 2 ≤ m}

/-- Half of the horizontal period. -/
def halfPeriod (m : Parameter) : ℤ := m.val ^ 2 + 2 * m.val - 1

theorem parameter_pos (m : Parameter) : 0 < m.val := by
  have hm := m.property
  omega

theorem halfPeriod_pos (m : Parameter) : 0 < halfPeriod m := by
  unfold halfPeriod
  have hm := m.property
  nlinarith [sq_nonneg m.val]

/-- The binary residue of any signed integer, with values in `Fin 2`. -/
def binaryState (z : ℤ) : Fin 2 := ⟨(z % 2).toNat, by omega⟩

@[simp] theorem binaryState_val (z : ℤ) :
    ((binaryState z).val : ℤ) = z % 2 := by
  unfold binaryState
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))

@[simp] theorem binaryState_of_bit (e : Fin 2) : binaryState (e.val : ℤ) = e := by
  apply Fin.ext
  simp only [binaryState]
  have he := e.isLt
  omega

/-- The representative formula with both low-row overrides. -/
def representativeHeight (e v : Fin 2) (r s : ℤ) : ℤ :=
  if e = 0 then
    if v = 0 then PlusEvenBulk.u00 r s else PlusEvenBulk.u01 r s
  else if r = 0 ∧ s = 0 then
    -(v.val : ℤ)
  else if v = 0 then PlusEvenBulk.u10 r s else PlusEvenBulk.u11 r s

/-- Evaluate a representative cell in the two-row strip. -/
def stripHeight (m : Parameter) (X : ℤ) (e : Fin 2) : ℤ :=
  representativeHeight e (binaryState (X % (2 * m.val)))
    (X / (2 * m.val)) ((X % (2 * m.val)) / 2)

/-- The global profile, using exactly the manuscript's affine extension. -/
def profile (m : Parameter) (x y : ℤ) : ℤ :=
  let k := y / 2
  let e := y % 2
  let q := (x - 2 * m.val * k) / (2 * halfPeriod m)
  let X := (x - 2 * m.val * k) % (2 * halfPeriod m)
  stripHeight m X (binaryState y) - q * X + q * m.val * e - halfPeriod m * q ^ 2
    - k * e - k ^ 2 - k

end FLattice.Auxiliary.PlusEvenProfile
