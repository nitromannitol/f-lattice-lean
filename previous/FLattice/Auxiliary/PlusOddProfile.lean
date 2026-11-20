import FLattice.Auxiliary.PlusOddBulk
import FLattice.Auxiliary.PlusEvenProfile

/-!
# The literal global odd-plus comparison profile

The parameter, binary residues and period lattice are shared with the
even-plus family. The heights are independent: the two low rows are zero,
and the last odd column is lowered by one in every remaining valid row.
The affine extension has the odd family's `(m - 1)q` term and no `-k` term.
No superharmonicity or comparison property is assumed by these definitions.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- The four odd-plus ramps, corrected on the two low rows and the last
odd column. The global decoder evaluates this formula only on valid cells. -/
def representativeHeight (m : Parameter) (e v : Fin 2) (r s : ℤ) : ℤ :=
  if r = 0 ∨ r = 1 then 0
  else
    (if e = 0 then
      if v = 0 then PlusOddBulk.v00 r s else PlusOddBulk.v01 r s
    else if v = 0 then PlusOddBulk.v10 r s else PlusOddBulk.v11 r s) -
      if s = m.val - 1 ∧ v = 1 then 1 else 0

/-- Evaluate the corrected odd-plus representative in the two-row strip. -/
def stripHeight (m : Parameter) (X : ℤ) (e : Fin 2) : ℤ :=
  representativeHeight m e (binaryState (X % (2 * m.val)))
    (X / (2 * m.val)) ((X % (2 * m.val)) / 2)

/-- The global odd-plus function, with the source's exact signed affine extension. -/
def profile (m : Parameter) (x y : ℤ) : ℤ :=
  let k := y / 2
  let e := y % 2
  let q := (x - 2 * m.val * k) / (2 * halfPeriod m)
  let X := (x - 2 * m.val * k) % (2 * halfPeriod m)
  stripHeight m X (binaryState y) - q * X + q * m.val * e - halfPeriod m * q ^ 2
    + (m.val - 1) * q - k * e - k ^ 2

end FLattice.Auxiliary.PlusOddProfile
