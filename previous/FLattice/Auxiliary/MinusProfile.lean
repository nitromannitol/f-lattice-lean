import FLattice.Auxiliary.PlusEvenCells

/-!
# The literal general-minus comparison profiles for m >= 2

Only the parameter and exact representative geometry are shared with the
larger plus family. The heights and affine extension are independent literal
definitions. Here `ε` selects the profile/native parity, whereas `c.e` is the
vertical representative residue and `c.v` its horizontal binary residue.
All representative heights are defined on the source's exact valid Cell
carrier; the separately treated m = 1 case is outside this module.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile

/-- The source's E/O representative heights on the exact truncated cell domain.
This retains E10(0,0)=0, both other even low rows, and the odd row-zero override. -/
def representativeHeight (m : Parameter) (ε : Fin 2) (c : Cell m) : ℤ :=
  if ε = 0 then
    if c.r = 0 ∨ c.r = 1 then
      if c.r = 0 ∧ c.s = 0 ∧ c.e = 1 ∧ c.v = 0 then 0 else 1
    else
      -c.r ^ 2 + ((c.e.val : ℤ) + 1) * c.r + 1 - (c.e.val : ℤ) +
        (if c.e = 0 then
          if c.v = 0 then max (c.r - c.s) 0 + max (c.r - c.s - 2) 0
          else max (c.r - c.s - 1) 0 + max (c.r - c.s - 2) 0
        else if c.v = 0 then max (c.r - c.s - 1) 0 + max (c.r - c.s - 2) 0
        else max (c.r - c.s - 1) 0 + max (c.r - c.s - 3) 0)
  else
    let j := 2 * c.s + (c.v.val : ℤ);
    -c.r ^ 2 + (c.e.val : ℤ) * c.r +
      (if c.r = 0 then
        if c.e = 0 then (if j ≤ 2 * m.val - 3 then 1 else 0) else 0
      else max (1 - (c.e.val : ℤ)) (2 * c.r - 3 - 2 * (c.e.val : ℤ) - j) -
        max (j - 2 * m.val + 3) 0)

/-- The horizontal affine constant: c0=m+1 and c1=-2. -/
def periodConstant (m : Parameter) (ε : Fin 2) : ℤ :=
  if ε = 0 then m.val + 1 else -2

/-- The source affine extension, using the actual Euclidean canonical Cell. -/
def profile (m : Parameter) (ε : Fin 2) (x y : ℤ) : ℤ :=
  let c := cellOf m x y
  let t := y / 2
  let q := (x - 2 * m.val * t) / (2 * halfPeriod m)
  representativeHeight m ε c - q * c.x + q * m.val * c.y - halfPeriod m * q ^ 2 +
    periodConstant m ε * q - t * c.y - t ^ 2 - (ε.val : ℤ) * t

end FLattice.Auxiliary.MinusProfile
