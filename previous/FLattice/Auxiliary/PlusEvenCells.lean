import FLattice.Auxiliary.PlusEvenCoordinates

/-!
# Canonical cells of the even-plus profile

The data and proof fields below describe exactly the truncated representative
domain. The decoder uses the literal Euclidean reductions of the global
profile. Recovery and coverage hold at every signed physical coordinate and
every signed pair of period indices. No choice of representatives is made.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- A representative in the exact truncated cell domain. -/
structure Cell (m : Parameter) where
  r : ℤ
  s : ℤ
  e : Fin 2
  v : Fin 2
  hr0 : 0 ≤ r
  hrm : r ≤ m.val + 1
  hs0 : 0 ≤ s
  hsm : s < m.val
  hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1)

/-- The physical horizontal coordinate of a representative. -/
def Cell.x {m : Parameter} (c : Cell m) : ℤ :=
  2 * m.val * c.r + 2 * c.s + (c.v.val : ℤ)

/-- The physical vertical coordinate of a representative. -/
def Cell.y {m : Parameter} (c : Cell m) : ℤ := (c.e.val : ℤ)

/-- Equality of the four data fields determines a cell. -/
@[ext] theorem Cell.ext {m : Parameter} {c d : Cell m}
    (hr : c.r = d.r) (hs : c.s = d.s) (he : c.e = d.e) (hv : c.v = d.v) :
    c = d := by
  cases c
  cases d
  cases hr
  cases hs
  cases he
  cases hv
  rfl

/-- Decode a signed physical point by the actual Euclidean reductions. -/
def cellOf (m : Parameter) (x y : ℤ) : Cell m := by
  let k := y / 2
  let X := (x - 2 * m.val * k) % (2 * halfPeriod m)
  have hPeriod : 0 < 2 * halfPeriod m := by
    have := halfPeriod_pos m
    omega
  have hX0 : 0 ≤ X := Int.emod_nonneg _ (ne_of_gt hPeriod)
  have hXlt : X < 2 * halfPeriod m := Int.emod_lt_of_pos _ hPeriod
  have hBounds := canonical_cell_bounds m X hX0 hXlt
  exact ⟨X / (2 * m.val), (X % (2 * m.val)) / 2,
    binaryState y, binaryState (X % (2 * m.val)), hBounds.1, hBounds.2.1,
    hBounds.2.2.1, hBounds.2.2.2.1, hBounds.2.2.2.2⟩

/-- Decoding any valid signed lift recovers its representative. -/
theorem cellOf_lifted_cell (m : Parameter) (c : Cell m) (k q : ℤ) :
    cellOf m (c.x + 2 * m.val * k + 2 * halfPeriod m * q) (2 * k + c.y) = c := by
  have hm := parameter_pos m
  have he := c.e.isLt
  have hv := c.v.isLt
  obtain ⟨hX0, hXlt⟩ := cell_coordinate_bounds m c.r c.s c.v
    c.hr0 c.hrm c.hs0 c.hsm c.hMissing
  have hRow : (2 * k + c.y) / 2 = k ∧
      (2 * k + c.y) % 2 = (c.e.val : ℤ) := by
    apply (Int.ediv_emod_unique (by omega : (0 : ℤ) < 2)).mpr
    exact ⟨by unfold Cell.y; ring, by omega, by omega⟩
  have hCol :
      (c.x + 2 * m.val * k + 2 * halfPeriod m * q - 2 * m.val * k) /
        (2 * halfPeriod m) = q ∧
      (c.x + 2 * m.val * k + 2 * halfPeriod m * q - 2 * m.val * k) %
        (2 * halfPeriod m) = c.x := by
    apply (Int.ediv_emod_unique (by have := halfPeriod_pos m; omega)).mpr
    exact ⟨by ring, hX0, hXlt⟩
  have hFirst : c.x / (2 * m.val) = c.r ∧
      c.x % (2 * m.val) = 2 * c.s + (c.v.val : ℤ) := by
    apply (Int.ediv_emod_unique (by omega : 0 < 2 * m.val)).mpr
    exact ⟨by unfold Cell.x; ring, by have := c.hs0; omega,
      by have := c.hsm; omega⟩
  have hSecond : (2 * c.s + (c.v.val : ℤ)) / 2 = c.s ∧
      (2 * c.s + (c.v.val : ℤ)) % 2 = (c.v.val : ℤ) := by
    apply (Int.ediv_emod_unique (by omega : (0 : ℤ) < 2)).mpr
    exact ⟨by ring, by omega, by omega⟩
  have hE : binaryState (2 * k + c.y) = c.e := by
    apply Fin.ext
    have hValue := binaryState_val (2 * k + c.y)
    omega
  have hV : binaryState (2 * c.s + (c.v.val : ℤ)) = c.v := by
    apply Fin.ext
    have hValue := binaryState_val (2 * c.s + (c.v.val : ℤ))
    omega
  apply Cell.ext
  · change ((c.x + 2 * m.val * k + 2 * halfPeriod m * q -
        2 * m.val * ((2 * k + c.y) / 2)) % (2 * halfPeriod m)) /
        (2 * m.val) = c.r
    rw [hRow.1, hCol.2, hFirst.1]
  · change (((c.x + 2 * m.val * k + 2 * halfPeriod m * q -
        2 * m.val * ((2 * k + c.y) / 2)) % (2 * halfPeriod m)) %
        (2 * m.val)) / 2 = c.s
    rw [hRow.1, hCol.2, hFirst.2, hSecond.1]
  · exact hE
  · change binaryState (((c.x + 2 * m.val * k + 2 * halfPeriod m * q -
        2 * m.val * ((2 * k + c.y) / 2)) % (2 * halfPeriod m)) %
        (2 * m.val)) = c.v
    rw [hRow.1, hCol.2, hFirst.2, hV]

/-- The canonical cell and explicit Euclidean indices reconstruct every point. -/
theorem canonical_lift (m : Parameter) (x y : ℤ) :
    let k := y / 2
    let q := (x - 2 * m.val * k) / (2 * halfPeriod m)
    x = (cellOf m x y).x + 2 * m.val * k + 2 * halfPeriod m * q ∧
      y = 2 * k + (cellOf m x y).y := by
  let k := y / 2
  let q := (x - 2 * m.val * k) / (2 * halfPeriod m)
  let X := (x - 2 * m.val * k) % (2 * halfPeriod m)
  constructor
  · change x = 2 * m.val * (X / (2 * m.val)) +
        2 * ((X % (2 * m.val)) / 2) +
        ((binaryState (X % (2 * m.val))).val : ℤ) +
        2 * m.val * k + 2 * halfPeriod m * q
    rw [binaryState_val]
    have hOuter : X + 2 * halfPeriod m * q = x - 2 * m.val * k :=
      Int.emod_add_mul_ediv _ _
    have hCell := Int.emod_add_mul_ediv X (2 * m.val)
    have hInner := Int.emod_add_mul_ediv (X % (2 * m.val)) 2
    omega
  · change y = 2 * (y / 2) + ((binaryState y).val : ℤ)
    rw [binaryState_val]
    have hRow := Int.emod_add_mul_ediv y 2
    omega

/-- Every point is a signed lift of its canonical cell. -/
theorem exists_lifted_cell (m : Parameter) (x y : ℤ) :
    ∃ k q : ℤ, x = (cellOf m x y).x + 2 * m.val * k + 2 * halfPeriod m * q ∧
      y = 2 * k + (cellOf m x y).y := by
  exact ⟨y / 2, (x - 2 * m.val * (y / 2)) / (2 * halfPeriod m),
    canonical_lift m x y⟩

/-- Decoding is invariant under arbitrary signed combinations of both periods. -/
theorem cellOf_add_periods (m : Parameter) (x y k q : ℤ) :
    cellOf m (x + 2 * m.val * k + 2 * halfPeriod m * q) (y + 2 * k) =
      cellOf m x y := by
  obtain ⟨k₀, q₀, hx, hy⟩ := exists_lifted_cell m x y
  have hX : x + 2 * m.val * k + 2 * halfPeriod m * q =
      (cellOf m x y).x + 2 * m.val * (k₀ + k) + 2 * halfPeriod m * (q₀ + q) := by
    calc
      _ = ((cellOf m x y).x + 2 * m.val * k₀ + 2 * halfPeriod m * q₀) +
          2 * m.val * k + 2 * halfPeriod m * q := by rw [← hx]
      _ = _ := by ring
  have hY : y + 2 * k = 2 * (k₀ + k) + (cellOf m x y).y := by omega
  rw [hX, hY]
  exact cellOf_lifted_cell m (cellOf m x y) (k₀ + k) (q₀ + q)

end FLattice.Auxiliary.PlusEvenProfile
