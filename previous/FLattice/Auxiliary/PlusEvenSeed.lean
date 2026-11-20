import FLattice.Auxiliary.PlusEvenPhysicalCells

/-!
# A one-dimensional seed for the even-plus profile

The restriction to even-even physical coordinates separates into a fixed
quadratic in the row and one affine-periodic integer sequence. The sequence
is an explicit Euclidean formula on all signed integer inputs.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- The explicit integer sequence determining the even-even sublattice. -/
def evenSeed (m : Parameter) (n : ℤ) : ℤ :=
  let q := n / halfPeriod m
  let t := n % halfPeriod m
  PlusEvenBulk.u00 (t / m.val) (t % m.val) - 2 * q * t - halfPeriod m * q ^ 2

/-- In the adapted coordinate `n=i-m*j`, the even-even profile has one-dimensional data. -/
theorem profile_even_even (m : Parameter) (i j : ℤ) :
    profile m (2 * i) (2 * j) = evenSeed m (i - m.val * j) - j ^ 2 - j := by
  let n := i - m.val * j
  let q := n / halfPeriod m
  let t := n % halfPeriod m
  have hJ := halfPeriod_pos m
  have hm := parameter_pos m
  have ht0 : 0 ≤ t := Int.emod_nonneg n (ne_of_gt hJ)
  have htJ : t < halfPeriod m := Int.emod_lt_of_pos n hJ
  have hOuter : t + halfPeriod m * q = n := Int.emod_add_mul_ediv n (halfPeriod m)
  have hs0 := Int.emod_nonneg t (ne_of_gt hm)
  have hsm := Int.emod_lt_of_pos t hm
  have hInner := Int.emod_add_mul_ediv t m.val
  have hProfile := profile_of_reduction m (2 * i) (2 * j) j q (2 * t) 0
    (by norm_num) (by dsimp [n] at hOuter; nlinarith) (by omega) (by omega)
  have hStrip := stripHeight_at_cell m (t / m.val) (t % m.val) 0 0 hs0 hsm
  norm_num at hStrip hProfile
  have hStrip' : stripHeight m (2 * t) 0 =
      PlusEvenBulk.u00 (t / m.val) (t % m.val) := by
    rw [show 2 * t = 2 * m.val * (t / m.val) + 2 * (t % m.val) by nlinarith [hInner]]
    exact hStrip
  rw [hStrip'] at hProfile
  change profile m (2 * i) (2 * j) =
    PlusEvenBulk.u00 (t / m.val) (t % m.val) - 2 * q * t - halfPeriod m * q ^ 2
      - j ^ 2 - j
  rw [hProfile]
  ring

/-- The seed has an explicit affine period on every signed integer input. -/
theorem evenSeed_add_period (m : Parameter) (n : ℤ) :
    evenSeed m (n + halfPeriod m) - evenSeed m n = -2 * n - halfPeriod m := by
  have h := profile_add_horizontal_period m (2 * n) 0
  have hBase := profile_even_even m n 0
  have hShift := profile_even_even m (n + halfPeriod m) 0
  norm_num at h hBase hShift
  rw [show 2 * n + 2 * halfPeriod m = 2 * (n + halfPeriod m) by ring,
    hShift, hBase] at h
  linarith

end FLattice.Auxiliary.PlusEvenProfile
