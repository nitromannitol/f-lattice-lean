import FLatticePaper.Plane.Induction.EPolicyValues

/-!
# Deck transfer of the value inequalities of the signed policy (task 118, W1 base)

The increments `incr F e z = F (z + e) - F z` of the reciprocal field are invariant under the kernel vector `U = (d, 1)` and shift
by a constant under the transverse vector `T = (1 - d, 1 + d)`. Hence every edge inequality of `EPolicyValues` (slip, price and
chain) is invariant under the deck lattice: its two sides shift by the same constant. This module proves the shift laws for all
deck vectors `combine i j = i U + j T` and the transfer of the three edge inequalities from a centre to its deck translate.
-/

namespace FLatticePaper.EPolicy

open FLatticePaper FLatticePaper.Induction
open FLatticePaper.Construction
open FLatticePaper.PureRank
open FLatticePaper.Farey

/-- Shifts by `n` copies of the kernel vector `U = (d, 1)`. -/
theorem incr_U_mul (k : ℕ) (e z : Site) (n : ℤ) :
    incr (reciprocalField k) e (z + (n * (2 * (k : ℤ) + 3), n)) = incr (reciprocalField k) e z := by
  induction n using Int.induction_on with
  | zero => simp only [zero_mul, Prod.mk_zero_zero, add_zero]
  | succ i ih =>
    have h : z + (((i : ℤ) + 1) * (2 * (k : ℤ) + 3), (i : ℤ) + 1) =
        (z + ((i : ℤ) * (2 * (k : ℤ) + 3), (i : ℤ))) + ((2 * (k : ℤ) + 3), 1) := by
      ext <;> (simp; try ring)
    rw [h, incr_U_inv, ih]
  | pred i ih =>
    have h : z + ((-(i : ℤ) - 1) * (2 * (k : ℤ) + 3), -(i : ℤ) - 1) + ((2 * (k : ℤ) + 3), 1) =
        z + (-(i : ℤ) * (2 * (k : ℤ) + 3), -(i : ℤ)) := by
      ext <;> (simp; try ring)
    rw [← incr_U_inv k e (z + ((-(i : ℤ) - 1) * (2 * (k : ℤ) + 3), -(i : ℤ) - 1)), h, ih]

/-- Shifts by `m` copies of the transverse vector `T = (1 - d, 1 + d)`: the increment changes by the grade term. -/
theorem incr_T_mul (k : ℕ) (e z : Site) (m : ℤ) :
    incr (reciprocalField k) e (z + (m * (1 - (2 * (k : ℤ) + 3)), m * (1 + (2 * (k : ℤ) + 3)))) =
      incr (reciprocalField k) e z - m * ((2 * (k : ℤ) + 3) * e.2 - e.1) := by
  induction m using Int.induction_on with
  | zero => simp only [zero_mul, Prod.mk_zero_zero, add_zero, sub_zero]
  | succ i ih =>
    have h : z + (((i : ℤ) + 1) * (1 - (2 * (k : ℤ) + 3)), ((i : ℤ) + 1) * (1 + (2 * (k : ℤ) + 3))) =
        (z + ((i : ℤ) * (1 - (2 * (k : ℤ) + 3)), (i : ℤ) * (1 + (2 * (k : ℤ) + 3)))) +
          (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) := by
      ext <;> (simp; try ring)
    rw [h, incr_T, ih]
    ring
  | pred i ih =>
    have h : z + ((-(i : ℤ) - 1) * (1 - (2 * (k : ℤ) + 3)), (-(i : ℤ) - 1) * (1 + (2 * (k : ℤ) + 3))) +
          (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) =
        z + (-(i : ℤ) * (1 - (2 * (k : ℤ) + 3)), -(i : ℤ) * (1 + (2 * (k : ℤ) + 3))) := by
      ext <;> (simp; try ring)
    have hT := incr_T k e (z + ((-(i : ℤ) - 1) * (1 - (2 * (k : ℤ) + 3)), (-(i : ℤ) - 1) * (1 + (2 * (k : ℤ) + 3))))
    rw [h, ih] at hT
    linear_combination -hT

/-- The increments shift by a constant under every deck vector `combine i j = i U + j T`. -/
theorem incr_combine (k : ℕ) (e z : Site) (i j : ℤ) :
    incr (reciprocalField k) e (z + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j) =
      incr (reciprocalField k) e z - j * ((2 * (k : ℤ) + 3) * e.2 - e.1) := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  rw [combine_mk_one hd]
  have h : z + (i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3)), i + j * (1 + (2 * (k : ℤ) + 3))) =
      (z + (j * (1 - (2 * (k : ℤ) + 3)), j * (1 + (2 * (k : ℤ) + 3)))) + (i * (2 * (k : ℤ) + 3), i) := by
    ext <;> (simp; try ring)
  rw [h, incr_U_mul, incr_T_mul]

/-- The slip inequality of an edge is invariant under the deck: the two increments shift by the same constant. -/
theorem slip_inc_shift (k : ℕ) (η : ℤ) (e r : Site) (i j : ℤ)
    (h : incr (reciprocalField k) e r ≤ incr (reciprocalField k) e (r + η • (reciprocalFrame k).shortShift)) :
    incr (reciprocalField k) e (r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j) ≤
      incr (reciprocalField k) e
        (r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j + η • (reciprocalFrame k).shortShift) := by
  rw [add_right_comm, incr_combine, incr_combine]
  linarith

/-- The price inequality of an edge is invariant under the deck. -/
theorem price_inc_shift (k : ℕ) (e r : Site) (i j : ℤ)
    (h : incr (reciprocalField k) e r - incr (reciprocalField k) e (r - (1, -1)) ≤ e.2) :
    incr (reciprocalField k) e (r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j) -
        incr (reciprocalField k) e (r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j - (1, -1)) ≤ e.2 := by
  rw [add_sub_right_comm, incr_combine, incr_combine]
  linarith

/-- The chain inequality of an edge is invariant under the deck. -/
theorem chain_inc_shift (k : ℕ) (η : ℤ) (e r : Site) (i j : ℤ)
    (h : incr (reciprocalField k) e r -
        incr (reciprocalField k) e (r + η • (reciprocalFrame k).shortShift - (1, -1)) ≤ e.2) :
    incr (reciprocalField k) e (r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j) -
        incr (reciprocalField k) e
          (r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j + η • (reciprocalFrame k).shortShift - (1, -1)) ≤
      e.2 := by
  have e1 : r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j + η • (reciprocalFrame k).shortShift - (1, -1) =
      (r + η • (reciprocalFrame k).shortShift - (1, -1)) + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j := by
    abel
  rw [e1, incr_combine, incr_combine]
  linarith

end FLatticePaper.EPolicy
