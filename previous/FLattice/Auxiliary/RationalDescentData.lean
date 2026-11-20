import Mathlib.Data.Nat.GCD.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Primitive rational parameters and the literal descent size

This is arithmetic infrastructure only. It defines no matrix admissibility
or graph property. The natural subtraction in T is exact on valid pairs.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.RationalDescent

/-- The exact primitive pairs 0≤n≤d, d>0 in the source. -/
structure Pair where
  n : ℕ
  d : ℕ
  d_pos : 0 < d
  n_le_d : n ≤ d
  coprime : Nat.Coprime n d

/-- The parity factor, using the literal sum parity. -/
def kappa (n d : ℕ) : ℕ := if (n + d) % 2 = 0 then 1 else 2

/-- The source polynomial, as a natural number on a valid pair. -/
def sizePolynomial (n d : ℕ) : ℕ := d ^ 2 + 2 * d * n - n ^ 2

/-- The positive primary coordinate Q=κT. -/
def primary (p : Pair) : ℕ := kappa p.n p.d * sizePolynomial p.n p.d

/-- The source's secondary indicator of slope greater than one half. -/
def secondary (p : Pair) : ℕ := if p.d < 2 * p.n then 1 else 0

/-- There is no truncation in T on the valid range. -/
theorem sizePolynomial_add_square (n d : ℕ) (hnd : n ≤ d) :
    sizePolynomial n d + n ^ 2 = d ^ 2 + 2 * d * n := by
  apply Nat.sub_add_cancel
  nlinarith

/-- The primary polynomial is strictly positive throughout the valid range. -/
theorem sizePolynomial_pos (n d : ℕ) (hd : 0 < d) (hnd : n ≤ d) :
    0 < sizePolynomial n d := by
  have h := sizePolynomial_add_square n d hnd
  have hD : 0 < d ^ 2 := by positivity
  nlinarith

/-- Both values of κ are positive. -/
theorem kappa_pos (n d : ℕ) : 0 < kappa n d := by
  unfold kappa
  split <;> omega

/-- The source primary coordinate is a positive integer. -/
theorem primary_pos (p : Pair) : 0 < primary p :=
  Nat.mul_pos (kappa_pos p.n p.d) (sizePolynomial_pos p.n p.d p.d_pos p.n_le_d)

/-- Primitivity identifies the zero endpoint exactly. -/
theorem zero_endpoint (p : Pair) (hn : p.n = 0) : p.d = 1 := by
  have h := p.coprime
  simpa [hn] using h

/-- Primitivity identifies the unit endpoint exactly. -/
theorem one_endpoint (p : Pair) (hne : p.n = p.d) : p.n = 1 ∧ p.d = 1 := by
  have h := p.coprime
  simp only [hne, Nat.coprime_self] at h
  exact ⟨hne.trans h, h⟩

/-- The only primitive parameter at slope one half is (1,2). -/
theorem half_endpoint (p : Pair) (hHalf : p.d = 2 * p.n) : p.n = 1 ∧ p.d = 2 := by
  have h := p.coprime.gcd_eq_one
  rw [hHalf, Nat.gcd_mul_left_right] at h
  exact ⟨h, by omega⟩

/-- A common divisor of d−n and d+n divides two, for every primitive pair. -/
theorem dual_gcd_dvd_two (p : Pair) : Nat.gcd (p.d - p.n) (p.d + p.n) ∣ 2 := by
  have hnd := p.n_le_d
  let b := Nat.gcd (p.d - p.n) (p.d + p.n)
  have hLeft : b ∣ p.d - p.n := Nat.gcd_dvd_left _ _
  have hRight : b ∣ p.d + p.n := Nat.gcd_dvd_right _ _
  have hD : b ∣ 2 * p.d := by
    have hSum := Nat.dvd_add hLeft hRight
    convert hSum using 1
    omega
  have hN : b ∣ 2 * p.n := by
    have hSub := Nat.dvd_sub hRight hLeft
    convert hSub using 1
    omega
  have hG := Nat.dvd_gcd hN hD
  rw [Nat.gcd_mul_left, p.coprime.gcd_eq_one, mul_one] at hG
  exact hG

/-- The normalizing divisor is exactly one or two, without a parity assumption. -/
theorem dual_gcd_cases (p : Pair) :
    Nat.gcd (p.d - p.n) (p.d + p.n) = 1 ∨ Nat.gcd (p.d - p.n) (p.d + p.n) = 2 := by
  have hd := p.d_pos
  have h := dual_gcd_dvd_two p
  rcases h with ⟨a, ha⟩
  have hb0 : 0 < Nat.gcd (p.d - p.n) (p.d + p.n) := by
    apply Nat.gcd_pos_of_pos_right
    omega
  have ha0 : 0 < a := by nlinarith
  have hb2 : Nat.gcd (p.d - p.n) (p.d + p.n) ≤ 2 := by nlinarith
  omega

/-- Exact homogeneity of the source polynomial on its valid range. -/
theorem sizePolynomial_scale (a n d : ℕ) (hnd : n ≤ d) :
    sizePolynomial (a*n) (a*d) = a^2 * sizePolynomial n d := by
  have h0 := sizePolynomial_add_square n d hnd
  have h1 := sizePolynomial_add_square (a*n) (a*d) (Nat.mul_le_mul_left a hnd)
  have h2 := congrArg (fun z : ℕ => a^2*z) h0
  nlinarith only [h1, h2]

/-- The unreduced dual doubles T exactly. -/
theorem sizePolynomial_dual (n d : ℕ) (hnd : n ≤ d) :
    sizePolynomial (d-n) (d+n) = 2 * sizePolynomial n d := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hnd
  have h0 := sizePolynomial_add_square n (n+s) (by omega)
  have h1 := sizePolynomial_add_square s (n+s+n) (by omega)
  simp only [Nat.add_sub_cancel_left]
  nlinarith only [h0, h1]

end FLattice.Auxiliary.RationalDescent
