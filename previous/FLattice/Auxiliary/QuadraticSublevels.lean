import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite sublevels from an eventual quadratic lower bound

The carrier is the integer plane and the squared size is the explicit sum of
the two real coordinate squares. The proofs use finite integer rectangles;
no norm convention, asymptotic interface, or lattice profile is assumed.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary

/-- Every real squared-size sublevel of the integer plane is finite,
including the empty sublevels with a negative bound. -/
theorem finite_lattice_normSq_le (R : ℝ) :
    {z : ℤ × ℤ | (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 ≤ R}.Finite := by
  obtain ⟨N, hN⟩ := exists_int_gt (R + 1)
  let rectangle : Finset (ℤ × ℤ) :=
    (Finset.Icc (-N) N).product (Finset.Icc (-N) N)
  apply rectangle.finite_toSet.subset
  intro z hz
  have hsize : (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 ≤ R := hz
  have hxlo : -(N : ℝ) ≤ (z.1 : ℝ) := by
    nlinarith [sq_nonneg ((z.1 : ℝ) + 1), sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]
  have hxhi : (z.1 : ℝ) ≤ (N : ℝ) := by
    nlinarith [sq_nonneg ((z.1 : ℝ) - 1), sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]
  have hylo : -(N : ℝ) ≤ (z.2 : ℝ) := by
    nlinarith [sq_nonneg ((z.2 : ℝ) + 1), sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]
  have hyhi : (z.2 : ℝ) ≤ (N : ℝ) := by
    nlinarith [sq_nonneg ((z.2 : ℝ) - 1), sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]
  have hx : -N ≤ z.1 ∧ z.1 ≤ N := by exact_mod_cast And.intro hxlo hxhi
  have hy : -N ≤ z.2 ∧ z.2 ≤ N := by exact_mod_cast And.intro hylo hyhi
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hx, Finset.mem_Icc.mpr hy⟩

/-- An eventual positive quadratic lower bound makes every real sublevel finite.
The threshold and additive constant are arbitrary real numbers. -/
theorem finite_sublevel_of_eventual_quadratic_lower_bound
    (g : ℤ × ℤ → ℝ) (c C T : ℝ) (hc : 0 < c)
    (hLower : ∀ z : ℤ × ℤ,
      T ≤ (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 →
        c * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) - C ≤ g z)
    (b : ℝ) : {z | g z ≤ b}.Finite := by
  apply (finite_lattice_normSq_le (max T ((b + C) / c))).subset
  intro z hz
  change (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 ≤ max T ((b + C) / c)
  by_cases hT : T ≤ (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2
  · have hquad := hLower z hT
    have hbound : (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 ≤ (b + C) / c := by
      apply (le_div_iff₀ hc).mpr
      change g z ≤ b at hz
      nlinarith
    exact hbound.trans (le_max_right _ _)
  · exact (le_of_lt (lt_of_not_ge hT)).trans (le_max_left _ _)

end FLattice.Auxiliary
