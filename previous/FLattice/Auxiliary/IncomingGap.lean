import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Order.Basic
import Lean.Elab.Tactic.Omega

/-!
# Integer counting and subtraction for indexed incoming values

Conditional internal algebraic infrastructure. No graph, lattice, growth,
or recurrence definitions are used. The finite type indexes incoming
slots; different indices may name the same vertex, so multiplicities are
retained in every sum and cardinality.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary

open scoped BigOperators

/-- If every indexed value is at least `t`, and the values at the selected
indices are at least `t + 1`, their sum gains one per selected index. -/
theorem card_mul_add_card_le_sum {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (t : ℤ) (S : Finset ι)
    (hLower : ∀ i, t ≤ a i)
    (hSelected : ∀ i ∈ S, t + 1 ≤ a i) :
    (Fintype.card ι : ℤ) * t + (S.card : ℤ) ≤ ∑ i, a i := by
  classical
  calc
    (Fintype.card ι : ℤ) * t + (S.card : ℤ) =
        ∑ i, (t + if i ∈ S then (1 : ℤ) else 0) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ ≤ ∑ i, a i := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ S
      · simpa only [if_pos hi] using hSelected i hi
      · simpa only [if_neg hi, add_zero] using hLower i

/-- Subtracting a reference function from a capped incoming inequality
produces the stated residual deficit. No injectivity of `incoming` is
assumed, and `d` is an arbitrary integer coefficient. -/
theorem sum_incoming_gap_le {ι V : Type*} [Fintype ι]
    (incoming : ι → V) (h u : V → ℤ) (x : V) (d β η : ℤ)
    (hBound : (∑ i, h (incoming i)) - d * h x ≤ β)
    (hDeficit : η = β - ((∑ i, u (incoming i)) - d * u x)) :
    (∑ i, (h (incoming i) - u (incoming i))) ≤ d * (h x - u x) + η := by
  rw [Finset.sum_sub_distrib, mul_sub]
  omega

end FLattice.Auxiliary
