import FLattice.Auxiliary.BranchMatrix
import FLattice.Auxiliary.TransportGrowthData

/-!
# The branch matrices are the matrices of the proved integer transports

The source coefficient is k=2m for plus and k=2m+2 for minus. These literal
equalities connect the branch algebra to the concrete transport APIs.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.BranchMatrix

/-- The plus coefficient is k=2m, including the smallest m=1. -/
theorem plusC_eq_periodMatrix (m : ℤ) :
    plusC (2 * (m : ℝ)) = PlusTransport.periodMatrix m := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [plusC, PlusTransport.periodMatrix]
  ring

/-- The minus coefficient is k=2m+2 and has the same actual C. -/
theorem minusC_eq_periodMatrix (m : ℤ) :
    minusC (2 * (m : ℝ) + 2) = PlusTransport.periodMatrix m := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [minusC, PlusTransport.periodMatrix]
  ring

/-- Exact identification of the plus inverse map with the integer transport's real map. -/
theorem plusG_inv_eq_transportMatrix (m : ℤ) :
    (plusG (2 * (m : ℝ)))⁻¹ = TransportGrowthData.plusMatrix m := by
  rw [plusG_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plusB, TransportGrowthData.plusMatrix]

/-- Exact identification of the minus inverse map with the integer transport's real map. -/
theorem minusG_inv_eq_transportMatrix (m : ℤ) :
    (minusG (2 * (m : ℝ) + 2))⁻¹ = TransportGrowthData.minusMatrix m := by
  rw [minusG_inv]
  rfl

/-- The concrete plus transport has the exact branch domain and parent image. -/
theorem plus_integer_coefficient_domain_and_map (m : ℤ) (hm : 1 ≤ m)
    (n e : ℝ) (he : 0 < e) (hn : 0 ≤ n) (hne : n ≤ e) :
    (rankOneMatrix e (2 * (m : ℝ) * e + n) + (PlusTransport.periodMatrix m)⁻¹).PosDef ∧
      MatrixInverseOrder.transportMatrix (PlusTransport.periodMatrix m)⁻¹
        (TransportGrowthData.plusMatrix m) (rankOneMatrix e (2 * (m : ℝ) * e + n)) =
          rankOneMatrix n e := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simpa only [plusC_eq_periodMatrix, plusG_inv_eq_transportMatrix] using
    plus_domain_and_map (2 * (m : ℝ)) n e (by linarith) he hn hne

/-- The concrete minus transport has the exact branch domain and parent image. -/
theorem minus_integer_coefficient_domain_and_map (m : ℤ) (hm : 1 ≤ m)
    (n e : ℝ) (he : 0 < e) (hn : 0 < n) (hne : n < e) :
    (rankOneMatrix e ((2 * (m : ℝ) + 2) * e - n) + (PlusTransport.periodMatrix m)⁻¹).PosDef ∧
      MatrixInverseOrder.transportMatrix (PlusTransport.periodMatrix m)⁻¹
        (TransportGrowthData.minusMatrix m) (rankOneMatrix e ((2 * (m : ℝ) + 2) * e - n)) =
          rankOneMatrix n e := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simpa only [minusC_eq_periodMatrix, minusG_inv_eq_transportMatrix] using
    minus_domain_and_map (2 * (m : ℝ) + 2) n e (by linarith) he hn hne

/-- Source-shaped strict domination for the concrete plus transport. -/
theorem plus_integer_coefficient_strict_dominator (m : ℤ) (hm : 1 ≤ m)
    (n e : ℝ) (he : 0 < e) (hn : 0 ≤ n) (hne : n ≤ e)
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hAbove : (M - rankOneMatrix e (2 * (m : ℝ) * e + n)).PosDef) :
    (M + (PlusTransport.periodMatrix m)⁻¹).PosDef ∧
      (MatrixInverseOrder.transportMatrix (PlusTransport.periodMatrix m)⁻¹
        (TransportGrowthData.plusMatrix m) M - rankOneMatrix n e).PosDef := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simpa only [plusC_eq_periodMatrix, plusG_inv_eq_transportMatrix] using
    plus_strict_dominator (2 * (m : ℝ)) n e (by linarith) he hn hne M hAbove

/-- Source-shaped strict domination for the concrete minus transport. -/
theorem minus_integer_coefficient_strict_dominator (m : ℤ) (hm : 1 ≤ m)
    (n e : ℝ) (he : 0 < e) (hn : 0 < n) (hne : n < e)
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hAbove : (M - rankOneMatrix e ((2 * (m : ℝ) + 2) * e - n)).PosDef) :
    (M + (PlusTransport.periodMatrix m)⁻¹).PosDef ∧
      (MatrixInverseOrder.transportMatrix (PlusTransport.periodMatrix m)⁻¹
        (TransportGrowthData.minusMatrix m) M - rankOneMatrix n e).PosDef := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simpa only [minusC_eq_periodMatrix, minusG_inv_eq_transportMatrix] using
    minus_strict_dominator (2 * (m : ℝ) + 2) n e (by linarith) he hn hne M hAbove

end FLattice.Auxiliary.BranchMatrix
