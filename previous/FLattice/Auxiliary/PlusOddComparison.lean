import FLattice.Auxiliary.PlusOddCellClock
import FLattice.Auxiliary.PlusOddDeficitTable
import FLattice.Auxiliary.PlusOddCellCoset
import FLattice.Auxiliary.PlusOddIncomingSums
import FLattice.Auxiliary.PlusOddSpecialValues
import FLattice.Auxiliary.PlusOddQuadratic
import FLattice.Auxiliary.BoundedRankComparison
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Global odd comparison from the actual profile and incoming edges

The literal deficit identity, signed prescribed coset and full overridden
cell clock discharge all geometric inputs of the bounded-clock comparison.
The unknown has no periodicity assumption. The minimum set may be infinite.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- The full signed physical deficit is exactly the displayed cell table. -/
theorem incomingDeficit_eq_table (m : Parameter) (x y : ℤ) :
    incomingDeficit m x y = cellDeficitTable (cellOf m x y) := by
  rw [incomingDeficit_eq_cell, incomingDeficit_at_cell]

/-- Native superharmonicity, the original signed prescribed values and a
bounded-below gap imply the global odd-profile comparison. -/
theorem profile_le_of_bounded_gap
    (m : Parameter) (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hPrescribed : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
        h (-1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -2 * m.val * a - 2 * b))
    (hGapBounded : ∃ B : ℤ, ∀ z : ℤ × ℤ, B ≤ h z - profile m z.1 z.2) :
    ∀ z : ℤ × ℤ, profile m z.1 z.2 ≤ h z := by
  apply le_of_bounded_gap_and_rank
    (fun z : ℤ × ℤ => incomingPoint z.1 z.2) h
    (fun z => profile m z.1 z.2) (fun _ => 0)
    (fun z => cellClock (cellOf m z.1 z.2))
    {z | cellPrescribed (cellOf m z.1 z.2)} hGapBounded
  · exact ⟨0, fun z => cellClock_cellOf_nonneg m z.1 z.2⟩
  · rintro ⟨x, y⟩
    have hStar := hSuperharmonic x y
    rw [incomingPoint_sum]
    norm_num only [Fintype.card_fin, Nat.cast_ofNat]
    omega
  · rintro ⟨x, y⟩ hPin
    obtain ⟨a, b, rfl, rfl⟩ := (cellPrescribed_cellOf_iff m x y).mp hPin
    rw [profile_prescribed_coset]
    exact hPrescribed a b
  · rintro ⟨x, y⟩ hNotPin
    obtain ⟨S, hCount, hClock⟩ := cell_clock_selected (cellOf m x y) hNotPin
    refine ⟨S, ?_, ?_⟩
    · rw [← incomingDeficit_eq_table m x y, incomingDeficit_eq_residual] at hCount
      simpa only [Fintype.card_fin, Nat.cast_ofNat] using hCount
    · intro i hi
      rw [cellOf_incomingPoint]
      exact hClock i hi

private theorem gap_bounded_of_finite_nonpositive_sublevel
    (g : ℤ × ℤ → ℤ) (hFinite : {z | g z ≤ 0}.Finite) :
    ∃ B : ℤ, ∀ z, B ≤ g z := by
  by_cases hNonempty : {z | g z ≤ 0}.Nonempty
  · obtain ⟨z, hz, hMin⟩ := Set.exists_min_image {z | g z ≤ 0} g hFinite hNonempty
    refine ⟨g z, ?_⟩
    intro w
    by_cases hw : g w ≤ 0
    · exact hMin w hw
    · change g z ≤ 0 at hz
      omega
  · refine ⟨0, ?_⟩
    intro z
    have hz : ¬g z ≤ 0 := fun hz => hNonempty ⟨z, hz⟩
    omega

/-- The same comparison under the source's uniform quadratic growth and
strict domination by the actual inverse matrix. -/
theorem profile_le_of_quadratic_growth
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          ε * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hPrescribed : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
        h (-1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -2 * m.val * a - 2 * b)) :
    ∀ z : ℤ × ℤ, profile m z.1 z.2 ≤ h z := by
  apply profile_le_of_bounded_gap m h hSuperharmonic hPrescribed
  apply gap_bounded_of_finite_nonpositive_sublevel
  exact finite_gap_sublevels_of_quadratic_growth m h M hGrowth hPositive 0

end FLattice.Auxiliary.PlusOddProfile
