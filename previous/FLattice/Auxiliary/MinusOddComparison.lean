import FLattice.Auxiliary.MinusOddStagedEdges
import FLattice.Auxiliary.MinusSpecialValues
import FLattice.Auxiliary.MinusQuadratic
import FLattice.Auxiliary.StagedLowerComparison
import Mathlib.Algebra.BigOperators.Fin

/-!
# Odd-minus comparison through three physical directions

The complete physical table and source regions discharge every geometric
input of staged integer comparison. Only a finite negative gap set is
needed in the first theorem. The final theorem derives it from the original
quadratic growth and positivity of the actual matrix gap. Neither theorem
assumes periodicity of the unknown or a bounded physical rank.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile PlusOddProfile

private theorem odd_incoming_sum (h : ℤ × ℤ → ℤ) (x y : ℤ) :
    (∑ i : Fin 2, h (incomingPoint x y i)) =
      if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
      else h (x, y - 1) + h (x, y + 1) := by
  simp only [Fin.sum_univ_two, incomingPoint]
  split_ifs <;> norm_num [sub_eq_add_neg] at *

private theorem odd_deficit_eq_residual (m : Parameter) (x y : ℤ) :
    incomingDeficit m 1 x y =
      0 - ((∑ i : Fin 2, profile m 1 (incomingPoint x y i).1 (incomingPoint x y i).2) -
        2 * profile m 1 x y) := by
  rw [odd_incoming_sum (fun z => profile m 1 z.1 z.2)]
  unfold incomingDeficit
  norm_num only [Fin.val_one, Int.cast_one]
  split_ifs <;> ring

/-- Actual odd superharmonicity, all source prescribed values and finiteness
of the negative gap set imply the global odd-minus lower comparison. -/
theorem odd_profile_le_of_finite_negative_gap
    (m : Parameter) (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hPrescribed : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        h (-1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -2 * m.val * a - 2 * b))
    (hFinite : {z : ℤ × ℤ | h z - profile m 1 z.1 z.2 < 0}.Finite) :
    ∀ z : ℤ × ℤ, profile m 1 z.1 z.2 ≤ h z := by
  have hGap : ∀ z : ℤ × ℤ, 0 ≤ h z - profile m 1 z.1 z.2 := by
    apply zero_le_gap_of_staged_incoming (fun _ : ℤ × ℤ => 2)
      (fun z => incomingPoint z.1 z.2)
      (fun z => h z - profile m 1 z.1 z.2)
      (fun z => (incomingDeficit m 1 z.1 z.2).toNat)
      (fun z => oddCellStage (cellOf m z.1 z.2))
      (fun z => oddPhysicalRank m z.1 z.2)
      {z | oddCellPrescribed (cellOf m z.1 z.2)}
    · rintro ⟨x, y⟩ hPin
      obtain ⟨a, b, rfl, rfl⟩ := (oddCellPrescribed_cellOf_iff m x y).mp hPin
      have hValue := profile_prescribed_coset m 1 a b
      have hBound := hPrescribed a b
      norm_num at hValue hBound ⊢
      omega
    · rintro ⟨x, y⟩ _
      change (∑ i : Fin 2, (h (incomingPoint x y i) -
          profile m 1 (incomingPoint x y i).1 (incomingPoint x y i).2)) ≤
        2 * (h (x, y) - profile m 1 x y) + ((incomingDeficit m 1 x y).toNat : ℤ)
      rw [Int.toNat_of_nonneg (odd_incomingDeficit_bounds m x y).1]
      have hCap : (∑ i : Fin 2, h (incomingPoint x y i)) - 2 * h (x, y) ≤ 0 := by
        rw [odd_incoming_sum]
        exact sub_nonpos.mpr (hSuperharmonic x y)
      exact sum_incoming_gap_le (incomingPoint x y) h
        (fun z => profile m 1 z.1 z.2) (x, y) 2 0 (incomingDeficit m 1 x y)
        hCap (odd_deficit_eq_residual m x y)
    · rintro ⟨x, y⟩ hNotPin
      obtain ⟨S, hCount, hMove⟩ := odd_physical_selected m x y hNotPin
      refine ⟨S, ?_, hMove⟩
      change (incomingDeficit m 1 x y).toNat < S.card
      have hCast := Int.toNat_of_nonneg (odd_incomingDeficit_bounds m x y).1
      omega
    · exact hFinite
  intro z
  exact sub_nonneg.mp (hGap z)

/-- The source's original uniform quadratic growth and actual inverse-matrix
positivity imply the odd-minus comparison, without any added finite-gap or
geometric assumption. -/
theorem odd_profile_le_of_quadratic_growth
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hPrescribed : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        h (-1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -2 * m.val * a - 2 * b)) :
    ∀ z : ℤ × ℤ, profile m 1 z.1 z.2 ≤ h z := by
  apply odd_profile_le_of_finite_negative_gap m h hSuperharmonic hPrescribed
  have hFinite : {z : ℤ × ℤ | h z - profile m 1 z.1 z.2 ≤ 0}.Finite := by
    simpa only [add_zero] using
      finite_shifted_gap_sublevels_of_quadratic_growth m 1 0 0 h M hGrowth hPositive 0
  apply hFinite.subset
  intro z hz
  change h z - profile m 1 z.1 z.2 < 0 at hz
  change h z - profile m 1 z.1 z.2 ≤ 0
  omega

end FLattice.Auxiliary.MinusProfile
