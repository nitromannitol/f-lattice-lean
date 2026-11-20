import FLattice.Auxiliary.MinusEvenClock
import FLattice.Auxiliary.MinusSpecialValues
import FLattice.Auxiliary.MinusQuadratic
import FLattice.Auxiliary.BoundedRankComparison
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Set.Finite.Lemmas

/-!
# The even-minus comparison from two directed paths

The bounded cell clock, literal physical deficits and exact signed coset
identity discharge all inputs of the generic integer-minimum comparison.
The unknown needs only a bounded-below gap, not periodicity or a finite
minimum set. The growth corollary derives that bound from the original
uniform quadratic asymptotic and actual inverse-matrix positivity.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile

/-- The pin cell is exactly the complete signed even-minus prescribed coset. -/
theorem evenCellPrescribed_cellOf_iff (m : Parameter) (x y : ℤ) :
    evenCellPrescribed (cellOf m x y) ↔ ∃ a b : ℤ,
      x = 2 * m.val + 2 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b ∧
      y = 1 - 2 * m.val * a - 2 * b := by
  constructor
  · rintro ⟨hr, hs, he, hv⟩
    obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
    simp only [Cell.x, Cell.y, hr, hs, he, hv] at hx hy
    norm_num at hx hy
    refine ⟨-q, m.val * q - k, ?_, ?_⟩
    · rw [hx]
      unfold halfPeriod
      ring
    · rw [hy]
      ring
  · rintro ⟨a, b, rfl, rfl⟩
    have hm := m.property
    let p : Cell m := ⟨1, 1, 1, 0, by omega, by omega, by omega, by omega, by omega⟩
    have hLift := cellOf_lifted_cell m p (-m.val * a - b) (-a)
    have hX : p.x + 2 * m.val * (-m.val * a - b) + 2 * halfPeriod m * (-a) =
        2 * m.val + 2 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b := by
      dsimp [p, Cell.x, halfPeriod]
      ring
    have hY : 2 * (-m.val * a - b) + p.y = 1 - 2 * m.val * a - 2 * b := by
      dsimp [p, Cell.y]
      ring
    rw [hX, hY] at hLift
    rw [hLift]
    exact ⟨rfl, rfl, rfl, rfl⟩

private theorem even_incoming_sum (h : ℤ × ℤ → ℤ) (x y : ℤ) :
    (∑ i : Fin 2, h (incomingPoint x y i)) =
      if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
      else h (x, y - 1) + h (x, y + 1) := by
  simp only [Fin.sum_univ_two, incomingPoint]
  split_ifs <;> norm_num [sub_eq_add_neg] at *

private theorem even_deficit_eq_residual (m : Parameter) (x y : ℤ) :
    incomingDeficit m 0 x y =
      0 - ((∑ i : Fin 2, profile m 0 (incomingPoint x y i).1 (incomingPoint x y i).2) -
        2 * profile m 0 x y) := by
  rw [even_incoming_sum (fun z => profile m 0 z.1 z.2)]
  unfold incomingDeficit
  norm_num only [Fin.val_zero, Int.cast_zero, add_zero]
  split_ifs <;> ring

private theorem even_cellOf_incomingPoint (m : Parameter) (x y : ℤ) (i : Fin 2) :
    cellOf m (incomingPoint x y i).1 (incomingPoint x y i).2 =
      incomingCell (cellOf m x y) i := by
  obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
  have h := cellOf_incomingPoint_lifted_cell m (cellOf m x y) k q i
  rw [← hx, ← hy] at h
  exact h

/-- Actual even superharmonicity, all signed prescribed values and a
bounded-below gap imply the even-minus comparison on the whole plane. -/
theorem even_profile_le_of_bounded_gap
    (m : Parameter) (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hPrescribed : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        h (2 * m.val + 2 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          1 - 2 * m.val * a - 2 * b))
    (hGapBounded : ∃ B : ℤ, ∀ z : ℤ × ℤ, B ≤ h z - profile m 0 z.1 z.2) :
    ∀ z : ℤ × ℤ, profile m 0 z.1 z.2 ≤ h z := by
  apply le_of_bounded_gap_and_rank
    (fun z : ℤ × ℤ => incomingPoint z.1 z.2) h
    (fun z => profile m 0 z.1 z.2) (fun _ => 0)
    (fun z => evenCellClock (cellOf m z.1 z.2))
    {z | evenCellPrescribed (cellOf m z.1 z.2)} hGapBounded
  · exact ⟨0, fun z => evenCellClock_nonneg (cellOf m z.1 z.2)⟩
  · rintro ⟨x, y⟩
    have hStar := hSuperharmonic x y
    rw [even_incoming_sum]
    norm_num only [Fintype.card_fin, Nat.cast_ofNat]
    omega
  · rintro ⟨x, y⟩ hPin
    obtain ⟨a, b, rfl, rfl⟩ := (evenCellPrescribed_cellOf_iff m x y).mp hPin
    have hValue := profile_prescribed_coset m 0 a b
    norm_num only [ite_true, Fin.isValue] at hValue
    rw [hValue]
    exact hPrescribed a b
  · rintro ⟨x, y⟩ hNotPin
    obtain ⟨S, hCount, hClock⟩ := even_cell_clock_selected (cellOf m x y) hNotPin
    refine ⟨S, ?_, ?_⟩
    · rw [← incomingDeficit_eq_cellOf m 0 x y, even_deficit_eq_residual] at hCount
      simpa only [Fintype.card_fin, Nat.cast_ofNat] using hCount
    · intro i hi
      rw [even_cellOf_incomingPoint]
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

/-- The original quadratic growth and actual inverse positivity supply
the gap bound, with no extra comparison or geometric assumption. -/
theorem even_profile_le_of_quadratic_growth
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
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
        h (2 * m.val + 2 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          1 - 2 * m.val * a - 2 * b)) :
    ∀ z : ℤ × ℤ, profile m 0 z.1 z.2 ≤ h z := by
  apply even_profile_le_of_bounded_gap m h hSuperharmonic hPrescribed
  apply gap_bounded_of_finite_nonpositive_sublevel
  simpa only [add_zero] using
    finite_shifted_gap_sublevels_of_quadratic_growth m 0 0 0 h M hGrowth hPositive 0

end FLattice.Auxiliary.MinusProfile
