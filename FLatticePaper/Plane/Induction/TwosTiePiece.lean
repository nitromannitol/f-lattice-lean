import FLatticePaper.Plane.Induction.TwosReciprocal
import FLatticePaper.Construction.NearOneBaseCases

/-! Task 50, step 2 (one piece): the upper tie line of the twos sheets.

For `k` with `d = 2k+4` and `1 <= m <= d-1`, at `z = (m, m+d-1)` (so that `z + (0,1) = (m, m+d)`):
  sheetA(z) = V(m, m+d) = sheetC(z),
where `V = paperNearLadderValue d` is the near-one doubled staircase of `lemma:basecase_2k_even_std`.
The sheet `A` reads the reciprocal field at the reduction `(-2,0)` of `(-(m+d-2), m-2)`, the sheet `C` at the reduction
`(-1,0)` of `(3-(m+d), m-1)`; both give tile values of `stairEvenValue` at `(d-m, m)` and `(2-m, m)`, and the harmonic
terms are evaluated exactly by `harmonicGrid_exact`. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- The staircase value on the upper tie line: `V(m, m+d) = -(k+2)^2 - m + 1` for `1 <= m <= d-1`. -/
theorem paperNearLadderValue_tie (k : ℕ) (m : ℤ) (h1 : 1 ≤ m) (h2 : m ≤ 2 * (k : ℤ) + 3) :
    paperNearLadderValue (2 * (k : ℤ) + 4) (m, m + (2 * (k : ℤ) + 4)) = -((k : ℤ) + 2) ^ 2 - m + 1 := by
  have hsq : (2 * (k : ℤ) + 4) ^ 2 / 4 = ((k : ℤ) + 2) ^ 2 := by
    rw [show (2 * (k : ℤ) + 4) ^ 2 = 4 * ((k : ℤ) + 2) ^ 2 by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hind : (paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4)).indicator
      (fun _ => (1 : ℤ)) (m, m + (2 * (k : ℤ) + 4)) = 1 := by
    apply Set.indicator_of_mem
    right
    show (m + (2 * (k : ℤ) + 4)) - m = 2 * (k : ℤ) + 4 ∧ 0 < m ∧ m < 2 * (k : ℤ) + 4
    refine ⟨by ring, by omega, by omega⟩
  unfold paperNearLadderValue
  rw [hind]
  have e1 : m + (2 * (k : ℤ) + 4) - m = 2 * (k : ℤ) + 4 := by ring
  rw [e1, hsq]
  have e2 : min 0 (2 * (k : ℤ) + 4 - (m + (2 * (k : ℤ) + 4))) = -m := by
    have : (2 * (k : ℤ) + 4 - (m + (2 * (k : ℤ) + 4))) = -m := by ring
    rw [this]
    exact min_eq_right (by omega)
  have e3 : min 0 (2 * (2 * (k : ℤ) + 4) - (m + (2 * (k : ℤ) + 4))) = 0 := by
    apply min_eq_left; omega
  have e4 : max ((2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4)) 0 = 0 := by simp
  rw [e2, e3, e4]
  ring

/-- `m(m-1)/2` as an exact half. -/
theorem two_mul_triangle (m : ℤ) : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
  Int.mul_ediv_cancel' ((even_iff_two_dvd).mp (Int.even_mul_pred_self m))

/-- The reciprocal field at `(-(m+d-2), m-2)` on the tie line (sheet `A`): the tile value at `(d-m, m)`. -/
theorem reciprocalField_tie_A (k : ℕ) (m : ℤ) (h1 : 1 ≤ m) (h2 : m ≤ 2 * (k : ℤ) + 3) :
    reciprocalField k (-(m + (2 * (k : ℤ) + 4) - 2), m - 2) = -(m * (m - 1) / 2) := by
  have hy : ((2 * (k : ℤ) + 4) - m, m) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
    BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩
  have hμ : (1 + (2 * (k : ℤ) + 3)) % 2 = 0 := by omega
  have hred : (-(m + (2 * (k : ℤ) + 4) - 2), m - 2) =
      ((2 * (k : ℤ) + 4) - m, m) +
        (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine (-2) 0 := by
    refine Prod.ext ?_ ?_
    · simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, hμ, PeriodDeck.combine, Fraction.unmodifiedDeck]
      ring
    · simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, hμ, PeriodDeck.combine, Fraction.unmodifiedDeck]
      ring
  have hR := reciprocalField_reduction k hy hred
  have hval : BaseMask.stairEvenValue (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 4) - m, m) = -(m * (m - 1) / 2) := by
    unfold BaseMask.stairEvenValue
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 4) - m, m) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [if_neg hc, min_eq_right (by omega : (0 : ℤ) ≤ (2 * (k : ℤ) + 4) - m - 1)]
    ring
  rw [hval] at hR
  simp only [mul_zero, zero_mul, sub_zero, add_zero] at hR
  linarith

/-- The harmonic term of sheet `A` on the tie line, exactly: `4 H = 2m^2 - 6m + 4 - d^2`. -/
theorem harmonicGrid_tie_A (k : ℕ) (m : ℤ) :
    4 * harmonicGrid (m - 1, m + (2 * (k : ℤ) + 4) - 2) =
      2 * m ^ 2 - 6 * m + 4 - (2 * (k : ℤ) + 4) ^ 2 := by
  have e := harmonicGrid_exact (m - 1, m + (2 * (k : ℤ) + 4) - 2)
  have hp : (m - 1 + (m + (2 * (k : ℤ) + 4) - 2)) % 2 = 1 := by omega
  simp only at e
  rw [hp] at e
  linear_combination e

/-- Sheet `A` on the tie line: `A(z) = -(k+2)^2 - m + 1` at `z = (m, m+d-1)`. -/
theorem twos_sheetA_tie (k : ℕ) (m : ℤ) (h1 : 1 ≤ m) (h2 : m ≤ 2 * (k : ℤ) + 3) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (m, m + (2 * (k : ℤ) + 4) - 1) = -((k : ℤ) + 2) ^ 2 - m + 1 := by
  rw [twos_sheetA, show conjWord (List.replicate (k + 1) Digit.two) = List.replicate k Digit.three from
    conjWord_replicate_two k, standardField_threes, quarterTurnField_eq]
  have e1 : (-((m, m + (2 * (k : ℤ) + 4) - 1) - (1, 1)).2, ((m, m + (2 * (k : ℤ) + 4) - 1) - (1, 1)).1 - 1) =
      (-(m + (2 * (k : ℤ) + 4) - 2), m - 2) := by
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  have e2 : ((m, m + (2 * (k : ℤ) + 4) - 1) - (1, 1)) = (m - 1, m + (2 * (k : ℤ) + 4) - 2) := by
    refine Prod.ext ?_ ?_ <;> (simp; try ring)
  show reciprocalField k (-((m, m + (2 * (k : ℤ) + 4) - 1) - (1, 1)).2,
      ((m, m + (2 * (k : ℤ) + 4) - 1) - (1, 1)).1 - 1) +
      harmonicGrid ((m, m + (2 * (k : ℤ) + 4) - 1) - (1, 1)) = _
  rw [e1, e2, reciprocalField_tie_A k m h1 h2]
  have hQ := two_mul_triangle m
  have hH := harmonicGrid_tie_A k m
  have key : 4 * (-(m * (m - 1) / 2) + harmonicGrid (m - 1, m + (2 * (k : ℤ) + 4) - 2)) =
      4 * (-((k : ℤ) + 2) ^ 2 - m + 1) := by
    linear_combination hH - 2 * hQ
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) key

/-- The reciprocal field at `(-(m+d-3), m-1)` on the tie line (sheet `C`): the tile value at `(2-m, m)`. -/
theorem reciprocalField_tie_C (k : ℕ) (m : ℤ) (h1 : 1 ≤ m) (h2 : m ≤ 2 * (k : ℤ) + 3) :
    reciprocalField k (-(m + (2 * (k : ℤ) + 4) - 3), m - 1) = -(m * (m - 1) / 2) + (1 - m) := by
  have hy : (2 - m, m) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
    BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩
  have hμ : (1 + (2 * (k : ℤ) + 3)) % 2 = 0 := by omega
  have hred : (-(m + (2 * (k : ℤ) + 4) - 3), m - 1) =
      (2 - m, m) + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine (-1) 0 := by
    refine Prod.ext ?_ ?_ <;> (simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, hμ, PeriodDeck.combine,
      Fraction.unmodifiedDeck]; try ring)
  have hR := reciprocalField_reduction k hy hred
  have hval : BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (2 - m, m) = -(m * (m - 1) / 2) + (1 - m) := by
    unfold BaseMask.stairEvenValue
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 - m, m) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [if_neg hc, min_eq_left (by omega : (2 - m : ℤ) - 1 ≤ 0)]
    ring
  rw [hval] at hR
  simp only [mul_zero, zero_mul, sub_zero, add_zero] at hR
  linarith

/-- The harmonic term of sheet `C` on the tie line, exactly: `4 H = 2m^2 - 2m - (d-2)^2`. -/
theorem harmonicGrid_tie_C (k : ℕ) (m : ℤ) :
    4 * harmonicGrid (m, m + (2 * (k : ℤ) + 4) - 3) =
      2 * m ^ 2 - 2 * m - (2 * (k : ℤ) + 2) ^ 2 := by
  have e := harmonicGrid_exact (m, m + (2 * (k : ℤ) + 4) - 3)
  have hp : (m + (m + (2 * (k : ℤ) + 4) - 3)) % 2 = 1 := by omega
  simp only at e
  rw [hp] at e
  linear_combination e

/-- Sheet `C` on the tie line: `C(z) = -(k+2)^2 - m + 1` at `z = (m, m+d-1)`. -/
theorem twos_sheetC_tie (k : ℕ) (m : ℤ) (h1 : 1 ≤ m) (h2 : m ≤ 2 * (k : ℤ) + 3) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (m, m + (2 * (k : ℤ) + 4) - 1) = -((k : ℤ) + 2) ^ 2 - m + 1 := by
  rw [twos_sheetC, show conjWord (List.replicate (k + 1) Digit.two) = List.replicate k Digit.three from
    conjWord_replicate_two k, standardField_threes, quarterTurnField_eq]
  have e1 : (-((m, m + (2 * (k : ℤ) + 4) - 1) - (0, 2)).2, ((m, m + (2 * (k : ℤ) + 4) - 1) - (0, 2)).1 - 1) =
      (-(m + (2 * (k : ℤ) + 4) - 3), m - 1) := by
    refine Prod.ext ?_ ?_ <;> (simp; try ring)
  have e2 : ((m, m + (2 * (k : ℤ) + 4) - 1) - (0, 2)) = (m, m + (2 * (k : ℤ) + 4) - 3) := by
    refine Prod.ext ?_ ?_ <;> (simp; try ring)
  show reciprocalField k (-((m, m + (2 * (k : ℤ) + 4) - 1) - (0, 2)).2,
      ((m, m + (2 * (k : ℤ) + 4) - 1) - (0, 2)).1 - 1) +
      harmonicGrid ((m, m + (2 * (k : ℤ) + 4) - 1) - (0, 2)) +
      (m - (m + (2 * (k : ℤ) + 4) - 1)) = _
  rw [e1, e2, reciprocalField_tie_C k m h1 h2]
  have hQ := two_mul_triangle m
  have hH := harmonicGrid_tie_C k m
  have key : 4 * (-(m * (m - 1) / 2) + (1 - m) + harmonicGrid (m, m + (2 * (k : ℤ) + 4) - 3) +
      (m - (m + (2 * (k : ℤ) + 4) - 1))) = 4 * (-((k : ℤ) + 2) ^ 2 - m + 1) := by
    linear_combination hH - 2 * hQ
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) key

/-- The minimum of the two sheets on the tie line is the staircase value. -/
theorem twos_tie_min (k : ℕ) (m : ℤ) (h1 : 1 ≤ m) (h2 : m ≤ 2 * (k : ℤ) + 3) :
    min ((frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (m, m + (2 * (k : ℤ) + 4) - 1))
      ((frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (m, m + (2 * (k : ℤ) + 4) - 1)) =
      paperNearLadderValue (2 * (k : ℤ) + 4) (m, m + (2 * (k : ℤ) + 4)) := by
  rw [twos_sheetA_tie k m h1 h2, twos_sheetC_tie k m h1 h2, paperNearLadderValue_tie k m h1 h2, min_self]

end FLatticePaper.Induction
