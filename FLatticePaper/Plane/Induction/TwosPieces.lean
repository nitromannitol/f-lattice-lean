import FLatticePaper.Plane.Induction.TwosTiePiece

/-! Task 50, step 2 (the piece table): generic sheet formulas and the lower tie piece.

For a deck reduction `(y1, y2)` of `(2 - w2, w1 - 2)` (sheet A) or `(3 - w2, w1 - 1)` (sheet C) by the integer pair `(i, j)`,
the sheet value is the tile value at `(y1, y2)` corrected by the period formula, plus the exact harmonic term. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- `4 * (t^2/4) + t % 2 = t^2`. -/
theorem sq_div4_add_mod2 (t : ℤ) : 4 * (t ^ 2 / 4) + t % 2 = t ^ 2 := by
  rcases Int.even_or_odd t with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have e : (q + q) ^ 2 = 4 * q ^ 2 := by ring
    rw [e, Int.mul_ediv_cancel_left _ (by norm_num : (4 : ℤ) ≠ 0)]
    have h2 : (q + q) % 2 = 0 := by omega
    simp [h2]
  · have e : (2 * q + 1) ^ 2 = 4 * (q ^ 2 + q) + 1 := by ring
    rw [e]
    have h4 : (4 * (q ^ 2 + q) + 1) / 4 = q ^ 2 + q := by
      generalize q ^ 2 + q = X
      omega
    have h2 : (2 * q + 1) % 2 = 1 := by omega
    rw [h4, h2]

/-- The tile value of `stairEvenValue`, unfolded. -/
theorem stairEvenValue_formula (dR y1 y2 : ℤ) :
    BaseMask.stairEvenValue dR (y1, y2) =
      -(y2 * (y2 - 1) / 2) + min (y1 - 1) 0 + (if BaseMask.StairEvenCorner dR (y1, y2) then 1 else 0) := rfl

/-- The sheet `A` of `2^(k+1)` at `(w1, w2-1)` through a deck reduction `(i, j)` with reduced point `(y1, y2)`. -/
theorem sheetA_via (k : ℕ) (w1 w2 i j y1 y2 : ℤ)
    (hy1 : y1 = 2 - w2 - i * (2 * (k : ℤ) + 3) - j * (1 - (2 * (k : ℤ) + 3)))
    (hy2 : y2 = w1 - 2 - i - j * (1 + (2 * (k : ℤ) + 3)))
    (hmem : (y1, y2) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    2 * (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) =
      2 * BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (y1, y2) +
        2 * j * (-((Fraction.mk 1 (2 * (k : ℤ) + 3)).transverseGrade (y1, y2)) +
          stairEvenConstantV (2 * (k : ℤ) + 3)) -
        (Fraction.mk 1 (2 * (k : ℤ) + 3)).periodDenominator * j * (j - 1) +
        2 * harmonicGrid (w1 - 1, w2 - 2) := by
  have hμ : (1 + (2 * (k : ℤ) + 3)) % 2 = 0 := by omega
  have hred : (2 - w2, w1 - 2) = (y1, y2) + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j := by
    subst hy1 hy2
    refine Prod.ext ?_ ?_ <;> (simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, hμ, PeriodDeck.combine,
      Fraction.unmodifiedDeck]; try ring)
  have hR := reciprocalField_reduction k hmem hred
  rw [twos_sheetA, show conjWord (List.replicate (k + 1) Digit.two) = List.replicate k Digit.three from
    conjWord_replicate_two k, standardField_threes, quarterTurnField_eq]
  have e1 : (-((w1, w2 - 1) - (1, 1)).2, ((w1, w2 - 1) - (1, 1)).1 - 1) = (2 - w2, w1 - 2) := by
    refine Prod.ext ?_ ?_ <;> (simp; try ring)
  have e2 : ((w1, w2 - 1) - (1, 1)) = (w1 - 1, w2 - 2) := by
    refine Prod.ext ?_ ?_ <;> (simp; try ring)
  show 2 * (reciprocalField k (-((w1, w2 - 1) - (1, 1)).2, ((w1, w2 - 1) - (1, 1)).1 - 1) +
      harmonicGrid ((w1, w2 - 1) - (1, 1))) = _
  rw [e1, e2]
  linarith [hR]

/-- The sheet `C` of `2^(k+1)` at `(w1, w2-1)` through a deck reduction `(i, j)` with reduced point `(y1, y2)`. -/
theorem sheetC_via (k : ℕ) (w1 w2 i j y1 y2 : ℤ)
    (hy1 : y1 = 3 - w2 - i * (2 * (k : ℤ) + 3) - j * (1 - (2 * (k : ℤ) + 3)))
    (hy2 : y2 = w1 - 1 - i - j * (1 + (2 * (k : ℤ) + 3)))
    (hmem : (y1, y2) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    2 * (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) =
      2 * BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (y1, y2) +
        2 * j * (-((Fraction.mk 1 (2 * (k : ℤ) + 3)).transverseGrade (y1, y2)) +
          stairEvenConstantV (2 * (k : ℤ) + 3)) -
        (Fraction.mk 1 (2 * (k : ℤ) + 3)).periodDenominator * j * (j - 1) +
        2 * harmonicGrid (w1, w2 - 3) + 2 * (w1 - (w2 - 1)) := by
  have hμ : (1 + (2 * (k : ℤ) + 3)) % 2 = 0 := by omega
  have hred : (3 - w2, w1 - 1) = (y1, y2) + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j := by
    subst hy1 hy2
    refine Prod.ext ?_ ?_ <;> (simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, hμ, PeriodDeck.combine,
      Fraction.unmodifiedDeck]; try ring)
  have hR := reciprocalField_reduction k hmem hred
  rw [twos_sheetC, show conjWord (List.replicate (k + 1) Digit.two) = List.replicate k Digit.three from
    conjWord_replicate_two k, standardField_threes, quarterTurnField_eq]
  have e1 : (-((w1, w2 - 1) - (0, 2)).2, ((w1, w2 - 1) - (0, 2)).1 - 1) = (3 - w2, w1 - 1) := by
    refine Prod.ext ?_ ?_ <;> (simp; try ring)
  have e2 : ((w1, w2 - 1) - (0, 2)) = (w1, w2 - 3) := by
    refine Prod.ext ?_ ?_ <;> (simp; try ring)
  show 2 * (reciprocalField k (-((w1, w2 - 1) - (0, 2)).2, ((w1, w2 - 1) - (0, 2)).1 - 1) +
      harmonicGrid ((w1, w2 - 1) - (0, 2)) + (w1 - (w2 - 1))) = _
  rw [e1, e2]
  linarith [hR]

/-- The staircase on the lower rows: `V(w1, w2) = -((w2-w1)^2/4)` for `1 <= w1 < w2 <= d`. -/
theorem paperNearLadderValue_lower (k : ℕ) (w1 w2 : ℤ) (h1 : 1 ≤ w1) (h2 : w1 < w2)
    (h3 : w2 ≤ 2 * (k : ℤ) + 4) :
    paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) = -((w2 - w1) ^ 2 / 4) := by
  classical
  have hnot : (w1, w2) ∉ paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4) := by
    rintro (hA | hB)
    · simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hA
      omega
    · simp only [paperNearLadderB, Set.mem_setOf_eq] at hB
      omega
  unfold paperNearLadderValue
  simp only
  rw [Set.indicator_apply, if_neg hnot]
  rw [min_eq_left (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 4 - w2),
    min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - w2),
    max_eq_right (by omega : w2 - w1 - (2 * (k : ℤ) + 4) ≤ 0)]
  ring

/-- The lower tie piece: for `3 <= w2 <= d` and `1 <= w1 <= w2 - 1`, both sheets equal the staircase value. -/
theorem lower_tie_piece (k : ℕ) (w1 w2 : ℤ) (h1 : 1 ≤ w1) (h2 : w1 ≤ w2 - 1) (h3 : 3 ≤ w2)
    (h4 : w2 ≤ 2 * (k : ℤ) + 4) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  rw [paperNearLadderValue_lower k w1 w2 h1 (by omega) h4]
  constructor
  · -- sheet A: reduction (-1, 0) at (2k+5-w2, w1-1)
    have hmem : (2 * (k : ℤ) + 5 - w2, w1 - 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        Or.inr ⟨by omega, by omega⟩⟩
    have hA := sheetA_via k w1 w2 (-1) 0 (2 * (k : ℤ) + 5 - w2) (w1 - 1) (by ring) (by ring) hmem
    rw [stairEvenValue_formula] at hA
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5 - w2, w1 - 1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [if_neg hc, min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 5 - w2 - 1)] at hA
    have hQ := two_mul_triangle (w1 - 1)
    have hH := harmonicGrid_exact (w1 - 1, w2 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - w1)
    have hpar : (w1 - 1 + (w2 - 2)) % 2 = 1 - (w2 - w1) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA - 2 * hQ + hH + hP - hpar
  · -- sheet C: reduction (-1, 0) at (2k+6-w2, w1)
    have hmem : (2 * (k : ℤ) + 6 - w2, w1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        Or.inr ⟨by omega, by omega⟩⟩
    have hC := sheetC_via k w1 w2 (-1) 0 (2 * (k : ℤ) + 6 - w2) w1 (by ring) (by ring) hmem
    rw [stairEvenValue_formula] at hC
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 6 - w2, w1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [if_neg hc, min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 6 - w2 - 1)] at hC
    have hQ := two_mul_triangle w1
    have hH := harmonicGrid_exact (w1, w2 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - w1)
    have hpar : (w1 + (w2 - 3)) % 2 = 1 - (w2 - w1) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- The staircase on the second tie band (`2d <= w2`, `1 <= w1 <= d-1`): `V = -((w2-w1)^2/4) + 2d - w2 - w1`. -/
theorem paperNearLadderValue_band2 (k : ℕ) (w1 w2 : ℤ) (h1 : 1 ≤ w1) (h2 : 2 * (2 * (k : ℤ) + 4) ≤ w2)
    (h3 : w1 ≤ 2 * (k : ℤ) + 3) :
    paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) =
      -((w2 - w1) ^ 2 / 4) + (2 * (2 * (k : ℤ) + 4) - w2 - w1) := by
  classical
  have hnot : (w1, w2) ∉ paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4) := by
    rintro (hA | hB)
    · simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hA
      omega
    · simp only [paperNearLadderB, Set.mem_setOf_eq] at hB
      omega
  unfold paperNearLadderValue
  simp only
  rw [Set.indicator_apply, if_neg hnot]
  rw [min_eq_right (by omega : 2 * (k : ℤ) + 4 - w2 ≤ 0),
    min_eq_right (by omega : 2 * (2 * (k : ℤ) + 4) - w2 ≤ 0),
    max_eq_left (by omega : 0 ≤ w2 - w1 - (2 * (k : ℤ) + 4))]
  ring

/-- The second tie band: for `2d <= w2 <= 3d-3` and `w2 - 2d + 1 <= w1 <= d-1`, both sheets equal the staircase value. -/
theorem band2_tie_piece (k : ℕ) (w1 w2 : ℤ) (h1 : 1 ≤ w1) (h2 : 2 * (2 * (k : ℤ) + 4) ≤ w2)
    (h3 : w1 ≤ 2 * (k : ℤ) + 3) (h4 : w2 ≤ 3 * (2 * (k : ℤ) + 4) - 3)
    (h5 : w2 - 2 * (2 * (k : ℤ) + 4) + 1 ≤ w1) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  rw [paperNearLadderValue_band2 k w1 w2 h1 h2 h3]
  constructor
  · -- sheet A: reduction (-2, 0) at (2d - w2, w1)
    have hmem : (2 * (2 * (k : ℤ) + 4) - w2, w1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        Or.inr ⟨by omega, by omega⟩⟩
    have hA := sheetA_via k w1 w2 (-2) 0 (2 * (2 * (k : ℤ) + 4) - w2) w1 (by ring) (by ring) hmem
    rw [stairEvenValue_formula] at hA
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 4) - w2, w1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [if_neg hc, min_eq_left (by omega : 2 * (2 * (k : ℤ) + 4) - w2 - 1 ≤ 0)] at hA
    have hQ := two_mul_triangle w1
    have hH := harmonicGrid_exact (w1 - 1, w2 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - w1)
    have hpar : (w1 - 1 + (w2 - 2)) % 2 = 1 - (w2 - w1) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA - 2 * hQ + hH + hP - hpar
  · -- sheet C: reduction (-2, 0) at (2d + 1 - w2, w1 + 1)
    have hmem : (2 * (2 * (k : ℤ) + 4) + 1 - w2, w1 + 1) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        Or.inr ⟨by omega, by omega⟩⟩
    have hC := sheetC_via k w1 w2 (-2) 0 (2 * (2 * (k : ℤ) + 4) + 1 - w2) (w1 + 1) (by ring) (by ring) hmem
    rw [stairEvenValue_formula] at hC
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 4) + 1 - w2, w1 + 1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [if_neg hc, min_eq_left (by omega : 2 * (2 * (k : ℤ) + 4) + 1 - w2 - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle (w1 + 1)
    have hH := harmonicGrid_exact (w1, w2 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - w1)
    have hpar : (w1 + (w2 - 3)) % 2 = 1 - (w2 - w1) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- The staircase on the first upper band with `A` attaining (`d+1 <= w2 <= 2d-2`, `w2-d+1 <= w1 <= d`):
`V = -((w2-w1)^2/4) + (d - w2)`. -/
theorem paperNearLadderValue_upA1 (k : ℕ) (w1 w2 : ℤ) (h1 : 1 ≤ w1) (h2 : 2 * (k : ℤ) + 5 ≤ w2)
    (h3 : w2 ≤ 4 * (k : ℤ) + 6) (h4 : w2 - (2 * (k : ℤ) + 4) + 1 ≤ w1) (h5 : w1 ≤ 2 * (k : ℤ) + 4) :
    paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) =
      -((w2 - w1) ^ 2 / 4) + (2 * (k : ℤ) + 4 - w2) := by
  classical
  have hnot : (w1, w2) ∉ paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4) := by
    rintro (hA | hB)
    · simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hA
      omega
    · simp only [paperNearLadderB, Set.mem_setOf_eq] at hB
      omega
  unfold paperNearLadderValue
  simp only
  rw [Set.indicator_apply, if_neg hnot]
  rw [min_eq_right (by omega : 2 * (k : ℤ) + 4 - w2 ≤ 0),
    min_eq_left (by omega : 0 ≤ 2 * (2 * (k : ℤ) + 4) - w2),
    max_eq_right (by omega : w2 - w1 - (2 * (k : ℤ) + 4) ≤ 0)]
  ring

/-- First upper band, `A` attaining: both sheets with the reduction `(-1,0)`; `A = V` and `C = V + 1`. -/
theorem upA1_piece (k : ℕ) (w1 w2 : ℤ) (h1 : 1 ≤ w1) (h2 : 2 * (k : ℤ) + 5 ≤ w2)
    (h3 : w2 ≤ 4 * (k : ℤ) + 6) (h4 : w2 - (2 * (k : ℤ) + 4) + 1 ≤ w1) (h5 : w1 ≤ 2 * (k : ℤ) + 4) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 1 := by
  rw [paperNearLadderValue_upA1 k w1 w2 h1 h2 h3 h4 h5]
  constructor
  · have hmem : (2 * (k : ℤ) + 5 - w2, w1 - 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        Or.inr ⟨by omega, by omega⟩⟩
    have hA := sheetA_via k w1 w2 (-1) 0 (2 * (k : ℤ) + 5 - w2) (w1 - 1) (by ring) (by ring) hmem
    rw [stairEvenValue_formula] at hA
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5 - w2, w1 - 1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [if_neg hc, min_eq_left (by omega : 2 * (k : ℤ) + 5 - w2 - 1 ≤ 0)] at hA
    have hQ := two_mul_triangle (w1 - 1)
    have hH := harmonicGrid_exact (w1 - 1, w2 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - w1)
    have hpar : (w1 - 1 + (w2 - 2)) % 2 = 1 - (w2 - w1) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA - 2 * hQ + hH + hP - hpar
  · have hmem : (2 * (k : ℤ) + 6 - w2, w1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        Or.inr ⟨by omega, by omega⟩⟩
    have hC := sheetC_via k w1 w2 (-1) 0 (2 * (k : ℤ) + 6 - w2) w1 (by ring) (by ring) hmem
    rw [stairEvenValue_formula] at hC
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 6 - w2, w1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [if_neg hc, min_eq_left (by omega : 2 * (k : ℤ) + 6 - w2 - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle w1
    have hH := harmonicGrid_exact (w1, w2 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - w1)
    have hpar : (w1 + (w2 - 3)) % 2 = 1 - (w2 - w1) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- The staircase on the upper rows with `C` attaining (`d+2 <= w2 <= 2d-1`, `0 <= w1 <= w2-d-1`): `V = -((w2-w1)^2/4) - w1`. -/
theorem paperNearLadderValue_upC1 (k : ℕ) (w1 w2 : ℤ) (h1 : 0 ≤ w1) (h2 : 2 * (k : ℤ) + 6 ≤ w2)
    (h3 : w2 ≤ 4 * (k : ℤ) + 7) (h4 : w1 ≤ w2 - (2 * (k : ℤ) + 5)) :
    paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) = -((w2 - w1) ^ 2 / 4) - w1 := by
  classical
  have hnot : (w1, w2) ∉ paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4) := by
    rintro (hA | hB)
    · simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hA
      omega
    · simp only [paperNearLadderB, Set.mem_setOf_eq] at hB
      omega
  unfold paperNearLadderValue
  simp only
  rw [Set.indicator_apply, if_neg hnot]
  rw [min_eq_right (by omega : 2 * (k : ℤ) + 4 - w2 ≤ 0),
    min_eq_left (by omega : 0 ≤ 2 * (2 * (k : ℤ) + 4) - w2),
    max_eq_left (by omega : 0 ≤ w2 - w1 - (2 * (k : ℤ) + 4))]
  ring

/-- Upper rows, `C` attaining: `C = V` (reduction `(-2,0)`), `A = V + 1` (reduction `(-2,0)`). -/
theorem upC1_piece (k : ℕ) (w1 w2 : ℤ) (h1 : 0 ≤ w1) (h2 : 2 * (k : ℤ) + 6 ≤ w2)
    (h3 : w2 ≤ 4 * (k : ℤ) + 7) (h4 : w1 ≤ w2 - (2 * (k : ℤ) + 5)) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 1 ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  rw [paperNearLadderValue_upC1 k w1 w2 h1 h2 h3 h4]
  constructor
  · have hmem : (2 * (2 * (k : ℤ) + 4) - w2, w1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        Or.inr ⟨by omega, by omega⟩⟩
    have hA := sheetA_via k w1 w2 (-2) 0 (2 * (2 * (k : ℤ) + 4) - w2) w1 (by ring) (by ring) hmem
    rw [stairEvenValue_formula] at hA
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 4) - w2, w1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [if_neg hc, min_eq_right (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - w2 - 1)] at hA
    have hQ := two_mul_triangle w1
    have hH := harmonicGrid_exact (w1 - 1, w2 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - w1)
    have hpar : (w1 - 1 + (w2 - 2)) % 2 = 1 - (w2 - w1) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA - 2 * hQ + hH + hP - hpar
  · have hmem : (2 * (2 * (k : ℤ) + 4) + 1 - w2, w1 + 1) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        Or.inr ⟨by omega, by omega⟩⟩
    have hC := sheetC_via k w1 w2 (-2) 0 (2 * (2 * (k : ℤ) + 4) + 1 - w2) (w1 + 1) (by ring) (by ring) hmem
    rw [stairEvenValue_formula] at hC
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 4) + 1 - w2, w1 + 1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [if_neg hc, min_eq_right (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) + 1 - w2 - 1)] at hC
    have hQ := two_mul_triangle (w1 + 1)
    have hH := harmonicGrid_exact (w1, w2 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - w1)
    have hpar : (w1 + (w2 - 3)) % 2 = 1 - (w2 - w1) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- The staircase on the lower rows with `A` attaining and `w2 <= w1 <= w2+1`: `V = -((w2-w1)^2/4)`. -/
theorem paperNearLadderValue_lowerA1 (k : ℕ) (w1 w2 : ℤ) (h1 : 1 ≤ w1)
    (h3 : w2 ≤ 2 * (k : ℤ) + 4) (h4 : w2 ≤ w1) (h5 : w1 ≤ w2 + 1) :
    paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) = -((w2 - w1) ^ 2 / 4) := by
  classical
  have hnot : (w1, w2) ∉ paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4) := by
    rintro (hA | hB)
    · simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hA
      omega
    · simp only [paperNearLadderB, Set.mem_setOf_eq] at hB
      omega
  unfold paperNearLadderValue
  simp only
  rw [Set.indicator_apply, if_neg hnot]
  rw [min_eq_left (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 4 - w2),
    min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - w2),
    max_eq_right (by omega : w2 - w1 - (2 * (k : ℤ) + 4) ≤ 0)]
  ring

/-- Lower rows, `A` attaining on `w2 <= w1 <= w2+1`: `A = V` (reduction `(-1,0)`), `C = V + (w1-w2+1)` (reduction `(0,0)`). -/
theorem lowerA1_piece (k : ℕ) (w1 w2 : ℤ) (h1 : 1 ≤ w1) (h2 : 2 ≤ w2) (h3 : w2 ≤ 2 * (k : ℤ) + 4)
    (h4 : w2 ≤ w1) (h5 : w1 ≤ w2 + 1) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + (w1 - w2 + 1) := by
  rw [paperNearLadderValue_lowerA1 k w1 w2 h1 h3 h4 h5]
  constructor
  · have hmem : (2 * (k : ℤ) + 5 - w2, w1 - 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        Or.inr ⟨by omega, by omega⟩⟩
    have hA := sheetA_via k w1 w2 (-1) 0 (2 * (k : ℤ) + 5 - w2) (w1 - 1) (by ring) (by ring) hmem
    rw [stairEvenValue_formula] at hA
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5 - w2, w1 - 1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [if_neg hc, min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 5 - w2 - 1)] at hA
    have hQ := two_mul_triangle (w1 - 1)
    have hH := harmonicGrid_exact (w1 - 1, w2 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - w1)
    have hpar : (w1 - 1 + (w2 - 2)) % 2 = 1 - (w2 - w1) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA - 2 * hQ + hH + hP - hpar
  · have hmem : (3 - w2, w1 - 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        Or.inr ⟨by omega, by omega⟩⟩
    have hC := sheetC_via k w1 w2 0 0 (3 - w2) (w1 - 1) (by ring) (by ring) hmem
    rw [stairEvenValue_formula] at hC
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (3 - w2, w1 - 1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [if_neg hc, min_eq_left (by omega : 3 - w2 - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle (w1 - 1)
    have hH := harmonicGrid_exact (w1, w2 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - w1)
    have hpar : (w1 + (w2 - 3)) % 2 = 1 - (w2 - w1) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

end FLatticePaper.Induction
