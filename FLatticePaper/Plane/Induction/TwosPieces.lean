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

/-- The transverse grade of the child `1/dR` at `(y1, y2)`. -/
theorem transverseGrade_one (dR y1 y2 : ℤ) :
    (Fraction.mk 1 dR).transverseGrade (y1, y2) = dR * y2 - 1 * y1 := rfl

/-- The period denominator of the child `1/dR`. -/
theorem periodDenominator_one (dR : ℤ) :
    (Fraction.mk 1 dR).periodDenominator = dR ^ 2 + 2 * dR * 1 - 1 ^ 2 := rfl

/-- `2 * stairEvenConstantV dR = -(dR+1)dR - 2 dR`, with the parity of `(dR+1)dR` absorbed. -/
theorem stairEvenConstantV_double (dR : ℤ) :
    2 * stairEvenConstantV dR = -((dR + 1) * (dR + 1 - 1)) - 2 * dR := by
  unfold stairEvenConstantV chooseTwo
  linear_combination (-1 : ℤ) * two_mul_triangle (dR + 1)

/-- Off the sets `A` and `B`, the staircase is the explicit formula: the indicator vanishes. -/
theorem paperNearLadderValue_off (d : ℤ) (w1 w2 : ℤ) (hA : (w1, w2) ∉ paperNearLadderA d)
    (hB : (w1, w2) ∉ paperNearLadderB d) :
    paperNearLadderValue d (w1, w2) =
      -((w2 - w1) ^ 2 / 4) + min 0 (d - w2) + min 0 (2 * d - w2) + max ((w2 - w1) - d) 0 := by
  classical
  have hnot : (w1, w2) ∉ paperNearLadderA d ∪ paperNearLadderB d := by
    rintro (h | h)
    · exact hA h
    · exact hB h
  unfold paperNearLadderValue
  simp only
  rw [Set.indicator_apply, if_neg hnot, add_zero]

/-- The left edge (`w1 = -1`, `d+2 <= w2 <= 2d-1`): `C = V` via `(-2,0)`, `A = V + 2` via `(-2,-1)`. -/
theorem leftEdge_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = -1) (h2 : 2 * (k : ℤ) + 6 ≤ w2)
    (h3 : w2 ≤ 4 * (k : ℤ) + 7) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 2 ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw1
  have hA : ((-1 : ℤ), w2) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : ((-1 : ℤ), w2) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (-1, w2) = -((w2 - -1) ^ 2 / 4) + 1 := by
    rw [paperNearLadderValue_off _ _ _ hA hB, min_eq_right (by omega : 2 * (k : ℤ) + 4 - w2 ≤ 0),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - w2),
      max_eq_left (by omega : (0 : ℤ) ≤ w2 - -1 - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : (2 * (k : ℤ) + 6 - w2, 2 * (k : ℤ) + 3) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (-1) w2 (-2) (-1) (2 * (k : ℤ) + 6 - w2) (2 * (k : ℤ) + 3)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 6 - w2, 2 * (k : ℤ) + 3) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : 2 * (k : ℤ) + 6 - w2 - 1 ≤ 0)] at hA'
    rw [transverseGrade_one, periodDenominator_one] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 3)
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (-1 - 1, w2 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - -1)
    have hpar : (-1 - 1 + (w2 - 2)) % 2 = 1 - (w2 - -1) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar - 2 * hcV
  · have hmem : (4 * (k : ℤ) + 9 - w2, 0) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (-1) w2 (-2) 0 (4 * (k : ℤ) + 9 - w2) 0 (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (4 * (k : ℤ) + 9 - w2, 0) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_right (by omega : (0 : ℤ) ≤ 4 * (k : ℤ) + 9 - w2 - 1)] at hC
    have hQ := two_mul_triangle 0
    have hH := harmonicGrid_exact (-1, w2 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - -1)
    have hpar : (-1 + (w2 - 3)) % 2 = 1 - (w2 - -1) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- The left edge at the double point `w2 = 2d` (`w1 = -1`): `C = V` via `(-2,0)`, `A = V + 2` via `(-3,0)`. -/
theorem leftEdgeDouble_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = -1) (hw2 : w2 = 4 * (k : ℤ) + 8) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 2 ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw1 hw2
  have hA : ((-1 : ℤ), 4 * (k : ℤ) + 8) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : ((-1 : ℤ), 4 * (k : ℤ) + 8) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (-1, 4 * (k : ℤ) + 8) =
      -((4 * (k : ℤ) + 8 - -1) ^ 2 / 4) + 1 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (4 * (k : ℤ) + 8) ≤ 0),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - (4 * (k : ℤ) + 8)),
      max_eq_left (by omega : (0 : ℤ) ≤ 4 * (k : ℤ) + 8 - -1 - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : (2 * (k : ℤ) + 3, 0) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (-1) (4 * (k : ℤ) + 8) (-3) 0 (2 * (k : ℤ) + 3) 0
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3, 0) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 3 - 1)] at hA'
    have hQ := two_mul_triangle 0
    have hH := harmonicGrid_exact (-1 - 1, 4 * (k : ℤ) + 8 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (4 * (k : ℤ) + 8 - -1)
    have hpar : (-1 - 1 + (4 * (k : ℤ) + 8 - 2)) % 2 = 1 - (4 * (k : ℤ) + 8 - -1) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar
  · have hmem : ((1 : ℤ), 0) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (-1) (4 * (k : ℤ) + 8) (-2) 0 1 0 (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((1 : ℤ), 0) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (1 : ℤ) - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle 0
    have hH := harmonicGrid_exact (-1, 4 * (k : ℤ) + 8 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (4 * (k : ℤ) + 8 - -1)
    have hpar : (-1 + (4 * (k : ℤ) + 8 - 3)) % 2 = 1 - (4 * (k : ℤ) + 8 - -1) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- On the sets `A` or `B`, the staircase is the explicit formula plus the indicator `1`. -/
theorem paperNearLadderValue_on (d w1 w2 : ℤ) (h : (w1, w2) ∈ paperNearLadderA d ∪ paperNearLadderB d) :
    paperNearLadderValue d (w1, w2) =
      -((w2 - w1) ^ 2 / 4) + min 0 (d - w2) + min 0 (2 * d - w2) + max ((w2 - w1) - d) 0 + 1 := by
  classical
  unfold paperNearLadderValue
  simp only [Set.indicator_of_mem h]

/-- The top point of the left edge `(-1, 2d+1)`, on the set `A`: `C = V` via `(-2,0)`, `A = V + 2` via `(-3,0)`. -/
theorem leftEdgeTop_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = -1) (hw2 : w2 = 4 * (k : ℤ) + 9) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 2 ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw1 hw2
  have hind : ((-1 : ℤ), 4 * (k : ℤ) + 9) ∈
      paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4) :=
    Set.mem_union_left _ (by
      unfold paperNearLadderA
      exact Set.mem_insert_iff.mpr (Or.inl (Prod.ext rfl (by ring))))
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (-1, 4 * (k : ℤ) + 9) =
      -((4 * (k : ℤ) + 9 - -1) ^ 2 / 4) + 1 := by
    rw [paperNearLadderValue_on _ _ _ hind,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (4 * (k : ℤ) + 9) ≤ 0),
      min_eq_right (by omega : 2 * (2 * (k : ℤ) + 4) - (4 * (k : ℤ) + 9) ≤ 0),
      max_eq_left (by omega : (0 : ℤ) ≤ 4 * (k : ℤ) + 9 - -1 - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : (2 * (k : ℤ) + 2, 0) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (-1) (4 * (k : ℤ) + 9) (-3) 0 (2 * (k : ℤ) + 2) 0
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 2, 0) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 2 - 1)] at hA'
    have hQ := two_mul_triangle 0
    have hH := harmonicGrid_exact (-1 - 1, 4 * (k : ℤ) + 9 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (4 * (k : ℤ) + 9 - -1)
    have hpar : (-1 - 1 + (4 * (k : ℤ) + 9 - 2)) % 2 = 1 - (4 * (k : ℤ) + 9 - -1) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar
  · have hmem : ((0 : ℤ), 0) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (-1) (4 * (k : ℤ) + 9) (-2) 0 0 0 (by ring) (by ring) hmem
    have hcorner : BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((0 : ℤ), 0) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_pos hcorner,
      min_eq_left (by omega : (0 : ℤ) - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle 0
    have hH := harmonicGrid_exact (-1, 4 * (k : ℤ) + 9 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (4 * (k : ℤ) + 9 - -1)
    have hpar : (-1 + (4 * (k : ℤ) + 9 - 3)) % 2 = 1 - (4 * (k : ℤ) + 9 - -1) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- The column `w1 = 0`, `3 <= w2 <= d`: `C = V` via `(-1,0)`, `A = V + 1` via `(-1,-1)`. -/
theorem zeroColumn_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 0) (h3 : 3 ≤ w2)
    (h4 : w2 ≤ 2 * (k : ℤ) + 4) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 1 ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw1
  have hA : ((0 : ℤ), w2) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : ((0 : ℤ), w2) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (0, w2) = -((w2 - 0) ^ 2 / 4) := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 4 - w2),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - w2),
      max_eq_right (by omega : w2 - 0 - (2 * (k : ℤ) + 4) ≤ 0)]
    ring
  rw [hV]
  constructor
  · have hmem : (3 - w2, 2 * (k : ℤ) + 3) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k 0 w2 (-1) (-1) (3 - w2) (2 * (k : ℤ) + 3) (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (3 - w2, 2 * (k : ℤ) + 3) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : 3 - w2 - 1 ≤ 0)] at hA'
    rw [transverseGrade_one, periodDenominator_one] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 3)
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (0 - 1, w2 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - 0)
    have hpar : (0 - 1 + (w2 - 2)) % 2 = 1 - (w2 - 0) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar - 2 * hcV
  · have hmem : (2 * (k : ℤ) + 6 - w2, 0) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k 0 w2 (-1) 0 (2 * (k : ℤ) + 6 - w2) 0 (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 6 - w2, 0) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 6 - w2 - 1)] at hC
    have hQ := two_mul_triangle 0
    have hH := harmonicGrid_exact (0, w2 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - 0)
    have hpar : (0 + (w2 - 3)) % 2 = 1 - (w2 - 0) % 2 := by omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- The point `(0, d+1)`: `C = V` via `(-1,0)`, `A = V + 1` via `(-2,0)`. -/
theorem zeroColumnTop_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 0) (hw2 : w2 = 2 * (k : ℤ) + 5) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 1 ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw1 hw2
  have hA : ((0 : ℤ), 2 * (k : ℤ) + 5) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : ((0 : ℤ), 2 * (k : ℤ) + 5) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (0, 2 * (k : ℤ) + 5) =
      -((2 * (k : ℤ) + 5 - 0) ^ 2 / 4) := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (2 * (k : ℤ) + 5) ≤ 0),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 5)),
      max_eq_left (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 5 - 0 - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : (2 * (k : ℤ) + 3, 0) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k 0 (2 * (k : ℤ) + 5) (-2) 0 (2 * (k : ℤ) + 3) 0
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3, 0) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 3 - 1)] at hA'
    have hQ := two_mul_triangle 0
    have hH := harmonicGrid_exact (0 - 1, 2 * (k : ℤ) + 5 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (2 * (k : ℤ) + 5 - 0)
    have hpar : (0 - 1 + (2 * (k : ℤ) + 5 - 2)) % 2 = 1 - (2 * (k : ℤ) + 5 - 0) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar
  · have hmem : ((1 : ℤ), 0) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k 0 (2 * (k : ℤ) + 5) (-1) 0 1 0 (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((1 : ℤ), 0) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (1 : ℤ) - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle 0
    have hH := harmonicGrid_exact (0, 2 * (k : ℤ) + 5 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (2 * (k : ℤ) + 5 - 0)
    have hpar : (0 + (2 * (k : ℤ) + 5 - 3)) % 2 = 1 - (2 * (k : ℤ) + 5 - 0) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- The diagonal `w2 - w1 = 2d` for `0 <= w1 <= d-2`: `C = V` via `(-2,0)`, `A = V + 1` via `(-3,0)`. -/
theorem diagonalEven_piece (k : ℕ) (w1 w2 : ℤ) (h1 : 0 ≤ w1) (h2 : w1 ≤ 2 * (k : ℤ) + 2)
    (hw2 : w2 = w1 + (4 * (k : ℤ) + 8)) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 1 ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw2
  have hA : (w1, w1 + (4 * (k : ℤ) + 8)) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : (w1, w1 + (4 * (k : ℤ) + 8)) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w1 + (4 * (k : ℤ) + 8)) =
      -((w1 + (4 * (k : ℤ) + 8) - w1) ^ 2 / 4) - 2 * w1 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (w1 + (4 * (k : ℤ) + 8)) ≤ 0),
      min_eq_right (by omega : 2 * (2 * (k : ℤ) + 4) - (w1 + (4 * (k : ℤ) + 8)) ≤ 0),
      max_eq_left (by omega : (0 : ℤ) ≤ w1 + (4 * (k : ℤ) + 8) - w1 - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : (2 * (k : ℤ) + 3 - w1, w1 + 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k w1 (w1 + (4 * (k : ℤ) + 8)) (-3) 0 (2 * (k : ℤ) + 3 - w1) (w1 + 1)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3 - w1, w1 + 1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 3 - w1 - 1)] at hA'
    have hQ := two_mul_triangle (w1 + 1)
    have hH := harmonicGrid_exact (w1 - 1, w1 + (4 * (k : ℤ) + 8) - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (w1 + (4 * (k : ℤ) + 8) - w1)
    have hpar : (w1 - 1 + (w1 + (4 * (k : ℤ) + 8) - 2)) % 2 =
        1 - (w1 + (4 * (k : ℤ) + 8) - w1) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar
  · have hmem : (1 - w1, w1 + 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k w1 (w1 + (4 * (k : ℤ) + 8)) (-2) 0 (1 - w1) (w1 + 1)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (1 - w1, w1 + 1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : 1 - w1 - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle (w1 + 1)
    have hH := harmonicGrid_exact (w1, w1 + (4 * (k : ℤ) + 8) - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (w1 + (4 * (k : ℤ) + 8) - w1)
    have hpar : (w1 + (w1 + (4 * (k : ℤ) + 8) - 3)) % 2 =
        1 - (w1 + (4 * (k : ℤ) + 8) - w1) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- The diagonal `w2 - w1 = 2d+1` for `0 <= w1 <= d-3`: `C = V` via `(-2,0)`, `A = V + 2` via `(-3,0)`. -/
theorem diagonalOdd_piece (k : ℕ) (w1 w2 : ℤ) (h1 : 0 ≤ w1) (h2 : w1 ≤ 2 * (k : ℤ) + 1)
    (hw2 : w2 = w1 + (4 * (k : ℤ) + 9)) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 2 ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw2
  have hA : (w1, w1 + (4 * (k : ℤ) + 9)) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : (w1, w1 + (4 * (k : ℤ) + 9)) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w1 + (4 * (k : ℤ) + 9)) =
      -((w1 + (4 * (k : ℤ) + 9) - w1) ^ 2 / 4) - 2 * w1 - 1 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (w1 + (4 * (k : ℤ) + 9)) ≤ 0),
      min_eq_right (by omega : 2 * (2 * (k : ℤ) + 4) - (w1 + (4 * (k : ℤ) + 9)) ≤ 0),
      max_eq_left (by omega : (0 : ℤ) ≤ w1 + (4 * (k : ℤ) + 9) - w1 - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : (2 * (k : ℤ) + 2 - w1, w1 + 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k w1 (w1 + (4 * (k : ℤ) + 9)) (-3) 0 (2 * (k : ℤ) + 2 - w1) (w1 + 1)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 2 - w1, w1 + 1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 2 - w1 - 1)] at hA'
    have hQ := two_mul_triangle (w1 + 1)
    have hH := harmonicGrid_exact (w1 - 1, w1 + (4 * (k : ℤ) + 9) - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (w1 + (4 * (k : ℤ) + 9) - w1)
    have hpar : (w1 - 1 + (w1 + (4 * (k : ℤ) + 9) - 2)) % 2 =
        1 - (w1 + (4 * (k : ℤ) + 9) - w1) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar
  · have hmem : (-w1, w1 + 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k w1 (w1 + (4 * (k : ℤ) + 9)) (-2) 0 (-w1) (w1 + 1)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (-w1, w1 + 1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : -w1 - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle (w1 + 1)
    have hH := harmonicGrid_exact (w1, w1 + (4 * (k : ℤ) + 9) - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (w1 + (4 * (k : ℤ) + 9) - w1)
    have hpar : (w1 + (w1 + (4 * (k : ℤ) + 9) - 3)) % 2 =
        1 - (w1 + (4 * (k : ℤ) + 9) - w1) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- The point `(d-2, 3d-1)`: `C = V` via `(-3,0)`, `A = V + 1` via `(-3,0)`. -/
theorem diagonalTop_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 2 * (k : ℤ) + 2)
    (hw2 : w2 = 6 * (k : ℤ) + 11) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 1 ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw1 hw2
  have hA : (2 * (k : ℤ) + 2, 6 * (k : ℤ) + 11) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : (2 * (k : ℤ) + 2, 6 * (k : ℤ) + 11) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 2, 6 * (k : ℤ) + 11) =
      -((6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 2)) ^ 2 / 4) - 4 * (k : ℤ) - 5 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (6 * (k : ℤ) + 11) ≤ 0),
      min_eq_right (by omega : 2 * (2 * (k : ℤ) + 4) - (6 * (k : ℤ) + 11) ≤ 0),
      max_eq_left (by omega : (0 : ℤ) ≤ 6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 2) - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : ((0 : ℤ), 2 * (k : ℤ) + 3) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (2 * (k : ℤ) + 2) (6 * (k : ℤ) + 11) (-3) 0 0 (2 * (k : ℤ) + 3)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((0 : ℤ), 2 * (k : ℤ) + 3) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (0 : ℤ) - 1 ≤ 0)] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 2 - 1, 6 * (k : ℤ) + 11 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 2))
    have hpar : (2 * (k : ℤ) + 2 - 1 + (6 * (k : ℤ) + 11 - 2)) % 2 =
        1 - (6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 2)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar
  · have hmem : ((1 : ℤ), 2 * (k : ℤ) + 4) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (2 * (k : ℤ) + 2) (6 * (k : ℤ) + 11) (-3) 0 1 (2 * (k : ℤ) + 4)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((1 : ℤ), 2 * (k : ℤ) + 4) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (1 : ℤ) - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle (2 * (k : ℤ) + 4)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 2, 6 * (k : ℤ) + 11 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 2))
    have hpar : (2 * (k : ℤ) + 2 + (6 * (k : ℤ) + 11 - 3)) % 2 =
        1 - (6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 2)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

end FLatticePaper.Induction
