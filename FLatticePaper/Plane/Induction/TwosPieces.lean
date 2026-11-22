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

/-- The point `(d-1, 3d-2)`: `A = V` via `(-3,0)` and `C = V` via `(-2,0)`. -/
theorem columnDTop_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 2 * (k : ℤ) + 3)
    (hw2 : w2 = 6 * (k : ℤ) + 10) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw1 hw2
  have hA : (2 * (k : ℤ) + 3, 6 * (k : ℤ) + 10) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : (2 * (k : ℤ) + 3, 6 * (k : ℤ) + 10) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 3, 6 * (k : ℤ) + 10) =
      -((6 * (k : ℤ) + 10 - (2 * (k : ℤ) + 3)) ^ 2 / 4) - 4 * (k : ℤ) - 5 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (6 * (k : ℤ) + 10) ≤ 0),
      min_eq_right (by omega : 2 * (2 * (k : ℤ) + 4) - (6 * (k : ℤ) + 10) ≤ 0),
      max_eq_left (by omega : (0 : ℤ) ≤ 6 * (k : ℤ) + 10 - (2 * (k : ℤ) + 3) - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : ((1 : ℤ), 2 * (k : ℤ) + 4) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (2 * (k : ℤ) + 3) (6 * (k : ℤ) + 10) (-3) 0 1 (2 * (k : ℤ) + 4)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((1 : ℤ), 2 * (k : ℤ) + 4) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (1 : ℤ) - 1 ≤ 0)] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 4)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 3 - 1, 6 * (k : ℤ) + 10 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (6 * (k : ℤ) + 10 - (2 * (k : ℤ) + 3))
    have hpar : (2 * (k : ℤ) + 3 - 1 + (6 * (k : ℤ) + 10 - 2)) % 2 =
        1 - (6 * (k : ℤ) + 10 - (2 * (k : ℤ) + 3)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar
  · have hmem : (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 4) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (2 * (k : ℤ) + 3) (6 * (k : ℤ) + 10) (-2) 0 (-2 * (k : ℤ) - 1)
      (2 * (k : ℤ) + 4) (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3)
        (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 4) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : -2 * (k : ℤ) - 1 - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle (2 * (k : ℤ) + 4)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 3, 6 * (k : ℤ) + 10 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (6 * (k : ℤ) + 10 - (2 * (k : ℤ) + 3))
    have hpar : (2 * (k : ℤ) + 3 + (6 * (k : ℤ) + 10 - 3)) % 2 =
        1 - (6 * (k : ℤ) + 10 - (2 * (k : ℤ) + 3)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- The point `(d-1, 3d-1)`: `A = V` via `(-3,0)` and `C = V` via `(-2,1)` (a corner of the tile). -/
theorem columnDTopCorner_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 2 * (k : ℤ) + 3)
    (hw2 : w2 = 6 * (k : ℤ) + 11) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw1 hw2
  have hA : (2 * (k : ℤ) + 3, 6 * (k : ℤ) + 11) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : (2 * (k : ℤ) + 3, 6 * (k : ℤ) + 11) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 3, 6 * (k : ℤ) + 11) =
      -((6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 3)) ^ 2 / 4) - 4 * (k : ℤ) - 6 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (6 * (k : ℤ) + 11) ≤ 0),
      min_eq_right (by omega : 2 * (2 * (k : ℤ) + 4) - (6 * (k : ℤ) + 11) ≤ 0),
      max_eq_left (by omega : (0 : ℤ) ≤ 6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 3) - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : ((0 : ℤ), 2 * (k : ℤ) + 4) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (2 * (k : ℤ) + 3) (6 * (k : ℤ) + 11) (-3) 0 0 (2 * (k : ℤ) + 4)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((0 : ℤ), 2 * (k : ℤ) + 4) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (0 : ℤ) - 1 ≤ 0)] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 4)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 3 - 1, 6 * (k : ℤ) + 11 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 3))
    have hpar : (2 * (k : ℤ) + 3 - 1 + (6 * (k : ℤ) + 11 - 2)) % 2 =
        1 - (6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 3)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar
  · have hmem : ((0 : ℤ), 0) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (2 * (k : ℤ) + 3) (6 * (k : ℤ) + 11) (-2) 1 0 0 (by ring) (by ring) hmem
    have hcorner : BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((0 : ℤ), 0) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_pos hcorner, min_eq_left (by omega : (0 : ℤ) - 1 ≤ 0)] at hC
    rw [transverseGrade_one, periodDenominator_one] at hC
    have hQ := two_mul_triangle 0
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 3, 6 * (k : ℤ) + 11 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 3))
    have hpar : (2 * (k : ℤ) + 3 + (6 * (k : ℤ) + 11 - 3)) % 2 =
        1 - (6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 3)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar + 2 * hcV

/-- The point `(d, 2d-1)`: `A = V` via `(-2,0)`, `C = V + 1` via `(-1,0)`. -/
theorem columnDTwoLess_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 2 * (k : ℤ) + 4)
    (hw2 : w2 = 4 * (k : ℤ) + 7) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 1 := by
  subst hw1 hw2
  have hA : (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 7) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 7) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 7) =
      -((4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 4)) ^ 2 / 4) - 2 * (k : ℤ) - 3 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (4 * (k : ℤ) + 7) ≤ 0),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - (4 * (k : ℤ) + 7)),
      max_eq_right (by omega : 4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4) ≤ 0)]
    ring
  rw [hV]
  constructor
  · have hmem : ((1 : ℤ), 2 * (k : ℤ) + 4) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (2 * (k : ℤ) + 4) (4 * (k : ℤ) + 7) (-2) 0 1 (2 * (k : ℤ) + 4)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((1 : ℤ), 2 * (k : ℤ) + 4) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (1 : ℤ) - 1 ≤ 0)] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 4)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 4 - 1, 4 * (k : ℤ) + 7 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 4))
    have hpar : (2 * (k : ℤ) + 4 - 1 + (4 * (k : ℤ) + 7 - 2)) % 2 =
        1 - (4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 4)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar
  · have hmem : (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 4) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (2 * (k : ℤ) + 4) (4 * (k : ℤ) + 7) (-1) 0 (-2 * (k : ℤ) - 1)
      (2 * (k : ℤ) + 4) (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3)
        (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 4) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : -2 * (k : ℤ) - 1 - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle (2 * (k : ℤ) + 4)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 7 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 4))
    have hpar : (2 * (k : ℤ) + 4 + (4 * (k : ℤ) + 7 - 3)) % 2 =
        1 - (4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 4)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar

/-- The point `(d, 2d)`: `A = V` via `(-2,0)`, `C = V + 1` via `(-1,1)` (a corner of the tile). -/
theorem columnDTwo_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 2 * (k : ℤ) + 4)
    (hw2 : w2 = 4 * (k : ℤ) + 8) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 1 := by
  subst hw1 hw2
  have hA : (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 8) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 8) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 8) =
      -((4 * (k : ℤ) + 8 - (2 * (k : ℤ) + 4)) ^ 2 / 4) - (2 * (k : ℤ) + 4) := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (4 * (k : ℤ) + 8) ≤ 0),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - (4 * (k : ℤ) + 8)),
      max_eq_right (by omega : 4 * (k : ℤ) + 8 - (2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4) ≤ 0)]
    ring
  rw [hV]
  constructor
  · have hmem : ((0 : ℤ), 2 * (k : ℤ) + 4) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (2 * (k : ℤ) + 4) (4 * (k : ℤ) + 8) (-2) 0 0 (2 * (k : ℤ) + 4)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((0 : ℤ), 2 * (k : ℤ) + 4) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (0 : ℤ) - 1 ≤ 0)] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 4)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 4 - 1, 4 * (k : ℤ) + 8 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (4 * (k : ℤ) + 8 - (2 * (k : ℤ) + 4))
    have hpar : (2 * (k : ℤ) + 4 - 1 + (4 * (k : ℤ) + 8 - 2)) % 2 =
        1 - (4 * (k : ℤ) + 8 - (2 * (k : ℤ) + 4)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar
  · have hmem : ((0 : ℤ), 0) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (2 * (k : ℤ) + 4) (4 * (k : ℤ) + 8) (-1) 1 0 0 (by ring) (by ring) hmem
    have hcorner : BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((0 : ℤ), 0) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_pos hcorner, min_eq_left (by omega : (0 : ℤ) - 1 ≤ 0)] at hC
    rw [transverseGrade_one, periodDenominator_one] at hC
    have hQ := two_mul_triangle 0
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 8 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (4 * (k : ℤ) + 8 - (2 * (k : ℤ) + 4))
    have hpar : (2 * (k : ℤ) + 4 + (4 * (k : ℤ) + 8 - 3)) % 2 =
        1 - (4 * (k : ℤ) + 8 - (2 * (k : ℤ) + 4)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar + 2 * hcV

/-- The column `w1 = d` above `2d`: `A = V` via `(-2,0)`, `C = V + 1` via `(-2,1)`, for `2d+1 <= w2 <= 3d-3`. -/
theorem columnDAbove_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 2 * (k : ℤ) + 4)
    (h1 : 4 * (k : ℤ) + 9 ≤ w2) (h2 : w2 ≤ 6 * (k : ℤ) + 9) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 1 := by
  subst hw1
  have hA : (2 * (k : ℤ) + 4, w2) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : (2 * (k : ℤ) + 4, w2) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4, w2) =
      -((w2 - (2 * (k : ℤ) + 4)) ^ 2 / 4) + (2 * (k : ℤ) + 4 - w2) := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - w2 ≤ 0),
      min_eq_right (by omega : 2 * (2 * (k : ℤ) + 4) - w2 ≤ 0),
      max_eq_left (by omega : (0 : ℤ) ≤ w2 - (2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : (4 * (k : ℤ) + 8 - w2, 2 * (k : ℤ) + 4) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (2 * (k : ℤ) + 4) w2 (-2) 0 (4 * (k : ℤ) + 8 - w2)
      (2 * (k : ℤ) + 4) (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3)
        (4 * (k : ℤ) + 8 - w2, 2 * (k : ℤ) + 4) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : 4 * (k : ℤ) + 8 - w2 - 1 ≤ 0)] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 4)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 4 - 1, w2 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - (2 * (k : ℤ) + 4))
    have hpar : (2 * (k : ℤ) + 4 - 1 + (w2 - 2)) % 2 = 1 - (w2 - (2 * (k : ℤ) + 4)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar
  · have hmem : (6 * (k : ℤ) + 11 - w2, (1 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (2 * (k : ℤ) + 4) w2 (-2) 1 (6 * (k : ℤ) + 11 - w2) 1
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (6 * (k : ℤ) + 11 - w2, (1 : ℤ)) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_right (by omega : (0 : ℤ) ≤ 6 * (k : ℤ) + 11 - w2 - 1)] at hC
    rw [transverseGrade_one, periodDenominator_one] at hC
    have hQ := two_mul_triangle 1
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 4, w2 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - (2 * (k : ℤ) + 4))
    have hpar : (2 * (k : ℤ) + 4 + (w2 - 3)) % 2 = 1 - (w2 - (2 * (k : ℤ) + 4)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar + 2 * hcV

/-- The point `(d, 3d-2)`: `A = V` via `(-2,1)` (a corner of the tile), `C = V + 1` via `(-2,1)`. -/
theorem columnDTopLess_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 2 * (k : ℤ) + 4)
    (hw2 : w2 = 6 * (k : ℤ) + 10) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 1 := by
  subst hw1 hw2
  have hA : (2 * (k : ℤ) + 4, 6 * (k : ℤ) + 10) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : (2 * (k : ℤ) + 4, 6 * (k : ℤ) + 10) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4, 6 * (k : ℤ) + 10) =
      -((6 * (k : ℤ) + 10 - (2 * (k : ℤ) + 4)) ^ 2 / 4) - 4 * (k : ℤ) - 6 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (6 * (k : ℤ) + 10) ≤ 0),
      min_eq_right (by omega : 2 * (2 * (k : ℤ) + 4) - (6 * (k : ℤ) + 10) ≤ 0),
      max_eq_left (by omega : (0 : ℤ) ≤ 6 * (k : ℤ) + 10 - (2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : ((0 : ℤ), 0) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (2 * (k : ℤ) + 4) (6 * (k : ℤ) + 10) (-2) 1 0 0
      (by ring) (by ring) hmem
    have hcorner : BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((0 : ℤ), 0) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_pos hcorner, min_eq_left (by omega : (0 : ℤ) - 1 ≤ 0)] at hA'
    rw [transverseGrade_one, periodDenominator_one] at hA'
    have hQ := two_mul_triangle 0
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 4 - 1, 6 * (k : ℤ) + 10 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (6 * (k : ℤ) + 10 - (2 * (k : ℤ) + 4))
    have hpar : (2 * (k : ℤ) + 4 - 1 + (6 * (k : ℤ) + 10 - 2)) % 2 =
        1 - (6 * (k : ℤ) + 10 - (2 * (k : ℤ) + 4)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar + 2 * hcV
  · have hmem : ((1 : ℤ), 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (2 * (k : ℤ) + 4) (6 * (k : ℤ) + 10) (-2) 1 1 1 (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((1 : ℤ), 1) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (1 : ℤ) - 1 ≤ 0)] at hC
    rw [transverseGrade_one, periodDenominator_one] at hC
    have hQ := two_mul_triangle 1
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 4, 6 * (k : ℤ) + 10 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (6 * (k : ℤ) + 10 - (2 * (k : ℤ) + 4))
    have hpar : (2 * (k : ℤ) + 4 + (6 * (k : ℤ) + 10 - 3)) % 2 =
        1 - (6 * (k : ℤ) + 10 - (2 * (k : ℤ) + 4)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar + 2 * hcV

/-- The point `(d, 3d-1)`: `A = V` via `(-3,1)` and `C = V` via `(-2,1)`. -/
theorem columnDTopMax_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 2 * (k : ℤ) + 4)
    (hw2 : w2 = 6 * (k : ℤ) + 11) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw1 hw2
  have hA : (2 * (k : ℤ) + 4, 6 * (k : ℤ) + 11) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : (2 * (k : ℤ) + 4, 6 * (k : ℤ) + 11) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4, 6 * (k : ℤ) + 11) =
      -((6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 4)) ^ 2 / 4) - 4 * (k : ℤ) - 7 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (6 * (k : ℤ) + 11) ≤ 0),
      min_eq_right (by omega : 2 * (2 * (k : ℤ) + 4) - (6 * (k : ℤ) + 11) ≤ 0),
      max_eq_left (by omega : (0 : ℤ) ≤ 6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : (2 * (k : ℤ) + 2, (1 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (2 * (k : ℤ) + 4) (6 * (k : ℤ) + 11) (-3) 1 (2 * (k : ℤ) + 2) 1
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 2, (1 : ℤ)) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 2 - 1)] at hA'
    rw [transverseGrade_one, periodDenominator_one] at hA'
    have hQ := two_mul_triangle 1
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 4 - 1, 6 * (k : ℤ) + 11 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 4))
    have hpar : (2 * (k : ℤ) + 4 - 1 + (6 * (k : ℤ) + 11 - 2)) % 2 =
        1 - (6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 4)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar + 2 * hcV
  · have hmem : ((0 : ℤ), (1 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (2 * (k : ℤ) + 4) (6 * (k : ℤ) + 11) (-2) 1 0 1 (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((0 : ℤ), (1 : ℤ)) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (0 : ℤ) - 1 ≤ 0)] at hC
    rw [transverseGrade_one, periodDenominator_one] at hC
    have hQ := two_mul_triangle 1
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 4, 6 * (k : ℤ) + 11 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 4))
    have hpar : (2 * (k : ℤ) + 4 + (6 * (k : ℤ) + 11 - 3)) % 2 =
        1 - (6 * (k : ℤ) + 11 - (2 * (k : ℤ) + 4)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar + 2 * hcV

/-- The column `w1 = d+1` for `d+1 <= w2 <= 2d-2`: `A = V` via `(-1,0)`, `C = V + 2` via `(-1,1)`. -/
theorem columnDPlusOne_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 2 * (k : ℤ) + 5)
    (h1 : 2 * (k : ℤ) + 5 ≤ w2) (h2 : w2 ≤ 4 * (k : ℤ) + 6) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 2 := by
  subst hw1
  have hA : (2 * (k : ℤ) + 5, w2) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : (2 * (k : ℤ) + 5, w2) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 5, w2) =
      -((w2 - (2 * (k : ℤ) + 5)) ^ 2 / 4) + (2 * (k : ℤ) + 4 - w2) := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - w2 ≤ 0),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - w2),
      max_eq_right (by omega : w2 - (2 * (k : ℤ) + 5) - (2 * (k : ℤ) + 4) ≤ 0)]
    ring
  rw [hV]
  constructor
  · have hmem : (2 * (k : ℤ) + 5 - w2, 2 * (k : ℤ) + 4) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (2 * (k : ℤ) + 5) w2 (-1) 0 (2 * (k : ℤ) + 5 - w2)
      (2 * (k : ℤ) + 4) (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3)
        (2 * (k : ℤ) + 5 - w2, 2 * (k : ℤ) + 4) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : 2 * (k : ℤ) + 5 - w2 - 1 ≤ 0)] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 4)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 5 - 1, w2 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - (2 * (k : ℤ) + 5))
    have hpar : (2 * (k : ℤ) + 5 - 1 + (w2 - 2)) % 2 = 1 - (w2 - (2 * (k : ℤ) + 5)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar
  · have hmem : (4 * (k : ℤ) + 8 - w2, (1 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (2 * (k : ℤ) + 5) w2 (-1) 1 (4 * (k : ℤ) + 8 - w2) 1
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (4 * (k : ℤ) + 8 - w2, (1 : ℤ)) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_right (by omega : (0 : ℤ) ≤ 4 * (k : ℤ) + 8 - w2 - 1)] at hC
    rw [transverseGrade_one, periodDenominator_one] at hC
    have hQ := two_mul_triangle 1
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 5, w2 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (w2 - (2 * (k : ℤ) + 5))
    have hpar : (2 * (k : ℤ) + 5 + (w2 - 3)) % 2 = 1 - (w2 - (2 * (k : ℤ) + 5)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar + 2 * hcV

/-- The point `(d+1, d-1)` of the set `A`: `A = V = 0` via `(0,0)`, `C = V + 2` via `(0,0)`. -/
theorem apexA_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 2 * (k : ℤ) + 5) (hw2 : w2 = 2 * (k : ℤ) + 3) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 2 := by
  subst hw1 hw2
  have hind : ((2 * (k : ℤ) + 5), (2 * (k : ℤ) + 3)) ∈
      paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4) :=
    Set.mem_union_left _ (by
      unfold paperNearLadderA
      exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (Prod.ext (by ring) (by ring))))
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) = 0 := by
    rw [paperNearLadderValue_on _ _ _ hind,
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 4 - (2 * (k : ℤ) + 3)),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 3)),
      max_eq_right (by omega : 2 * (k : ℤ) + 3 - (2 * (k : ℤ) + 5) - (2 * (k : ℤ) + 4) ≤ 0)]
    have e : 2 * (k : ℤ) + 3 - (2 * (k : ℤ) + 5) = -2 := by ring
    rw [e]
    norm_num
  rw [hV]
  constructor
  · have hmem : (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 3) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (2 * (k : ℤ) + 5) (2 * (k : ℤ) + 3) 0 0 (-2 * (k : ℤ) - 1)
      (2 * (k : ℤ) + 3) (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 3) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : -2 * (k : ℤ) - 1 - 1 ≤ 0)] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 5 - 1, 2 * (k : ℤ) + 3 - 2)
    simp only at hH
    have hpar : (2 * (k : ℤ) + 5 - 1 + (2 * (k : ℤ) + 3 - 2)) % 2 = 1 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH - hpar
  · have hmem : (-2 * (k : ℤ), 2 * (k : ℤ) + 4) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (2 * (k : ℤ) + 5) (2 * (k : ℤ) + 3) 0 0 (-2 * (k : ℤ))
      (2 * (k : ℤ) + 4) (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (-2 * (k : ℤ), 2 * (k : ℤ) + 4) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : -2 * (k : ℤ) - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle (2 * (k : ℤ) + 4)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3 - 3)
    simp only at hH
    have hpar : (2 * (k : ℤ) + 5 + (2 * (k : ℤ) + 3 - 3)) % 2 = 1 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH - hpar

/-- The corner `(0,1)`: `A = V = 0` and `C = V = 0`, both via `(0,-1)`. -/
theorem cornerZeroOne_piece (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        ((0 : ℤ), (1 : ℤ) - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) ((0 : ℤ), (1 : ℤ)) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        ((0 : ℤ), (1 : ℤ) - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) ((0 : ℤ), (1 : ℤ)) := by
  have hA : ((0 : ℤ), (1 : ℤ)) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : ((0 : ℤ), (1 : ℤ)) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) ((0 : ℤ), (1 : ℤ)) = 0 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 4 - 1),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - 1),
      max_eq_right (by omega : (1 : ℤ) - 0 - (2 * (k : ℤ) + 4) ≤ 0)]
    norm_num
  rw [hV]
  constructor
  · have hmem : (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 2) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k 0 1 0 (-1) (-2 * (k : ℤ) - 1) (2 * (k : ℤ) + 2)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 2) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : -2 * (k : ℤ) - 1 - 1 ≤ 0)] at hA'
    rw [transverseGrade_one, periodDenominator_one] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 2)
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (0 - 1, 1 - 2)
    simp only at hH
    have hpar : ((0 : ℤ) - 1 + (1 - 2)) % 2 = 0 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH - hpar - 2 * hcV
  · have hmem : (-2 * (k : ℤ), 2 * (k : ℤ) + 3) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k 0 1 0 (-1) (-2 * (k : ℤ)) (2 * (k : ℤ) + 3)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (-2 * (k : ℤ), 2 * (k : ℤ) + 3) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : -2 * (k : ℤ) - 1 ≤ 0)] at hC
    rw [transverseGrade_one, periodDenominator_one] at hC
    have hQ := two_mul_triangle (2 * (k : ℤ) + 3)
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (0, 1 - 3)
    simp only at hH
    have hpar : ((0 : ℤ) + (1 - 3)) % 2 = 0 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH - hpar - 2 * hcV

/-- The corner `(1,1)`: `A = V = 0` via `(0,-1)` and `C = V = 0` via `(0,0)`. -/
theorem cornerOneOne_piece (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        ((1 : ℤ), (1 : ℤ) - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) ((1 : ℤ), (1 : ℤ)) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        ((1 : ℤ), (1 : ℤ) - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) ((1 : ℤ), (1 : ℤ)) := by
  have hA : ((1 : ℤ), (1 : ℤ)) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : ((1 : ℤ), (1 : ℤ)) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) ((1 : ℤ), (1 : ℤ)) = 0 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 4 - 1),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - 1),
      max_eq_right (by omega : (1 : ℤ) - 1 - (2 * (k : ℤ) + 4) ≤ 0)]
    norm_num
  rw [hV]
  constructor
  · have hmem : (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 3) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k 1 1 0 (-1) (-2 * (k : ℤ) - 1) (2 * (k : ℤ) + 3)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 3) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : -2 * (k : ℤ) - 1 - 1 ≤ 0)] at hA'
    rw [transverseGrade_one, periodDenominator_one] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 3)
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact ((1 : ℤ) - 1, 1 - 2)
    simp only at hH
    have hpar : ((1 : ℤ) - 1 + (1 - 2)) % 2 = 1 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH - hpar - 2 * hcV
  · have hmem : ((2 : ℤ), (0 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k 1 1 0 0 2 0 (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((2 : ℤ), (0 : ℤ)) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_right (by omega : (0 : ℤ) ≤ 2 - 1)] at hC
    have hQ := two_mul_triangle 0
    have hH := harmonicGrid_exact ((1 : ℤ), 1 - 3)
    simp only at hH
    have hpar : ((1 : ℤ) + (1 - 3)) % 2 = 1 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH - hpar

/-- The corner `(2,1)`: `A = V = 0` via `(0,0)` and `C = V + 1` via `(0,0)`. -/
theorem cornerTwoOne_piece (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        ((2 : ℤ), (1 : ℤ) - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) ((2 : ℤ), (1 : ℤ)) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        ((2 : ℤ), (1 : ℤ) - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) ((2 : ℤ), (1 : ℤ)) + 1 := by
  have hA : ((2 : ℤ), (1 : ℤ)) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : ((2 : ℤ), (1 : ℤ)) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) ((2 : ℤ), (1 : ℤ)) = 0 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 4 - 1),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - 1),
      max_eq_right (by omega : (1 : ℤ) - 2 - (2 * (k : ℤ) + 4) ≤ 0)]
    norm_num
  rw [hV]
  constructor
  · have hmem : ((1 : ℤ), (0 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k 2 1 0 0 1 0 (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((1 : ℤ), (0 : ℤ)) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (1 : ℤ) - 1 ≤ 0)] at hA'
    have hQ := two_mul_triangle 0
    have hH := harmonicGrid_exact ((2 : ℤ) - 1, 1 - 2)
    simp only at hH
    have hpar : ((2 : ℤ) - 1 + (1 - 2)) % 2 = 0 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH - hpar
  · have hmem : ((2 : ℤ), (1 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k 2 1 0 0 2 1 (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((2 : ℤ), (1 : ℤ)) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_right (by omega : (0 : ℤ) ≤ 2 - 1)] at hC
    have hQ := two_mul_triangle 1
    have hH := harmonicGrid_exact ((2 : ℤ), 1 - 3)
    simp only at hH
    have hpar : ((2 : ℤ) + (1 - 3)) % 2 = 0 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH - hpar

/-- The point `(0,2)`, `V = -1`: `C = V` via `(0,-1)` and `A = V + 1` via `(-1,-1)`. -/
theorem cornerZeroTwo_piece (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        ((0 : ℤ), (2 : ℤ) - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) ((0 : ℤ), (2 : ℤ)) + 1 ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        ((0 : ℤ), (2 : ℤ) - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) ((0 : ℤ), (2 : ℤ)) := by
  have hA : ((0 : ℤ), (2 : ℤ)) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : ((0 : ℤ), (2 : ℤ)) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) ((0 : ℤ), (2 : ℤ)) = -1 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 4 - 2),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - 2),
      max_eq_right (by omega : (2 : ℤ) - 0 - (2 * (k : ℤ) + 4) ≤ 0)]
    norm_num
  rw [hV]
  constructor
  · have hmem : ((1 : ℤ), 2 * (k : ℤ) + 3) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k 0 2 (-1) (-1) 1 (2 * (k : ℤ) + 3) (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((1 : ℤ), 2 * (k : ℤ) + 3) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (1 : ℤ) - 1 ≤ 0)] at hA'
    rw [transverseGrade_one, periodDenominator_one] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 3)
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact ((0 : ℤ) - 1, 2 - 2)
    simp only at hH
    have hpar : ((0 : ℤ) - 1 + (2 - 2)) % 2 = 1 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH - hpar - 2 * hcV
  · have hmem : (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 3) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k 0 2 0 (-1) (-2 * (k : ℤ) - 1) (2 * (k : ℤ) + 3)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 3) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : -2 * (k : ℤ) - 1 - 1 ≤ 0)] at hC
    rw [transverseGrade_one, periodDenominator_one] at hC
    have hQ := two_mul_triangle (2 * (k : ℤ) + 3)
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact ((0 : ℤ), 2 - 3)
    simp only at hH
    have hpar : ((0 : ℤ) + (2 - 3)) % 2 = 1 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH - hpar - 2 * hcV

/-- The point `(1,2)`, `V = 0`: `A = V` via `(-1,0)` and `C = V` via `(0,0)`. -/
theorem cornerOneTwo_piece (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        ((1 : ℤ), (2 : ℤ) - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) ((1 : ℤ), (2 : ℤ)) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        ((1 : ℤ), (2 : ℤ) - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) ((1 : ℤ), (2 : ℤ)) := by
  have hA : ((1 : ℤ), (2 : ℤ)) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : ((1 : ℤ), (2 : ℤ)) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) ((1 : ℤ), (2 : ℤ)) = 0 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 4 - 2),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - 2),
      max_eq_right (by omega : (2 : ℤ) - 1 - (2 * (k : ℤ) + 4) ≤ 0)]
    norm_num
  rw [hV]
  constructor
  · have hmem : (2 * (k : ℤ) + 3, (0 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k 1 2 (-1) 0 (2 * (k : ℤ) + 3) 0 (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3, (0 : ℤ)) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 3 - 1)] at hA'
    have hQ := two_mul_triangle 0
    have hH := harmonicGrid_exact ((1 : ℤ) - 1, 2 - 2)
    simp only at hH
    have hpar : ((1 : ℤ) - 1 + (2 - 2)) % 2 = 0 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH - hpar
  · have hmem : ((1 : ℤ), (0 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k 1 2 0 0 1 0 (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((1 : ℤ), (0 : ℤ)) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (1 : ℤ) - 1 ≤ 0)] at hC
    have hQ := two_mul_triangle 0
    have hH := harmonicGrid_exact ((1 : ℤ), 2 - 3)
    simp only at hH
    have hpar : ((1 : ℤ) + (2 - 3)) % 2 = 0 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH - hpar

/-- Two values with one equal to the staircase `V` and the other at least `V`: the minimum is `V`. -/
theorem min_tile0 (V x y : ℤ) (h1 : x = V) (h2 : y = V) : min x y = V := by
  omega

theorem min_tile_left (V x y b : ℤ) (h1 : x = V) (h2 : y = V + b) (hb : 0 ≤ b) : min x y = V := by
  omega

theorem min_tile_right (V x y a : ℤ) (h1 : x = V + a) (h2 : y = V) (ha : 0 ≤ a) : min x y = V := by
  omega

/-- The tie line `w2 = w1 + d` of the tile: the minimum is the staircase value (`twos_tie_min`). -/
theorem tie_leaf (k : ℕ) (w1 w2 : ℤ) (hw : w2 = w1 + (2 * (k : ℤ) + 4)) (h1 : 1 ≤ w1)
    (h2 : w1 ≤ 2 * (k : ℤ) + 3) :
    min ((frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1))
      ((frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1)) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw
  exact twos_tie_min k w1 h1 h2

/-- The identification on the tile: `min(A, C) = V` at every point of `(A ∪ B ∪ C) \ D`, for every `k`. -/
theorem twos_tile_min (k : ℕ) (w1 w2 : ℤ) (hE : (w1, w2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    min ((frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1))
      ((frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1)) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  obtain ⟨hU, hnD⟩ := hE
  simp only [paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq] at hU hnD
  rcases hU with ((⟨hA1, hA2⟩ | ⟨hA1, hA2⟩) | ⟨hB1, hB2, hB3⟩) | ⟨hC1, hC2, hC3, hC4, hC5, hC6⟩
  · -- the point (-1, 2d+1) of A
    obtain ⟨h1, h2⟩ := leftEdgeTop_piece k w1 w2 hA1 (by omega)
    exact min_tile_right _ _ _ 2 h1 h2 (by norm_num)
  · -- the point (d+1, d-1) of A
    obtain ⟨h1, h2⟩ := apexA_piece k w1 w2 (by omega) (by omega)
    exact min_tile_left _ _ _ 2 h1 h2 (by norm_num)
  · -- the tie line B
    exact tie_leaf k w1 w2 (by omega) (by omega) (by omega)
  · -- the box C minus D: split by the band of w2
    have hT : w2 ≤ 2 ∨ (3 ≤ w2 ∧ w2 ≤ 2 * (k : ℤ) + 4) ∨ w2 = 2 * (k : ℤ) + 5 ∨
        (2 * (k : ℤ) + 6 ≤ w2 ∧ w2 ≤ 4 * (k : ℤ) + 7) ∨ w2 = 4 * (k : ℤ) + 8 ∨
        (4 * (k : ℤ) + 9 ≤ w2 ∧ w2 ≤ 6 * (k : ℤ) + 9) ∨ 6 * (k : ℤ) + 10 ≤ w2 := by
      omega
    rcases hT with hT | hT | hT | hT | hT | hT | hT
    · -- band w2 ≤ 2: corners and the first lower row
      obtain rfl | rfl : w2 = 1 ∨ w2 = 2 := by omega
      · have hw : w1 = 0 ∨ w1 = 1 ∨ w1 = 2 := by omega
        rcases hw with rfl | rfl | rfl
        · obtain ⟨h1, h2⟩ := cornerZeroOne_piece k
          exact min_tile0 _ _ _ h1 h2
        · obtain ⟨h1, h2⟩ := cornerOneOne_piece k
          exact min_tile0 _ _ _ h1 h2
        · obtain ⟨h1, h2⟩ := cornerTwoOne_piece k
          exact min_tile_left _ _ _ 1 h1 h2 (by norm_num)
      · have hw : w1 = 0 ∨ w1 = 1 ∨ w1 = 2 ∨ w1 = 3 := by omega
        rcases hw with rfl | rfl | rfl | rfl
        · obtain ⟨h1, h2⟩ := cornerZeroTwo_piece k
          exact min_tile_right _ _ _ 1 h1 h2 (by norm_num)
        · obtain ⟨h1, h2⟩ := cornerOneTwo_piece k
          exact min_tile0 _ _ _ h1 h2
        · obtain ⟨h1, h2⟩ := lowerA1_piece k 2 2 (by norm_num) (by norm_num) (by omega)
            (by norm_num) (by norm_num)
          exact min_tile_left _ _ _ _ h1 h2 (by norm_num)
        · obtain ⟨h1, h2⟩ := lowerA1_piece k 3 2 (by norm_num) (by norm_num) (by omega)
            (by norm_num) (by norm_num)
          exact min_tile_left _ _ _ _ h1 h2 (by norm_num)
    · -- band 3 <= w2 <= d: the zero column, the lower tie, and the lower edge
      have hw : w1 = 0 ∨ (1 ≤ w1 ∧ w1 ≤ w2 - 1) ∨ w2 ≤ w1 := by omega
      rcases hw with hw | hw | hw
      · obtain ⟨h1, h2⟩ := zeroColumn_piece k w1 w2 hw (by omega) (by omega)
        exact min_tile_right _ _ _ 1 h1 h2 (by norm_num)
      · obtain ⟨h1, h2⟩ := lower_tie_piece k w1 w2 (by omega) (by omega) (by omega) (by omega)
        exact min_tile0 _ _ _ h1 h2
      · obtain ⟨h1, h2⟩ := lowerA1_piece k w1 w2 (by omega) (by omega) (by omega) hw (by omega)
        exact min_tile_left _ _ _ _ h1 h2 (by omega)
    · -- the row w2 = d+1
      have hw : w1 = 0 ∨ w1 = 1 ∨ (2 ≤ w1 ∧ w1 ≤ 2 * (k : ℤ) + 4) ∨ w1 = 2 * (k : ℤ) + 5 := by
        omega
      rcases hw with hw | hw | hw | hw
      · obtain ⟨h1, h2⟩ := zeroColumnTop_piece k w1 w2 hw (by omega)
        exact min_tile_right _ _ _ 1 h1 h2 (by norm_num)
      · exact tie_leaf k w1 w2 (by omega) (by omega) (by omega)
      · obtain ⟨h1, h2⟩ := upA1_piece k w1 w2 (by omega) (by omega) (by omega) (by omega) (by omega)
        exact min_tile_left _ _ _ 1 h1 h2 (by norm_num)
      · obtain ⟨h1, h2⟩ := columnDPlusOne_piece k w1 w2 hw (by omega) (by omega)
        exact min_tile_left _ _ _ 2 h1 h2 (by norm_num)
    · -- the band d+2 <= w2 <= 2d-1
      have hw : w1 = -1 ∨ (0 ≤ w1 ∧ w1 ≤ w2 - (2 * (k : ℤ) + 5)) ∨ w1 = w2 - (2 * (k : ℤ) + 4) ∨
          (w2 - (2 * (k : ℤ) + 3) ≤ w1 ∧ w1 ≤ 2 * (k : ℤ) + 4) ∨ w1 = 2 * (k : ℤ) + 5 := by
        omega
      rcases hw with hw | hw | hw | hw | hw
      · obtain ⟨h1, h2⟩ := leftEdge_piece k w1 w2 hw (by omega) (by omega)
        exact min_tile_right _ _ _ 2 h1 h2 (by norm_num)
      · obtain ⟨h1, h2⟩ := upC1_piece k w1 w2 hw.1 (by omega) (by omega) hw.2
        exact min_tile_right _ _ _ 1 h1 h2 (by norm_num)
      · exact tie_leaf k w1 w2 (by omega) (by omega) (by omega)
      · have hw2 : w2 = 4 * (k : ℤ) + 7 ∨ w2 ≤ 4 * (k : ℤ) + 6 := by omega
        rcases hw2 with hw2 | hw2
        · obtain ⟨h1, h2⟩ := columnDTwoLess_piece k w1 w2 (by omega) hw2
          exact min_tile_left _ _ _ 1 h1 h2 (by norm_num)
        · obtain ⟨h1, h2⟩ := upA1_piece k w1 w2 (by omega) (by omega) hw2 (by omega) (by omega)
          exact min_tile_left _ _ _ 1 h1 h2 (by norm_num)
      · obtain ⟨h1, h2⟩ := columnDPlusOne_piece k w1 w2 hw (by omega) (by omega)
        exact min_tile_left _ _ _ 2 h1 h2 (by norm_num)
    · -- the row w2 = 2d
      have hw : w1 = -1 ∨ w1 = 0 ∨ (1 ≤ w1 ∧ w1 ≤ 2 * (k : ℤ) + 3) ∨ w1 = 2 * (k : ℤ) + 4 := by
        omega
      rcases hw with hw | hw | hw | hw
      · obtain ⟨h1, h2⟩ := leftEdgeDouble_piece k w1 w2 hw hT
        exact min_tile_right _ _ _ 2 h1 h2 (by norm_num)
      · obtain ⟨h1, h2⟩ := diagonalEven_piece k w1 w2 (by omega) (by omega) (by omega)
        exact min_tile_right _ _ _ 1 h1 h2 (by norm_num)
      · obtain ⟨h1, h2⟩ := band2_tie_piece k w1 w2 (by omega) (by omega) (by omega) (by omega)
          (by omega)
        exact min_tile0 _ _ _ h1 h2
      · obtain ⟨h1, h2⟩ := columnDTwo_piece k w1 w2 hw hT
        exact min_tile_left _ _ _ 1 h1 h2 (by norm_num)
    · -- the band 2d+1 <= w2 <= 3d-3
      have hw : w1 = w2 - (4 * (k : ℤ) + 9) ∨ w1 = w2 - (4 * (k : ℤ) + 8) ∨
          (w2 - (4 * (k : ℤ) + 7) ≤ w1 ∧ w1 ≤ 2 * (k : ℤ) + 3) ∨ w1 = 2 * (k : ℤ) + 4 := by
        omega
      rcases hw with hw | hw | hw | hw
      · obtain ⟨h1, h2⟩ := diagonalOdd_piece k w1 w2 (by omega) (by omega) (by omega)
        exact min_tile_right _ _ _ 2 h1 h2 (by norm_num)
      · obtain ⟨h1, h2⟩ := diagonalEven_piece k w1 w2 (by omega) (by omega) (by omega)
        exact min_tile_right _ _ _ 1 h1 h2 (by norm_num)
      · obtain ⟨h1, h2⟩ := band2_tie_piece k w1 w2 (by omega) (by omega) (by omega) (by omega)
          (by omega)
        exact min_tile0 _ _ _ h1 h2
      · obtain ⟨h1, h2⟩ := columnDAbove_piece k w1 w2 hw (by omega) (by omega)
        exact min_tile_left _ _ _ 1 h1 h2 (by norm_num)
    · -- the top rows w2 = 3d-2 and 3d-1
      have hw2 : w2 = 6 * (k : ℤ) + 10 ∨ w2 = 6 * (k : ℤ) + 11 := by omega
      rcases hw2 with hw2 | hw2
      · have hw : w1 = 2 * (k : ℤ) + 1 ∨ w1 = 2 * (k : ℤ) + 2 ∨ w1 = 2 * (k : ℤ) + 3 ∨
            w1 = 2 * (k : ℤ) + 4 := by
          omega
        rcases hw with hw | hw | hw | hw
        · obtain ⟨h1, h2⟩ := diagonalOdd_piece k w1 w2 (by omega) (by omega) (by omega)
          exact min_tile_right _ _ _ 2 h1 h2 (by norm_num)
        · obtain ⟨h1, h2⟩ := diagonalEven_piece k w1 w2 (by omega) (by omega) (by omega)
          exact min_tile_right _ _ _ 1 h1 h2 (by norm_num)
        · obtain ⟨h1, h2⟩ := columnDTop_piece k w1 w2 hw hw2
          exact min_tile0 _ _ _ h1 h2
        · obtain ⟨h1, h2⟩ := columnDTopLess_piece k w1 w2 hw hw2
          exact min_tile_left _ _ _ 1 h1 h2 (by norm_num)
      · have hw : w1 = 2 * (k : ℤ) + 2 ∨ w1 = 2 * (k : ℤ) + 3 ∨ w1 = 2 * (k : ℤ) + 4 := by
          omega
        rcases hw with hw | hw | hw
        · obtain ⟨h1, h2⟩ := diagonalTop_piece k w1 w2 hw hw2
          exact min_tile_right _ _ _ 1 h1 h2 (by norm_num)
        · obtain ⟨h1, h2⟩ := columnDTopCorner_piece k w1 w2 hw hw2
          exact min_tile0 _ _ _ h1 h2
        · obtain ⟨h1, h2⟩ := columnDTopMax_piece k w1 w2 hw hw2
          exact min_tile0 _ _ _ h1 h2

/-- The boundary point `(-1, d+1)` of `E` (the point `(-1, d)` in sheet coordinates): `A = V + 2` via `(-2,-1)`,
`C = V` via `(-1,-1)`. -/
theorem boundaryLeft_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = -1) (hw2 : w2 = 2 * (k : ℤ) + 5) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 2 ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) := by
  subst hw1 hw2
  have hA : ((-1 : ℤ), 2 * (k : ℤ) + 5) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : ((-1 : ℤ), 2 * (k : ℤ) + 5) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (-1, 2 * (k : ℤ) + 5) =
      -((2 * (k : ℤ) + 5 - -1) ^ 2 / 4) + 1 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (2 * (k : ℤ) + 5) ≤ 0),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 5)),
      max_eq_left (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 5 - -1 - (2 * (k : ℤ) + 4))]
    ring
  rw [hV]
  constructor
  · have hmem : ((1 : ℤ), 2 * (k : ℤ) + 3) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (-1) (2 * (k : ℤ) + 5) (-2) (-1) 1 (2 * (k : ℤ) + 3)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((1 : ℤ), 2 * (k : ℤ) + 3) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (1 : ℤ) - 1 ≤ 0)] at hA'
    rw [transverseGrade_one, periodDenominator_one] at hA'
    have hQ := two_mul_triangle (2 * (k : ℤ) + 3)
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (-1 - 1, 2 * (k : ℤ) + 5 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (2 * (k : ℤ) + 5 - -1)
    have hpar : (-1 - 1 + (2 * (k : ℤ) + 5 - 2)) % 2 = 1 - (2 * (k : ℤ) + 5 - -1) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar - 2 * hcV
  · have hmem : (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 3) ∈
        (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (-1) (2 * (k : ℤ) + 5) (-1) (-1) (-2 * (k : ℤ) - 1) (2 * (k : ℤ) + 3)
      (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 3) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc,
      min_eq_left (by omega : -2 * (k : ℤ) - 1 - 1 ≤ 0)] at hC
    rw [transverseGrade_one, periodDenominator_one] at hC
    have hQ := two_mul_triangle (2 * (k : ℤ) + 3)
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (-1, 2 * (k : ℤ) + 5 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (2 * (k : ℤ) + 5 - -1)
    have hpar : (-1 + (2 * (k : ℤ) + 5 - 3)) % 2 = 1 - (2 * (k : ℤ) + 5 - -1) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar - 2 * hcV

/-- The boundary point `(d+1, 2d-1)` of `E` (the point `(d+1, 2d-2)` in sheet coordinates): `A = V` via `(-1,1)`
(a corner of the tile), `C = V + 2` via `(-1,1)`. -/
theorem boundaryRight_piece (k : ℕ) (w1 w2 : ℤ) (hw1 : w1 = 2 * (k : ℤ) + 5)
    (hw2 : w2 = 4 * (k : ℤ) + 7) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) ∧
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))
        (w1, w2 - 1) = paperNearLadderValue (2 * (k : ℤ) + 4) (w1, w2) + 2 := by
  subst hw1 hw2
  have hA : (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 7) ∉ paperNearLadderA (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hB : (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 7) ∉ paperNearLadderB (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderB, Set.mem_setOf_eq]
    omega
  have hV : paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 7) =
      -((4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 5)) ^ 2 / 4) - 2 * (k : ℤ) - 3 := by
    rw [paperNearLadderValue_off _ _ _ hA hB,
      min_eq_right (by omega : 2 * (k : ℤ) + 4 - (4 * (k : ℤ) + 7) ≤ 0),
      min_eq_left (by omega : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 4) - (4 * (k : ℤ) + 7)),
      max_eq_right (by omega : 4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 5) - (2 * (k : ℤ) + 4) ≤ 0)]
    ring
  rw [hV]
  constructor
  · have hmem : ((0 : ℤ), (0 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hA' := sheetA_via k (2 * (k : ℤ) + 5) (4 * (k : ℤ) + 7) (-1) 1 0 0
      (by ring) (by ring) hmem
    have hcorner : BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((0 : ℤ), (0 : ℤ)) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_pos hcorner, min_eq_left (by omega : (0 : ℤ) - 1 ≤ 0)] at hA'
    rw [transverseGrade_one, periodDenominator_one] at hA'
    have hQ := two_mul_triangle 0
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 5 - 1, 4 * (k : ℤ) + 7 - 2)
    simp only at hH
    have hP := sq_div4_add_mod2 (4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 5))
    have hpar : (2 * (k : ℤ) + 5 - 1 + (4 * (k : ℤ) + 7 - 2)) % 2 =
        1 - (4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 5)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hA' - 2 * hQ + hH + hP - hpar + 2 * hcV
  · have hmem : ((1 : ℤ), (1 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
      BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        by unfold BaseMask.StairEvenCorner; omega⟩
    have hC := sheetC_via k (2 * (k : ℤ) + 5) (4 * (k : ℤ) + 7) (-1) 1 1 1 (by ring) (by ring) hmem
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((1 : ℤ), (1 : ℤ)) := by
      unfold BaseMask.StairEvenCorner
      omega
    rw [stairEvenValue_formula, if_neg hc, min_eq_left (by omega : (1 : ℤ) - 1 ≤ 0)] at hC
    rw [transverseGrade_one, periodDenominator_one] at hC
    have hQ := two_mul_triangle 1
    have hcV := stairEvenConstantV_double (2 * (k : ℤ) + 3)
    have hH := harmonicGrid_exact (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 7 - 3)
    simp only at hH
    have hP := sq_div4_add_mod2 (4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 5))
    have hpar : (2 * (k : ℤ) + 5 + (4 * (k : ℤ) + 7 - 3)) % 2 =
        1 - (4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 5)) % 2 := by
      omega
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 2 * hC - 2 * hQ + hH + hP - hpar + 2 * hcV

/-- The closed polygon of `2^(k+1)` in the coordinates `(z1, v = z2 - z1)`, with `t = -2 z1 - (d+1) v` and
`u = (d+1) z1 + v` (so `s = 2u`), `d = 2k+4`, `P = d^2 + 2d - 1` (so `T = 2P`): every point lies in the tile
shifted by `(0,-1)`, or is one of the two boundary points `(-1, d)`, `(d+1, 2d-2)`. -/
theorem twos_E_arith (d z1 v : ℤ) (hd : 4 ≤ d)
    (hu0 : 0 ≤ (d + 1) * z1 + v) (huP : (d + 1) * z1 + v ≤ d * d + 2 * d - 1 + d - 1)
    (hev : v % 2 = 0 → 2 - 2 * (d * d + 2 * d - 1) ≤ -2 * z1 - (d + 1) * v ∧
      -2 * z1 - (d + 1) * v ≤ 2 * d - 2)
    (hod : v % 2 = 1 → d - 1 - 2 * (d * d + 2 * d - 1) ≤ -2 * z1 - (d + 1) * v ∧
      -2 * z1 - (d + 1) * v ≤ d + 1) :
    (-1 ≤ z1 ∧ z1 ≤ d + 1 ∧ -2 ≤ v ∧ v ≤ 2 * d ∧ 0 ≤ z1 + v ∧ z1 + v ≤ 3 * d - 2 ∧
        ¬(z1 = -1 ∧ z1 + v ≤ d) ∧ ¬(z1 = d + 1 ∧ 2 * d - 2 ≤ z1 + v)) ∨
      (z1 = -1 ∧ v = 2 * d + 1) ∨ (z1 = d + 1 ∧ v = -3) ∨ (z1 = -1 ∧ z1 + v = d) ∨
      (z1 = d + 1 ∧ z1 + v = 2 * d - 2) := by
  have hP : 0 < d * d + 2 * d - 1 := by nlinarith
  -- edge facts on u (parity independent)
  have hzd1 : z1 = -1 → d + 1 ≤ v := by
    intro h; subst h; nlinarith
  have hz10 : z1 = 0 → 0 ≤ v := by
    intro h; subst h; nlinarith
  have hzd1' : z1 = d + 1 → v ≤ d - 3 := by
    intro h; subst h; nlinarith
  have hzd : z1 = d → v ≤ 2 * d - 2 := by
    intro h; subst h; nlinarith
  have hz1n : z1 ≠ -1 ∨ d + 1 ≤ v := by
    rcases eq_or_ne z1 (-1) with h | h
    · right; exact hzd1 h
    · left; exact h
  have hz10' : z1 ≠ 0 ∨ 0 ≤ v := by
    rcases eq_or_ne z1 0 with h | h
    · right; exact hz10 h
    · left; exact h
  have hzd1'' : z1 ≠ d + 1 ∨ v ≤ d - 3 := by
    rcases eq_or_ne z1 (d + 1) with h | h
    · right; exact hzd1' h
    · left; exact h
  have hzd'' : z1 ≠ d ∨ v ≤ 2 * d - 2 := by
    rcases eq_or_ne z1 d with h | h
    · right; exact hzd h
    · left; exact h
  clear hzd1 hz10 hzd1' hzd
  rcases Int.emod_two_eq_zero_or_one v with hv | hv
  · obtain ⟨he1, he2⟩ := hev hv
    have hz1l : -1 ≤ z1 := by
      by_contra h
      have h2 : z1 ≤ -2 := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ d + 1 by omega) hu0,
        mul_nonneg hP.le (show (0 : ℤ) ≤ -2 - z1 by omega)]
    have hz1u : z1 ≤ d + 1 := by
      by_contra h
      have h2 : d + 2 ≤ z1 := by omega
      nlinarith [mul_nonneg hP.le (show (0 : ℤ) ≤ z1 - (d + 2) by omega),
        mul_nonneg (show (0 : ℤ) ≤ d + 1 by omega)
          (show (0 : ℤ) ≤ d * d + 2 * d - 1 + d - 1 - ((d + 1) * z1 + v) by linarith)]
    have hvt : v ≤ 2 * d := by
      by_contra h
      have h2 : 2 * d + 2 ≤ v := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ d + 1 by omega) (show (0 : ℤ) ≤ v - (2 * d + 2) by omega)]
    have hvl : -2 ≤ v := by
      by_contra h
      have h2 : v ≤ -4 := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ d + 1 by omega) (show (0 : ℤ) ≤ -4 - v by omega)]
    have hm2 : v ≠ -2 ∨ 2 ≤ z1 := by
      rcases eq_or_ne v (-2) with h | h
      · right; subst h; nlinarith
      · left; exact h
    have hvd : v ≠ 2 * d ∨ z1 ≤ d - 2 := by
      rcases eq_or_ne v (2 * d) with h | h
      · right; subst h; nlinarith
      · left; exact h
    clear hev hod hu0 huP he1 he2
    omega
  · obtain ⟨ho1, ho2⟩ := hod hv
    have hz1l : -1 ≤ z1 := by
      by_contra h
      have h2 : z1 ≤ -2 := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ d + 1 by omega) hu0,
        mul_nonneg hP.le (show (0 : ℤ) ≤ -2 - z1 by omega)]
    have hz1u : z1 ≤ d + 1 := by
      by_contra h
      have h2 : d + 2 ≤ z1 := by omega
      nlinarith [mul_nonneg hP.le (show (0 : ℤ) ≤ z1 - (d + 2) by omega),
        mul_nonneg (show (0 : ℤ) ≤ d + 1 by omega)
          (show (0 : ℤ) ≤ d * d + 2 * d - 1 + d - 1 - ((d + 1) * z1 + v) by linarith)]
    have hvt1 : v ≤ 2 * d + 1 := by
      by_contra h
      have h2 : 2 * d + 2 ≤ v := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ d + 1 by omega) (show (0 : ℤ) ≤ v - (2 * d + 2) by omega)]
    have hvt : v ≤ 2 * d ∨ (z1 = -1 ∧ v = 2 * d + 1) := by
      by_cases h : v ≤ 2 * d
      · left; exact h
      · right
        have h2 : v = 2 * d + 1 := by omega
        subst h2
        constructor
        · nlinarith
        · rfl
    have hvl : -2 ≤ v ∨ (v = -3 ∧ z1 = d + 1) := by
      by_cases h : -2 ≤ v
      · left; exact h
      · have h2 : v ≤ -3 := by omega
        have h3 : -3 ≤ v := by
          by_contra h4
          have h5 : v ≤ -5 := by omega
          nlinarith [mul_nonneg (show (0 : ℤ) ≤ d + 1 by omega) (show (0 : ℤ) ≤ -5 - v by omega)]
        have h4 : v = -3 := by omega
        subst h4
        right
        constructor
        · rfl
        · nlinarith
    have hm2 : v ≠ -2 ∨ 2 ≤ z1 := Or.inl (by omega)
    have hvd : v ≠ 2 * d ∨ z1 ≤ d - 2 := Or.inl (by omega)
    clear hev hod hu0 huP ho1 ho2 hvt1
    omega

/-- The child of `2^(k+1)` is `(2k+3)/(2k+5)`. -/
theorem twos_child_num_den (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).child.num = 2 * (k : ℤ) + 3 ∧
      (frameAt (List.replicate (k + 1) Digit.two)).child.den = 2 * (k : ℤ) + 5 := by
  rw [child_replicate_two_succ]
  unfold Fraction.rotate
  split_ifs with h
  · exact ⟨by show (2 * (k : ℤ) + 4) - 1 = 2 * (k : ℤ) + 3; ring,
      by show (2 * (k : ℤ) + 4) + 1 = 2 * (k : ℤ) + 5; ring⟩
  · exfalso
    simp only at h
    omega

/-- Every point of the closed polygon of `2^(k+1)` lies in the tile shifted by `(0,-1)`, or is one of the two
boundary points `(-1, d)`, `(d+1, 2d-2)` (here `d = 2k+4`). -/
theorem closedPolygon_twos_tile (k : ℕ) (z : Site)
    (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon) :
    (z.1, z.2 + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) ∨
      z = (-1, 2 * (k : ℤ) + 4) ∨ z = (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 6) := by
  obtain ⟨hn, hd⟩ := twos_child_num_den k
  have hT : (frameAt (List.replicate (k + 1) Digit.two)).child.periodDenominator =
      2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) := by
    simp only [Fraction.periodDenominator, hn, hd]
    ring
  obtain ⟨z1, z2⟩ := z
  rw [ChildFrame.mem_closedPolygon_iff] at hz
  simp only [ChildFrame.tGrade, ChildFrame.sGrade, hn, hd, hT, EvenSite] at hz
  have hu0 : 0 ≤ (2 * (k : ℤ) + 4 + 1) * z1 + (z2 - z1) := by
    rcases hz with ⟨_, _, _, h3, _⟩ | ⟨_, _, _, h3, _⟩ <;> linarith
  have huP : (2 * (k : ℤ) + 4 + 1) * z1 + (z2 - z1) ≤
      (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1 + (2 * (k : ℤ) + 4) - 1 := by
    rcases hz with ⟨_, _, _, _, h4⟩ | ⟨_, _, _, _, h4⟩ <;> linarith
  have hev : (z2 - z1) % 2 = 0 → 2 - 2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) ≤
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ∧
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ≤ 2 * (2 * (k : ℤ) + 4) - 2 := by
    intro hv
    rcases hz with ⟨_, h1, h2, _, _⟩ | ⟨ho, _⟩
    · exact ⟨by linarith, by linarith⟩
    · exfalso
      omega
  have hod : (z2 - z1) % 2 = 1 → (2 * (k : ℤ) + 4) - 1 - 2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) ≤
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ∧
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ≤ (2 * (k : ℤ) + 4) + 1 := by
    intro hv
    rcases hz with ⟨he, _, _, _, _⟩ | ⟨_, h1, h2, _, _⟩
    · exfalso
      omega
    · exact ⟨by linarith, by linarith⟩
  have key := twos_E_arith (2 * (k : ℤ) + 4) z1 (z2 - z1) (by omega) hu0 huP hev hod
  show (z1, z2 + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) ∨
      (z1, z2) = (-1, 2 * (k : ℤ) + 4) ∨ (z1, z2) = (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 6)
  rcases key with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩ | ⟨hP1, hP2⟩ | ⟨hP1, hP2⟩
  · left
    have hC : (z1, z2 + 1) ∈ paperNearLadderC (2 * (k : ℤ) + 4) := by
      simp only [paperNearLadderC, Set.mem_setOf_eq]
      omega
    refine ⟨Set.mem_union_right _ hC, ?_⟩
    simp only [paperNearLadderD, Set.mem_setOf_eq]
    omega
  · left
    refine ⟨Set.mem_union_left _ (Set.mem_union_left _ ?_), ?_⟩
    · simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      left
      constructor <;> omega
    · simp only [paperNearLadderD, Set.mem_setOf_eq]
      omega
  · left
    refine ⟨Set.mem_union_left _ (Set.mem_union_left _ ?_), ?_⟩
    · simp only [paperNearLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      right
      constructor <;> omega
    · simp only [paperNearLadderD, Set.mem_setOf_eq]
      omega
  · right; left
    exact Prod.ext (by omega) (by omega)
  · right; right
    exact Prod.ext (by omega) (by omega)

end FLatticePaper.Induction
