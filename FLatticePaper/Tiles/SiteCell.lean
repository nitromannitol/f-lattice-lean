import FLatticePaper.Tiles.SiteInduction

/-! Task 53, item 2 (cell reduction): a set that contains every integer point of the half-open shifted cell covers every class.

The cell is `B0 + [0,1) U + [0,1) V` with `B0 = (1/2, −1/2)`. Every integer `w` has rational coordinates `(u0, v0)` with
`w − B0 = u0 U + v0 V`, and `z = w − ⌊u0⌋ U − ⌊v0⌋ V` is an integer point of the cell congruent to `w`. So a set `S` covers every
class modulo `ℤU + ℤV` as soon as the integer points of the cell lie in `S` (`cell_cover`). The ordinary propagation note uses this
reduction (its "pay each such lattice point z"). No parent covers are needed for this step. -/

namespace FLatticePaper.Tiles.SiteCell

open FLatticePaper.Farey FLatticePaper.Tiles.SiteInduction

/-- The integer point `z` lies in the half-open shifted cell `B0 + [0,1) U + [0,1) V`, `B0 = (1/2, −1/2)`. -/
def InCell (U V : ℤ × ℤ) (z : ℤ × ℤ) : Prop :=
  ∃ u v : ℚ, 0 ≤ u ∧ u < 1 ∧ 0 ≤ v ∧ v < 1 ∧
    (z.1 : ℚ) - 1 / 2 = u * (U.1 : ℚ) + v * (V.1 : ℚ) ∧
      (z.2 : ℚ) + 1 / 2 = u * (U.2 : ℚ) + v * (V.2 : ℚ)

/-- If `U, V` are independent, every class modulo `ℤU + ℤV` has a representative in the cell. -/
theorem exists_cell_rep (U V : ℤ × ℤ) (hD : U.1 * V.2 - U.2 * V.1 ≠ 0) (w : ℤ × ℤ) :
    ∃ z : ℤ × ℤ, InCell U V z ∧ ∃ k l : ℤ, w.1 - z.1 = k * U.1 + l * V.1 ∧ w.2 - z.2 = k * U.2 + l * V.2 := by
  have hDq : ((U.1 : ℚ) * V.2 - U.2 * V.1) ≠ 0 := by exact_mod_cast hD
  obtain ⟨u0, hu0⟩ : ∃ u0 : ℚ, u0 = (((w.1 : ℚ) - 1 / 2) * V.2 - ((w.2 : ℚ) + 1 / 2) * V.1) /
      ((U.1 : ℚ) * V.2 - U.2 * V.1) := ⟨_, rfl⟩
  obtain ⟨v0, hv0⟩ : ∃ v0 : ℚ, v0 = ((U.1 : ℚ) * ((w.2 : ℚ) + 1 / 2) - U.2 * ((w.1 : ℚ) - 1 / 2)) /
      ((U.1 : ℚ) * V.2 - U.2 * V.1) := ⟨_, rfl⟩
  have hp1 : (w.1 : ℚ) - 1 / 2 = u0 * (U.1 : ℚ) + v0 * (V.1 : ℚ) := by
    rw [hu0, hv0, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hDq]
    ring
  have hq1 : (w.2 : ℚ) + 1 / 2 = u0 * (U.2 : ℚ) + v0 * (V.2 : ℚ) := by
    rw [hu0, hv0, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hDq]
    ring
  refine ⟨(w.1 - ⌊u0⌋ * U.1 - ⌊v0⌋ * V.1, w.2 - ⌊u0⌋ * U.2 - ⌊v0⌋ * V.2), ?_, ⌊u0⌋, ⌊v0⌋, by ring, by ring⟩
  refine ⟨u0 - ⌊u0⌋, v0 - ⌊v0⌋, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sub_nonneg.mpr (Int.floor_le u0)
  · have := Int.fract_lt_one u0
    unfold Int.fract at this
    exact this
  · exact sub_nonneg.mpr (Int.floor_le v0)
  · have := Int.fract_lt_one v0
    unfold Int.fract at this
    exact this
  · push_cast
    linarith [hp1]
  · push_cast
    linarith [hq1]

/-- **Cell reduction.** A set containing every integer point of the half-open shifted cell covers every class modulo `ℤU + ℤV`. -/
theorem cell_cover (U V : ℤ × ℤ) (hD : U.1 * V.2 - U.2 * V.1 ≠ 0) (S : Set (ℤ × ℤ))
    (h : ∀ z : ℤ × ℤ, InCell U V z → z ∈ S) : QuotientCover S U V := by
  intro w
  obtain ⟨z, hz, k, l, h1, h2⟩ := exists_cell_rep U V hD w
  exact ⟨z, h z hz, k, l, h1, h2⟩

/-- The periods of a proper fraction are independent: `det(U_X, V_X) = μ T_X > 0`. -/
theorem det_perUV (X : Fraction) (h0 : 0 < X.num) (h1 : X.num < X.den) :
    (perU X).1 * (perV X).2 - (perU X).2 * (perV X).1 ≠ 0 := by
  have hT : 0 < X.den ^ 2 + 2 * X.den * X.num - X.num ^ 2 := by nlinarith
  have hmu : 0 < muOf X := by unfold muOf; split_ifs <;> norm_num
  have heq : (perU X).1 * (perV X).2 - (perU X).2 * (perV X).1 =
      muOf X * (X.den ^ 2 + 2 * X.den * X.num - X.num ^ 2) := by
    unfold perU perV; ring
  rw [heq]
  exact (mul_pos hmu hT).ne'

/-- **Propagation reduced to the cell.** For a proper fraction `X`, a set containing the integer points of the cell of `X` covers
the quotient deck of `X`. -/
theorem quotientCover_of_cell (X : Fraction) (h0 : 0 < X.num) (h1 : X.num < X.den) (S : Set (ℤ × ℤ))
    (h : ∀ z : ℤ × ℤ, InCell (perU X) (perV X) z → z ∈ S) : QuotientCover S (perU X) (perV X) :=
  cell_cover _ _ (det_perUV X h0 h1) S h

end FLatticePaper.Tiles.SiteCell
