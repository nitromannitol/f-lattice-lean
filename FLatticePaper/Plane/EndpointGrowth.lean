import FLatticePaper.Endpoint
import FLatticePaper.Plane.QuadraticGrowth

namespace FLatticePaper

open Farey

private theorem floor_div_error (value den : ℤ) (hden : 0 < den) :
    |(value : ℝ) / (den : ℝ) - ((value / den : ℤ) : ℝ)| ≤ 1 := by
  have hpos : 0 < (den : ℝ) := by exact_mod_cast hden
  have hmod : 0 ≤ ((value % den : ℤ) : ℝ) := by
    exact_mod_cast Int.emod_nonneg value (ne_of_gt hden)
  have hmodLt : ((value % den : ℤ) : ℝ) < (den : ℝ) := by
    exact_mod_cast Int.emod_lt_of_pos value hden
  have hemod : ((value % den : ℤ) : ℝ) + (den : ℝ) * ((value / den : ℤ) : ℝ) =
      (value : ℝ) := by exact_mod_cast Int.emod_add_mul_ediv value den
  have heq : (value : ℝ) / (den : ℝ) - ((value / den : ℤ) : ℝ) =
      ((value % den : ℤ) : ℝ) / (den : ℝ) := by
    field_simp
    linarith
  rw [heq, abs_of_nonneg (div_nonneg hmod hpos.le)]
  exact (div_le_iff₀ hpos).mpr (by simpa only [one_mul] using hmodLt.le)

theorem zeroEndpoint_growth : HasQuadraticGrowth zeroEndpoint (Fraction.mk 0 1).matrix := by
  apply quadraticGrowth_of_bounded_linear_error 0 (-(1 / 2)) 1 (by norm_num)
  intro site
  rw [matrixQuadratic_eq_grade]
  have h := floor_div_error (site.2 * (site.2 + 1)) 2 (by decide)
  convert h using 1
  congr 1
  simp [zeroEndpoint, Fraction.transverseGrade, Fraction.periodDenominator]
  ring

theorem oneEndpoint_growth : HasQuadraticGrowth oneEndpoint (Fraction.mk 1 1).matrix := by
  apply quadraticGrowth_of_bounded_linear_error 0 0 1 (by norm_num)
  intro site
  rw [matrixQuadratic_eq_grade]
  have h := floor_div_error ((site.2 - site.1) ^ 2) 4 (by decide)
  convert h using 1
  congr 1
  simp [oneEndpoint, Fraction.transverseGrade, Fraction.periodDenominator]
  ring

/-- The two literal endpoint odometers of `lemma:checkerboard_recurrence`. -/
theorem checkerboard_endpoints :
    (Superharmonic zeroEndpoint ∧ Recurrent zeroEndpoint ∧
      HasQuadraticGrowth zeroEndpoint (Fraction.mk 0 1).matrix) ∧
    (Superharmonic oneEndpoint ∧ Recurrent oneEndpoint ∧
      HasQuadraticGrowth oneEndpoint (Fraction.mk 1 1).matrix) :=
  ⟨⟨zeroEndpoint_rank.superharmonic, zeroEndpoint_recurrent, zeroEndpoint_growth⟩,
    ⟨oneEndpoint_rank.superharmonic, oneEndpoint_recurrent, oneEndpoint_growth⟩⟩

end FLatticePaper
