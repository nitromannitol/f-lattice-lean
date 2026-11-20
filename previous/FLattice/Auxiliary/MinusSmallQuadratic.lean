import FLattice.Auxiliary.MinusSmallCoordinates
import FLattice.Auxiliary.MinusSmallMatrix
import FLattice.Auxiliary.QuadraticGap

/-!
# Uniform quadratic error and proper translated gaps for the smallest-minus profiles

The exact signed lift cancels against the background polynomial. The eight
representatives give an absolute error at most four for either parity.
Any fixed integer translation of either profile therefore has finite gap
sublevels under the original growth and actual matrix domination premises.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusSmallProfile

/-- The profile-minus-background residual is unchanged by every signed lift. -/
theorem profile_sub_quadraticBackground_at_lift
    (ε : Fin 2) (X : Fin 4) (e : Fin 2) (k q : ℤ) :
    (profile ε ((X.val : ℤ) + 2 * k + 4 * q) (2 * k + (e.val : ℤ)) : ℝ) -
        quadraticBackground ε ((X.val : ℤ) + 2 * k + 4 * q) (2 * k + (e.val : ℤ)) =
      (profile ε (X.val : ℤ) (e.val : ℤ) : ℝ) -
        quadraticBackground ε (X.val : ℤ) (e.val : ℤ) := by
  rw [profile_at_lifted_cell, profile_at_cell, quadraticBackground_at_lift]
  push_cast
  ring

/-- A uniform bound of four holds on the entire integer plane for both parities. -/
theorem abs_profile_sub_quadraticBackground_le_four (ε : Fin 2) (x y : ℤ) :
    |(profile ε x y : ℝ) - quadraticBackground ε x y| ≤ 4 := by
  obtain ⟨X, e, k, q, rfl, rfl⟩ := exists_lifted_cell x y
  rw [profile_sub_quadraticBackground_at_lift, profile_at_cell]
  fin_cases ε <;> fin_cases X <;> fin_cases e <;>
    norm_num [representativeHeight, periodConstant, quadraticBackground, Fin.ext_iff]

/-- Every translated comparison profile has finite integer gap sublevels
under the original uniform growth and strict matrix domination assumptions. -/
theorem finite_shifted_gap_sublevels_of_quadratic_growth
    (ε : Fin 2) (a b : ℤ) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + periodMatrix⁻¹).PosDef) :
    ∀ t : ℤ, {z : ℤ × ℤ | h z - profile ε (z.1 + a) (z.2 + b) ≤ t}.Finite := by
  intro t
  have hFinite := QuadraticGap.finite_sublevels
    (fun z : ℤ × ℤ => (h z : ℝ))
    (fun z : ℤ × ℤ => (profile ε (z.1 + a) (z.2 + b) : ℝ))
    M periodMatrix⁻¹ (((b : ℝ) - (a : ℝ) + (periodConstant ε : ℝ)) / 4)
    (((a : ℝ) - 3 * (b : ℝ) - (periodConstant ε : ℝ)) / 4 - (ε.val : ℝ) / 2)
    (-((a : ℝ) - (b : ℝ)) ^ 2 / 8 - (b : ℝ) ^ 2 / 4 +
      (periodConstant ε : ℝ) * ((a : ℝ) - (b : ℝ)) / 4 - (ε.val : ℝ) * (b : ℝ) / 2) 4
    hGrowth (fun x y => by
      simpa only [quadraticBackground_shift_eq_inverse] using
        abs_profile_sub_quadraticBackground_le_four ε (x + a) (y + b)) hPositive (t : ℝ)
  apply hFinite.subset
  intro z hz
  change (h z : ℝ) - (profile ε (z.1 + a) (z.2 + b) : ℝ) ≤ (t : ℝ)
  exact_mod_cast hz

end FLattice.Auxiliary.MinusSmallProfile
