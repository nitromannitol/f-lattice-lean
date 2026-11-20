import FLattice.Auxiliary.MiddleCoordinates
import FLattice.Auxiliary.MiddleMatrix
import FLattice.Auxiliary.QuadraticGap

/-!
# Uniform quadratic error and proper translated gaps for the middle profiles

The exact signed lift cancels against the background polynomial. The eight
representatives give an absolute error at most two for either parity.
Any fixed integer translation of either profile therefore has finite gap
sublevels under the original growth and actual matrix domination premises.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MiddleProfile

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

/-- A uniform bound of two holds on the entire integer plane for both parities. -/
theorem abs_profile_sub_quadraticBackground_le_two (ε : Fin 2) (x y : ℤ) :
    |(profile ε x y : ℝ) - quadraticBackground ε x y| ≤ 2 := by
  obtain ⟨X, e, k, q, rfl, rfl⟩ := exists_lifted_cell x y
  rw [profile_sub_quadraticBackground_at_lift, profile_at_cell]
  fin_cases ε <;> fin_cases X <;> fin_cases e <;>
    norm_num [representativeHeight, quadraticBackground, Fin.ext_iff]

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
    M periodMatrix⁻¹ (((b : ℝ) - (a : ℝ)) / 4)
    (((a : ℝ) - 3 * (b : ℝ)) / 4 - (1 - (ε.val : ℝ)) / 2)
    (-((a : ℝ) - (b : ℝ)) ^ 2 / 8 - (b : ℝ) ^ 2 / 4 -
      (1 - (ε.val : ℝ)) * (b : ℝ) / 2) 2
    hGrowth (fun x y => by
      simpa only [quadraticBackground_shift_eq_inverse] using
        abs_profile_sub_quadraticBackground_le_two ε (x + a) (y + b)) hPositive (t : ℝ)
  apply hFinite.subset
  intro z hz
  change (h z : ℝ) - (profile ε (z.1 + a) (z.2 + b) : ℝ) ≤ (t : ℝ)
  exact_mod_cast hz

end FLattice.Auxiliary.MiddleProfile
