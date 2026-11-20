import FLattice.Auxiliary.QuadraticSublevels
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Global envelopes for uniform subquadratic errors

On the integer plane a finite-ball bound turns the uniform eventual
epsilon estimate into a global quadratic estimate with an additive
constant. Conversely, every such constant is absorbed at a sufficiently
large radius. The error is arbitrary and real-valued.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.QuadraticErrorEnvelope

/-- An eventual epsilon-quadratic bound has a global additive-constant envelope. -/
theorem global_envelope_of_eventual_bound
    (E : ℤ × ℤ → ℝ)
    (hEventual : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |E (x, y)| ≤ δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℤ,
      |E (x, y)| ≤ δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) + C := by
  intro δ hδ
  obtain ⟨R, _, hBound⟩ := hEventual δ hδ
  have hFinite := finite_lattice_normSq_le (R ^ 2)
  have hNonempty : {z : ℤ × ℤ | (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 ≤ R ^ 2}.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp only [Set.mem_setOf_eq, Int.cast_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
    exact sq_nonneg R
  obtain ⟨z, _, hMax⟩ := Set.exists_max_image
    {z : ℤ × ℤ | (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 ≤ R ^ 2}
    (fun z => |E z|) hFinite hNonempty
  refine ⟨|E z|, abs_nonneg _, ?_⟩
  intro x y
  by_cases hInside : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 ≤ R ^ 2
  · have hLocal := hMax (x, y) hInside
    have hQuad : 0 ≤ δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by positivity
    linarith
  · have hOutside := hBound x y (le_of_lt (lt_of_not_ge hInside))
    exact hOutside.trans (le_add_of_nonneg_right (abs_nonneg _))

/-- Every global epsilon-quadratic envelope gives the literal uniform
eventual estimate, with no continuity or regularity premise on the error. -/
theorem eventual_bound_of_global_envelope
    (E : ℤ × ℤ → ℝ)
    (hGlobal : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℤ,
      |E (x, y)| ≤ δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) + C) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |E (x, y)| ≤ δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  intro δ hδ
  obtain ⟨C, hC, hBound⟩ := hGlobal (δ / 2) (by positivity)
  let K : ℝ := 2 * C / δ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 1, by positivity, ?_⟩
  intro x y hSize
  have hLarge : K ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by
    nlinarith only [hK, hSize, sq_nonneg K]
  have hMultiply := mul_le_mul_of_nonneg_left hLarge (le_of_lt hδ)
  have hCancel : δ * K = 2 * C := by dsimp [K]; field_simp
  rw [hCancel] at hMultiply
  have hError := hBound x y
  nlinarith only [hError, hMultiply]

end FLattice.Auxiliary.QuadraticErrorEnvelope
