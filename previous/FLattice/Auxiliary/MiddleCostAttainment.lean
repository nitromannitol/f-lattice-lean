import FLattice.Auxiliary.MiddleMatrix
import FLattice.Auxiliary.QuadraticCostAttainment

/-!
# Attainment for the smallest-coefficient transport cost

The literal matrix is C = [[6,2],[2,2]]. Its quadratic integer cost has
arbitrary signed integer linear coefficients, covering both smallest plus
and minus normalizations. The exact sampled-coordinate cost identity is
proved internally. This module proves attainment, not preservation of
superharmonicity or recurrence.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MiddleCostAttainment

open MiddleProfile

/-- The integer quadratic cost with arbitrary integer linear coefficients. -/
def cost (ℓ₁ ℓ₂ : ℤ) (p : ℤ × ℤ) : ℤ :=
  3 * p.1 ^ 2 + 2 * p.1 * p.2 + p.2 ^ 2 + ℓ₁ * p.1 + ℓ₂ * p.2

/-- The actual sampled point z₀-Cp for C = [[6,2],[2,2]]. -/
def samplePoint (x₀ y₀ : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (x₀ - 6 * p.1 - 2 * p.2, y₀ - 2 * p.1 - 2 * p.2)

/-- Original quadratic growth and positivity with the actual inverse matrix
give an attained integer minimum at every signed integer base point. -/
theorem exists_minimizer
    (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (x₀ y₀ ℓ₁ ℓ₂ : ℤ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + periodMatrix⁻¹).PosDef) :
    ∃ p : ℤ × ℤ, ∀ q : ℤ × ℤ,
      h (samplePoint x₀ y₀ p) + cost ℓ₁ ℓ₂ p ≤
        h (samplePoint x₀ y₀ q) + cost ℓ₁ ℓ₂ q := by
  let A : ℝ := ((x₀ : ℝ) - (y₀ : ℝ) + (ℓ₁ : ℝ) - (ℓ₂ : ℝ)) / 4
  let B : ℝ := ((y₀ : ℝ) + (ℓ₂ : ℝ)) / 2 - A
  let d : ℝ := ((x₀ : ℝ) - (y₀ : ℝ)) ^ 2 / 8 + (y₀ : ℝ) ^ 2 / 4 -
    A * (x₀ : ℝ) - B * (y₀ : ℝ)
  apply QuadraticCostAttainment.exists_minimizer_of_quadratic_cost
    h (samplePoint x₀ y₀) (cost ℓ₁ ℓ₂) M periodMatrix⁻¹ A B d hGrowth hPositive
  rintro ⟨p₁, p₂⟩
  rw [periodMatrix_inv]
  norm_num [cost, samplePoint, A, B, d]
  ring

end FLattice.Auxiliary.MiddleCostAttainment
