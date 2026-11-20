import FLattice.Auxiliary.PlusEvenMatrix
import FLattice.Auxiliary.QuadraticCostAttainment

/-!
# Attained minima for the common m >= 2 period cost

The plus and minus transports have the same period matrix and quadratic
integer cost; their linear coefficients differ. An exact square expansion
in the sampled physical coordinates supplies the cost identity required
by the generic attainment theorem. No graph hypothesis is needed here.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PeriodCostAttainment

open PlusEvenProfile

/-- The integer quadratic period cost with arbitrary integer linear coefficients. -/
def cost (m : Parameter) (ℓ₁ ℓ₂ : ℤ) (p : ℤ × ℤ) : ℤ :=
  halfPeriod m * p.1 ^ 2 + (m.val * p.1 + p.2) ^ 2 + ℓ₁ * p.1 + ℓ₂ * p.2

/-- The literal physical point z₀-Cp sampled by the period infimum. -/
def samplePoint (m : Parameter) (x₀ y₀ : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (x₀ - (4 * m.val ^ 2 + 4 * m.val - 2) * p.1 - 2 * m.val * p.2,
    y₀ - 2 * m.val * p.1 - 2 * p.2)

/-- The period-cost objective attains its integer minimum under the source
growth and actual inverse-matrix positivity, for every physical base point. -/
theorem exists_minimizer
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (x₀ y₀ ℓ₁ ℓ₂ : ℤ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef) :
    ∃ p : ℤ × ℤ, ∀ q : ℤ × ℤ,
      h (samplePoint m x₀ y₀ p) + cost m ℓ₁ ℓ₂ p ≤
        h (samplePoint m x₀ y₀ q) + cost m ℓ₁ ℓ₂ q := by
  let A : ℝ := ((x₀ : ℝ) - (m.val : ℝ) * (y₀ : ℝ) +
    (ℓ₁ : ℝ) - (m.val : ℝ) * (ℓ₂ : ℝ)) / (2 * (halfPeriod m : ℝ))
  let B : ℝ := ((y₀ : ℝ) + (ℓ₂ : ℝ)) / 2 - (m.val : ℝ) * A
  let d : ℝ := ((x₀ : ℝ) - (m.val : ℝ) * (y₀ : ℝ)) ^ 2 / (4 * (halfPeriod m : ℝ)) +
    (y₀ : ℝ) ^ 2 / 4 - A * (x₀ : ℝ) - B * (y₀ : ℝ)
  apply QuadraticCostAttainment.exists_minimizer_of_quadratic_cost
    h (samplePoint m x₀ y₀) (cost m ℓ₁ ℓ₂) M ((periodMatrix m)⁻¹)
    A B d hGrowth hPositive
  rintro ⟨p₁, p₂⟩
  have hJ : (halfPeriod m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (halfPeriod_pos m)
  rw [periodMatrix_inv]
  norm_num [cost, samplePoint, A, B, d]
  field_simp
  unfold halfPeriod
  push_cast
  ring

end FLattice.Auxiliary.PeriodCostAttainment
