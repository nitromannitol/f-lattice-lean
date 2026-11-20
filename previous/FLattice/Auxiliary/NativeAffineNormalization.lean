import FLattice.Auxiliary.QuadraticGrowthTranslation

/-!
# Native parity under integer affine normalization

Translating an F-superharmonic integer function to any lattice point changes
the native parity by the parity of that point. Subtracting the specified
integer affine function preserves superharmonicity and quadratic growth.
These statements impose no periodicity on the unknown function.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.NativeAffineNormalization

/-- Translate to `(a,b)`, subtract the integer linear part, and set the origin to zero. -/
def normalized (g : ℤ × ℤ → ℤ) (a b α β : ℤ) (z : ℤ × ℤ) : ℤ :=
  g (z.1 + a, z.2 + b) - α * z.1 - β * z.2 - g (a, b)

/-- The normalized function is exactly zero at the origin. -/
theorem normalized_origin (g : ℤ × ℤ → ℤ) (a b α β : ℤ) :
    normalized g a b α β (0, 0) = 0 := by
  simp only [normalized, zero_add, mul_zero, sub_zero, sub_self]

/-- Native superharmonicity after translating to a point of parity `ε`. -/
theorem normalized_superharmonic
    (g : ℤ × ℤ → ℤ) (a b α β : ℤ) (ε : Fin 2)
    (hParity : (a + b) % 2 = (ε.val : ℤ))
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then g (x - 1, y) + g (x + 1, y)
        else g (x, y - 1) + g (x, y + 1)) ≤ 2 * g (x, y)) :
    ∀ x y : ℤ,
      (if (x + y + (ε.val : ℤ)) % 2 = 0 then
          normalized g a b α β (x - 1, y) + normalized g a b α β (x + 1, y)
        else normalized g a b α β (x, y - 1) + normalized g a b α β (x, y + 1)) ≤
      2 * normalized g a b α β (x, y) := by
  intro x y
  have hNative : (x + a + (y + b)) % 2 = (x + y + (ε.val : ℤ)) % 2 := by omega
  have hStar := hSuperharmonic (x + a) (y + b)
  rw [hNative] at hStar
  by_cases hEven : (x + y + (ε.val : ℤ)) % 2 = 0
  · rw [if_pos hEven] at hStar ⊢
    simp only [normalized]
    rw [show x - 1 + a = x + a - 1 by ring, show x + 1 + a = x + a + 1 by ring]
    nlinarith only [hStar]
  · rw [if_neg hEven] at hStar ⊢
    simp only [normalized]
    rw [show y - 1 + b = y + b - 1 by ring, show y + 1 + b = y + b + 1 by ring]
    nlinarith only [hStar]

/-- The same literal quadratic matrix governs the normalized integer function. -/
theorem normalized_quadratic_growth
    (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ) (a b α β : ℤ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(normalized g a b α β (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  have h := QuadraticGrowthTranslation.translate_sub_affine
    (fun z => (g z : ℝ)) M a b (α : ℝ) (β : ℝ) (g (a, b) : ℝ) hGrowth
  simpa only [normalized, Int.cast_sub, Int.cast_mul] using h

end FLattice.Auxiliary.NativeAffineNormalization
