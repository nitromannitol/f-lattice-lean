import FLattice.Auxiliary.QuadraticGap

/-!
# Quadratic growth under translation and affine subtraction

Normalization of a failed transport star translates the integer argument
and subtracts an affine function. The uniform epsilon definition of growth
is preserved, with the same quadratic matrix. This analytic statement needs
no graph, integrality of the values, or symmetry assumption on the matrix.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.QuadraticGrowthTranslation

private theorem affine_abs_bound (δ A B C x y : ℝ) (hδ : 0 < δ) :
    |A * x + B * y + C| ≤
      (δ / 8) * (x ^ 2 + y ^ 2) + 2 * (A ^ 2 + B ^ 2) / δ + |C| := by
  have hPlus := QuadraticGap.linear_lower_bound δ A B x y hδ
  have hMinus := QuadraticGap.linear_lower_bound δ (-A) (-B) x y hδ
  simp only [neg_sq, neg_neg] at hMinus
  have hAbs := abs_le.mp (le_refl |C|)
  apply abs_le.mpr
  constructor <;> nlinarith

private theorem radius_implies_large (T N : ℝ) (hT : 0 ≤ T)
    (hSize : (T + 1) ^ 2 ≤ N) : T ≤ N := by
  nlinarith only [hT, hSize, sq_nonneg T]

private theorem translated_size_bounds (R a b x y tail : ℝ) (hTail : 0 ≤ tail)
    (hLarge : 2 * R ^ 2 + 2 * (a ^ 2 + b ^ 2) + tail ≤ x ^ 2 + y ^ 2) :
    R ^ 2 ≤ (x + a) ^ 2 + (y + b) ^ 2 ∧
      (x + a) ^ 2 + (y + b) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2) ∧
      tail ≤ x ^ 2 + y ^ 2 := by
  constructor
  · nlinarith only [hTail, hLarge, sq_nonneg (x + 2 * a), sq_nonneg (y + 2 * b)]
  constructor
  · nlinarith only [hTail, hLarge, sq_nonneg R, sq_nonneg a, sq_nonneg b,
      sq_nonneg (x - a), sq_nonneg (y - b)]
  · nlinarith only [hLarge, sq_nonneg R, sq_nonneg a, sq_nonneg b]

private theorem small_constant_bound (δ K N : ℝ) (hδ : 0 < δ)
    (hTail : 8 * K / δ ≤ N) : K ≤ (δ / 8) * N := by
  have hMultiply := mul_le_mul_of_nonneg_left hTail (le_of_lt hδ)
  have hCancel : δ * (8 * K / δ) = 8 * K := by field_simp
  rw [hCancel] at hMultiply
  linarith only [hMultiply]

private theorem total_error_bound (δ N K S r a : ℝ)
    (hδ : 0 < δ) (hN : 0 ≤ N) (hSize : S ≤ 4 * N)
    (hResidual : |r| ≤ (δ / 8) * S)
    (hAffine : |a| ≤ (δ / 8) * N + K)
    (hK : K ≤ (δ / 8) * N) : |r + a| ≤ δ * N := by
  have hScale := mul_le_mul_of_nonneg_left hSize (by positivity : 0 ≤ δ / 8)
  calc
    |r + a| ≤ |r| + |a| := abs_add_le r a
    _ ≤ (δ / 8) * S + ((δ / 8) * N + K) := add_le_add hResidual hAffine
    _ ≤ (δ / 8) * (4 * N) + ((δ / 8) * N + (δ / 8) * N) :=
      add_le_add hScale (add_le_add (le_refl _) hK)
    _ = (3 / 4) * (δ * N) := by ring
    _ ≤ δ * N := by nlinarith only [mul_nonneg (le_of_lt hδ) hN]

/-- Translating the argument by any fixed integer vector and subtracting
any real affine function preserves the literal uniform quadratic growth. -/
theorem translate_sub_affine
    (f : ℤ × ℤ → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (a b : ℤ) (α β γ : ℝ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |f (x, y) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |f (x + a, y + b) - α * (x : ℝ) - β * (y : ℝ) - γ - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  intro δ hδ
  obtain ⟨R₀, _, hApprox⟩ := hGrowth (δ / 8) (by positivity)
  let A : ℝ := (a : ℝ) * M 0 0 + (b : ℝ) * (M 0 1 + M 1 0) / 2 - α
  let B : ℝ := (b : ℝ) * M 1 1 + (a : ℝ) * (M 0 1 + M 1 0) / 2 - β
  let C : ℝ := (1 / 2 : ℝ) *
    ((a : ℝ) * M 0 0 * (a : ℝ) + (a : ℝ) * M 0 1 * (b : ℝ) +
      (b : ℝ) * M 1 0 * (a : ℝ) + (b : ℝ) * M 1 1 * (b : ℝ)) - γ
  let K : ℝ := 2 * (A ^ 2 + B ^ 2) / δ + |C|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let T : ℝ := 2 * R₀ ^ 2 + 2 * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) + 8 * K / δ
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨T + 1, by positivity, ?_⟩
  intro x y hSize
  have hLarge : T ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 :=
    radius_implies_large T _ hT hSize
  have hTailNonnegative : 0 ≤ 8 * K / δ := by positivity
  obtain ⟨hTranslationSize, hTranslationUpper, hTail⟩ :=
    translated_size_bounds R₀ (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ)
      (8 * K / δ) hTailNonnegative hLarge
  have hSmallK : K ≤ (δ / 8) * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) :=
    small_constant_bound δ K _ hδ hTail
  have hTranslationSizeInt : R₀ ^ 2 ≤
      ((x + a : ℤ) : ℝ) ^ 2 + ((y + b : ℤ) : ℝ) ^ 2 := by
    simpa only [Int.cast_add] using hTranslationSize
  have hApproxShift := hApprox (x + a) (y + b) hTranslationSizeInt
  have hAffine := affine_abs_bound δ A B C (x : ℝ) (y : ℝ) hδ
  have hAffineBound : |A * (x : ℝ) + B * (y : ℝ) + C| ≤
      (δ / 8) * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) + K := by
    simpa only [K, add_assoc] using hAffine
  have hIdentity :
      f (x + a, y + b) - α * (x : ℝ) - β * (y : ℝ) - γ - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ)) =
        (f (x + a, y + b) - (1 / 2 : ℝ) *
          (((x + a : ℤ) : ℝ) * M 0 0 * ((x + a : ℤ) : ℝ) +
            ((x + a : ℤ) : ℝ) * M 0 1 * ((y + b : ℤ) : ℝ) +
            ((y + b : ℤ) : ℝ) * M 1 0 * ((x + a : ℤ) : ℝ) +
            ((y + b : ℤ) : ℝ) * M 1 1 * ((y + b : ℤ) : ℝ))) +
          (A * (x : ℝ) + B * (y : ℝ) + C) := by
    dsimp [A, B, C]
    push_cast
    ring
  rw [hIdentity]
  apply total_error_bound δ _ K _ _ _ hδ (by positivity) _ hApproxShift hAffineBound hSmallK
  simpa only [Int.cast_add] using hTranslationUpper

end FLattice.Auxiliary.QuadraticGrowthTranslation
