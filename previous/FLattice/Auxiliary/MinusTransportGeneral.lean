import FLattice.Auxiliary.MinusTransportData
import FLattice.Auxiliary.MinusExclusion

/-!
# The general minus infimum transport preserves integer superharmonicity

This module proves preservation for every integer `m ≥ 2`;
the separate smallest-minus coefficient remains outside its scope. The original quadratic
growth and strict domination by minus the actual inverse imply attainment.
A failed target star yields the native normalized function and the signed
coset bounds, which the proved local comparisons exclude. No comparison,
finite-contact, periodicity or minimum-attainment assumption remains in
the final existence theorem.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusTransport

open PlusTransport (squareCoefficient periodMatrix targetPoint targetPoint_zero)

private theorem normalized_exclusion
    (m : ℤ) (hm : 2 ≤ m) (ε : Fin 2) (h : ℤ × ℤ → ℤ)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + (ε.val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hOrigin : h (0, 0) = 0)
    (hPins : ∀ c : ℤ, c = -1 ∨ c = 0 ∨ c = 1 → ∀ p : ℤ × ℤ,
      c * τ + (if c = -1 then 1 else 0) - cost m p ≤
        h (TransportStarNormalization.displacedPoint (squareCoefficient m) (2 * m) 1
          (direction m ε).1 (direction m ε).2 c p)) : False := by
  let μ : PlusEvenProfile.Parameter := ⟨m, hm⟩
  apply MinusExclusion.not_normalized_failed_star_of_quadratic_growth
    μ ε h M τ hSuperharmonic hGrowth hPositive hOrigin
  intro c hc a b
  have hBound := hPins c hc (a, b)
  rw [cost_eq] at hBound
  convert hBound using 1
  · rfl
  · congr 1
    apply Prod.ext <;>
      simp only [TransportStarNormalization.displacedPoint, squareCoefficient, direction, μ] <;>
      split_ifs <;> ring

/-- Any function with the literal attained-minimum property is F-superharmonic.
The concrete existence theorem below supplies that property from growth. -/
theorem superharmonic_of_minimum_of_two_le
    (m : ℤ) (hm : 2 ≤ m) (g T : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then g (x - 1, y) + g (x + 1, y)
        else g (x, y - 1) + g (x, y + 1)) ≤ 2 * g (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hMinimum : ∀ w : ℤ × ℤ, ∃ p : ℤ × ℤ,
      T w = g (samplePoint m w p) + cost m p ∧
      ∀ q : ℤ × ℤ, T w ≤ g (samplePoint m w q) + cost m q) :
    ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then T (x - 1, y) + T (x + 1, y)
        else T (x, y - 1) + T (x, y + 1)) ≤ 2 * T (x, y) := by
  intro x y
  by_contra hFailed
  have hFailureNative : 2 * T (x, y) <
      (if (x + y) % 2 = 0 then T (x - 1, y) + T (x + 1, y)
        else T (x, y - 1) + T (x, y + 1)) := lt_of_not_ge hFailed
  let w : ℤ × ℤ := (x, y)
  let ε : Fin 2 := PlusEvenProfile.binaryState (x + y)
  have hε : (ε.val : ℤ) = (x + y) % 2 := PlusEvenProfile.binaryState_val (x + y)
  obtain ⟨p₀, hAttained, hMinimumBound⟩ := hMinimum w
  let z₀ := samplePoint m w p₀
  let h := NativeAffineNormalization.normalized g z₀.1 z₀.2 p₀.1 p₀.2
  let S : ℤ → ℤ := fun c => T (targetPoint w ε c)
  let τ : ℤ := S 1 - S 0 - (p₀.1 * (direction m ε).1 + p₀.2 * (direction m ε).2)
  have hParity : (z₀.1 + z₀.2) % 2 = (ε.val : ℤ) := by
    rw [samplePoint_parity]
    exact hε.symm
  have hSH := NativeAffineNormalization.normalized_superharmonic
    g z₀.1 z₀.2 p₀.1 p₀.2 ε hParity hSuperharmonic
  have hHGrowth := NativeAffineNormalization.normalized_quadratic_growth
    g M z₀.1 z₀.2 p₀.1 p₀.2 hGrowth
  have hOrigin := NativeAffineNormalization.normalized_origin g z₀.1 z₀.2 p₀.1 p₀.2
  have hFailure : 2 * S 0 < S (-1) + S 1 := by
    dsimp [S]
    rw [targetPoint_zero]
    by_cases hEven : (x + y) % 2 = 0
    · have hεZero : ε = 0 := by apply Fin.ext; omega
      simpa [targetPoint, w, hEven, hεZero, sub_eq_add_neg] using hFailureNative
    · have hεNonzero : ε ≠ 0 := by
        intro hZero
        rw [hZero] at hε
        norm_num at hε
        exact hEven hε.symm
      simpa [targetPoint, w, hEven, hεNonzero, sub_eq_add_neg] using hFailureNative
  have hBounds := TransportStarNormalization.signed_bounds_of_failed_star
    g (squareCoefficient m) (2 * m) 1 (-(m + 1)) (-1)
    (backwardPoint m w).1 (backwardPoint m w).2 (direction m ε).1 (direction m ε).2
    S p₀ (by
      intro c _ q
      obtain ⟨_, _, hBound⟩ := hMinimum (targetPoint w ε c)
      have hq := hBound q
      rw [samplePoint_at_target] at hq
      exact hq) (by simpa only [S, targetPoint_zero, samplePoint, cost] using hAttained) hFailure
  apply normalized_exclusion m hm ε h M τ hSH hHGrowth hPositive hOrigin
  intro c hc p
  exact hBounds c hc p

/-- The general-minus transport is an attained integer minimum and is F-superharmonic,
for every `m ≥ 2`, from the original source assumptions alone. -/
theorem exists_superharmonic_minimum_of_two_le
    (m : ℤ) (hm : 2 ≤ m) (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then g (x - 1, y) + g (x + 1, y)
        else g (x, y - 1) + g (x, y + 1)) ≤ 2 * g (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef) :
    ∃ T : ℤ × ℤ → ℤ,
      (∀ w : ℤ × ℤ, ∃ p : ℤ × ℤ,
        T w = g (samplePoint m w p) + cost m p ∧
        ∀ q : ℤ × ℤ, T w ≤ g (samplePoint m w q) + cost m q) ∧
      (∀ x y : ℤ,
        (if (x + y) % 2 = 0 then T (x - 1, y) + T (x + 1, y)
          else T (x, y - 1) + T (x, y + 1)) ≤ 2 * T (x, y)) := by
  choose p hp using exists_minimizer m (by omega) g M hGrowth hPositive
  let T : ℤ × ℤ → ℤ := fun w => g (samplePoint m w (p w)) + cost m (p w)
  have hMinimum : ∀ w : ℤ × ℤ, ∃ p : ℤ × ℤ,
      T w = g (samplePoint m w p) + cost m p ∧
      ∀ q : ℤ × ℤ, T w ≤ g (samplePoint m w q) + cost m q := by
    intro w
    exact ⟨p w, rfl, hp w⟩
  exact ⟨T, hMinimum, superharmonic_of_minimum_of_two_le m hm g T M hSuperharmonic hGrowth hPositive hMinimum⟩

end FLattice.Auxiliary.MinusTransport
