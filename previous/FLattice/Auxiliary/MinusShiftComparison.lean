import FLattice.Auxiliary.MinusEvenComparison
import FLattice.Auxiliary.MinusOddComparison
import FLattice.Auxiliary.QuadraticGrowthTranslation

/-!
# Signed-coset shifts for general-minus comparison

Translations and integer constants preserve the original quadratic growth.
The two normalized prescribed cosets therefore give two actual profile
lower bounds, with their original native parity. No translated-growth or
finite-gap hypothesis is assumed.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile

private def translateAdd (h : ℤ × ℤ → ℤ) (a b t : ℤ) (z : ℤ × ℤ) : ℤ :=
  h (z.1 + a, z.2 + b) + t

private theorem translateAdd_superharmonic
    (h : ℤ × ℤ → ℤ) (ε η : Fin 2) (a b t : ℤ)
    (hParity : (a + b + (ε.val : ℤ)) % 2 = (η.val : ℤ))
    (hSH : ∀ x y : ℤ,
      (if (x + y + (ε.val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y)) :
    ∀ x y : ℤ,
      (if (x + y + (η.val : ℤ)) % 2 = 0 then
          translateAdd h a b t (x - 1, y) + translateAdd h a b t (x + 1, y)
        else translateAdd h a b t (x, y - 1) + translateAdd h a b t (x, y + 1)) ≤
      2 * translateAdd h a b t (x, y) := by
  intro x y
  have hStar := hSH (x + a) (y + b)
  have hParity' : (x + a + (y + b) + (ε.val : ℤ)) % 2 =
      (x + y + (η.val : ℤ)) % 2 := by omega
  rw [hParity'] at hStar
  dsimp [translateAdd]
  rw [show x - 1 + a = x + a - 1 by omega,
    show x + 1 + a = x + a + 1 by omega,
    show y - 1 + b = y + b - 1 by omega,
    show y + 1 + b = y + b + 1 by omega]
  split_ifs at hStar ⊢ <;> omega

private theorem translateAdd_growth
    (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ) (a b t : ℤ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(translateAdd h a b t (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  have hResult := QuadraticGrowthTranslation.translate_sub_affine
    (fun z => (h z : ℝ)) M a b 0 0 (-(t : ℝ)) hGrowth
  simpa only [translateAdd, Int.cast_add, zero_mul, sub_zero, sub_neg_eq_add] using hResult

/-- Both signed cosets yield the exact two global even-minus profile bounds. -/
theorem even_signed_shift_bounds
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hPins : ∀ c : ℤ, c = -1 ∨ c = 1 → ∀ a b : ℤ,
      c * τ + (if c = -1 then 1 else 0) -
        (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        h (c * (2 * m.val + 2) - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          c - 2 * m.val * a - 2 * b)) :
    (∀ x y : ℤ, profile m 0 x y + τ - 1 ≤ h (x, y)) ∧
    (∀ x y : ℤ, profile m 0 (x + (4 * m.val + 4)) (y + 2) - τ ≤ h (x, y)) := by
  have hSH : ∀ x y : ℤ,
      (if (x + y + ((0 : Fin 2).val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
    simpa using hSuperharmonic
  have hPlusSH := translateAdd_superharmonic h 0 0 0 0 (1 - τ) (by norm_num) hSH
  have hMinusSH := translateAdd_superharmonic h 0 0 (-(4 * m.val + 4)) (-2) τ
    (by norm_num; omega) hSH
  have hPlusPins : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        translateAdd h 0 0 (1 - τ)
          (2 * m.val + 2 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
            1 - 2 * m.val * a - 2 * b) := by
    intro a b
    have hBound := hPins 1 (Or.inr rfl) a b
    norm_num only [one_mul, if_false, add_zero] at hBound
    dsimp [translateAdd]
    simp only [add_zero]
    omega
  have hMinusPins : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        translateAdd h (-(4 * m.val + 4)) (-2) τ
          (2 * m.val + 2 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
            1 - 2 * m.val * a - 2 * b) := by
    intro a b
    have hBound := hPins (-1) (Or.inl rfl) a b
    simp only [neg_one_mul, if_true] at hBound
    dsimp [translateAdd]
    rw [show 2 * m.val + 2 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b +
        -(4 * m.val + 4) = -(2 * m.val + 2) - (4 * m.val ^ 2 + 4 * m.val - 2) * a -
        2 * m.val * b by ring,
      show 1 - 2 * m.val * a - 2 * b + -2 = -1 - 2 * m.val * a - 2 * b by ring]
    omega
  have hPlus := even_profile_le_of_quadratic_growth m (translateAdd h 0 0 (1 - τ)) M
    (by simpa using hPlusSH) (translateAdd_growth h M 0 0 (1 - τ) hGrowth) hPositive hPlusPins
  have hMinus := even_profile_le_of_quadratic_growth m (translateAdd h (-(4 * m.val + 4)) (-2) τ) M
    (by simpa using hMinusSH) (translateAdd_growth h M (-(4 * m.val + 4)) (-2) τ hGrowth)
    hPositive hMinusPins
  constructor
  · intro x y
    have hBound := hPlus (x, y)
    dsimp [translateAdd] at hBound
    simp only [add_zero] at hBound
    omega
  · intro x y
    have hBound := hMinus (x + (4 * m.val + 4), y + 2)
    dsimp [translateAdd] at hBound
    simp only [add_neg_cancel_right] at hBound
    omega

/-- Normalization leaves only threshold zero in even native parity. -/
theorem even_threshold_eq_zero
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hPins : ∀ c : ℤ, c = -1 ∨ c = 1 → ∀ a b : ℤ,
      c * τ + (if c = -1 then 1 else 0) -
        (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        h (c * (2 * m.val + 2) - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          c - 2 * m.val * a - 2 * b))
    (hOrigin : h (0, 0) = 0) : τ = 0 := by
  obtain ⟨hPlus, hMinus⟩ := even_signed_shift_bounds m h M τ
    hSuperharmonic hGrowth hPositive hPins
  have hPlusZero := hPlus 0 0
  have hMinusZero := hMinus 0 0
  rw [profile_origin, hOrigin] at hPlusZero
  norm_num only [zero_add, profile_even_shifted_origin, hOrigin] at hMinusZero
  omega

/-- The two signed odd cosets give the unshifted and twice-shifted profile bounds. -/
theorem odd_signed_shift_bounds
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hPins : ∀ c : ℤ, c = -1 ∨ c = 1 → ∀ a b : ℤ,
      c * τ + (if c = -1 then 1 else 0) -
        (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        h (-c - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -2 * m.val * a - 2 * b)) :
    (∀ x y : ℤ, profile m 1 x y + τ - 1 ≤ h (x, y)) ∧
    (∀ x y : ℤ, profile m 1 (x - 2) y - τ ≤ h (x, y)) := by
  have hSH : ∀ x y : ℤ,
      (if (x + y + ((1 : Fin 2).val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
    simpa using hSuperharmonic
  have hPlusSH := translateAdd_superharmonic h 1 1 0 0 (1 - τ) (by norm_num) hSH
  have hMinusSH := translateAdd_superharmonic h 1 1 2 0 τ (by norm_num) hSH
  have hPlusPins : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        translateAdd h 0 0 (1 - τ)
          (-1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
            -2 * m.val * a - 2 * b) := by
    intro a b
    have hBound := hPins 1 (Or.inr rfl) a b
    norm_num only [one_mul, if_false, add_zero] at hBound
    dsimp [translateAdd]
    simp only [add_zero]
    omega
  have hMinusPins : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        translateAdd h 2 0 τ
          (-1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
            -2 * m.val * a - 2 * b) := by
    intro a b
    have hBound := hPins (-1) (Or.inl rfl) a b
    simp only [neg_one_mul, neg_neg, if_true] at hBound
    dsimp [translateAdd]
    simp only [add_zero]
    rw [show -1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b + 2 =
      1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b by ring]
    omega
  have hPlus := odd_profile_le_of_quadratic_growth m (translateAdd h 0 0 (1 - τ)) M
    (by simpa using hPlusSH) (translateAdd_growth h M 0 0 (1 - τ) hGrowth) hPositive hPlusPins
  have hMinus := odd_profile_le_of_quadratic_growth m (translateAdd h 2 0 τ) M
    (by simpa using hMinusSH) (translateAdd_growth h M 2 0 τ hGrowth) hPositive hMinusPins
  constructor
  · intro x y
    have hBound := hPlus (x, y)
    dsimp [translateAdd] at hBound
    simp only [add_zero] at hBound
    omega
  · intro x y
    have hBound := hMinus (x - 2, y)
    dsimp [translateAdd] at hBound
    simp only [sub_add_cancel, add_zero] at hBound
    omega

/-- Both root values equal one, so no integer odd threshold survives. -/
theorem odd_signed_cosets_exclude_zero_origin
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hPins : ∀ c : ℤ, c = -1 ∨ c = 1 → ∀ a b : ℤ,
      c * τ + (if c = -1 then 1 else 0) -
        (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        h (-c - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -2 * m.val * a - 2 * b))
    (hOrigin : h (0, 0) = 0) : False := by
  obtain ⟨hPlus, hMinus⟩ := odd_signed_shift_bounds m h M τ
    hSuperharmonic hGrowth hPositive hPins
  have hPlusZero := hPlus 0 0
  have hMinusZero := hMinus 0 0
  rw [profile_origin, hOrigin] at hPlusZero
  norm_num only [zero_sub, profile_odd_shifted_origin, hOrigin] at hMinusZero
  omega

/-- The central normalized coset, shifted by one horizontal edge, supplies
an odd comparison bound for an even-native unknown. -/
theorem even_central_coset_odd_lower_bound
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hCentral : ∀ a b : ℤ,
      -(halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        h (-(4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -2 * m.val * a - 2 * b)) :
    ∀ x y : ℤ, profile m 1 (x - 1) y - 1 ≤ h (x, y) := by
  have hSH : ∀ x y : ℤ,
      (if (x + y + ((0 : Fin 2).val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
    simpa using hSuperharmonic
  have hfSH := translateAdd_superharmonic h 0 1 1 0 1 (by norm_num) hSH
  have hfPins : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        translateAdd h 1 0 1
          (-1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
            -2 * m.val * a - 2 * b) := by
    intro a b
    have hBound := hCentral a b
    dsimp [translateAdd]
    simp only [add_zero]
    rw [show -1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b + 1 =
      -(4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b by ring]
    omega
  have hf := odd_profile_le_of_quadratic_growth m (translateAdd h 1 0 1) M
    (by simpa using hfSH) (translateAdd_growth h M 1 0 1 hGrowth) hPositive hfPins
  intro x y
  have hBound := hf (x - 1, y)
  dsimp [translateAdd] at hBound
  simp only [sub_add_cancel, add_zero] at hBound
  omega

end FLattice.Auxiliary.MinusProfile
