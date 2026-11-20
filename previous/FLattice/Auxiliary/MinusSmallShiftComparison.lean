import FLattice.Auxiliary.MinusSmallComparison
import FLattice.Auxiliary.QuadraticGrowthTranslation

/-!
# Original-coset shifts for the smallest minus branch

Both displaced-coset comparisons and the central-to-odd comparison are
derived from the unshifted source hypotheses. The unknown is never assumed
periodic, and its translated growth is proved rather than imposed.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusSmallProfile

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

/-- The two original signed cosets give the two exact global profile bounds. -/
theorem signed_shift_bounds
    (ε : Fin 2) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + (ε.val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + periodMatrix⁻¹).PosDef)
    (hPins : ∀ c : ℤ, c = -1 ∨ c = 1 → ∀ a b : ℤ,
      c * τ + (if c = -1 then 1 else 0) - cost a b ≤
        h (c * prescribedX ε - 6 * a - 2 * b,
          c * prescribedY ε - 2 * a - 2 * b)) :
    (∀ x y : ℤ, profile ε x y + τ - 1 ≤ h (x, y)) ∧
    (∀ x y : ℤ, profile ε (x + 2 * prescribedX ε) (y + 2 * prescribedY ε) - τ ≤ h (x, y)) := by
  have he := ε.isLt
  have hPlusSH := translateAdd_superharmonic h ε ε 0 0 (1 - τ) (by omega) hSuperharmonic
  have hMinusSH := translateAdd_superharmonic h ε ε
    (-2 * prescribedX ε) (-2 * prescribedY ε) τ (by omega) hSuperharmonic
  have hPlusPins : ∀ a b : ℤ, 1 - cost a b ≤
      translateAdd h 0 0 (1 - τ)
        (prescribedX ε - 6 * a - 2 * b, prescribedY ε - 2 * a - 2 * b) := by
    intro a b
    have hBound := hPins 1 (Or.inr rfl) a b
    norm_num only [one_mul, if_false, add_zero] at hBound
    dsimp [translateAdd]
    simp only [add_zero]
    omega
  have hMinusPins : ∀ a b : ℤ, 1 - cost a b ≤
      translateAdd h (-2 * prescribedX ε) (-2 * prescribedY ε) τ
        (prescribedX ε - 6 * a - 2 * b, prescribedY ε - 2 * a - 2 * b) := by
    intro a b
    have hBound := hPins (-1) (Or.inl rfl) a b
    simp only [neg_one_mul, if_true] at hBound
    dsimp [translateAdd]
    rw [show prescribedX ε - 6 * a - 2 * b + -2 * prescribedX ε =
        -prescribedX ε - 6 * a - 2 * b by ring,
      show prescribedY ε - 2 * a - 2 * b + -2 * prescribedY ε =
        -prescribedY ε - 2 * a - 2 * b by ring]
    omega
  have hPlus := profile_le_of_quadratic_growth ε (translateAdd h 0 0 (1 - τ)) M
    hPlusSH (translateAdd_growth h M 0 0 (1 - τ) hGrowth) hPositive hPlusPins
  have hMinus := profile_le_of_quadratic_growth ε
    (translateAdd h (-2 * prescribedX ε) (-2 * prescribedY ε) τ) M
    hMinusSH (translateAdd_growth h M (-2 * prescribedX ε) (-2 * prescribedY ε) τ hGrowth)
    hPositive hMinusPins
  constructor
  · intro x y
    have hBound := hPlus (x, y)
    dsimp [translateAdd] at hBound
    simp only [add_zero] at hBound
    omega
  · intro x y
    have hBound := hMinus (x + 2 * prescribedX ε, y + 2 * prescribedY ε)
    dsimp [translateAdd] at hBound
    rw [show x + 2 * prescribedX ε + -2 * prescribedX ε = x by ring,
      show y + 2 * prescribedY ε + -2 * prescribedY ε = y by ring] at hBound
    omega

/-- The two exact profile root values restrict the surviving integer thresholds. -/
theorem threshold_cases_of_shift_bounds
    (ε : Fin 2) (h : ℤ × ℤ → ℤ) (τ : ℤ) (hOrigin : h (0, 0) = 0)
    (hPlus : ∀ x y : ℤ, profile ε x y + τ - 1 ≤ h (x, y))
    (hMinus : ∀ x y : ℤ,
      profile ε (x + 2 * prescribedX ε) (y + 2 * prescribedY ε) - τ ≤ h (x, y)) :
    if ε = 0 then τ = -2 ∨ τ = -1 ∨ τ = 0 else τ = 1 := by
  have hP := hPlus 0 0
  have hN := hMinus 0 0
  fin_cases ε
  · norm_num [prescribedX, prescribedY, even_origin, even_twice_prescribed,
      hOrigin, Fin.ext_iff] at hP hN ⊢
    omega
  · norm_num [prescribedX, prescribedY, odd_origin, odd_twice_prescribed,
      hOrigin, Fin.ext_iff] at hP hN ⊢
    omega

/-- The central coset of an even-native unknown supplies the shifted odd profile. -/
theorem even_central_coset_odd_lower_bound
    (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + periodMatrix⁻¹).PosDef)
    (hCentral : ∀ a b : ℤ, -cost a b ≤ h (-6 * a - 2 * b, -2 * a - 2 * b)) :
    ∀ x y : ℤ, profile 1 (x - 1) y - 1 ≤ h (x, y) := by
  have hSH : ∀ x y : ℤ,
      (if (x + y + ((0 : Fin 2).val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
    simpa using hSuperharmonic
  have hfSH := translateAdd_superharmonic h 0 1 1 0 1 (by norm_num) hSH
  have hfPins : ∀ a b : ℤ, 1 - cost a b ≤
      translateAdd h 1 0 1 (prescribedX 1 - 6 * a - 2 * b, prescribedY 1 - 2 * a - 2 * b) := by
    intro a b
    have hBound := hCentral a b
    norm_num [translateAdd, prescribedX, prescribedY, Fin.ext_iff] at hBound ⊢
    rw [show -1 - 6 * a - 2 * b + 1 = -6 * a - 2 * b by ring]
    ring_nf at hBound ⊢
    omega
  have hf := profile_le_of_quadratic_growth 1 (translateAdd h 1 0 1) M
    hfSH (translateAdd_growth h M 1 0 1 hGrowth) hPositive hfPins
  intro x y
  have hBound := hf (x - 1, y)
  dsimp [translateAdd] at hBound
  simp only [sub_add_cancel, add_zero] at hBound
  omega

end FLattice.Auxiliary.MinusSmallProfile
