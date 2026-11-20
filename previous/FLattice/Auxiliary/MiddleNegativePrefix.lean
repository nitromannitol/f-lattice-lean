import FLattice.Auxiliary.MiddleProfile

/-!
# The finite prefixes in the two negative smallest-coefficient cases

Both displaced pin families are used in three integer averages near the
origin. A few more actual native-star inequalities then force contact at
the start of the repeating white path. No finiteness or periodicity of h
is assumed here; those enter only in the subsequent path exclusion.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MiddleProfile

/-- The two signed pin families and the shifted even lower profile force
contact at `(0,2)`, the start of the repeating negative even path. -/
theorem negative_even_cycle_contact
    (h : ℤ × ℤ → ℤ) (τ : ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hOrigin : h (0, 0) = 0)
    (hPositivePins : ∀ a b : ℤ,
      τ - (3 * a ^ 2 + 2 * a * b + b ^ 2 + a) ≤ h (-2 - 6 * a - 2 * b, -1 - 2 * a - 2 * b))
    (hNegativePins : ∀ a b : ℤ,
      1 - τ - (3 * a ^ 2 + 2 * a * b + b ^ 2 + a) ≤ h (2 - 6 * a - 2 * b, 1 - 2 * a - 2 * b))
    (hLower : ∀ z : ℤ × ℤ, profile 0 (z.1 - 4) (z.2 - 2) ≤ h z) :
    h (0, 2) = -2 := by
  have hp₀ := hPositivePins 0 0
  have hn₀ := hNegativePins 0 1
  have hp₁ := hPositivePins 0 (-1)
  have hn₁ := hNegativePins 1 (-1)
  norm_num at hp₀ hn₀ hp₁ hn₁
  have hBelow := hSuperharmonic (-1) (-1)
  have hAbove := hSuperharmonic (-1) 1
  have hMiddle := hSuperharmonic (-1) 0
  norm_num at hBelow hAbove hMiddle
  have hLeft : 0 ≤ h (-1, 0) := by omega
  have hAt₁ := hLower (1, 0)
  have hAt₂ := hLower (1, 1)
  have hAt₃ := hLower (0, 1)
  have hAt₄ := hLower (0, 2)
  have hOther₁ := hLower (1, -1)
  have hOther₂ := hLower (2, 1)
  change 0 ≤ h (1, 0) at hAt₁
  change 0 ≤ h (1, 1) at hAt₂
  change -1 ≤ h (0, 1) at hAt₃
  change -2 ≤ h (0, 2) at hAt₄
  change 0 ≤ h (1, -1) at hOther₁
  change 1 ≤ h (2, 1) at hOther₂
  have hs₀ := hSuperharmonic 0 0
  have hs₁ := hSuperharmonic 1 0
  have hs₂ := hSuperharmonic 1 1
  have hs₃ := hSuperharmonic 0 1
  norm_num at hs₀ hs₁ hs₂ hs₃
  omega

/-- The two signed pin families and the shifted odd lower profile force
contact at `(1,-1)`, the start of the repeating negative odd path. -/
theorem negative_odd_cycle_contact
    (h : ℤ × ℤ → ℤ) (τ : ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hOrigin : h (0, 0) = 0)
    (hPositivePins : ∀ a b : ℤ,
      τ - (3 * a ^ 2 + 2 * a * b + b ^ 2 + a) ≤ h (-1 - 6 * a - 2 * b, -2 * a - 2 * b))
    (hNegativePins : ∀ a b : ℤ,
      1 - τ - (3 * a ^ 2 + 2 * a * b + b ^ 2 + a) ≤ h (1 - 6 * a - 2 * b, -2 * a - 2 * b))
    (hLower : ∀ z : ℤ × ℤ, profile 1 (z.1 - 2) z.2 ≤ h z) :
    h (1, -1) = 0 := by
  have hp₀ := hPositivePins 0 0
  have hn₀ := hNegativePins 1 (-2)
  have hp₁ := hPositivePins 0 (-1)
  have hn₁ := hNegativePins 0 0
  norm_num at hp₀ hn₀ hp₁ hn₁
  have hLeft := hSuperharmonic (-1) 1
  have hRight := hSuperharmonic 1 1
  have hMiddle := hSuperharmonic 0 1
  norm_num at hLeft hRight hMiddle
  have hUpper : 0 ≤ h (0, 1) := by omega
  have hAt₁ := hLower (0, -1)
  have hAt₂ := hLower (1, -1)
  have hOther := hLower (-1, -1)
  change 0 ≤ h (0, -1) at hAt₁
  change 0 ≤ h (1, -1) at hAt₂
  change 0 ≤ h (-1, -1) at hOther
  have hs₀ := hSuperharmonic 0 0
  have hs₁ := hSuperharmonic 0 (-1)
  norm_num at hs₀ hs₁
  omega

end FLattice.Auxiliary.MiddleProfile
