import FLattice.Auxiliary.PlusOddComparison

/-!
# The odd negative prescribed coset and its finite comparison gap

Translation by `(2,0)` preserves the native odd graph. The finite gap for the
shifted reference is derived from the original quadratic-growth hypothesis,
retaining the exact affine part of the shifted reference polynomial. The
result is a lower comparison, not a root exclusion or recurrence assertion.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- The odd reference polynomial at the negative shift, including all affine terms. -/
theorem quadraticBackground_negative_shift (m : Parameter) (x y : ℤ) :
    quadraticBackground m (x - 2) y = -(1 / 2 : ℝ) *
      ((x : ℝ) * ((periodMatrix m)⁻¹ 0 0) * (x : ℝ) +
        (x : ℝ) * ((periodMatrix m)⁻¹ 0 1) * (y : ℝ) +
        (y : ℝ) * ((periodMatrix m)⁻¹ 1 0) * (x : ℝ) +
        (y : ℝ) * ((periodMatrix m)⁻¹ 1 1) * (y : ℝ)) +
      (((m.val : ℝ) + 1) / (2 * (halfPeriod m : ℝ))) * (x : ℝ) +
      (-(m.val : ℝ) * ((m.val : ℝ) + 1) / (2 * (halfPeriod m : ℝ))) * (y : ℝ) +
      (1 - (2 * (m.val : ℝ) + 1) / (4 * (halfPeriod m : ℝ))) := by
  have hJ : (halfPeriod m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (halfPeriod_pos m)
  rw [periodMatrix_inv]
  norm_num [quadraticBackground]
  field_simp
  unfold halfPeriod
  push_cast
  ring

/-- Every sublevel of the negative-shift gap is finite under the original
uniform growth and strict domination by the actual inverse matrix. -/
theorem finite_negative_gap_sublevels_of_quadratic_growth
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          ε * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef) :
    ∀ b : ℤ, {z : ℤ × ℤ | h z - profile m (z.1 - 2) z.2 ≤ b}.Finite := by
  obtain ⟨B, _, hBound⟩ := exists_bound_profile_sub_quadraticBackground m
  intro b
  have hFinite := QuadraticGap.finite_sublevels
    (fun z : ℤ × ℤ => (h z : ℝ))
    (fun z : ℤ × ℤ => (profile m (z.1 - 2) z.2 : ℝ))
    M ((periodMatrix m)⁻¹)
    (((m.val : ℝ) + 1) / (2 * (halfPeriod m : ℝ)))
    (-(m.val : ℝ) * ((m.val : ℝ) + 1) / (2 * (halfPeriod m : ℝ)))
    (1 - (2 * (m.val : ℝ) + 1) / (4 * (halfPeriod m : ℝ))) B
    hGrowth (fun x y => by
      simpa only [quadraticBackground_negative_shift] using hBound (x - 2) y)
    hPositive (b : ℝ)
  apply hFinite.subset
  intro z hz
  change (h z : ℝ) - (profile m (z.1 - 2) z.2 : ℝ) ≤ (b : ℝ)
  exact_mod_cast hz

private theorem bounded_gap_of_finite_nonpositive_sublevel
    (g : ℤ × ℤ → ℤ) (hFinite : {z | g z ≤ 0}.Finite) :
    ∃ B : ℤ, ∀ z, B ≤ g z := by
  by_cases hNonempty : {z | g z ≤ 0}.Nonempty
  · obtain ⟨z, hz, hMin⟩ := Set.exists_min_image {z | g z ≤ 0} g hFinite hNonempty
    refine ⟨g z, ?_⟩
    intro w
    by_cases hw : g w ≤ 0
    · exact hMin w hw
    · change g z ≤ 0 at hz
      omega
  · refine ⟨0, ?_⟩
    intro z
    have hz : ¬g z ≤ 0 := fun hz => hNonempty ⟨z, hz⟩
    omega

/-- The negative prescribed coset yields the globally shifted odd lower
comparison. The growth premise concerns the original unknown function only. -/
theorem negative_shift_comparison_of_quadratic_growth
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          ε * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hPrescribed : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
        h (1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -2 * m.val * a - 2 * b)) :
    ∀ x y : ℤ, profile m (x - 2) y ≤ h (x, y) := by
  let f : ℤ × ℤ → ℤ := fun z => h (z.1 + 2, z.2)
  have hfSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then f (x - 1, y) + f (x + 1, y)
        else f (x, y - 1) + f (x, y + 1)) ≤ 2 * f (x, y) := by
    intro x y
    have hSH := hSuperharmonic (x + 2) y
    have hParity : (x + 2 + y + 1) % 2 = (x + y + 1) % 2 := by omega
    rw [hParity] at hSH
    dsimp [f]
    simpa only [show x - 1 + 2 = x + 2 - 1 by omega,
      show x + 1 + 2 = x + 2 + 1 by omega] using hSH
  have hfPins : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
        f (-1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -2 * m.val * a - 2 * b) := by
    intro a b
    dsimp [f]
    convert hPrescribed a b using 1
    congr 2
    ring
  have hFinite := finite_negative_gap_sublevels_of_quadratic_growth m h M hGrowth hPositive 0
  obtain ⟨B, hB⟩ := bounded_gap_of_finite_nonpositive_sublevel
    (fun z : ℤ × ℤ => h z - profile m (z.1 - 2) z.2) hFinite
  have hfGap : ∃ B : ℤ, ∀ z : ℤ × ℤ, B ≤ f z - profile m z.1 z.2 := by
    refine ⟨B, ?_⟩
    rintro ⟨x, y⟩
    simpa only [f, Prod.fst, Prod.snd, add_sub_cancel_right] using hB (x + 2, y)
  have hfLower := profile_le_of_bounded_gap m f hfSuperharmonic hfPins hfGap
  intro x y
  have hLower := hfLower (x - 2, y)
  simpa only [f, Prod.fst, Prod.snd, sub_add_cancel] using hLower

end FLattice.Auxiliary.PlusOddProfile
