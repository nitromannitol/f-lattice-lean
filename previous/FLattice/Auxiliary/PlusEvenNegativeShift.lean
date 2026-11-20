import FLattice.Auxiliary.PlusEvenMatrix
import FLattice.Auxiliary.PlusEvenComparison
import FLattice.Auxiliary.QuadraticGap

/-!
# Translating the strengthened comparison to the negative prescribed coset

The unknown function is translated by (4m,2), an even-parity vector. Its
finite comparison gap is derived from the original quadratic-growth data
using the translated reference polynomial, with every affine term retained.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- The reference polynomial at the negative comparison shift, with its exact affine part. -/
theorem quadraticBackground_negative_shift (m : Parameter) (x y : ℤ) :
    quadraticBackground m (x - 4 * m.val) (y - 2) =
      -(1 / 2 : ℝ) *
        ((x : ℝ) * ((periodMatrix m)⁻¹ 0 0) * (x : ℝ) +
          (x : ℝ) * ((periodMatrix m)⁻¹ 0 1) * (y : ℝ) +
          (y : ℝ) * ((periodMatrix m)⁻¹ 1 0) * (x : ℝ) +
          (y : ℝ) * ((periodMatrix m)⁻¹ 1 1) * (y : ℝ)) +
        ((m.val : ℝ) / (halfPeriod m : ℝ)) * (x : ℝ) +
        ((1 / 2 : ℝ) - (m.val : ℝ) ^ 2 / (halfPeriod m : ℝ)) * (y : ℝ) +
        ((3 / 4 : ℝ) - 3 * (m.val : ℝ) ^ 2 / (4 * (halfPeriod m : ℝ))) := by
  have hJ : (halfPeriod m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (halfPeriod_pos m)
  rw [periodMatrix_inv]
  norm_num [quadraticBackground]
  field_simp
  unfold halfPeriod
  push_cast
  ring

/-- The translated reference still has finite gap sublevels under the original growth hypothesis. -/
theorem finite_negative_gap_sublevels_of_quadratic_growth
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          ε * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef) :
    ∀ b : ℤ, {z : ℤ × ℤ | h z - profile m (z.1 - 4 * m.val) (z.2 - 2) ≤ b}.Finite := by
  obtain ⟨B, _, hBound⟩ := exists_bound_profile_sub_quadraticBackground m
  intro b
  have hFinite := QuadraticGap.finite_sublevels
    (fun z : ℤ × ℤ => (h z : ℝ))
    (fun z : ℤ × ℤ => (profile m (z.1 - 4 * m.val) (z.2 - 2) : ℝ))
    M ((periodMatrix m)⁻¹)
    ((m.val : ℝ) / (halfPeriod m : ℝ))
    ((1 / 2 : ℝ) - (m.val : ℝ) ^ 2 / (halfPeriod m : ℝ))
    ((3 / 4 : ℝ) - 3 * (m.val : ℝ) ^ 2 / (4 * (halfPeriod m : ℝ))) B
    hGrowth (fun x y => by
      simpa only [quadraticBackground_negative_shift] using
        hBound (x - 4 * m.val) (y - 2)) hPositive (b : ℝ)
  apply hFinite.subset
  intro z hz
  change (h z : ℝ) - (profile m (z.1 - 4 * m.val) (z.2 - 2) : ℝ) ≤ (b : ℝ)
  exact_mod_cast hz

/-- The strengthened positive comparison applies at the shifted negative coset.
All bounds concern the original nonperiodic unknown on the full lattice. -/
theorem negative_shift_comparison_of_quadratic_growth
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
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
        h (2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          1 - 2 * m.val * a - 2 * b)) :
    (∀ x y : ℤ, ¬cellPrescribed (cellOf m (x - 4 * m.val) (y - 2)) →
      profile m (x - 4 * m.val) (y - 2) + 1 ≤ h (x, y)) ∧
    (∀ x y : ℤ, regionI (cellOf m (x - 4 * m.val) (y - 2)) →
      profile m (x - 4 * m.val) (y - 2) + 2 ≤ h (x, y)) := by
  let f : ℤ × ℤ → ℤ := fun z => h (z.1 + 4 * m.val, z.2 + 2)
  have hfSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then f (x - 1, y) + f (x + 1, y)
        else f (x, y - 1) + f (x, y + 1)) ≤ 2 * f (x, y) := by
    intro x y
    have hSH := hSuperharmonic (x + 4 * m.val) (y + 2)
    have hParity : (x + 4 * m.val + (y + 2)) % 2 = (x + y) % 2 := by omega
    rw [hParity] at hSH
    dsimp [f]
    simpa only [show x - 1 + 4 * m.val = x + 4 * m.val - 1 by omega,
      show x + 1 + 4 * m.val = x + 4 * m.val + 1 by omega,
      show y - 1 + 2 = y + 2 - 1 by omega,
      show y + 1 + 2 = y + 2 + 1 by omega] using hSH
  have hfPins : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
        f (-2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -1 - 2 * m.val * a - 2 * b) := by
    intro a b
    dsimp [f]
    convert hPrescribed a b using 1
    congr 2 <;> ring
  have hOriginalFinite := finite_negative_gap_sublevels_of_quadratic_growth m h M hGrowth hPositive
  have hfFinite : ∀ b : ℤ, {z : ℤ × ℤ | f z - profile m z.1 z.2 ≤ b}.Finite := by
    intro b
    apply ((hOriginalFinite b).image (fun w : ℤ × ℤ => (w.1 - 4 * m.val, w.2 - 2))).subset
    intro z hz
    refine ⟨(z.1 + 4 * m.val, z.2 + 2), ?_, ?_⟩
    · simpa only [Set.mem_setOf_eq, add_sub_cancel_right] using hz
    · ext <;> dsimp <;> omega
  obtain ⟨hOne, hTwo⟩ := profile_comparison_of_finite_sublevels m f hfSuperharmonic hfPins hfFinite
  constructor
  · intro x y hOutside
    have h := hOne (x - 4 * m.val, y - 2) hOutside
    simpa only [f, sub_add_cancel, Prod.fst, Prod.snd] using h
  · intro x y hI
    have h := hTwo (x - 4 * m.val, y - 2) hI
    simpa only [f, sub_add_cancel, Prod.fst, Prod.snd] using h

end FLattice.Auxiliary.PlusEvenProfile
