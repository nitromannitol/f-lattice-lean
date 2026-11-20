import FLattice.Auxiliary.DownwardClosure

/-!
# Adding and subtracting the literal harmonic peaks

These operations preserve actual native SH and shift the original uniform
quadratic growth by the corresponding signed harmonic peak matrix. No
order assumption on that matrix is made.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.HarmonicPeakActions

open HarmonicPeaks
open LatticeQuadraticRounding (quadratic)

/-- Negating both integer labels negates the actual harmonic function. -/
theorem peakHarmonic_neg_labels (s t : ℤ) (z : ℤ × ℤ) :
    peakHarmonic (-s) (-t) z = -peakHarmonic s t z := by
  dsimp [peakHarmonic]
  ring

/-- Negating both labels negates the literal peak matrix. -/
theorem peakMatrix_neg_labels (s t : ℤ) : peakMatrix (-s) (-t) = -peakMatrix s t := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [peakMatrix,Matrix.smul_apply] <;> ring

/-- Arbitrary signed peak addition preserves actual native SH. -/
theorem add_peak_superharmonic (g : ℤ × ℤ → ℤ) (s t : ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x+y)%2=0 then g (x-1,y)+g (x+1,y) else g (x,y-1)+g (x,y+1)) ≤ 2*g (x,y)) :
    ∀ x y : ℤ,
      (if (x+y)%2=0 then (g (x-1,y)+peakHarmonic s t (x-1,y))+
          (g (x+1,y)+peakHarmonic s t (x+1,y))
        else (g (x,y-1)+peakHarmonic s t (x,y-1))+
          (g (x,y+1)+peakHarmonic s t (x,y+1))) ≤
        2*(g (x,y)+peakHarmonic s t (x,y)) := by
  intro x y
  have hG := hSuperharmonic x y
  have hH := peakHarmonic_native s t x y
  split_ifs at hG hH ⊢ <;> omega

/-- Subtraction also preserves native SH without a matrix order hypothesis. -/
theorem sub_peak_superharmonic (g : ℤ × ℤ → ℤ) (s t : ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x+y)%2=0 then g (x-1,y)+g (x+1,y) else g (x,y-1)+g (x,y+1)) ≤ 2*g (x,y)) :
    ∀ x y : ℤ,
      (if (x+y)%2=0 then (g (x-1,y)-peakHarmonic s t (x-1,y))+
          (g (x+1,y)-peakHarmonic s t (x+1,y))
        else (g (x,y-1)-peakHarmonic s t (x,y-1))+
          (g (x,y+1)-peakHarmonic s t (x,y+1))) ≤
        2*(g (x,y)-peakHarmonic s t (x,y)) := by
  simpa only [peakHarmonic_neg_labels,←sub_eq_add_neg] using
    add_peak_superharmonic g (-s) (-t) hSuperharmonic

/-- Peak subtraction shifts the original uniform growth by the exact negative peak. -/
theorem sub_peak_quadratic_growth (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (s t : ℤ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |(g (x,y):ℝ)-(1/2:ℝ)*((x:ℝ)*M 0 0*(x:ℝ)+(x:ℝ)*M 0 1*(y:ℝ)+
        (y:ℝ)*M 1 0*(x:ℝ)+(y:ℝ)*M 1 1*(y:ℝ))| ≤ δ*((x:ℝ)^2+(y:ℝ)^2)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |((g (x,y)-peakHarmonic s t (x,y):ℤ):ℝ)-quadratic (M-peakMatrix s t) (x:ℝ) (y:ℝ)| ≤
        δ*((x:ℝ)^2+(y:ℝ)^2) :=
  DownwardClosure.quadratic_growth_sub g (peakHarmonic s t) M (peakMatrix s t)
    hGrowth (peakHarmonic_quadratic_growth s t)

/-- Peak addition shifts the original uniform growth by the exact positive peak. -/
theorem add_peak_quadratic_growth (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (s t : ℤ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |(g (x,y):ℝ)-(1/2:ℝ)*((x:ℝ)*M 0 0*(x:ℝ)+(x:ℝ)*M 0 1*(y:ℝ)+
        (y:ℝ)*M 1 0*(x:ℝ)+(y:ℝ)*M 1 1*(y:ℝ))| ≤ δ*((x:ℝ)^2+(y:ℝ)^2)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |((g (x,y)+peakHarmonic s t (x,y):ℤ):ℝ)-quadratic (M+peakMatrix s t) (x:ℝ) (y:ℝ)| ≤
        δ*((x:ℝ)^2+(y:ℝ)^2) := by
  simpa only [peakHarmonic_neg_labels,peakMatrix_neg_labels,sub_neg_eq_add] using
    sub_peak_quadratic_growth g M (-s) (-t) hGrowth

end FLattice.Auxiliary.HarmonicPeakActions
