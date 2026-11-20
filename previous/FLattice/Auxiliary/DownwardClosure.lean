import FLattice.Auxiliary.HarmonicPeaks
import FLattice.Auxiliary.RoundedTangentApproximation

/-!
# Constructive downward closure and sufficiency below harmonic peaks

Subtracting the explicit integer midpoint-convex approximation preserves the
actual native SH inequality and subtracts its quadratic matrix. The final
peak theorem assumes only the literal positive-semidefinite matrix gap.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.DownwardClosure

open LatticeQuadraticRounding (quadratic)

/-- Subtracting a midpoint-convex integer function preserves native SH. -/
theorem superharmonic_sub_midpoint_convex (f V : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x+y)%2=0 then f (x-1,y)+f (x+1,y) else f (x,y-1)+f (x,y+1)) ≤ 2*f (x,y))
    (hConvex : ∀ x v : ℤ × ℤ, 2*V x ≤ V (x-v)+V (x+v)) :
    ∀ x y : ℤ,
      (if (x+y)%2=0 then (f (x-1,y)-V (x-1,y))+(f (x+1,y)-V (x+1,y))
        else (f (x,y-1)-V (x,y-1))+(f (x,y+1)-V (x,y+1))) ≤ 2*(f (x,y)-V (x,y)) := by
  intro x y
  have hSH := hSuperharmonic x y
  have hX := hConvex (x,y) (1,0)
  have hY := hConvex (x,y) (0,1)
  change 2*V (x,y) ≤ V (x-1,y-0)+V (x+1,y+0) at hX
  change 2*V (x,y) ≤ V (x-0,y-1)+V (x+0,y+1) at hY
  simp only [sub_zero,add_zero] at hX hY
  split_ifs at hSH ⊢ <;> omega

/-- Subtracting two original uniform quadratic asymptotics subtracts their matrices. -/
theorem quadratic_growth_sub (f V : ℤ × ℤ → ℤ) (N P : Matrix (Fin 2) (Fin 2) ℝ)
    (hf : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |(f (x,y):ℝ)-quadratic N (x:ℝ) (y:ℝ)| ≤ δ*((x:ℝ)^2+(y:ℝ)^2))
    (hV : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |(V (x,y):ℝ)-quadratic P (x:ℝ) (y:ℝ)| ≤ δ*((x:ℝ)^2+(y:ℝ)^2)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |((f (x,y)-V (x,y):ℤ):ℝ)-quadratic (N-P) (x:ℝ) (y:ℝ)| ≤
        δ*((x:ℝ)^2+(y:ℝ)^2) := by
  intro δ hδ
  obtain ⟨R,hR,hfR⟩ := hf (δ/2) (by positivity)
  obtain ⟨S,hS,hVS⟩ := hV (δ/2) (by positivity)
  refine ⟨R+S,by positivity,?_⟩
  intro x y hSize
  have hF := hfR x y (by nlinarith only [hSize,mul_pos hR hS,sq_nonneg S])
  have hG := hVS x y (by nlinarith only [hSize,mul_pos hR hS,sq_nonneg R])
  have hIdentity : ((f (x,y)-V (x,y):ℤ):ℝ)-quadratic (N-P) (x:ℝ) (y:ℝ) =
      ((f (x,y):ℝ)-quadratic N (x:ℝ) (y:ℝ))-
        ((V (x,y):ℝ)-quadratic P (x:ℝ) (y:ℝ)) := by
    simp only [Int.cast_sub,quadratic,Matrix.sub_apply]
    ring
  rw [hIdentity]
  calc
    _ ≤ |(f (x,y):ℝ)-quadratic N (x:ℝ) (y:ℝ)|+
        |(V (x,y):ℝ)-quadratic P (x:ℝ) (y:ℝ)| := abs_sub _ _
    _ ≤ (δ/2)*((x:ℝ)^2+(y:ℝ)^2)+(δ/2)*((x:ℝ)^2+(y:ℝ)^2) := add_le_add hF hG
    _ = δ*((x:ℝ)^2+(y:ℝ)^2) := by ring

/-- Actual native SH growth matrices are downward closed in PSD order.
The integer convex function and its growth are constructed internally. -/
theorem exists_superharmonic_with_growth_below
    (f : ℤ × ℤ → ℤ) (N M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x+y)%2=0 then f (x-1,y)+f (x+1,y) else f (x,y-1)+f (x,y+1)) ≤ 2*f (x,y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |(f (x,y):ℝ)-(1/2:ℝ)*((x:ℝ)*N 0 0*(x:ℝ)+(x:ℝ)*N 0 1*(y:ℝ)+
        (y:ℝ)*N 1 0*(x:ℝ)+(y:ℝ)*N 1 1*(y:ℝ))| ≤ δ*((x:ℝ)^2+(y:ℝ)^2))
    (hPSD : (N-M).PosSemidef) :
    ∃ g : ℤ × ℤ → ℤ,
      (∀ x y : ℤ,
        (if (x+y)%2=0 then g (x-1,y)+g (x+1,y) else g (x,y-1)+g (x,y+1)) ≤ 2*g (x,y)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
        R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
        |(g (x,y):ℝ)-(1/2:ℝ)*((x:ℝ)*M 0 0*(x:ℝ)+(x:ℝ)*M 0 1*(y:ℝ)+
          (y:ℝ)*M 1 0*(x:ℝ)+(y:ℝ)*M 1 1*(y:ℝ))| ≤ δ*((x:ℝ)^2+(y:ℝ)^2)) := by
  let V := RoundedTangentApproximation.approximation (N-M)
  have hConvex := RoundedTangentApproximation.midpoint_convex (N-M) hPSD
  have hVGrowth := RoundedTangentApproximation.approximation_quadratic_growth (N-M) hPSD
  refine ⟨fun z => f z-V z,superharmonic_sub_midpoint_convex f V hSuperharmonic hConvex,?_⟩
  have h := quadratic_growth_sub f V N (N-M) hGrowth hVGrowth
  simpa only [sub_sub_cancel,quadratic] using h

/-- Constructive sufficiency below every literal harmonic peak, from the PSD
matrix gap alone. The witness is integer valued and satisfies the original
native inequality and original uniform growth; there are no auxiliary
convexity, attainment, periodicity, or asymptotic hypotheses. -/
theorem exists_superharmonic_with_growth_below_peak
    (M : Matrix (Fin 2) (Fin 2) ℝ) (s t : ℤ)
    (hPSD : (HarmonicPeaks.peakMatrix s t-M).PosSemidef) :
    ∃ g : ℤ × ℤ → ℤ,
      (∀ x y : ℤ,
        (if (x+y)%2=0 then g (x-1,y)+g (x+1,y) else g (x,y-1)+g (x,y+1)) ≤ 2*g (x,y)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
        R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
        |(g (x,y):ℝ)-(1/2:ℝ)*((x:ℝ)*M 0 0*(x:ℝ)+(x:ℝ)*M 0 1*(y:ℝ)+
          (y:ℝ)*M 1 0*(x:ℝ)+(y:ℝ)*M 1 1*(y:ℝ))| ≤ δ*((x:ℝ)^2+(y:ℝ)^2)) := by
  apply exists_superharmonic_with_growth_below (HarmonicPeaks.peakHarmonic s t)
    (HarmonicPeaks.peakMatrix s t) M
  · intro x y
    exact le_of_eq (HarmonicPeaks.peakHarmonic_native s t x y)
  · exact HarmonicPeaks.peakHarmonic_quadratic_growth s t
  · exact hPSD

end FLattice.Auxiliary.DownwardClosure
