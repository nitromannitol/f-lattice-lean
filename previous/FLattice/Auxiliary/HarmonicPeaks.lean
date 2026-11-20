import FLattice.Auxiliary.ElementaryProfiles
import FLattice.Auxiliary.QuadraticSandwich

/-!
# The complete integer harmonic peak family

Every pair of signed integers gives the literal source harmonic function
(s-t)H+txy. Its exact native incoming sum and real parity remainder establish
the stated peak matrix and its original uniform quadratic growth.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.HarmonicPeaks

open LatticeQuadraticRounding (quadratic)

/-- The literal integer harmonic function attached to a peak. -/
def peakHarmonic (s t : ℤ) (z : ℤ × ℤ) : ℤ :=
  (s-t)*ElementaryProfiles.harmonic z+t*z.1*z.2

/-- The full source family of harmonic peak matrices. -/
noncomputable def peakMatrix (s t : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1/2 : ℝ) • !![(s:ℝ)-(t:ℝ),(s:ℝ)+(t:ℝ);(s:ℝ)+(t:ℝ),(t:ℝ)-(s:ℝ)]

/-- Every peak function is exactly harmonic for the actual native incoming pair. -/
theorem peakHarmonic_native (s t x y : ℤ) :
    (if (x+y)%2=0 then peakHarmonic s t (x-1,y)+peakHarmonic s t (x+1,y)
      else peakHarmonic s t (x,y-1)+peakHarmonic s t (x,y+1)) =
      2*peakHarmonic s t (x,y) := by
  have h := congrArg (fun a : ℤ => (s-t)*a) (ElementaryProfiles.harmonic_native x y)
  split_ifs at h ⊢ <;> dsimp [peakHarmonic] <;> nlinarith only [h]

/-- The peak quadratic is the indicated harmonic quadratic plus the bilinear term. -/
theorem peak_quadratic (s t : ℤ) (x y : ℝ) :
    quadratic (peakMatrix s t) x y =
      ((s:ℝ)-(t:ℝ))/4*(x^2+2*x*y-y^2)+(t:ℝ)*x*y := by
  norm_num [quadratic,peakMatrix,Matrix.smul_apply]
  ring

/-- Exact real identity, including the bounded parity correction. -/
theorem peakHarmonic_real (s t x y : ℤ) :
    (peakHarmonic s t (x,y) : ℝ) =
      quadratic (peakMatrix s t) (x:ℝ) (y:ℝ) -
        ((s:ℝ)-(t:ℝ))*(y:ℝ)/2 -
        ((s:ℝ)-(t:ℝ))*(ElementaryProfiles.parity x y:ℝ)/4 := by
  simp only [peakHarmonic,Int.cast_add,Int.cast_mul,Int.cast_sub]
  rw [ElementaryProfiles.harmonic_real,peak_quadratic]
  ring

/-- Uniform affine bounds work for every signed peak coefficient. -/
theorem peakHarmonic_affine_bounds (s t x y : ℤ) :
    quadratic (peakMatrix s t) (x:ℝ) (y:ℝ) -
        ((s:ℝ)-(t:ℝ))*(y:ℝ)/2 - |(s:ℝ)-(t:ℝ)|/4 ≤ (peakHarmonic s t (x,y):ℝ) ∧
    (peakHarmonic s t (x,y):ℝ) ≤ quadratic (peakMatrix s t) (x:ℝ) (y:ℝ) -
        ((s:ℝ)-(t:ℝ))*(y:ℝ)/2 + |(s:ℝ)-(t:ℝ)|/4 := by
  rw [peakHarmonic_real]
  rcases ElementaryProfiles.parity_cases x y with hp | hp
  · rw [hp]
    norm_num only [Int.cast_zero,mul_zero,zero_div,sub_zero]
    constructor <;> linarith only [abs_nonneg ((s:ℝ)-(t:ℝ))]
  · rw [hp]
    norm_num only [Int.cast_one,mul_one]
    constructor <;> linarith only [le_abs_self ((s:ℝ)-(t:ℝ)),neg_abs_le ((s:ℝ)-(t:ℝ))]

/-- The actual integer harmonic function has the original uniform peak growth. -/
theorem peakHarmonic_quadratic_growth (s t : ℤ) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |(peakHarmonic s t (x,y):ℝ)-quadratic (peakMatrix s t) (x:ℝ) (y:ℝ)| ≤
        δ*((x:ℝ)^2+(y:ℝ)^2) := by
  apply QuadraticSandwich.quadratic_growth_of_sandwich
    (fun z => (peakHarmonic s t z:ℝ)) (peakMatrix s t)
  intro δ hδ
  refine ⟨peakMatrix s t,peakMatrix s t,0,-((s:ℝ)-(t:ℝ))/2,-|(s:ℝ)-(t:ℝ)|/4,
    0,-((s:ℝ)-(t:ℝ))/2,|(s:ℝ)-(t:ℝ)|/4,?_,?_,?_,?_⟩
  · intro i j
    simpa only [sub_self,abs_zero] using le_of_lt hδ
  · intro i j
    simpa only [sub_self,abs_zero] using le_of_lt hδ
  · intro x y
    have h := (peakHarmonic_affine_bounds s t x y).1
    nlinarith only [h]
  · intro x y
    have h := (peakHarmonic_affine_bounds s t x y).2
    nlinarith only [h]

end FLattice.Auxiliary.HarmonicPeaks
