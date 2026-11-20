import FLattice.Auxiliary.HarmonicPeakActions
import FLattice.Auxiliary.ElementaryReflections
import FLattice.Auxiliary.ConeClassificationGeometry
import FLattice.Auxiliary.RealReferenceExclusion
import FLattice.Auxiliary.ReferenceEdge

/-!
# Literal function-level closure for all-real necessity

The coordinate predicate below means existence of an actual integer native
superharmonic function with the original uniform quadratic growth. Its
translation and reflection closures are proved using the concrete functions.
The proved real-reference exclusion and edge parametrization discharge the
geometry hypotheses, yielding necessity for every real symmetric matrix.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.RealNecessity

open MatrixCoordinates

/-- Actual integer SH and original uniform growth, expressed in scalar matrix coordinates. -/
def admissibleCoordinates (a b c : ℝ) : Prop :=
  ∃ g : ℤ × ℤ → ℤ,
    (∀ x y : ℤ,
      (if (x+y)%2=0 then g (x-1,y)+g (x+1,y) else g (x,y-1)+g (x,y+1)) ≤ 2*g (x,y)) ∧
    (∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |(g (x,y):ℝ)-(1/2:ℝ)*((x:ℝ)*matrix a b c 0 0*(x:ℝ)+(x:ℝ)*matrix a b c 0 1*(y:ℝ)+
        (y:ℝ)*matrix a b c 1 0*(x:ℝ)+(y:ℝ)*matrix a b c 1 1*(y:ℝ))| ≤ δ*((x:ℝ)^2+(y:ℝ)^2))

/-- The constructed harmonic peak matrix is exactly the source coordinate peak. -/
theorem peak_matrix_coordinates (s t : ℤ) :
    HarmonicPeaks.peakMatrix s t = matrix ((s:ℝ)-(t:ℝ)) ((s:ℝ)+(t:ℝ)) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [HarmonicPeaks.peakMatrix,matrix,Matrix.smul_apply] <;> ring

/-- Subtracting the actual integer harmonic peak supplies the required coordinate translation. -/
theorem admissibleCoordinates_sub_peak (a b c : ℝ) (h : admissibleCoordinates a b c) (s t : ℤ) :
    admissibleCoordinates (a-((s:ℝ)-(t:ℝ))) (b-((s:ℝ)+(t:ℝ))) c := by
  obtain ⟨g,hSH,hGrowth⟩ := h
  refine ⟨fun z => g z-HarmonicPeaks.peakHarmonic s t z,
    HarmonicPeakActions.sub_peak_superharmonic g s t hSH,?_⟩
  have hNew := HarmonicPeakActions.sub_peak_quadratic_growth g (matrix a b c) s t hGrowth
  rw [peak_matrix_coordinates,matrix_sub] at hNew
  simpa only [sub_zero,LatticeQuadraticRounding.quadratic] using hNew

/-- The actual parity-corrected coordinate swap changes a to -a. -/
theorem admissibleCoordinates_flip_a (a b c : ℝ) (h : admissibleCoordinates a b c) :
    admissibleCoordinates (-a) b c := by
  obtain ⟨g,hSH,hGrowth⟩ := h
  refine ⟨fun z => g (ElementaryReflections.shiftedSwap z),
    ElementaryReflections.shiftedSwap_superharmonic g hSH,?_⟩
  have hNew := ElementaryReflections.shiftedSwap_quadratic_growth
    (fun z => (g z:ℝ)) (matrix a b c) hGrowth
  have hMatrix : ElementaryReflections.swapMatrix.transpose*matrix a b c*
      ElementaryReflections.swapMatrix = matrix (-a) b c := by
    exact ElementaryReflections.swap_matrix_coordinates a b c
  rw [hMatrix] at hNew
  exact hNew

/-- The actual horizontal reflection changes b to -b. -/
theorem admissibleCoordinates_flip_b (a b c : ℝ) (h : admissibleCoordinates a b c) :
    admissibleCoordinates a (-b) c := by
  obtain ⟨g,hSH,hGrowth⟩ := h
  refine ⟨fun z => g (ElementaryReflections.horizontalReflection z),
    ElementaryReflections.horizontalReflection_superharmonic g hSH,?_⟩
  have hNew := ElementaryReflections.horizontalReflection_quadratic_growth
    (fun z => (g z:ℝ)) (matrix a b c) hGrowth
  have hMatrix : ElementaryReflections.horizontalMatrix.transpose*matrix a b c*
      ElementaryReflections.horizontalMatrix = matrix a (-b) c := by
    exact ElementaryReflections.horizontal_matrix_coordinates a b c
  rw [hMatrix] at hNew
  exact hNew

/-- The proved real-reference exclusion covers every first-quadrant edge matrix. -/
theorem admissibleCoordinates_edge_exclusion
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hsum : u+v=1)
    (a b c : ℝ) (h : admissibleCoordinates a b c) :
    ¬(matrix a b c-matrix u v (-radius u v)).PosDef := by
  intro hAbove
  obtain ⟨g,hSH,hGrowth⟩ := h
  obtain ⟨r,hr0,hr1,hReference⟩ := ReferenceEdge.exists_reference u v hu hv hsum
  apply RealReferenceExclusion.not_strict_dominator r hr0 hr1 g (matrix a b c) hSH hGrowth
  simpa only [hReference] using hAbove

/-- Every real symmetric growth matrix of an actual integer native-SH function
lies below an integer harmonic peak. All closure and real-edge exclusion
premises are discharged by proved function-level constructions. -/
theorem exists_peak_above
    (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsSymm)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x+y)%2=0 then g (x-1,y)+g (x+1,y) else g (x,y-1)+g (x,y+1)) ≤ 2*g (x,y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |(g (x,y):ℝ)-(1/2:ℝ)*((x:ℝ)*M 0 0*(x:ℝ)+(x:ℝ)*M 0 1*(y:ℝ)+
        (y:ℝ)*M 1 0*(x:ℝ)+(y:ℝ)*M 1 1*(y:ℝ))| ≤ δ*((x:ℝ)^2+(y:ℝ)^2)) :
    ∃ s t : ℤ, (HarmonicPeaks.peakMatrix s t-M).PosSemidef := by
  have hReconstruct := matrix_reconstruct M hM
  have hAdmissible : admissibleCoordinates (M 0 0-M 1 1) (2*M 0 1) (M 0 0+M 1 1) := by
    refine ⟨g,hSuperharmonic,?_⟩
    simpa only [hReconstruct] using hGrowth
  obtain ⟨s,t,hPeak⟩ := ConeClassificationGeometry.exists_peak_above_of_invariances
    admissibleCoordinates admissibleCoordinates_sub_peak admissibleCoordinates_flip_a
    admissibleCoordinates_flip_b admissibleCoordinates_edge_exclusion
    (M 0 0-M 1 1) (2*M 0 1) (M 0 0+M 1 1) hAdmissible
  refine ⟨s,t,?_⟩
  simpa only [←peak_matrix_coordinates,hReconstruct] using hPeak

end FLattice.Auxiliary.RealNecessity
