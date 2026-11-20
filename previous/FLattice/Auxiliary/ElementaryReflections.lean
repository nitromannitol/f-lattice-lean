import FLattice.Auxiliary.ElementaryDualityAffine

/-!
# The two elementary spatial reflections

The literal maps (-x,y) and (y+1,x) preserve the native incoming pairs.
Their pullbacks preserve integer SH and the original uniform quadratic
growth. The second map's unit translation is essential to native parity.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.ElementaryReflections

open LatticeQuadraticRounding (quadratic)

/-- Horizontal reflection of the physical plane. -/
def horizontalReflection (z : ℤ × ℤ) : ℤ × ℤ := (-z.1,z.2)

/-- Swapping coordinates with the parity-correcting unit translation. -/
def shiftedSwap (z : ℤ × ℤ) : ℤ × ℤ := (z.2+1,z.1)

/-- The linear part of horizontal reflection. -/
noncomputable def horizontalMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![-1,0;0,1]

/-- The linear part of the shifted coordinate swap. -/
noncomputable def swapMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;1,0]

/-- The exact incoming sums agree under horizontal reflection. -/
theorem horizontalReflection_incoming_sum (g : ℤ × ℤ → ℤ) (x y : ℤ) :
    (if (x+y)%2=0 then g (horizontalReflection (x-1,y))+g (horizontalReflection (x+1,y))
      else g (horizontalReflection (x,y-1))+g (horizontalReflection (x,y+1))) =
    (if (-x+y)%2=0 then g (-x-1,y)+g (-x+1,y) else g (-x,y-1)+g (-x,y+1)) := by
  have hp : (-x+y)%2=(x+y)%2 := by omega
  rw [hp]
  by_cases he : (x+y)%2=0
  · simp only [he,if_true,horizontalReflection]
    rw [show -(x-1)=-x+1 by omega,show -(x+1)=-x-1 by omega]
    exact add_comm _ _
  · simp only [he,if_false,horizontalReflection]

/-- The unit-translated swap sends native incoming pairs to native pairs. -/
theorem shiftedSwap_incoming_sum (g : ℤ × ℤ → ℤ) (x y : ℤ) :
    (if (x+y)%2=0 then g (shiftedSwap (x-1,y))+g (shiftedSwap (x+1,y))
      else g (shiftedSwap (x,y-1))+g (shiftedSwap (x,y+1))) =
    (if (y+1+x)%2=0 then g (y+1-1,x)+g (y+1+1,x)
      else g (y+1,x-1)+g (y+1,x+1)) := by
  by_cases he : (x+y)%2=0
  · have ho : (y+1+x)%2≠0 := by omega
    simp only [he,ho,if_true,if_false,shiftedSwap]
  · have ho : (y+1+x)%2=0 := by omega
    simp only [he,ho,if_true,if_false,shiftedSwap]
    rw [sub_add_cancel,add_sub_cancel_right]

/-- Horizontal-reflection pullback preserves the actual integer SH inequality. -/
theorem horizontalReflection_superharmonic (g : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x+y)%2=0 then g (x-1,y)+g (x+1,y) else g (x,y-1)+g (x,y+1)) ≤ 2*g (x,y)) :
    ∀ x y : ℤ,
      (if (x+y)%2=0 then g (horizontalReflection (x-1,y))+g (horizontalReflection (x+1,y))
        else g (horizontalReflection (x,y-1))+g (horizontalReflection (x,y+1))) ≤
      2*g (horizontalReflection (x,y)) := by
  intro x y
  rw [horizontalReflection_incoming_sum]
  exact hSuperharmonic (-x) y

/-- The parity-corrected swap pullback preserves actual integer SH. -/
theorem shiftedSwap_superharmonic (g : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x+y)%2=0 then g (x-1,y)+g (x+1,y) else g (x,y-1)+g (x,y+1)) ≤ 2*g (x,y)) :
    ∀ x y : ℤ,
      (if (x+y)%2=0 then g (shiftedSwap (x-1,y))+g (shiftedSwap (x+1,y))
        else g (shiftedSwap (x,y-1))+g (shiftedSwap (x,y+1))) ≤
      2*g (shiftedSwap (x,y)) := by
  intro x y
  rw [shiftedSwap_incoming_sum]
  exact hSuperharmonic (y+1) x

/-- Exact quadratic action of the first reflection, for arbitrary real matrices. -/
theorem horizontal_quadratic (M : Matrix (Fin 2) (Fin 2) ℝ) (x y : ℝ) :
    quadratic (horizontalMatrix.transpose*M*horizontalMatrix) x y = quadratic M (-x) y := by
  norm_num [quadratic,horizontalMatrix,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]

/-- Exact quadratic action of the linear part of the second reflection. -/
theorem swap_quadratic (M : Matrix (Fin 2) (Fin 2) ℝ) (x y : ℝ) :
    quadratic (swapMatrix.transpose*M*swapMatrix) x y = quadratic M y x := by
  norm_num [quadratic,swapMatrix,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]
  ring

/-- The first reflection preserves original uniform growth with exact congruence. -/
theorem horizontalReflection_quadratic_growth
    (g : ℤ × ℤ → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |g (x,y)-(1/2:ℝ)*((x:ℝ)*M 0 0*(x:ℝ)+(x:ℝ)*M 0 1*(y:ℝ)+
        (y:ℝ)*M 1 0*(x:ℝ)+(y:ℝ)*M 1 1*(y:ℝ))| ≤ δ*((x:ℝ)^2+(y:ℝ)^2)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |g (horizontalReflection (x,y))-quadratic
        (horizontalMatrix.transpose*M*horizontalMatrix) (x:ℝ) (y:ℝ)| ≤
        δ*((x:ℝ)^2+(y:ℝ)^2) := by
  intro δ hδ
  obtain ⟨R,hR,h⟩ := hGrowth δ hδ
  refine ⟨R,hR,?_⟩
  intro x y hSize
  have hs : R^2 ≤ ((-x:ℤ):ℝ)^2+(y:ℝ)^2 := by simpa only [Int.cast_neg,neg_sq] using hSize
  have hh := h (-x) y hs
  rw [horizontal_quadratic]
  simpa only [horizontalReflection,quadratic,Int.cast_neg,neg_sq] using hh

/-- The translated swap preserves original uniform growth with the swap congruence. -/
theorem shiftedSwap_quadratic_growth
    (g : ℤ × ℤ → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |g (x,y)-(1/2:ℝ)*((x:ℝ)*M 0 0*(x:ℝ)+(x:ℝ)*M 0 1*(y:ℝ)+
        (y:ℝ)*M 1 0*(x:ℝ)+(y:ℝ)*M 1 1*(y:ℝ))| ≤ δ*((x:ℝ)^2+(y:ℝ)^2)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
      |g (shiftedSwap (x,y))-quadratic
        (swapMatrix.transpose*M*swapMatrix) (x:ℝ) (y:ℝ)| ≤
        δ*((x:ℝ)^2+(y:ℝ)^2) := by
  have hShift := QuadraticGrowthTranslation.translate_sub_affine g M 1 0 0 0 0 hGrowth
  intro δ hδ
  obtain ⟨R,hR,h⟩ := hShift δ hδ
  refine ⟨R,hR,?_⟩
  intro x y hSize
  have hs : R^2 ≤ (y:ℝ)^2+(x:ℝ)^2 := by simpa only [add_comm] using hSize
  have hh := h y x hs
  rw [swap_quadratic]
  simpa only [shiftedSwap,quadratic,add_zero,zero_mul,sub_zero,add_comm] using hh

/-- Both literal reflection matrices are units. -/
theorem reflectionMatrices_isUnit : IsUnit horizontalMatrix ∧ IsUnit swapMatrix := by
  constructor <;> apply (Matrix.isUnit_iff_isUnit_det _).mpr <;>
    norm_num [horizontalMatrix,swapMatrix,Matrix.det_fin_two_of]

/-- Horizontal reflection negates precisely the off-diagonal matrix coordinate. -/
theorem horizontal_matrix_coordinates (a b c : ℝ) :
    horizontalMatrix.transpose*!![(c+a)/2,b/2;b/2,(c-a)/2]*horizontalMatrix =
      !![(c+a)/2,(-b)/2;(-b)/2,(c-a)/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [horizontalMatrix,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two] <;> ring

/-- Coordinate swap negates precisely the diagonal-difference coordinate. -/
theorem swap_matrix_coordinates (a b c : ℝ) :
    swapMatrix.transpose*!![(c+a)/2,b/2;b/2,(c-a)/2]*swapMatrix =
      !![(c+(-a))/2,b/2;b/2,(c-(-a))/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapMatrix,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]
  all_goals ring

end FLattice.Auxiliary.ElementaryReflections
