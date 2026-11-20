import FLattice.Auxiliary.RealNecessity
import FLattice.Auxiliary.DownwardClosure

/-!
# Classification of the actual integer superharmonic growth matrices

This ordinary auxiliary implementation theorem combines the proved all-real
necessity and constructive sufficiency. Both sides are literal: the original
native inequality and uniform quadratic growth on the left, and the explicit
integer harmonic peak matrices on the right. It is not an author-facing
anchor or a claim about approval of any separate main declaration.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MatrixClassification

/-- A real symmetric matrix occurs as the original uniform quadratic growth
of an integer native-superharmonic function exactly when an explicit integer
harmonic peak dominates it in positive-semidefinite order. -/
theorem integer_superharmonic_growth_iff_peak_domination
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsSymm) :
    (∃ g : ℤ × ℤ → ℤ,
      (∀ x y : ℤ,
        (if (x+y)%2=0 then g (x-1,y)+g (x+1,y) else g (x,y-1)+g (x,y+1)) ≤ 2*g (x,y)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
        R^2 ≤ (x:ℝ)^2+(y:ℝ)^2 →
        |(g (x,y):ℝ)-(1/2:ℝ)*((x:ℝ)*M 0 0*(x:ℝ)+(x:ℝ)*M 0 1*(y:ℝ)+
          (y:ℝ)*M 1 0*(x:ℝ)+(y:ℝ)*M 1 1*(y:ℝ))| ≤ δ*((x:ℝ)^2+(y:ℝ)^2))) ↔
    ∃ s t : ℤ,
      ((1/2:ℝ) • !![(s:ℝ)-(t:ℝ),(s:ℝ)+(t:ℝ);(s:ℝ)+(t:ℝ),(t:ℝ)-(s:ℝ)]-M).PosSemidef := by
  constructor
  · rintro ⟨g,hSuperharmonic,hGrowth⟩
    exact RealNecessity.exists_peak_above g M hM hSuperharmonic hGrowth
  · rintro ⟨s,t,hAbove⟩
    exact DownwardClosure.exists_superharmonic_with_growth_below_peak M s t hAbove

end FLattice.Auxiliary.MatrixClassification
