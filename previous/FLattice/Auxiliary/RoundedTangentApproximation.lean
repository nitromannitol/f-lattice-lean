import FLattice.Auxiliary.QuadraticSandwich
import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# Integer convex approximation by rounded tangent planes

For an arbitrary real positive-semidefinite two-dimensional matrix, including
singular irrational matrices, take the supremum of explicit integer affine
planes. Coordinate rounding and a linear penalty give an attained integer
maximum, all integer-direction midpoint inequalities, and the original
uniform quadratic growth. No inverse matrix or periodicity is used.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.RoundedTangentApproximation

open LatticeQuadraticRounding (quadratic)

/-- Coordinatewise floor of the actual matrix gradient. -/
noncomputable def slope (P : Matrix (Fin 2) (Fin 2) ℝ) (z : ℤ × ℤ) : ℤ × ℤ :=
  (⌊P 0 0 * (z.1 : ℝ) + P 0 1 * (z.2 : ℝ)⌋,
   ⌊P 1 0 * (z.1 : ℝ) + P 1 1 * (z.2 : ℝ)⌋)

/-- The rounded quadratic cost, with a linear penalty on the tangent location. -/
noncomputable def cost (P : Matrix (Fin 2) (Fin 2) ℝ) (z : ℤ × ℤ) : ℤ :=
  ⌈quadratic P (z.1 : ℝ) (z.2 : ℝ)⌉ + |z.1| + |z.2|

/-- A literal integer affine plane. -/
noncomputable def plane (P : Matrix (Fin 2) (Fin 2) ℝ) (z x : ℤ × ℤ) : ℤ :=
  (slope P z).1 * x.1 + (slope P z).2 * x.2 - cost P z

/-- The integer supremum of the displayed planes. Attainment is proved below. -/
noncomputable def approximation (P : Matrix (Fin 2) (Fin 2) ℝ) (x : ℤ × ℤ) : ℤ :=
  sSup (Set.range (fun z => plane P z x))

private theorem floor_mul_bounds (a x : ℝ) :
    a * x - |x| ≤ (⌊a⌋ : ℝ) * x ∧ (⌊a⌋ : ℝ) * x ≤ a * x + |x| := by
  have he : |(⌊a⌋ : ℝ) - a| ≤ 1 := by
    apply abs_le.mpr
    have hl := Int.floor_le a
    have hu := Int.lt_floor_add_one a
    constructor <;> linarith only [hl, hu]
  have hp : |((⌊a⌋ : ℝ) - a) * x| ≤ |x| := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (abs_nonneg x)
  have hb := abs_le.mp hp
  constructor <;> nlinarith only [hb.1, hb.2]

/-- The PSD tangent inequality, proved with the actual matrix quadratic. -/
theorem tangent_bound (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosSemidef)
    (z₁ z₂ x₁ x₂ : ℝ) :
    (P 0 0 * z₁ + P 0 1 * z₂) * x₁ + (P 1 0 * z₁ + P 1 1 * z₂) * x₂ -
      quadratic P z₁ z₂ ≤ quadratic P x₁ x₂ := by
  have hSym : P 1 0 = P 0 1 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hP.isHermitian
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hQ := LatticeQuadraticRounding.quadratic_nonneg P hP (x₁-z₁) (x₂-z₂)
  unfold quadratic at hQ ⊢
  rw [hSym] at hQ ⊢
  nlinarith only [hQ]

/-- Every plane is bounded above by the target quadratic and a linear error. -/
theorem plane_upper_bound (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosSemidef)
    (z x : ℤ × ℤ) :
    (plane P z x : ℝ) ≤ quadratic P (x.1 : ℝ) (x.2 : ℝ) +
      |(x.1 : ℝ)| + |(x.2 : ℝ)| - |(z.1 : ℝ)| - |(z.2 : ℝ)| := by
  have h₁ := (floor_mul_bounds (P 0 0*(z.1:ℝ)+P 0 1*(z.2:ℝ)) (x.1:ℝ)).2
  have h₂ := (floor_mul_bounds (P 1 0*(z.1:ℝ)+P 1 1*(z.2:ℝ)) (x.2:ℝ)).2
  have hC := Int.le_ceil (quadratic P (z.1:ℝ) (z.2:ℝ))
  have hT := tangent_bound P hP (z.1:ℝ) (z.2:ℝ) (x.1:ℝ) (x.2:ℝ)
  simp only [plane, slope, cost, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_abs]
  linarith only [h₁, h₂, hC, hT]

/-- The plane indexed by the evaluation point supplies the uniform lower error. -/
theorem diagonal_plane_lower_bound (P : Matrix (Fin 2) (Fin 2) ℝ) (x : ℤ × ℤ) :
    quadratic P (x.1 : ℝ) (x.2 : ℝ) - 2*(|(x.1 : ℝ)|+|(x.2 : ℝ)|)-1 ≤
      (plane P x x : ℝ) := by
  have h₁ := (floor_mul_bounds (P 0 0*(x.1:ℝ)+P 0 1*(x.2:ℝ)) (x.1:ℝ)).1
  have h₂ := (floor_mul_bounds (P 1 0*(x.1:ℝ)+P 1 1*(x.2:ℝ)) (x.2:ℝ)).1
  have hC := Int.ceil_lt_add_one (quadratic P (x.1:ℝ) (x.2:ℝ))
  simp only [plane, slope, cost, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_abs]
  unfold quadratic at hC ⊢
  nlinarith only [h₁, h₂, hC]

/-- At each integer point the integer family of plane values is bounded above. -/
theorem planes_bddAbove (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosSemidef)
    (x : ℤ × ℤ) : BddAbove (Set.range (fun z => plane P z x)) := by
  refine ⟨⌈quadratic P (x.1:ℝ) (x.2:ℝ)+|(x.1:ℝ)|+|(x.2:ℝ)|⌉, ?_⟩
  rintro t ⟨z, rfl⟩
  have h := plane_upper_bound P hP z x
  have hc := Int.le_ceil (quadratic P (x.1:ℝ) (x.2:ℝ)+|(x.1:ℝ)|+|(x.2:ℝ)|)
  have hr : (plane P z x : ℝ) ≤
      (⌈quadratic P (x.1:ℝ) (x.2:ℝ)+|(x.1:ℝ)|+|(x.2:ℝ)|⌉ : ℝ) := by
    linarith only [h, hc, abs_nonneg (z.1:ℝ), abs_nonneg (z.2:ℝ)]
  exact_mod_cast hr

/-- Every displayed integer plane lies below the integer approximation. -/
theorem plane_le_approximation (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosSemidef)
    (z x : ℤ × ℤ) : plane P z x ≤ approximation P x := by
  exact le_csSup (planes_bddAbove P hP x) (Set.mem_range_self z)

/-- The supremum is an attained maximum over actual integer tangent points. -/
theorem approximation_attained (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosSemidef)
    (x : ℤ × ℤ) : ∃ z : ℤ × ℤ, approximation P x = plane P z x := by
  have h := Int.csSup_mem (Set.range_nonempty (fun z => plane P z x)) (planes_bddAbove P hP x)
  obtain ⟨z, hz⟩ := h
  exact ⟨z, hz.symm⟩

/-- The explicit global approximation error is at most linear. -/
theorem approximation_bounds (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosSemidef)
    (x : ℤ × ℤ) :
    quadratic P (x.1:ℝ) (x.2:ℝ)-2*(|(x.1:ℝ)|+|(x.2:ℝ)|)-1 ≤ (approximation P x : ℝ) ∧
    (approximation P x : ℝ) ≤ quadratic P (x.1:ℝ) (x.2:ℝ)+|(x.1:ℝ)|+|(x.2:ℝ)| := by
  constructor
  · exact (diagonal_plane_lower_bound P x).trans (by exact_mod_cast plane_le_approximation P hP x x)
  · obtain ⟨z, hz⟩ := approximation_attained P hP x
    rw [hz]
    have h := plane_upper_bound P hP z x
    linarith only [h, abs_nonneg (z.1:ℝ), abs_nonneg (z.2:ℝ)]

/-- The same maximizing affine plane proves midpoint convexity in every integer direction. -/
theorem midpoint_convex (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosSemidef)
    (x v : ℤ × ℤ) :
    2 * approximation P x ≤ approximation P (x-v) + approximation P (x+v) := by
  obtain ⟨z, hz⟩ := approximation_attained P hP x
  have hl := plane_le_approximation P hP z (x-v)
  have hr := plane_le_approximation P hP z (x+v)
  have hIdentity : plane P z (x-v) + plane P z (x+v) = 2*plane P z x := by
    simp only [plane, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
    ring
  rw [← hz] at hIdentity
  omega

/-- The constructed integer function has the original uniform quadratic growth. -/
theorem approximation_quadratic_growth (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosSemidef) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ)^2+(y : ℝ)^2 →
      |(approximation P (x,y) : ℝ)-quadratic P (x : ℝ) (y : ℝ)| ≤
        δ*((x : ℝ)^2+(y : ℝ)^2) := by
  apply QuadraticErrorEnvelope.eventual_bound_of_global_envelope
    (fun z => (approximation P z : ℝ)-quadratic P (z.1 : ℝ) (z.2 : ℝ))
  intro δ hδ
  obtain ⟨C,hC,hAffine⟩ := QuadraticSandwich.affine_envelope 2 2 1 δ hδ
  refine ⟨C,hC,?_⟩
  intro x y
  have hBounds := approximation_bounds P hP (x,y)
  have hError : |(approximation P (x,y) : ℝ)-quadratic P (x : ℝ) (y : ℝ)| ≤
      2*(|(x : ℝ)|+|(y : ℝ)|)+1 := by
    apply abs_le.mpr
    constructor <;> linarith only [hBounds.1,hBounds.2,abs_nonneg (x : ℝ),abs_nonneg (y : ℝ)]
  have hEnvelope := hAffine |(x : ℝ)| |(y : ℝ)|
  rw [abs_of_nonneg (by positivity), sq_abs, sq_abs] at hEnvelope
  exact hError.trans (by linarith only [hEnvelope])

/-- The displayed construction yields an actual integer midpoint-convex
approximation of every positive-semidefinite quadratic, with its original
uniform growth rather than an assumed envelope or regularity condition. -/
theorem exists_integer_midpoint_convex_approximation
    (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosSemidef) :
    ∃ V : ℤ × ℤ → ℤ,
      (∀ x v : ℤ × ℤ, 2 * V x ≤ V (x-v) + V (x+v)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
        R ^ 2 ≤ (x : ℝ)^2+(y : ℝ)^2 →
        |(V (x,y) : ℝ)-quadratic P (x : ℝ) (y : ℝ)| ≤
          δ*((x : ℝ)^2+(y : ℝ)^2)) := by
  exact ⟨approximation P, midpoint_convex P hP, approximation_quadratic_growth P hP⟩

end FLattice.Auxiliary.RoundedTangentApproximation
