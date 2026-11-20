import FLattice.Auxiliary.RationalExclusion
import FLattice.Auxiliary.RationalReferenceDensity
import FLattice.Auxiliary.PositiveMatrixNeighborhood

/-!
# Exclusion above all real reference slopes

Primitive rational references are dense entrywise, and the positive definite
cone is open within real symmetric matrices. The conclusion keeps the original
integer superharmonicity and uniform quadratic-growth hypotheses.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.RealReferenceExclusion

open BranchMatrix

/-- No actual integer superharmonic function with the original quadratic growth
strictly dominates a reference matrix at any real slope in the unit interval. -/
theorem not_strict_dominator
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then g (x - 1, y) + g (x + 1, y)
        else g (x, y - 1) + g (x, y + 1)) ≤ 2 * g (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hAbove : (M - rankOneMatrix r 1).PosDef) : False := by
  obtain ⟨δ, hδ, hNeighborhood⟩ :=
    PositiveMatrixNeighborhood.exists_entrywise_radius (M - rankOneMatrix r 1) hAbove
  obtain ⟨p, hp⟩ := RationalReferenceDensity.exists_primitive_reference_close r δ hr0 hr1 hδ
  have hSymm : M.IsSymm := by
    have h := Matrix.isHermitian_iff_isSymm.mp hAbove.isHermitian
    have hSum := h.add (rankOneMatrix_isSymm r 1)
    simpa only [sub_add_cancel] using hSum
  have hApprox : (M - rankOneMatrix (p.n : ℝ) (p.d : ℝ)).PosDef := by
    apply hNeighborhood _ (hSymm.sub (rankOneMatrix_isSymm _ _))
    intro i j
    have h := le_of_lt (hp i j)
    simpa only [Matrix.sub_apply, sub_sub_sub_cancel_left, abs_sub_comm] using h
  exact RationalExclusion.not_strict_dominator p g M hSuperharmonic hGrowth hApprox

end FLattice.Auxiliary.RealReferenceExclusion
