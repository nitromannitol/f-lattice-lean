import FLattice.Auxiliary.QuadraticSandwich

/-!
# An entrywise neighborhood inside the positive definite cone

The conclusion is for real symmetric matrices. A positive lower bound on
the original quadratic form absorbs sufficiently small changes of all four
entries. No eigenvalue formula or chosen operator norm is required.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PositiveMatrixNeighborhood

/-- A real positive definite two-by-two matrix has an explicitly bounded
entrywise neighborhood among symmetric matrices that is still positive definite. -/
theorem exists_entrywise_radius (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ B : Matrix (Fin 2) (Fin 2) ℝ, B.IsSymm →
      (∀ i j : Fin 2, |B i j - A i j| ≤ δ) → B.PosDef := by
  obtain ⟨c, hc, hQuadratic⟩ := exists_pos_quadratic_lower_bound A hA
  refine ⟨c / 4, by positivity, ?_⟩
  intro B hB hEntries
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr hB)
  intro v hv
  have hNorm : 0 < v 0 ^ 2 + v 1 ^ 2 := by
    by_contra hn
    have hZero : v 0 = 0 ∧ v 1 = 0 := by
      constructor <;> nlinarith only [sq_nonneg (v 0), sq_nonneg (v 1), le_of_not_gt hn]
    apply hv
    ext i
    fin_cases i <;> simp [hZero.1, hZero.2]
  have hOriginal := hQuadratic (v 0) (v 1)
  have hError := (abs_le.mp (QuadraticSandwich.abs_quadratic_le_of_entry_bound
    (B - A) (c / 4) (by positivity) hEntries (v 0) (v 1))).1
  simp only [LatticeQuadraticRounding.quadratic, Matrix.sub_apply] at hError
  have hVector : v = (![v 0, v 1] : Fin 2 → ℝ) := by ext i; fin_cases i <;> rfl
  rw [hVector, quadratic_two_expansion]
  have hPositive : 0 < c * (v 0 ^ 2 + v 1 ^ 2) := mul_pos hc hNorm
  nlinarith only [hOriginal, hError, hPositive]

end FLattice.Auxiliary.PositiveMatrixNeighborhood
