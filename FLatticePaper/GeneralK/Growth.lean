import FLatticePaper.GeneralK.Columns
import FLatticePaper.Plane.QuadraticGrowth
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace FLatticePaper.GeneralK

/-- The physical matrix `A(a,b,c)` used in the column classification. -/
def symmetricMatrix (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, c]

theorem isSymm_symmetricMatrix (a b c : ℝ) : (symmetricMatrix a b c).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem matrixQuadratic_symmetricMatrix (a b c : ℝ) (x y : ℤ) :
    matrixQuadratic (symmetricMatrix a b c) (x, y) =
      (a * (x : ℝ) ^ 2 + 2 * b * (x : ℝ) * (y : ℝ) + c * (y : ℝ) ^ 2) / 2 := by
  simp [matrixQuadratic, symmetricMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Farey.siteVector]
  ring

/-- The growth set on the physical graph with horizontal inputs in phase zero. -/
def growthSet (k : ℤ) : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {matrix | matrix.IsSymm ∧ ∃ field : Field, Superharmonic k field ∧ HasQuadraticGrowth field matrix}

theorem symmetricMatrix_mem_growthSet_iff (k : ℤ) (a b c : ℝ) :
    symmetricMatrix a b c ∈ growthSet k ↔
      ∃ field : Field, Superharmonic k field ∧ HasQuadraticGrowth field (symmetricMatrix a b c) :=
  and_iff_right (isSymm_symmetricMatrix a b c)

theorem mem_growthSet_two_iff {matrix : Matrix (Fin 2) (Fin 2) ℝ} (hsymm : matrix.IsSymm) :
    matrix ∈ growthSet 2 ↔ ∃ field : Field, FLatticePaper.Superharmonic field ∧ HasQuadraticGrowth field matrix := by
  simp only [growthSet, Set.mem_setOf_eq, hsymm, true_and, Superharmonic,
    FLatticePaper.Superharmonic, laplacian_two]

theorem zero_mem_growthSet (k : ℤ) : (0 : Matrix (Fin 2) (Fin 2) ℝ) ∈ growthSet k := by
  refine ⟨Matrix.isSymm_zero, 0, fun _ => by simp [laplacian], ?_⟩
  intro ε hε
  refine ⟨1, zero_lt_one, fun site _ => ?_⟩
  simp only [Pi.zero_apply, Int.cast_zero, matrixQuadratic, Matrix.zero_mulVec, dotProduct_zero,
    zero_div, sub_self, abs_zero]
  exact mul_nonneg hε.le (by unfold squaredSize; positivity)

theorem superharmonic_add {k : ℤ} {first second : Field}
    (hfirst : Superharmonic k first) (hsecond : Superharmonic k second) :
    Superharmonic k (first + second) := by
  intro site
  have hn := hfirst site
  have hp := hsecond site
  simp only [laplacian, Pi.add_apply] at hn hp ⊢
  omega

theorem quadraticGrowth_add {first second : Field} {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hfirst : HasQuadraticGrowth first A) (hsecond : HasQuadraticGrowth second B) :
    HasQuadraticGrowth (first + second) (A + B) := by
  intro ε hε
  obtain ⟨r₁, hr₁, hfirst⟩ := hfirst (ε / 2) (by positivity)
  obtain ⟨r₂, hr₂, hsecond⟩ := hsecond (ε / 2) (by positivity)
  refine ⟨max r₁ r₂, hr₁.trans_le (le_max_left ..), fun site hsize => ?_⟩
  have hsize₁ := (pow_le_pow_left₀ hr₁.le (le_max_left r₁ r₂) 2).trans hsize
  have hsize₂ := (pow_le_pow_left₀ hr₂.le (le_max_right r₁ r₂) 2).trans hsize
  have hquad : matrixQuadratic (A + B) site = matrixQuadratic A site + matrixQuadratic B site := by
    simp only [matrixQuadratic, Matrix.add_mulVec, dotProduct_add]
    ring
  calc
    |((first + second) site : ℝ) - matrixQuadratic (A + B) site| =
        |((first site : ℝ) - matrixQuadratic A site) + ((second site : ℝ) - matrixQuadratic B site)| := by
      rw [Pi.add_apply, Int.cast_add, hquad]
      congr 1
      ring
    _ ≤ |(first site : ℝ) - matrixQuadratic A site| + |(second site : ℝ) - matrixQuadratic B site| :=
      abs_add_le _ _
    _ ≤ (ε / 2) * squaredSize site + (ε / 2) * squaredSize site :=
      add_le_add (hfirst site hsize₁) (hsecond site hsize₂)
    _ = ε * squaredSize site := by ring

theorem add_mem_growthSet {k : ℤ} {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ growthSet k) (hB : B ∈ growthSet k) : A + B ∈ growthSet k := by
  obtain ⟨hAsymm, f, hf, hfGrowth⟩ := hA
  obtain ⟨hBsymm, g, hg, hgGrowth⟩ := hB
  exact ⟨hAsymm.add hBsymm, f + g, superharmonic_add hf hg, quadraticGrowth_add hfGrowth hgGrowth⟩

end FLatticePaper.GeneralK
