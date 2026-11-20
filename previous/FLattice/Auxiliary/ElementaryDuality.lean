import FLattice.Auxiliary.ElementaryDualityMatrix
import FLattice.Auxiliary.ElementaryProfiles
import FLattice.Auxiliary.QuadraticSandwich

/-!
# The actual integer harmonic dual transform

The source operation g(-y,x-1)+H(x,y) preserves native integer SH and the
original uniform quadratic growth, with matrix Pᵀ M P+A_H. Its harmonic
function is the literal integer function, including the parity remainder.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.ElementaryDuality

open LatticeQuadraticRounding (quadratic)

/-- The literal matrix of the source harmonic correction. -/
noncomputable def harmonicMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 : ℝ) / 2, 1 / 2; 1 / 2, -1 / 2]

/-- The actual integer dual operation, including its physical affine shift. -/
def dual (g : ℤ × ℤ → ℤ) (z : ℤ × ℤ) : ℤ :=
  g (affineRotation z) + ElementaryProfiles.harmonic z

/-- The harmonic quadratic is exactly the polynomial displayed in the source. -/
theorem harmonic_quadratic (x y : ℝ) :
    quadratic harmonicMatrix x y = (1 / 4 : ℝ) * (x ^ 2 + 2 * x * y - y ^ 2) := by
  norm_num [quadratic, harmonicMatrix]
  ring

/-- The exact harmonic remainder lies between two fixed affine functions. -/
theorem harmonic_affine_bounds (x y : ℤ) :
    quadratic harmonicMatrix (x : ℝ) (y : ℝ) - (y : ℝ) / 2 - 1 / 4 ≤
      (ElementaryProfiles.harmonic (x, y) : ℝ) ∧
    (ElementaryProfiles.harmonic (x, y) : ℝ) ≤
      quadratic harmonicMatrix (x : ℝ) (y : ℝ) - (y : ℝ) / 2 := by
  rw [ElementaryProfiles.harmonic_real, harmonic_quadratic]
  rcases ElementaryProfiles.parity_cases x y with hp | hp <;>
    rw [hp] <;> norm_num

/-- The literal harmonic integer function has the claimed uniform quadratic growth. -/
theorem harmonic_quadratic_growth :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(ElementaryProfiles.harmonic (x, y) : ℝ) - quadratic harmonicMatrix (x : ℝ) (y : ℝ)| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  apply QuadraticSandwich.quadratic_growth_of_sandwich
    (fun z => (ElementaryProfiles.harmonic z : ℝ)) harmonicMatrix
  intro δ hδ
  refine ⟨harmonicMatrix, harmonicMatrix, 0, -(1 / 2), -(1 / 4), 0, -(1 / 2), 0,
    ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [sub_self, abs_zero] using le_of_lt hδ
  · intro i j
    simpa only [sub_self, abs_zero] using le_of_lt hδ
  · intro x y
    have h := (harmonic_affine_bounds x y).1
    linarith only [h]
  · intro x y
    have h := (harmonic_affine_bounds x y).2
    linarith only [h]

/-- The affine rotation followed by literal harmonic addition preserves integer SH. -/
theorem dual_superharmonic (g : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then g (x - 1, y) + g (x + 1, y)
        else g (x, y - 1) + g (x, y + 1)) ≤ 2 * g (x, y)) :
    ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then dual g (x - 1, y) + dual g (x + 1, y)
        else dual g (x, y - 1) + dual g (x, y + 1)) ≤ 2 * dual g (x, y) := by
  intro x y
  have hRot := affineRotation_superharmonic g hSuperharmonic x y
  have hH := ElementaryProfiles.harmonic_native x y
  dsimp [dual]
  split_ifs at hRot hH ⊢ <;> omega

private theorem add_quadratic_growth
    (f g : ℤ × ℤ → ℝ) (M N : Matrix (Fin 2) (Fin 2) ℝ)
    (hf : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |f (x, y) - quadratic M (x : ℝ) (y : ℝ)| ≤ δ * ((x : ℝ)^2 + (y : ℝ)^2))
    (hg : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |g (x, y) - quadratic N (x : ℝ) (y : ℝ)| ≤ δ * ((x : ℝ)^2 + (y : ℝ)^2)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |f (x, y) + g (x, y) - quadratic (M + N) (x : ℝ) (y : ℝ)| ≤
          δ * ((x : ℝ)^2 + (y : ℝ)^2) := by
  intro δ hδ
  obtain ⟨R, hR, hF⟩ := hf (δ / 2) (by positivity)
  obtain ⟨S, hS, hG⟩ := hg (δ / 2) (by positivity)
  refine ⟨R + S, by positivity, ?_⟩
  intro x y hSize
  have hFR := hF x y (by nlinarith only [hSize, mul_pos hR hS, sq_nonneg S])
  have hGR := hG x y (by nlinarith only [hSize, mul_pos hR hS, sq_nonneg R])
  have hIdentity : f (x, y) + g (x, y) - quadratic (M + N) (x : ℝ) (y : ℝ) =
      (f (x, y) - quadratic M (x : ℝ) (y : ℝ)) +
        (g (x, y) - quadratic N (x : ℝ) (y : ℝ)) := by
    simp only [quadratic, Matrix.add_apply]
    ring
  rw [hIdentity]
  calc
    _ ≤ |f (x, y) - quadratic M (x : ℝ) (y : ℝ)| +
        |g (x, y) - quadratic N (x : ℝ) (y : ℝ)| := abs_add_le _ _
    _ ≤ (δ / 2) * ((x : ℝ)^2 + (y : ℝ)^2) +
        (δ / 2) * ((x : ℝ)^2 + (y : ℝ)^2) := add_le_add hFR hGR
    _ = δ * ((x : ℝ)^2 + (y : ℝ)^2) := by ring

/-- The exact integer dual has the original uniform quadratic growth at PᵀMP+A_H. -/
theorem dual_quadratic_growth (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(dual g (x, y) : ℝ) - quadratic
          (rotationMatrix.transpose * M * rotationMatrix + harmonicMatrix) (x : ℝ) (y : ℝ)| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  have hRot := affineRotation_quadratic_growth (fun z => (g z : ℝ)) M hGrowth
  have h := add_quadratic_growth (fun z => (g (affineRotation z) : ℝ))
    (fun z => (ElementaryProfiles.harmonic z : ℝ))
    (rotationMatrix.transpose * M * rotationMatrix) harmonicMatrix hRot harmonic_quadratic_growth
  simpa only [dual, Int.cast_add] using h

/-- The actual dual matrix maps the source rank-one reference to its dual parameter. -/
theorem dual_matrix_reference (n d : ℝ) (hd : 0 < d) (hn : 0 ≤ n) (hnd : n ≤ d) :
    rotationMatrix.transpose * BranchMatrix.rankOneMatrix n d * rotationMatrix + harmonicMatrix =
      BranchMatrix.rankOneMatrix (d - n) (d + n) :=
  dual_rankOneMatrix_of_source_range n d hd hn hnd

end FLattice.Auxiliary.ElementaryDuality
