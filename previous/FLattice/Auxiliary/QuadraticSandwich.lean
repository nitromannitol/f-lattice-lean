import FLattice.Auxiliary.LatticeQuadraticRounding
import FLattice.Auxiliary.QuadraticErrorEnvelope
import FLattice.Auxiliary.QuadraticGap

/-!
# Uniform growth from nearby affine quadratic bounds

Entrywise convergence of the bounding matrices controls their quadratic
forms uniformly over directions. Fixed affine errors are absorbed into an
arbitrarily small quadratic error plus a constant. Thus global lower and
upper affine quadratics with arbitrarily close matrices determine the
original uniform quadratic growth, without any regularity premise on F.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.QuadraticSandwich

open LatticeQuadraticRounding (quadratic)

private theorem term_bound (a x y δ : ℝ) (ha : |a| ≤ δ) :
    |x * a * y| ≤ δ * |x| * |y| := by
  calc
    |x * a * y| = |a| * |x| * |y| := by simp only [abs_mul]; ring
    _ ≤ δ * |x| * |y| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (abs_nonneg _)) (abs_nonneg _)

/-- An entrywise matrix bound controls the quadratic form uniformly in direction. -/
theorem abs_quadratic_le_of_entry_bound
    (A : Matrix (Fin 2) (Fin 2) ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hEntries : ∀ i j : Fin 2, |A i j| ≤ δ) (x y : ℝ) :
    |quadratic A x y| ≤ δ * (x ^ 2 + y ^ 2) := by
  have h00 := term_bound (A 0 0) x x δ (hEntries 0 0)
  have h01 := term_bound (A 0 1) x y δ (hEntries 0 1)
  have h10 := term_bound (A 1 0) y x δ (hEntries 1 0)
  have h11 := term_bound (A 1 1) y y δ (hEntries 1 1)
  have hSum : |x * A 0 0 * x + x * A 0 1 * y + y * A 1 0 * x + y * A 1 1 * y| ≤
      δ * |x| * |x| + δ * |x| * |y| + δ * |y| * |x| + δ * |y| * |y| := by
    calc
      _ ≤ |x * A 0 0 * x + x * A 0 1 * y + y * A 1 0 * x| + |y * A 1 1 * y| := abs_add_le _ _
      _ ≤ (|x * A 0 0 * x + x * A 0 1 * y| + |y * A 1 0 * x|) + |y * A 1 1 * y| :=
        add_le_add (abs_add_le _ _) (le_refl _)
      _ ≤ ((|x * A 0 0 * x| + |x * A 0 1 * y|) + |y * A 1 0 * x|) + |y * A 1 1 * y| :=
        add_le_add (add_le_add (abs_add_le _ _) (le_refl _)) (le_refl _)
      _ ≤ _ := add_le_add (add_le_add (add_le_add h00 h01) h10) h11
  have hCross : 2 * (|x| * |y|) ≤ x ^ 2 + y ^ 2 := by
    nlinarith only [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  have hScaled := mul_le_mul_of_nonneg_left hCross hδ
  have hxx : δ * |x| * |x| = δ * x ^ 2 := by
    calc
      _ = δ * |x| ^ 2 := by ring
      _ = _ := by rw [sq_abs]
  have hyy : δ * |y| * |y| = δ * y ^ 2 := by
    calc
      _ = δ * |y| ^ 2 := by ring
      _ = _ := by rw [sq_abs]
  rw [hxx, hyy] at hSum
  unfold quadratic
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith only [hSum, hScaled]

/-- A fixed affine function admits a global arbitrarily small quadratic envelope. -/
theorem affine_envelope (a b d δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, |a * x + b * y + d| ≤ δ * (x ^ 2 + y ^ 2) + C := by
  refine ⟨2 * (a ^ 2 + b ^ 2) / (8 * δ) + |d|, by positivity, ?_⟩
  intro x y
  have hUpper := QuadraticGap.linear_lower_bound (8 * δ) a b x y (by positivity)
  have hLower := QuadraticGap.linear_lower_bound (8 * δ) (-a) (-b) x y (by positivity)
  have hd := abs_le.mp (le_refl |d|)
  norm_num only [neg_sq, neg_neg, mul_div_cancel_left₀ _ (by norm_num : (8 : ℝ) ≠ 0)] at hUpper hLower
  apply abs_le.mpr
  constructor <;> nlinarith only [hUpper, hLower, hd.1, hd.2]

/-- Arbitrarily close affine quadratic sandwiches imply the original
uniform epsilon-radius growth with the limiting matrix. -/
theorem quadratic_growth_of_sandwich
    (F : ℤ × ℤ → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSandwich : ∀ δ : ℝ, 0 < δ →
      ∃ L U : Matrix (Fin 2) (Fin 2) ℝ, ∃ a b d a' b' d' : ℝ,
        (∀ i j : Fin 2, |L i j - M i j| ≤ δ) ∧
        (∀ i j : Fin 2, |U i j - M i j| ≤ δ) ∧
        (∀ x y : ℤ,
          quadratic L (x : ℝ) (y : ℝ) + a * (x : ℝ) + b * (y : ℝ) + d ≤ F (x, y)) ∧
        (∀ x y : ℤ,
          F (x, y) ≤ quadratic U (x : ℝ) (y : ℝ) + a' * (x : ℝ) + b' * (y : ℝ) + d')) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |F (x, y) - quadratic M (x : ℝ) (y : ℝ)| ≤ δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  apply QuadraticErrorEnvelope.eventual_bound_of_global_envelope
    (fun z => F z - quadratic M (z.1 : ℝ) (z.2 : ℝ))
  intro δ hδ
  obtain ⟨L, U, a, b, d, a', b', d', hLEntries, hUEntries, hLower, hUpper⟩ :=
    hSandwich (δ / 2) (by positivity)
  obtain ⟨CL, hCL, hLAffine⟩ := affine_envelope a b d (δ / 2) (by positivity)
  obtain ⟨CU, hCU, hUAffine⟩ := affine_envelope a' b' d' (δ / 2) (by positivity)
  refine ⟨CL + CU, add_nonneg hCL hCU, ?_⟩
  intro x y
  have hLQuad := abs_quadratic_le_of_entry_bound (L - M) (δ / 2) (by positivity)
    hLEntries (x : ℝ) (y : ℝ)
  have hUQuad := abs_quadratic_le_of_entry_bound (U - M) (δ / 2) (by positivity)
    hUEntries (x : ℝ) (y : ℝ)
  have hDifference : ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      quadratic (A - M) (x : ℝ) (y : ℝ) = quadratic A (x : ℝ) (y : ℝ) -
        quadratic M (x : ℝ) (y : ℝ) := by
    intro A
    simp only [quadratic, Matrix.sub_apply]
    ring
  rw [hDifference] at hLQuad hUQuad
  have hLQ := abs_le.mp hLQuad
  have hUQ := abs_le.mp hUQuad
  have hLA := abs_le.mp (hLAffine (x : ℝ) (y : ℝ))
  have hUA := abs_le.mp (hUAffine (x : ℝ) (y : ℝ))
  have hL := hLower x y
  have hU := hUpper x y
  apply abs_le.mpr
  constructor <;> linarith only [hLQ.1, hUQ.2, hLA.1, hUA.2, hL, hU, hCL, hCU]

end FLattice.Auxiliary.QuadraticSandwich
