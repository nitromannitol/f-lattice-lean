import FLattice.Auxiliary.MatrixSquareCompletion
import FLattice.Auxiliary.QuadraticSandwich
import FLattice.Auxiliary.TransportMatrixContinuity

/-!
# Quadratic growth of an attained lattice infimum transport

The sampling map and cost have their literal affine and quadratic forms.
Square completion and coordinatewise rounding give lower and upper bounds;
small perturbations of the input matrix then prove the original uniform
quadratic asymptotics. No periodicity of the input function is required.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.QuadraticTransportGrowth

open Matrix
open LatticeQuadraticRounding (quadratic entryBound)
open MatrixSquareCompletion (hessian center base)

/-- The real coordinate vector of an integer point. -/
def point (z : ℤ × ℤ) : Fin 2 → ℝ := ![(z.1 : ℝ), (z.2 : ℝ)]

private theorem quadratic_vector (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    MatrixSquareCompletion.quadratic A v = quadratic A (v 0) (v 1) := by
  have hv : v = (![v 0, v 1] : Fin 2 → ℝ) := by ext i; fin_cases i <;> rfl
  rw [hv]
  unfold MatrixSquareCompletion.quadratic quadratic
  have h := quadratic_two_expansion A (v 0) (v 1)
  simpa only [star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one] using
    congrArg (fun z : ℝ => (1 / 2 : ℝ) * z) h

/-- The square-completed base has the computed transport matrix as its
quadratic part and a fixed affine remainder. -/
theorem base_affine
    (C N B : Matrix (Fin 2) (Fin 2) ℝ) (hC : C.IsSymm) (hUnit : IsUnit C)
    (hDomain : (N + C⁻¹).PosDef) (ell : Fin 2 → ℝ) :
    ∃ a b d : ℝ, ∀ x y : ℝ,
      base C N B ell ![x, y] =
        quadratic (MatrixInverseOrder.transportMatrix C⁻¹ B N) x y + a * x + b * y + d := by
  let A := (hessian C N)⁻¹ * (C * N * B)
  refine ⟨ell 0 * A 0 0 + ell 1 * A 1 0,
    ell 0 * A 0 1 + ell 1 * A 1 1, -MatrixSquareCompletion.quadratic (hessian C N)⁻¹ ell, ?_⟩
  intro x y
  rw [MatrixSquareCompletion.base_eq_transport_quadratic_add_affine C N B hC hUnit hDomain,
    quadratic_vector, mulVec_mulVec]
  change quadratic (MatrixInverseOrder.transportMatrix C⁻¹ B N) x y +
    ell ⬝ᵥ (A *ᵥ ![x, y]) - MatrixSquareCompletion.quadratic (hessian C N)⁻¹ ell = _
  simp only [dotProduct, mulVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- A global quadratic lower bound on the input gives the continuous
square-completed lower bound on every attained lattice minimum. -/
theorem minimum_lower_bound
    (C N B : Matrix (Fin 2) (Fin 2) ℝ) (hC : C.IsSymm) (hUnit : IsUnit C)
    (hDomain : (N + C⁻¹).PosDef) (ell : Fin 2 → ℝ)
    (g : ℤ × ℤ → ℝ) (sample : ℤ × ℤ → ℤ × ℤ → ℤ × ℤ) (cost : ℤ × ℤ → ℝ)
    (hSample : ∀ w p, point (sample w p) = B *ᵥ point w - C *ᵥ point p)
    (hCost : ∀ p, cost p = MatrixSquareCompletion.quadratic C (point p) + ell ⬝ᵥ point p)
    (K : ℝ) (hLower : ∀ x y : ℤ, quadratic N (x : ℝ) (y : ℝ) - K ≤ g (x, y))
    (w : ℤ × ℤ) (T : ℝ)
    (hMinimum : ∃ p : ℤ × ℤ, T = g (sample w p) + cost p) :
    base C N B ell (point w) - K ≤ T := by
  obtain ⟨p, hAt⟩ := hMinimum
  have hBound := hLower (sample w p).1 (sample w p).2
  have hSquare := MatrixSquareCompletion.objective_eq_completed_square
    C N B hC hUnit hDomain ell (point w) (point p)
  rw [add_assoc, ← hSample w p, ← hCost p] at hSquare
  have hNonneg := LatticeQuadraticRounding.quadratic_nonneg (hessian C N)
    (MatrixSquareCompletion.hessian_posDef C N hC hUnit hDomain).posSemidef
    ((point p - center C N B ell (point w)) 0)
    ((point p - center C N B ell (point w)) 1)
  rw [quadratic_vector, quadratic_vector] at hSquare
  change quadratic N ((sample w p).1 : ℝ) ((sample w p).2 : ℝ) + cost p = _ at hSquare
  linarith only [hSquare, hNonneg, hBound, hAt]

/-- Testing the two coordinate floors of the real center gives the
uniform upper bound, without assuming a separate quadratic lattice minimum. -/
theorem minimum_upper_bound
    (C N B : Matrix (Fin 2) (Fin 2) ℝ) (hC : C.IsSymm) (hUnit : IsUnit C)
    (hDomain : (N + C⁻¹).PosDef) (ell : Fin 2 → ℝ)
    (g : ℤ × ℤ → ℝ) (sample : ℤ × ℤ → ℤ × ℤ → ℤ × ℤ) (cost : ℤ × ℤ → ℝ)
    (hSample : ∀ w p, point (sample w p) = B *ᵥ point w - C *ᵥ point p)
    (hCost : ∀ p, cost p = MatrixSquareCompletion.quadratic C (point p) + ell ⬝ᵥ point p)
    (K : ℝ) (hUpper : ∀ x y : ℤ, g (x, y) ≤ quadratic N (x : ℝ) (y : ℝ) + K)
    (w : ℤ × ℤ) (T : ℝ)
    (hMinimum : ∀ p : ℤ × ℤ, T ≤ g (sample w p) + cost p) :
    T ≤ base C N B ell (point w) + entryBound (hessian C N) + K := by
  let v := center C N B ell (point w)
  let p : ℤ × ℤ := (⌊v 0⌋, ⌊v 1⌋)
  have hBound := hUpper (sample w p).1 (sample w p).2
  have hAt := hMinimum p
  have hSquare := MatrixSquareCompletion.objective_eq_completed_square
    C N B hC hUnit hDomain ell (point w) (point p)
  rw [add_assoc, ← hSample w p, ← hCost p, quadratic_vector, quadratic_vector] at hSquare
  have hRounded := (abs_le.mp
    (LatticeQuadraticRounding.rounded_quadratic_bound (hessian C N) (v 0) (v 1))).2
  change quadratic N ((sample w p).1 : ℝ) ((sample w p).2 : ℝ) + cost p =
    quadratic (hessian C N) ((⌊v 0⌋ : ℝ) - v 0) ((⌊v 1⌋ : ℝ) - v 1) +
      base C N B ell (point w) at hSquare
  linarith only [hBound, hAt, hSquare, hRounded]

private theorem quadratic_scalar_perturbation
    (M : Matrix (Fin 2) (Fin 2) ℝ) (t x y : ℝ) :
    quadratic (M + t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) x y =
      quadratic M x y + (t / 2) * (x ^ 2 + y ^ 2) := by
  norm_num [quadratic, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  ring

/-- The exact attained lattice transport has the computed leading matrix.
Only the affine sampling and quadratic cost identities are assumed; no
periodic error, output growth estimate, or regularity of g is required. -/
theorem quadratic_growth_of_minimum
    (C M B : Matrix (Fin 2) (Fin 2) ℝ) (hC : C.IsSymm) (hUnit : IsUnit C)
    (hDomain : (M + C⁻¹).PosDef) (ell : Fin 2 → ℝ)
    (g T : ℤ × ℤ → ℝ) (sample : ℤ × ℤ → ℤ × ℤ → ℤ × ℤ) (cost : ℤ × ℤ → ℝ)
    (hSample : ∀ w p, point (sample w p) = B *ᵥ point w - C *ᵥ point p)
    (hCost : ∀ p, cost p = MatrixSquareCompletion.quadratic C (point p) + ell ⬝ᵥ point p)
    (hMinimum : ∀ w : ℤ × ℤ, ∃ p : ℤ × ℤ,
      T w = g (sample w p) + cost p ∧ ∀ q : ℤ × ℤ, T w ≤ g (sample w q) + cost q)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |g (x, y) - quadratic M (x : ℝ) (y : ℝ)| ≤ δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |T (x, y) - quadratic (MatrixInverseOrder.transportMatrix C⁻¹ B M)
          (x : ℝ) (y : ℝ)| ≤ δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  apply QuadraticSandwich.quadratic_growth_of_sandwich
  intro δ hδ
  obtain ⟨η, hη, hPerturb⟩ :=
    TransportMatrixContinuity.exists_scalar_radius_for_entry_bounds C⁻¹ B M hDomain δ hδ
  let t := η / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htSmall : |t| < η := by rw [abs_of_pos ht]; dsimp [t]; linarith
  have hNegSmall : |-t| < η := by simpa only [abs_neg] using htSmall
  obtain ⟨hLowerDomain, hLowerEntries⟩ := hPerturb (-t) hNegSmall
  obtain ⟨hUpperDomain, hUpperEntries⟩ := hPerturb t htSmall
  let L := M + (-t) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  let U := M + t • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  obtain ⟨K, _, hError⟩ := QuadraticErrorEnvelope.global_envelope_of_eventual_bound
    (fun z => g z - quadratic M (z.1 : ℝ) (z.2 : ℝ)) hGrowth (t / 2) (by positivity)
  have hLower : ∀ x y : ℤ, quadratic L (x : ℝ) (y : ℝ) - K ≤ g (x, y) := by
    intro x y
    have h := (abs_le.mp (hError x y)).1
    dsimp [L]
    rw [quadratic_scalar_perturbation]
    linarith only [h]
  have hUpper : ∀ x y : ℤ, g (x, y) ≤ quadratic U (x : ℝ) (y : ℝ) + K := by
    intro x y
    have h := (abs_le.mp (hError x y)).2
    dsimp [U]
    rw [quadratic_scalar_perturbation]
    linarith only [h]
  obtain ⟨a, b, d, hBaseLower⟩ := base_affine C L B hC hUnit hLowerDomain ell
  obtain ⟨a', b', d', hBaseUpper⟩ := base_affine C U B hC hUnit hUpperDomain ell
  refine ⟨MatrixInverseOrder.transportMatrix C⁻¹ B L,
    MatrixInverseOrder.transportMatrix C⁻¹ B U, a, b, d - K,
    a', b', d' + entryBound (hessian C U) + K, hLowerEntries, hUpperEntries, ?_, ?_⟩
  · intro x y
    obtain ⟨p, hAt, _⟩ := hMinimum (x, y)
    have hBound := minimum_lower_bound C L B hC hUnit hLowerDomain ell g sample cost
      hSample hCost K hLower (x, y) (T (x, y)) ⟨p, hAt⟩
    change base C L B ell ![(x : ℝ), (y : ℝ)] - K ≤ T (x, y) at hBound
    rw [hBaseLower] at hBound
    linarith only [hBound]
  · intro x y
    obtain ⟨_, _, hMinimumBound⟩ := hMinimum (x, y)
    have hBound := minimum_upper_bound C U B hC hUnit hUpperDomain ell g sample cost
      hSample hCost K hUpper (x, y) (T (x, y)) hMinimumBound
    change T (x, y) ≤ base C U B ell ![(x : ℝ), (y : ℝ)] +
      entryBound (hessian C U) + K at hBound
    rw [hBaseUpper] at hBound
    linarith only [hBound]

end FLattice.Auxiliary.QuadraticTransportGrowth
