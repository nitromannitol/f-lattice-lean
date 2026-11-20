import FLattice.Auxiliary.NativeAffineNormalization

/-!
# Algebraic normalization of a failed integer transport star

The cost has integral coefficients and symmetric Hessian. At an attained
central minimum, testing shifted indices at the two neighboring minima
gives the signed coset bounds. The extra unit comes from integer failure
of the target superharmonic inequality. No graph or growth premise is
needed for this algebraic step.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.TransportStarNormalization

/-- An arbitrary integral quadratic cost with its integer linear part. -/
def cost (A B C ℓ₁ ℓ₂ : ℤ) (p : ℤ × ℤ) : ℤ :=
  A * p.1 ^ 2 + B * p.1 * p.2 + C * p.2 ^ 2 + ℓ₁ * p.1 + ℓ₂ * p.2

/-- Sampling by the literal symmetric Hessian of the cost. -/
def samplePoint (A B C X Y : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (X - 2 * A * p.1 - B * p.2, Y - B * p.1 - 2 * C * p.2)

/-- The signed displacement minus a Hessian period. -/
def displacedPoint (A B C D₁ D₂ c : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (c * D₁ - 2 * A * p.1 - B * p.2, c * D₂ - B * p.1 - 2 * C * p.2)

/-- The exact quadratic cost increment, for all signed integer indices. -/
theorem cost_add (A B C ℓ₁ ℓ₂ : ℤ) (p₀ p : ℤ × ℤ) :
    cost A B C ℓ₁ ℓ₂ (p₀.1 + p.1, p₀.2 + p.2) - cost A B C ℓ₁ ℓ₂ p₀ =
      p₀.1 * (2 * A * p.1 + B * p.2) +
        p₀.2 * (B * p.1 + 2 * C * p.2) + cost A B C ℓ₁ ℓ₂ p := by
  simp only [cost]
  ring

/-- Exact objective expansion about any central index. -/
theorem objective_at_shifted_index
    (g : ℤ × ℤ → ℤ) (A B C ℓ₁ ℓ₂ X Y D₁ D₂ c : ℤ) (p₀ p : ℤ × ℤ) :
    g (samplePoint A B C (X + c * D₁) (Y + c * D₂) (p₀.1 + p.1, p₀.2 + p.2)) +
        cost A B C ℓ₁ ℓ₂ (p₀.1 + p.1, p₀.2 + p.2) =
      NativeAffineNormalization.normalized g
        (samplePoint A B C X Y p₀).1 (samplePoint A B C X Y p₀).2 p₀.1 p₀.2
        (displacedPoint A B C D₁ D₂ c p) +
      (g (samplePoint A B C X Y p₀) + cost A B C ℓ₁ ℓ₂ p₀) +
      c * (p₀.1 * D₁ + p₀.2 * D₂) + cost A B C ℓ₁ ℓ₂ p := by
  have hPoint :
      samplePoint A B C (X + c * D₁) (Y + c * D₂) (p₀.1 + p.1, p₀.2 + p.2) =
        ((displacedPoint A B C D₁ D₂ c p).1 + (samplePoint A B C X Y p₀).1,
          (displacedPoint A B C D₁ D₂ c p).2 + (samplePoint A B C X Y p₀).2) := by
    apply Prod.ext <;> simp only [samplePoint, displacedPoint] <;> ring
  rw [hPoint]
  simp only [NativeAffineNormalization.normalized, displacedPoint, samplePoint, cost]
  ring

/-- A failed integer target star gives the exact three signed coset bounds.
The lower-bound and attainment premises are the literal minimum properties,
to be supplied by the concrete transport construction. -/
theorem signed_bounds_of_failed_star
    (g : ℤ × ℤ → ℤ) (A B C ℓ₁ ℓ₂ X Y D₁ D₂ : ℤ)
    (T : ℤ → ℤ) (p₀ : ℤ × ℤ)
    (hLower : ∀ c : ℤ, c = -1 ∨ c = 0 ∨ c = 1 → ∀ p : ℤ × ℤ,
      T c ≤ g (samplePoint A B C (X + c * D₁) (Y + c * D₂) p) + cost A B C ℓ₁ ℓ₂ p)
    (hAttained : T 0 = g (samplePoint A B C X Y p₀) + cost A B C ℓ₁ ℓ₂ p₀)
    (hFailure : 2 * T 0 < T (-1) + T 1) :
    ∀ c : ℤ, c = -1 ∨ c = 0 ∨ c = 1 → ∀ p : ℤ × ℤ,
      c * (T 1 - T 0 - (p₀.1 * D₁ + p₀.2 * D₂)) +
        (if c = -1 then 1 else 0) - cost A B C ℓ₁ ℓ₂ p ≤
      NativeAffineNormalization.normalized g
        (samplePoint A B C X Y p₀).1 (samplePoint A B C X Y p₀).2 p₀.1 p₀.2
        (displacedPoint A B C D₁ D₂ c p) := by
  intro c hc p
  have hBound := hLower c hc (p₀.1 + p.1, p₀.2 + p.2)
  rw [objective_at_shifted_index, ← hAttained] at hBound
  rcases hc with rfl | rfl | rfl <;> norm_num at hBound ⊢ <;> omega

end FLattice.Auxiliary.TransportStarNormalization
