import FLattice.Auxiliary.QuadraticGap
import FLattice.Auxiliary.BoundedRankComparison
import Mathlib.Algebra.Order.Floor.Defs

/-!
# Attainment of integer objectives through a quadratic reference

An integer objective need only be bounded below to attain its minimum.
An exact cost identity expresses it as a supercritical quadratic gap at
the sampled lattice points. Properness of that gap supplies the bound;
the sampling map need not be injective. The exact cost identity is an
explicit premise of this generic helper and must be proved for a transport.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.QuadraticCostAttainment

private theorem bounded_below_of_finite_nonpositive_sublevel
    (g : ℤ × ℤ → ℝ) (hFinite : {z | g z ≤ 0}.Finite) :
    ∃ B : ℝ, ∀ z, B ≤ g z := by
  by_cases hNonempty : {z | g z ≤ 0}.Nonempty
  · obtain ⟨z, hz, hMin⟩ := Set.exists_min_image {z | g z ≤ 0} g hFinite hNonempty
    refine ⟨g z, ?_⟩
    intro w
    by_cases hw : g w ≤ 0
    · exact hMin w hw
    · change g z ≤ 0 at hz
      exact hz.trans (le_of_lt (lt_of_not_ge hw))
  · refine ⟨0, ?_⟩
    intro z
    have hz : ¬g z ≤ 0 := fun hz => hNonempty ⟨z, hz⟩
    exact le_of_lt (lt_of_not_ge hz)

/-- An integer cost whose literal sampled-coordinate quadratic is strictly
coercive with the input growth gives an attained finite integer minimum. -/
theorem exists_minimizer_of_quadratic_cost {I : Type*} [Nonempty I]
    (h : ℤ × ℤ → ℤ) (input : I → ℤ × ℤ) (cost : I → ℤ)
    (M N : Matrix (Fin 2) (Fin 2) ℝ) (a b d : ℝ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + N).PosDef)
    (hCost : ∀ p : I, (cost p : ℝ) = (1 / 2 : ℝ) *
      (((input p).1 : ℝ) * N 0 0 * ((input p).1 : ℝ) +
        ((input p).1 : ℝ) * N 0 1 * ((input p).2 : ℝ) +
        ((input p).2 : ℝ) * N 1 0 * ((input p).1 : ℝ) +
        ((input p).2 : ℝ) * N 1 1 * ((input p).2 : ℝ)) -
      a * ((input p).1 : ℝ) - b * ((input p).2 : ℝ) - d) :
    ∃ p : I, ∀ q : I, h (input p) + cost p ≤ h (input q) + cost q := by
  let u : ℤ × ℤ → ℝ := fun z => -(1 / 2 : ℝ) *
    ((z.1 : ℝ) * N 0 0 * (z.1 : ℝ) + (z.1 : ℝ) * N 0 1 * (z.2 : ℝ) +
      (z.2 : ℝ) * N 1 0 * (z.1 : ℝ) + (z.2 : ℝ) * N 1 1 * (z.2 : ℝ)) +
    a * (z.1 : ℝ) + b * (z.2 : ℝ) + d
  have hFinite := QuadraticGap.finite_sublevels (fun z : ℤ × ℤ => (h z : ℝ))
    u M N a b d 0 hGrowth (fun x y => by simp only [u, sub_self, abs_zero, le_refl]) hPositive 0
  obtain ⟨B, hB⟩ := bounded_below_of_finite_nonpositive_sublevel
    (fun z => (h z : ℝ) - u z) hFinite
  let objective : I → ℤ := fun p => h (input p) + cost p
  have hBounded : ∃ L : ℤ, ∀ p : I, L ≤ objective p := by
    refine ⟨⌊B⌋, ?_⟩
    intro p
    have hIdentity : (objective p : ℝ) = (h (input p) : ℝ) - u (input p) := by
      dsimp [objective]
      rw [Int.cast_add, hCost]
      dsimp [u]
      ring
    have hReal : (⌊B⌋ : ℝ) ≤ (objective p : ℝ) := by
      rw [hIdentity]
      exact (Int.floor_le B).trans (hB (input p))
    exact_mod_cast hReal
  obtain ⟨p, _, hMin⟩ := exists_min_image_of_int_bounded_below
    Set.univ objective Set.univ_nonempty
    (by obtain ⟨L, hL⟩ := hBounded; exact ⟨L, fun q _ => hL q⟩)
  exact ⟨p, fun q => hMin q (Set.mem_univ q)⟩

end FLattice.Auxiliary.QuadraticCostAttainment
