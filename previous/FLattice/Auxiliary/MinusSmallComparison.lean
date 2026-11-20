import FLattice.Auxiliary.MinusSmallClock
import FLattice.Auxiliary.MinusSmallSpecialValues
import FLattice.Auxiliary.MinusSmallQuadratic
import FLattice.Auxiliary.BoundedRankComparison
import Mathlib.Data.Set.Finite.Lemmas

/-!
# The smallest-minus lower comparisons on the whole plane

The complete eight-class clock discharges the integer minimum argument.
The comparison requires no periodicity of the unknown. Its growth version
retains only the source quadratic asymptotic, actual inverse positivity,
native superharmonicity and all signed prescribed-coset lower bounds.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary.MinusSmallProfile

private theorem deficit_eq_residual (ε : Fin 2) (x y : ℤ) :
    incomingDeficit ε x y =
      0 - ((∑ i : Fin 2, profile ε (incomingPoint ε x y i).1 (incomingPoint ε x y i).2) -
        2 * profile ε x y) := by
  rw [incomingPoint_sum ε (fun z => profile ε z.1 z.2)]
  unfold incomingDeficit
  split_ifs <;> ring

/-- Actual native superharmonicity, the complete signed pin inequalities and
an integer gap bounded below imply the literal smallest-minus profile bound. -/
theorem profile_le_of_bounded_gap
    (ε : Fin 2) (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + (ε.val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hPrescribed : ∀ a b : ℤ, 1 - cost a b ≤
      h (prescribedX ε - 6 * a - 2 * b, prescribedY ε - 2 * a - 2 * b))
    (hGapBounded : ∃ B : ℤ, ∀ z : ℤ × ℤ, B ≤ h z - profile ε z.1 z.2) :
    ∀ z : ℤ × ℤ, profile ε z.1 z.2 ≤ h z := by
  apply le_of_bounded_gap_and_rank
    (fun z : ℤ × ℤ => incomingPoint ε z.1 z.2) h
    (fun z => profile ε z.1 z.2) (fun _ => 0)
    (fun z => clock ε z.1 z.2) {z | prescribedCoset ε z.1 z.2} hGapBounded
  · exact ⟨0, fun z => clock_nonneg ε z.1 z.2⟩
  · rintro ⟨x, y⟩
    have hStar := hSuperharmonic x y
    rw [incomingPoint_sum]
    norm_num only [Fintype.card_fin, Nat.cast_ofNat]
    omega
  · rintro ⟨x, y⟩ ⟨a, b, rfl, rfl⟩
    rw [profile_prescribed_coset]
    exact hPrescribed a b
  · rintro ⟨x, y⟩ hNotPin
    obtain ⟨S, hCount, hClock⟩ := clock_selected ε x y hNotPin
    refine ⟨S, ?_, hClock⟩
    rw [deficit_eq_residual] at hCount
    simpa only [Fintype.card_fin, Nat.cast_ofNat] using hCount

private theorem gap_bounded_of_finite_nonpositive_sublevel
    (g : ℤ × ℤ → ℤ) (hFinite : {z | g z ≤ 0}.Finite) :
    ∃ B : ℤ, ∀ z, B ≤ g z := by
  by_cases hNonempty : {z | g z ≤ 0}.Nonempty
  · obtain ⟨z, hz, hMin⟩ := Set.exists_min_image {z | g z ≤ 0} g hFinite hNonempty
    refine ⟨g z, ?_⟩
    intro w
    by_cases hw : g w ≤ 0
    · exact hMin w hw
    · change g z ≤ 0 at hz
      omega
  · refine ⟨0, ?_⟩
    intro z
    have hz : ¬g z ≤ 0 := fun hz => hNonempty ⟨z, hz⟩
    omega

/-- The source's original quadratic growth supplies the required gap bound;
there is no extra finite-set, periodicity, or comparison hypothesis. -/
theorem profile_le_of_quadratic_growth
    (ε : Fin 2) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + (ε.val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + periodMatrix⁻¹).PosDef)
    (hPrescribed : ∀ a b : ℤ, 1 - cost a b ≤
      h (prescribedX ε - 6 * a - 2 * b, prescribedY ε - 2 * a - 2 * b)) :
    ∀ z : ℤ × ℤ, profile ε z.1 z.2 ≤ h z := by
  apply profile_le_of_bounded_gap ε h hSuperharmonic hPrescribed
  apply gap_bounded_of_finite_nonpositive_sublevel
  simpa only [add_zero] using
    finite_shifted_gap_sublevels_of_quadratic_growth ε 0 0 h M hGrowth hPositive 0

end FLattice.Auxiliary.MinusSmallProfile
