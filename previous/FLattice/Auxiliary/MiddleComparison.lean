import FLattice.Auxiliary.MiddleDeficit
import FLattice.Auxiliary.MiddleSpecialValues
import FLattice.Auxiliary.MiddleQuadratic
import FLattice.Auxiliary.MiddleRank
import FLattice.Auxiliary.FiniteComparison

/-!
# Global lower comparison for both smallest-coefficient profiles

The exact physical deficit table and the two simple directional ranks
exclude a finite negative minimum. The conclusion has no local table,
rank or periodicity premise. The source-growth version derives the finite
gap sublevels from the literal period matrix and its actual inverse.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MiddleProfile

/-- The actual deficit is the residual at the two indexed physical inputs. -/
theorem incomingDeficit_eq_inputs (ε : Fin 2) (x y : ℤ) :
    incomingDeficit ε x y = 2 * profile ε x y -
      profile ε (incomingPoint ε x y 0).1 (incomingPoint ε x y 0).2 -
      profile ε (incomingPoint ε x y 1).1 (incomingPoint ε x y 1).2 := by
  have hSum := incomingPoint_sum ε (fun z => profile ε z.1 z.2) x y
  rw [Fin.sum_univ_two] at hSum
  unfold incomingDeficit
  split_ifs at hSum ⊢ <;> dsimp at hSum <;> omega

/-- Both native parities satisfy the lower comparison when every gap
sublevel is finite and the original signed prescribed values hold. -/
theorem profile_le_of_finite_sublevels
    (ε : Fin 2) (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + (ε.val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hPrescribed : ∀ a b : ℤ,
      1 - (3 * a ^ 2 + 2 * a * b + b ^ 2 + a) ≤
        h (-2 + (ε.val : ℤ) - 6 * a - 2 * b, -1 + (ε.val : ℤ) - 2 * a - 2 * b))
    (hFinite : ∀ t : ℤ, {z : ℤ × ℤ | h z - profile ε z.1 z.2 ≤ t}.Finite) :
    ∀ z : ℤ × ℤ, profile ε z.1 z.2 ≤ h z := by
  let u : ℤ × ℤ → ℤ := fun z => profile ε z.1 z.2
  let gap : ℤ × ℤ → ℤ := fun z => h z - u z
  let sublevel : Set (ℤ × ℤ) := {z | gap z ≤ gap (0, 0)}
  obtain ⟨z, hz, hMin⟩ := Set.exists_min_image sublevel gap
    (hFinite (gap (0, 0))) ⟨(0, 0), by change gap (0, 0) ≤ gap (0, 0); exact le_rfl⟩
  have hGlobalMin : ∀ w, gap z ≤ gap w := by
    intro w
    by_cases hw : gap w ≤ gap (0, 0)
    · exact hMin w hw
    · change gap z ≤ gap (0, 0) at hz
      omega
  have hLevelFinite : {w : ℤ × ℤ | gap w = gap z}.Finite :=
    (hFinite (gap z)).subset (fun w hw => le_of_eq hw)
  apply le_of_finite_minimum_rank
    (fun z : ℤ × ℤ => incomingPoint ε z.1 z.2 0)
    (fun z : ℤ × ℤ => incomingPoint ε z.1 z.2 1)
    h u (fun z => physicalRank ε z.1 z.2)
    {z | prescribedCoset ε z.1 z.2} (gap z)
    hLevelFinite hGlobalMin ⟨z, rfl⟩
  · rintro ⟨x, y⟩
    have hStar := hSuperharmonic x y
    have hSum := incomingPoint_sum ε h x y
    rw [Fin.sum_univ_two] at hSum
    rw [hSum]
    exact hStar
  · rintro ⟨x, y⟩ ⟨a, b, rfl, rfl⟩
    dsimp [u]
    rw [profile_prescribed_coset]
    exact hPrescribed a b
  · rintro ⟨x, y⟩ hNotPrescribed
    dsimp [u]
    rw [← incomingDeficit_eq_inputs]
    exact incomingDeficit_zero_or_one ε x y hNotPrescribed
  · rintro ⟨x, y⟩ _ _
    obtain ⟨i, hi⟩ := (physicalRank_decreasing_inputs ε x y).1
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro ⟨x, y⟩ _ hOne
    have hActual : incomingDeficit ε x y = 1 := by
      rw [incomingDeficit_eq_inputs]
      exact hOne
    have hBoth := (physicalRank_decreasing_inputs ε x y).2
      (even_sum_of_incomingDeficit_eq_one ε x y hActual)
    exact ⟨hBoth 0, hBoth 1⟩

/-- The original quadratic growth and strict inverse-matrix domination
provide all gap-finiteness inputs to the two-parity lower comparison. -/
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
    (hPrescribed : ∀ a b : ℤ,
      1 - (3 * a ^ 2 + 2 * a * b + b ^ 2 + a) ≤
        h (-2 + (ε.val : ℤ) - 6 * a - 2 * b, -1 + (ε.val : ℤ) - 2 * a - 2 * b)) :
    ∀ z : ℤ × ℤ, profile ε z.1 z.2 ≤ h z := by
  apply profile_le_of_finite_sublevels ε h hSuperharmonic hPrescribed
  simpa only [add_zero] using
    finite_shifted_gap_sublevels_of_quadratic_growth ε 0 0 h M hGrowth hPositive

end FLattice.Auxiliary.MiddleProfile
