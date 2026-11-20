import FLattice.Auxiliary.MiddleComparison

/-!
# The negative prescribed coset for both smallest-coefficient profiles

The native parity is unchanged by translation through twice Dε. The gap
finiteness needed after translation follows from the original unknown's
growth and the arbitrary-shift quadratic estimate already proved.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MiddleProfile

/-- The original negative pin data give the translated lower profile in
both native parities, without a translated-growth assumption. -/
theorem negative_shift_comparison_of_quadratic_growth
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
        h (2 - (ε.val : ℤ) - 6 * a - 2 * b, 1 - (ε.val : ℤ) - 2 * a - 2 * b)) :
    ∀ x y : ℤ,
      profile ε (x + 2 * (-2 + (ε.val : ℤ))) (y + 2 * (-1 + (ε.val : ℤ))) ≤
        h (x, y) := by
  let a : ℤ := 2 * (-2 + (ε.val : ℤ))
  let b : ℤ := 2 * (-1 + (ε.val : ℤ))
  let f : ℤ × ℤ → ℤ := fun z => h (z.1 - a, z.2 - b)
  have hEven : (a + b) % 2 = 0 := by dsimp [a, b]; omega
  have hfSuperharmonic : ∀ x y : ℤ,
      (if (x + y + (ε.val : ℤ)) % 2 = 0 then f (x - 1, y) + f (x + 1, y)
        else f (x, y - 1) + f (x, y + 1)) ≤ 2 * f (x, y) := by
    intro x y
    have hSH := hSuperharmonic (x - a) (y - b)
    have hParity : (x - a + (y - b) + (ε.val : ℤ)) % 2 =
        (x + y + (ε.val : ℤ)) % 2 := by omega
    rw [hParity] at hSH
    dsimp [f]
    simpa only [show x - 1 - a = x - a - 1 by omega,
      show x + 1 - a = x - a + 1 by omega,
      show y - 1 - b = y - b - 1 by omega,
      show y + 1 - b = y - b + 1 by omega] using hSH
  have hfPins : ∀ i j : ℤ,
      1 - (3 * i ^ 2 + 2 * i * j + j ^ 2 + i) ≤
        f (-2 + (ε.val : ℤ) - 6 * i - 2 * j,
          -1 + (ε.val : ℤ) - 2 * i - 2 * j) := by
    intro i j
    dsimp [f, a, b]
    convert hPrescribed i j using 1
    congr 2 <;> ring
  have hOriginalFinite := finite_shifted_gap_sublevels_of_quadratic_growth
    ε a b h M hGrowth hPositive
  have hfFinite : ∀ t : ℤ, {z : ℤ × ℤ | f z - profile ε z.1 z.2 ≤ t}.Finite := by
    intro t
    apply ((hOriginalFinite t).image (fun w : ℤ × ℤ => (w.1 + a, w.2 + b))).subset
    intro z hz
    refine ⟨(z.1 - a, z.2 - b), ?_, ?_⟩
    · simpa only [Set.mem_setOf_eq, sub_add_cancel] using hz
    · apply Prod.ext
      · dsimp
        omega
      · dsimp
        omega
  have hfLower := profile_le_of_finite_sublevels ε f hfSuperharmonic hfPins hfFinite
  intro x y
  have hBound := hfLower (x + a, y + b)
  simpa only [f, Prod.fst, Prod.snd, add_sub_cancel_right] using hBound

end FLattice.Auxiliary.MiddleProfile
