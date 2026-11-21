import FLatticePaper.GeneralK.Harmonic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace FLatticePaper.GeneralK

open Construction

private theorem phasePrimitive_secondDifference_pos {k : ℤ} (hk : 0 < k) (n : ℤ) :
    phasePrimitive k (n - 1) + phasePrimitive k (n + 1) - 2 * phasePrimitive k n =
      if n % k = 0 then 1 else 0 := by
  by_cases h : 2 ≤ k
  · exact phasePrimitive_secondDifference h n
  · have hk₁ : k = 1 := by omega
    subst k
    simp only [phasePrimitive, Int.ediv_one, Int.emod_one, ite_true, one_mul, mul_zero, add_zero]
    apply (mul_right_inj' (show (2 : ℤ) ≠ 0 by decide)).mp
    linear_combination two_mul_chooseTwo (n - 1) + two_mul_chooseTwo (n + 1) - 2 * two_mul_chooseTwo n

/-- An integer second-difference primitive built by superposing the exact
phase indicators, translated to the first column of the period. -/
def periodicPrimitive {period : ℕ} (weights : Fin period → ℤ) (origin column : ℤ) : ℤ :=
  ∑ i : Fin period, weights i * phasePrimitive period (column - origin - (i.val : ℤ))

theorem periodicPrimitive_secondDifference {period : ℕ} (weights : Fin period → ℤ) (origin column : ℤ)
    (index : Fin period) (hindex : (index.val : ℤ) = (column - origin) % (period : ℤ)) :
    periodicPrimitive weights origin (column - 1) + periodicPrimitive weights origin (column + 1) -
      2 * periodicPrimitive weights origin column = weights index := by
  have hpos : (0 : ℤ) < (period : ℤ) := by exact_mod_cast Nat.zero_lt_of_lt index.isLt
  have hterm (i : Fin period) :
      ((column - origin - (i.val : ℤ)) % (period : ℤ) = 0) ↔ i = index := by
    have hi : (i.val : ℤ) < (period : ℤ) := by exact_mod_cast i.isLt
    rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero, ← hindex, Int.emod_eq_of_lt (by positivity) hi, Int.natCast_inj, Fin.val_inj]
    exact eq_comm
  unfold periodicPrimitive
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ i : Fin period, (if i = index then weights i else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := phasePrimitive_secondDifference_pos hpos (column - origin - (i.val : ℤ))
      simp only [hterm i] at h
      have hn : column - 1 - origin - (i.val : ℤ) = (column - origin - (i.val : ℤ)) - 1 := by ring
      have hp : column + 1 - origin - (i.val : ℤ) = (column - origin - (i.val : ℤ)) + 1 := by ring
      rw [hn, hp]
      calc
        _ = weights i * (phasePrimitive period (column - origin - (i.val : ℤ) - 1) +
            phasePrimitive period (column - origin - (i.val : ℤ) + 1) -
            2 * phasePrimitive period (column - origin - (i.val : ℤ))) := by ring
        _ = _ := by rw [h]; split <;> simp
    _ = _ := by simp

/-- The quadratic coefficient is the mean of the integer forcing over one
period. All deviations after subtracting one affine slope are bounded. -/
theorem periodicPrimitive_quadratic_bound {period : ℕ} (hperiod : 0 < period)
    (weights : Fin period → ℤ) (origin : ℤ) :
    ∃ tilt bound : ℝ, 0 ≤ bound ∧ ∀ column : ℤ,
      |(periodicPrimitive weights origin column : ℝ) -
        ((∑ i : Fin period, (weights i : ℝ)) / (period : ℝ)) * (column : ℝ) ^ 2 / 2 -
        tilt * (column : ℝ)| ≤ bound := by
  have hz : (0 : ℤ) < (period : ℤ) := by exact_mod_cast hperiod
  have hr : (0 : ℝ) < (period : ℝ) := by exact_mod_cast hperiod
  let offset (i : Fin period) : ℝ := (origin : ℝ) + (i.val : ℝ)
  let slope (i : Fin period) : ℝ := -offset i / (period : ℝ) - 1 / 2
  let constant (i : Fin period) : ℝ := offset i ^ 2 / (2 * (period : ℝ)) + offset i / 2
  let remainder (i : Fin period) (column : ℤ) : ℝ :=
    let r : ℝ := (((column - origin - (i.val : ℤ)) % (period : ℤ)) : ℤ)
    r * ((period : ℝ) - r) / (2 * (period : ℝ))
  let tilt := ∑ i : Fin period, (weights i : ℝ) * slope i
  let bound := ∑ i : Fin period, |(weights i : ℝ)| * (|constant i| + (period : ℝ))
  refine ⟨tilt, bound, Finset.sum_nonneg (fun _ _ => by positivity), fun column => ?_⟩
  have hterm (i : Fin period) : (phasePrimitive period (column - origin - (i.val : ℤ)) : ℝ) =
      (column : ℝ) ^ 2 / (2 * (period : ℝ)) + slope i * (column : ℝ) + constant i + remainder i column := by
    rw [cast_phasePrimitive hz]
    simp only [slope, constant, offset, remainder, Int.cast_sub, Int.cast_natCast]
    field_simp
    ring
  have hsum : (periodicPrimitive weights origin column : ℝ) -
      ((∑ i : Fin period, (weights i : ℝ)) / (period : ℝ)) * (column : ℝ) ^ 2 / 2 - tilt * (column : ℝ) =
    ∑ i : Fin period, (weights i : ℝ) * (constant i + remainder i column) := by
    simp only [periodicPrimitive, Int.cast_sum, Int.cast_mul, hterm, tilt, div_eq_mul_inv,
      Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add_right ?_ _)) (abs_nonneg _)
  let r : ℝ := (((column - origin - (i.val : ℤ)) % (period : ℤ)) : ℤ)
  have hlo : 0 ≤ r := by dsimp [r]; exact_mod_cast Int.emod_nonneg _ (ne_of_gt hz)
  have hhi : r ≤ (period : ℝ) := by
    dsimp [r]
    exact_mod_cast (Int.emod_lt_of_pos (column - origin - (i.val : ℤ)) hz).le
  change |r * ((period : ℝ) - r) / (2 * (period : ℝ))| ≤ _
  rw [abs_of_nonneg (by positivity [sub_nonneg.mpr hhi])]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (period : ℝ))).mpr
  have h := mul_le_mul_of_nonneg_left (show (period : ℝ) - r ≤ period by linarith) hlo
  nlinarith only [h, mul_le_mul_of_nonneg_right hhi hr.le, sq_nonneg (period : ℝ)]

end FLatticePaper.GeneralK
