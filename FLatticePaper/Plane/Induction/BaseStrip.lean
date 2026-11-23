import FLatticePaper.Plane.Induction.BaseFields
import FLatticePaper.Plane.Induction.ReciprocalInputs
import FLatticePaper.Construction.StaircaseStrips

/-! Task 41, step (1): the zero strip of the reciprocal standard field at `3^k`.

The zero strip of `Fp = quarterTurnField F` at `F = reciprocalField k` is the longitudinal strip of `F` under `Z`, where
`F = centeredQuarterTurnCorrection` (`stairEven_eq_harmonic_of_longitudinal`), and the correction cancels the harmonic grid at the
quarter turn (`i3_corr_add_harmonic`). The even line is outside this strip and is not proved here. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper Construction

/-- The cancellation of the quarter-turn correction against the harmonic grid, in generic variables. -/
theorem corr_cancel_aux (T Q ρ : ℤ) (h : Q % 4 = ρ) : T - Q / 4 + (Q - 4 * T - ρ) / 4 = 0 := by
  omega

/-- The centred correction at the quarter turn cancels the harmonic grid: `corr(Z x) + h0(x) = 0`. -/
theorem i3_corr_add_harmonic (x1 x2 : ℤ) :
    centeredQuarterTurnCorrection (-x2, x1 - 1) + harmonicGrid (x1, x2) = 0 := by
  have hT : 2 * chooseTwo (-x2) = x2 ^ 2 + x2 := by
    have := two_mul_chooseTwo (-x2)
    linear_combination this
  have hsq : (-x2 - (x1 - 1) - 1) ^ 2 = (x1 + x2) ^ 2 := by ring
  have hnum : x1 ^ 2 + 2 * x1 * x2 - x2 ^ 2 - 2 * x2 - (x1 + x2) % 2 =
      (x1 + x2) ^ 2 - 4 * chooseTwo (-x2) - (x1 + x2) % 2 := by
    linear_combination 2 * hT
  have hmod : (x1 + x2) ^ 2 % 4 = (x1 + x2) % 2 := by
    rcases Int.even_or_odd (x1 + x2) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have h4 : (x1 + x2) ^ 2 = 4 * (m * m) := by rw [hm]; ring
      rw [h4, hm]
      omega
    · have h4 : (x1 + x2) ^ 2 = 4 * (m * m + m) + 1 := by rw [hm]; ring
      rw [h4, hm]
      omega
  unfold centeredQuarterTurnCorrection harmonicGrid
  rw [hsq, hnum]
  exact corr_cancel_aux _ _ _ hmod

/-- **The zero strip of the reciprocal standard field** (in the coordinates of `Fp`): `Fp = 0` on the strip. -/
theorem reciprocal_zeroStrip (k : ℕ) (x : Site)
    (hlo : 1 - ((k : ℤ) + 2) ≤ ((k : ℤ) + 1) * x.1 - ((k : ℤ) + 2) * x.2)
    (hhi : ((k : ℤ) + 1) * x.1 - ((k : ℤ) + 2) * x.2 ≤ ((k : ℤ) + 1) + 2 * ((k : ℤ) + 2) - 1) :
    quarterTurnField (standardField (List.replicate k Digit.three)) x = 0 := by
  obtain ⟨hagree, hper⟩ := reciprocalField_spec k
  rw [standardField_threes]
  unfold quarterTurnField
  rw [i3_mapSite_eq]
  have hden := stairEven_valid_reciprocal k
  have hlo' : 1 - 2 * (2 * (k : ℤ) + 3) ≤
      (2 * (k : ℤ) + 3 + 1) * (i3Z x).1 + (2 * (k : ℤ) + 3 - 1) * (i3Z x).2 := by
    simp only [i3Z]
    nlinarith
  have hhi' : (2 * (k : ℤ) + 3 + 1) * (i3Z x).1 + (2 * (k : ℤ) + 3 - 1) * (i3Z x).2 ≤
      2 * (2 * (k : ℤ) + 3) + 1 := by
    simp only [i3Z]
    nlinarith
  have hc := stairEven_eq_harmonic_of_longitudinal hden hagree hper (i3Z x) hlo' hhi'
  rw [hc]
  exact i3_corr_add_harmonic x.1 x.2

/-- The `zeroStripInterval` field of the strong estimates at `3^k`: the strip in the parameters `parentN`, `parentD` of the
reciprocal child `1/(2k+3)`, which are `k+1` and `k+2`. -/
theorem reciprocal_zeroStripInterval (k : ℕ) : ∀ x : Site,
    1 - parentD (List.replicate k Digit.three) ≤
        parentN (List.replicate k Digit.three) * x.1 - parentD (List.replicate k Digit.three) * x.2 →
      parentN (List.replicate k Digit.three) * x.1 - parentD (List.replicate k Digit.three) * x.2 ≤
        parentN (List.replicate k Digit.three) + 2 * parentD (List.replicate k Digit.three) - 1 →
      quarterTurnField (standardField (List.replicate k Digit.three)) x = 0 := by
  intro x hlo hhi
  have hN : parentN (List.replicate k Digit.three) = (k : ℤ) + 1 := by
    unfold parentN
    show ((reciprocalFrame k).child.den - (reciprocalFrame k).child.num) / 2 = (k : ℤ) + 1
    rw [reciprocal_child_den, reciprocal_child_num]
    omega
  have hD : parentD (List.replicate k Digit.three) = (k : ℤ) + 2 := by
    unfold parentD
    show ((reciprocalFrame k).child.den + (reciprocalFrame k).child.num) / 2 = (k : ℤ) + 2
    rw [reciprocal_child_den, reciprocal_child_num]
    omega
  rw [hN, hD] at hlo hhi
  exact reciprocal_zeroStrip k x hlo hhi

end FLatticePaper.Induction
