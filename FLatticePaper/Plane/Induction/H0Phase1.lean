import FLatticePaper.Plane.Induction.PsiCalibration
import FLatticePaper.Plane.Induction.PhaseOneA
import FLatticePaper.Plane.Induction.RootCalibration
import FLatticePaper.Plane.Induction.ArcPsi
import FLatticePaper.Plane.Induction.Q3VStar

/-! `Ψ` at the reflected prescribed neighbours of `H_0` in phase one, for `η = +1` and for `η = −1` with `N ≥ 2`.

With `z = reflH (H_0 + (0,−η)) = (d, n − 1 + η)`: the A part vanishes by the harmonic strip and `harmonicGrid_Z`; the C part is the
sheet formula at the shifted point `x = z − (n_q, 2n_q + d_q)`; the conjugate packet reflection at the centre sends `i3Z x` into the zero
strip, so `G(i3Z x) = tGrade − symmetryConstant`; and the harmonic numerator of `x` equals `−4·(tGrade − symc + slope + c_e)` modulo the
parent relation `N d_q − n_q D = 1`. The pieces are separate lemmas so that each declaration builds within the default heartbeats. -/

namespace FLatticePaper.H0Phase1

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.PsiCalibration

/-- The harmonic numerator identity of the reflected `H_0` neighbour, over the integers. -/
theorem harm_numer (Dp Np dq nq η b : ℤ) (hR : Np * dq - nq * Dp = 1) (hb : dq + nq = 2 * b) (hη : η = 1 ∨ η = -1) :
    (2 * Dp + dq - nq) ^ 2 + 2 * (2 * Dp + dq - nq) * (2 * Np + nq - 1 + η - (2 * nq + dq)) -
        (2 * Np + nq - 1 + η - (2 * nq + dq)) ^ 2 - 2 * (2 * Np + nq - 1 + η - (2 * nq + dq)) -
      ((2 * Dp + dq - nq) + (2 * Np + nq - 1 + η - (2 * nq + dq))) % 2 =
      4 * (-((Dp - Np) * (-(2 * Np + nq - 1 + η - (2 * nq + dq))) - (Dp + Np) * ((2 * Dp + dq - nq) - 1)
        - (Dp - Dp ^ 2 - 2 * Dp * Np + Np ^ 2) + (nq * (2 * Dp + dq) - dq * (2 * Np + nq - 1 + η))
        + ((dq - nq) * b + dq * nq - b) + 2)) := by
  have hpar : ((2 * Dp + dq - nq) + (2 * Np + nq - 1 + η - (2 * nq + dq))) % 2 = 0 := by
    rcases hη with rfl | rfl <;> omega
  have he : dq * dq + 2 * dq * nq - nq * nq - dq - nq = 2 * ((dq - nq) * b + dq * nq - b) := by
    linear_combination (dq - nq - 1) * hb
  rw [hpar]
  rcases hη with rfl | rfl
  · linear_combination (-8 : ℤ) * hR - 2 * he
  · linear_combination (-8 : ℤ) * hR - 2 * he

/-- The parent division identity, over the integers. -/
theorem ce_div (dq nq b : ℤ) (hb : dq + nq = 2 * b) :
    (dq * dq + 2 * dq * nq - nq * nq - dq - nq) / 2 = (dq - nq) * b + dq * nq - b := by
  have he : dq * dq + 2 * dq * nq - nq * nq - dq - nq = 2 * ((dq - nq) * b + dq * nq - b) := by
    linear_combination (dq - nq - 1) * hb
  rw [he]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

/-- The A part: the harmonic strip at `i3Z z` for `z = (d, n − 1 + η)` in phase one. -/
theorem A_part {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (η : ℤ) (hη : η = 1 ∨ η = -1) (hN2 : η = 1 ∨ 2 ≤ (frameAt word).parents.odd.num) :
    (frameAt word).sheetA (FqW word) (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η) = 0 := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := FLatticePaper.PriceInputs.pdata h
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hR : (frameAt word).parents.odd.num * (frameAt word).parents.even.den - (frameAt word).parents.even.num * (frameAt word).parents.odd.den = 1 := heps.symm.trans hW1
  have hS := hSE.packet.strips
  unfold ChildFrame.sheetA
  rw [sheetShift_W1 word hW1, sub_zero]
  unfold FqW
  rw [quarterTurnField_apply]
  have hwin : standardField (conjWord word) (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η)) = harmonicGrid (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η)) := by
    apply hS.2
    · rw [sGrade_conj word h, hcd]
      unfold i3Z
      simp only
      rcases hη with rfl | rfl
      · nlinarith [hR]
      · have h2N : 2 ≤ (frameAt word).parents.odd.num := by
          rcases hN2 with h1 | h1
          · norm_num at h1
          · exact h1
        nlinarith [hR, h2N]
    · rw [sGrade_conj word h, hcd, hcn]
      unfold i3Z
      simp only
      rcases hη with rfl | rfl
      · nlinarith [hR]
      · have h2N : 2 ≤ (frameAt word).parents.odd.num := by
          rcases hN2 with h1 | h1
          · norm_num at h1
          · exact h1
        nlinarith [hR, h2N]
  rw [hwin, harmonicGrid_Z]
  ring

/-- The C part: the sheet formula at `z` in phase one, with the offset and the sibling slope. -/
theorem C_part {word : Word} (hW1 : (frameAt word).eps = 1) (η : ℤ) :
    (frameAt word).sheetC (FqW word) (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η) =
      standardField (conjWord word) (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))) + harmonicGrid (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den)) +
        ((frameAt word).parents.even.num * (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den) - (frameAt word).parents.even.den * (2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η)) +
        (((frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den - (frameAt word).parents.even.num) / 2 + 2) := by
  unfold ChildFrame.sheetC
  rw [sheetShift_W1 word hW1, sheetOffset_W1 word hW1, sheetConstant_W1 word hW1]
  simp only [sub_zero]
  have ex : (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η) - ((frameAt word).parents.even.num, 2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den) = (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den)) := by
    ext <;> simp
  rw [ex]
  unfold FqW
  rw [quarterTurnField_apply]
  unfold ChildFrame.siblingSlope
  simp only

/-- The packet reflection value at `i3Z x` in phase one: the conjugate's zero strip at the reflected point. -/
theorem refl_value {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    standardField (conjWord word) (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))) =
      (((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))).1 - ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))).2) - ((frameAt word).parents.odd.den - (frameAt word).parents.odd.den ^ 2 - 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num + (frameAt word).parents.odd.num ^ 2) := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := FLatticePaper.PriceInputs.pdata h
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hR : (frameAt word).parents.odd.num * (frameAt word).parents.even.den - (frameAt word).parents.even.num * (frameAt word).parents.odd.den = 1 := heps.symm.trans hW1
  have hS := hSE.packet.strips
  have hRf := hSE.packet.reflection
  have hcen : (frameAt (conjWord word)).centre = ((frameAt (conjWord word)).child.num + 1, 2 * (frameAt (conjWord word)).child.num + (frameAt (conjWord word)).child.den - 1) := by
    unfold ChildFrame.centre
    rw [ChildFrame.child_modifiedDeck_kernel, ChildFrame.child_modifiedDeck_transverse]
    ext <;> simp
    ring
  have hsymc : (frameAt (conjWord word)).symmetryConstant = (frameAt word).parents.odd.den - (frameAt word).parents.odd.den ^ 2 - 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num + (frameAt word).parents.odd.num ^ 2 := by
    unfold ChildFrame.symmetryConstant Fraction.periodDenominator
    rw [hcd, hcn]
    have e2 : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) - (((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) ^ 2 + 2 * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) - ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) ^ 2) =
        2 * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.den ^ 2 - 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num + (frameAt word).parents.odd.num ^ 2) := by ring
    rw [e2]
    omega
  have hwin : 1 - (frameAt (conjWord word)).child.den ≤ (frameAt (conjWord word)).tGrade ((frameAt (conjWord word)).centre - i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))) ∧
      (frameAt (conjWord word)).tGrade ((frameAt (conjWord word)).centre - i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))) ≤ (frameAt (conjWord word)).child.num + 2 * (frameAt (conjWord word)).child.den - 1 := by
    rw [hcen, tGrade_conj word h, hcd, hcn]
    unfold i3Z
    simp only [Prod.fst_sub, Prod.snd_sub]
    rcases hη with rfl | rfl
    · constructor <;> nlinarith [hR, hN1, hD2, hND]
    · constructor <;> nlinarith [hR, hN1, hD2, hND]
  have hzero : standardField (conjWord word) ((frameAt (conjWord word)).centre - i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))) = 0 := hS.1 _ hwin.1 hwin.2
  have hRe := hRf (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den)))
  rw [hzero, tGrade_conj word h, hsymc] at hRe
  linarith

/-- **The phase-one H_0 calibration.** `Ψ(reflH(H_0 + (0,−η))) = 0`, by the A part, the C formula, the reflection value,
the parent division and the harmonic numerator identity. -/
theorem sheetPsi_H0_refl_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (η : ℤ) (hη : η = 1 ∨ η = -1) (hN2 : η = 1 ∨ 2 ≤ (frameAt word).parents.odd.num) :
    sheetPsi word (FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η))) = 0 := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := FLatticePaper.PriceInputs.pdata h
  obtain ⟨hco1, hco2⟩ := (frameAt word).child_odd
  obtain ⟨b, hb⟩ : ∃ b : ℤ, (frameAt word).parents.even.den + (frameAt word).parents.even.num = 2 * b := by
    have hev : ((frameAt word).parents.even.den + (frameAt word).parents.even.num) % 2 = 0 := by omega
    exact ⟨((frameAt word).parents.even.den + (frameAt word).parents.even.num) / 2, by omega⟩
  have hpd : (frameAt word).parents.even.periodDenominator = (frameAt word).parents.even.den * (frameAt word).parents.even.den + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num - (frameAt word).parents.even.num * (frameAt word).parents.even.num := by
    unfold Fraction.periodDenominator
    ring
  have hR : (frameAt word).parents.odd.num * (frameAt word).parents.even.den - (frameAt word).parents.even.num * (frameAt word).parents.odd.den = 1 := heps.symm.trans hW1
  have hz : FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η)) =
      ((frameAt word).child.den, (frameAt word).child.num - 1 + η) := by
    unfold FLatticePaper.ArcPsi.reflH FLatticePaper.Induction.hFirst
    ext <;> simp
  rw [hz, hd_eq, hn_eq]
  unfold sheetPsi
  rw [A_part h hSE hW1 η hη hN2, C_part hW1 η, refl_value h hSE hW1 η hη, sub_zero]
  rw [harmonicGrid_eq_of_numerator _ _ _ (harm_numer (frameAt word).parents.odd.den (frameAt word).parents.odd.num (frameAt word).parents.even.den (frameAt word).parents.even.num η b hR hb hη),
    hpd, ce_div (frameAt word).parents.even.den (frameAt word).parents.even.num b hb]
  unfold i3Z
  simp only
  ring

end FLatticePaper.H0Phase1
