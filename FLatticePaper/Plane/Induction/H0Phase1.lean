import FLatticePaper.Plane.Induction.PsiCalibration
import FLatticePaper.Plane.Induction.PhaseOneA
import FLatticePaper.Plane.Induction.RootCalibration
import FLatticePaper.Plane.Induction.ArcPsi
import FLatticePaper.Plane.Induction.Q3VStar

/-! `Ψ` at the reflected prescribed neighbours of `H_0` in phase one, for `η = +1` and for `η = −1` with `N ≥ 2`.

Let `z = reflH (H_0 + (0,−η)) = (d, n − 1 + η)`. Then `A z = G(i3Z z) + harmonicGrid z`, and `G(i3Z z) = −harmonicGrid z` by the
harmonic strip (the parent grade `T_p(z) = 1 + D − Dη` lies in the window exactly when `η = +1` or `N ≥ 2`) and `harmonicGrid_Z`.
`C z = G(i3Z x) + harmonicGrid x + slope z + c_e` with `x = z − (n_q, 2n_q + d_q)`; the packet reflection at the conjugate centre sends
`i3Z x` into the zero strip, so `G(i3Z x) = tGrade(i3Z x) − symmetryConstant`. The remaining identity is the harmonic numerator of `x`,
which holds modulo the parent relation `N d_q − n_q D = 1`. -/

namespace FLatticePaper.H0Phase1

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.PsiCalibration

set_option maxHeartbeats 2000000 in
theorem sheetPsi_H0_refl_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (η : ℤ) (hη : η = 1 ∨ η = -1) (hN2 : η = 1 ∨ 2 ≤ (frameAt word).parents.odd.num) :
    sheetPsi word (FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η))) = 0 := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := FLatticePaper.PriceInputs.pdata h
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hR : (frameAt word).parents.odd.num * (frameAt word).parents.even.den -
      (frameAt word).parents.even.num * (frameAt word).parents.odd.den = 1 :=
    heps.symm.trans hW1
  obtain ⟨hco1, hco2⟩ := (frameAt word).child_odd
  have hb : ∃ b : ℤ, (frameAt word).parents.even.den + (frameAt word).parents.even.num = 2 * b := by
    have hev : ((frameAt word).parents.even.den + (frameAt word).parents.even.num) % 2 = 0 := by omega
    exact ⟨((frameAt word).parents.even.den + (frameAt word).parents.even.num) / 2, by omega⟩
  obtain ⟨b, hb⟩ := hb
  have hS := hSE.packet.strips
  have hRf := hSE.packet.reflection
  have hz : FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η)) =
      ((frameAt word).child.den, (frameAt word).child.num - 1 + η) := by
    unfold FLatticePaper.ArcPsi.reflH FLatticePaper.Induction.hFirst
    ext <;> simp
  rw [hz, hd_eq, hn_eq]
  unfold sheetPsi
  -- the A part: the harmonic strip at i3Z z
  have hA : (frameAt word).sheetA (FqW word)
      (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den,
        2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η) = 0 := by
    unfold ChildFrame.sheetA
    rw [sheetShift_W1 word hW1, sub_zero]
    unfold FqW
    rw [quarterTurnField_apply]
    have hwin : standardField (conjWord word)
        (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den,
          2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η)) =
        harmonicGrid (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den,
          2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η)) := by
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
  have hC : (frameAt word).sheetC (FqW word) (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η) =
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
  -- the conjugate centre and symmetry constant
  have hcen : (frameAt (conjWord word)).centre = ((frameAt (conjWord word)).child.num + 1, 2 * (frameAt (conjWord word)).child.num + (frameAt (conjWord word)).child.den - 1) := by
    unfold ChildFrame.centre
    rw [ChildFrame.child_modifiedDeck_kernel, ChildFrame.child_modifiedDeck_transverse]
    ext <;> simp
    ring
  have hsymc : (frameAt (conjWord word)).symmetryConstant = (frameAt word).parents.odd.den - (frameAt word).parents.odd.den^2 - 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num + (frameAt word).parents.odd.num^2 := by
    unfold ChildFrame.symmetryConstant Fraction.periodDenominator
    rw [hcd, hcn]
    have e2 : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) - (((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)^2 + 2 * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) - ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num)^2) =
        2 * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.den^2 - 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num + (frameAt word).parents.odd.num^2) := by ring
    rw [e2]
    omega
  -- the reflected point of the C-part lies in the zero strip of the conjugate
  have hzero : standardField (conjWord word)
      ((frameAt (conjWord word)).centre - i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))) = 0 := by
    apply hS.1
    · rw [hcen, tGrade_conj word h, hcd, hcn]
      unfold i3Z
      simp only [Prod.fst_sub, Prod.snd_sub]
      rcases hη with rfl | rfl <;> nlinarith [hR]
    · rw [hcen, tGrade_conj word h, hcd, hcn]
      unfold i3Z
      simp only [Prod.fst_sub, Prod.snd_sub]
      rcases hη with rfl | rfl <;> nlinarith [hR]
  have hRefl : standardField (conjWord word) ((frameAt (conjWord word)).centre - (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den)))) = standardField (conjWord word) ((i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den)))) - (frameAt (conjWord word)).tGrade ((i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den)))) + (frameAt (conjWord word)).symmetryConstant := hRf _
  rw [hzero] at hRefl
  rw [hsymc] at hRefl
  have hGx : standardField (conjWord word) (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))) =
      (((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))).1 - ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num, 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))).2) - ((frameAt word).parents.odd.den - (frameAt word).parents.odd.den^2 - 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num + (frameAt word).parents.odd.num^2) := by
    rw [tGrade_conj word h] at hRefl
    linarith
  -- the parent divisions
  have he : 2 * (((frameAt word).parents.even.den - (frameAt word).parents.even.num) * b + (frameAt word).parents.even.den * (frameAt word).parents.even.num - b) = (frameAt word).parents.even.den * (frameAt word).parents.even.den + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num - (frameAt word).parents.even.num * (frameAt word).parents.even.num - (frameAt word).parents.even.den - (frameAt word).parents.even.num := by
    linear_combination (-((frameAt word).parents.even.den - (frameAt word).parents.even.num - 1)) * hb
  have hpd : (frameAt word).parents.even.periodDenominator = (frameAt word).parents.even.den * (frameAt word).parents.even.den + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num - (frameAt word).parents.even.num * (frameAt word).parents.even.num := by
    unfold Fraction.periodDenominator
    ring
  have hce : ((frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den - (frameAt word).parents.even.num) / 2 = ((frameAt word).parents.even.den - (frameAt word).parents.even.num) * b + (frameAt word).parents.even.den * (frameAt word).parents.even.num - b := by
    rw [hpd, ← he]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hnum : (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num)^2 + 2 * (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num) * (2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den)) -
      (2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))^2 - 2 * (2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den)) -
      ((2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num) + (2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))) % 2 =
      4 * (-(((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (-(2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))) - ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * ((2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num) - 1)
        - ((frameAt word).parents.odd.den - (frameAt word).parents.odd.den^2 - 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num + (frameAt word).parents.odd.num^2) + ((frameAt word).parents.even.num * (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den) - (frameAt word).parents.even.den * (2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η)) + (((frameAt word).parents.even.den - (frameAt word).parents.even.num) * b + (frameAt word).parents.even.den * (frameAt word).parents.even.num - b) + 2)) := by
    have hpar : ((2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den - (frameAt word).parents.even.num) + (2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + η - (2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den))) % 2 = 0 := by
      rcases hη with rfl | rfl <;> omega
    rw [hpar]
    rcases hη with rfl | rfl
    · linear_combination (-8 : ℤ) * hR + 2 * he
    · linear_combination (-8 : ℤ) * hR + 2 * he
  rw [hC, hGx, hA, sub_zero, harmonicGrid_eq_of_numerator _ _ _ hnum, hce]
  unfold i3Z
  simp only
  ring

end FLatticePaper.H0Phase1
