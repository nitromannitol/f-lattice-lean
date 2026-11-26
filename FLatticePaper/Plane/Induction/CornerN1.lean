import FLatticePaper.Plane.Induction.H0Phase1
import FLatticePaper.Plane.Induction.EvenWindow

/-! # The phase-one corner at `N = 1` (`hcorner`): `Ψ = 0` and `A = 0` at `reflH (H₀ + (0, 1))` for `ε = +1`, `η = −1`, `odd.num = 1`

`H0Phase1.sheetPsi_H0_refl_W1` covers `N ≥ 2` for `η = −1`: its A part uses the even harmonic band, which stops one step short of the
corner's conjugate `s`-grade when `N = 1`. At `N = 1` the corner point `(d, n − 2) = (d, nq)` is odd (the child numerator and denominator are
odd, so `nq` is odd), its conjugate `s`-grade is exactly `4 · odd.den`, and this lies in the odd band `[2 − 3d' + n', 3d' + n' − 2]` of
`odd_band_conj`, with `d' = odd.den + odd.num` and `n' = odd.den − odd.num`. The rest of the computation is that of `sheetPsi_H0_refl_W1`. -/

namespace FLatticePaper.CornerN1

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.PsiCalibration
open FLatticePaper.H0Phase1

/-- The A part of the corner at `N = 1`: the conjugate field equals the harmonic grid at the odd point `i3Z x`, which lies in the odd band. -/
theorem A_part_N1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    (hW1 : (frameAt word).eps = 1) (hN1 : (frameAt word).parents.odd.num = 1) :
    (frameAt word).sheetA (FqW word) (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den,
      2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + (-1)) = 0 := by
  obtain ⟨hN1p, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := FLatticePaper.PriceInputs.pdata h
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hR : (frameAt word).parents.odd.num * (frameAt word).parents.even.den -
      (frameAt word).parents.even.num * (frameAt word).parents.odd.den = 1 := heps.symm.trans hW1
  have hR1 : (frameAt word).parents.even.den - (frameAt word).parents.even.num * (frameAt word).parents.odd.den = 1 := by
    rw [hN1] at hR
    linarith
  obtain ⟨hon, hod⟩ := (frameAt word).child_odd
  have hcdw := FLatticePaper.Induction.ZoneI1.child_den_eq (frameAt word)
  have hcnw := FLatticePaper.Induction.ZoneI1.child_num_eq (frameAt word)
  unfold ChildFrame.sheetA
  rw [sheetShift_W1 word hW1, sub_zero]
  unfold FqW
  rw [quarterTurnField_apply]
  have hwin : standardField (conjWord word) (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den,
      2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + (-1))) =
      harmonicGrid (i3Z (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den,
      2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num - 1 + (-1))) := by
    apply odd_band_conj hSE hpar
    · unfold EvenSite i3Z
      simp only
      omega
    · rw [sGrade_conj word h, hcd, hcn, hN1]
      unfold i3Z
      simp only
      nlinarith [hR1]
    · rw [sGrade_conj word h, hcd, hcn, hN1]
      unfold i3Z
      simp only
      nlinarith [hR1]
  rw [hwin, harmonicGrid_Z]
  ring

theorem sheetPsi_corner_N1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    (hW1 : (frameAt word).eps = 1) (hN1 : (frameAt word).parents.odd.num = 1) (η : ℤ) (hη1 : η = -1) :
    sheetPsi word (FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η))) = 0 := by
  subst hη1
  obtain ⟨hN1p, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := FLatticePaper.PriceInputs.pdata h
  obtain ⟨hco1, hco2⟩ := (frameAt word).child_odd
  obtain ⟨b, hb⟩ : ∃ b : ℤ, (frameAt word).parents.even.den + (frameAt word).parents.even.num = 2 * b := by
    have hev : ((frameAt word).parents.even.den + (frameAt word).parents.even.num) % 2 = 0 := by omega
    exact ⟨((frameAt word).parents.even.den + (frameAt word).parents.even.num) / 2, by omega⟩
  have hpd : (frameAt word).parents.even.periodDenominator = (frameAt word).parents.even.den * (frameAt word).parents.even.den + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num - (frameAt word).parents.even.num * (frameAt word).parents.even.num := by
    unfold Fraction.periodDenominator
    ring
  have hR : (frameAt word).parents.odd.num * (frameAt word).parents.even.den - (frameAt word).parents.even.num * (frameAt word).parents.odd.den = 1 := heps.symm.trans hW1
  have hz : FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -(-1))) =
      ((frameAt word).child.den, (frameAt word).child.num - 1 + (-1)) := by
    unfold FLatticePaper.ArcPsi.reflH FLatticePaper.Induction.hFirst
    ext <;> (simp; try ring)
  rw [hz, hd_eq, hn_eq]
  unfold sheetPsi
  rw [A_part_N1 h hSE hpar hW1 hN1, C_part hW1 (-1), refl_value h hSE hW1 (-1) (Or.inr rfl), sub_zero]
  rw [harmonicGrid_eq_of_numerator _ _ _ (harm_numer (frameAt word).parents.odd.den (frameAt word).parents.odd.num (frameAt word).parents.even.den (frameAt word).parents.even.num (-1) b hR hb (Or.inr rfl)),
    hpd, ce_div (frameAt word).parents.even.den (frameAt word).parents.even.num b hb]
  unfold i3Z
  simp only
  ring

/-- **The phase-one corner at `N = 1` (`hcorner`).** For `ε = +1`, `η = −1`, `odd.num = 1`: `Ψ` and `A` vanish at `reflH (H₀ + (0, 1))`. -/
theorem corner_N1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    (hW1 : (frameAt word).eps = 1) (hN1 : (frameAt word).parents.odd.num = 1) (η : ℤ) (hη1 : η = -1) :
    sheetPsi word (FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η))) = 0 ∧
    (frameAt word).sheetA (FqW word)
      (FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η))) = 0 := by
  refine ⟨sheetPsi_corner_N1 h hSE hpar hW1 hN1 η hη1, ?_⟩
  subst hη1
  obtain ⟨-, -, -, -, -, hn_eq, hd_eq, -, -⟩ := FLatticePaper.PriceInputs.pdata h
  have hz : FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -(-1))) =
      ((frameAt word).child.den, (frameAt word).child.num - 1 + (-1)) := by
    unfold FLatticePaper.ArcPsi.reflH FLatticePaper.Induction.hFirst
    ext <;> (simp; try ring)
  rw [hz, hd_eq, hn_eq]
  exact A_part_N1 h hSE hpar hW1 hN1

end FLatticePaper.CornerN1
