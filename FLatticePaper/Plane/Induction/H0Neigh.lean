import FLatticePaper.Plane.Induction.PsiCalibration
import FLatticePaper.Plane.Induction.FirstOfferGrade
import FLatticePaper.Plane.Induction.PsiMonoOffset
import FLatticePaper.Plane.Induction.RootCalibration

/-! The calibration of `Ψ` at the two prescribed neighbours of `H_0` in phase zero: `Ψ(H_0 + (0, −η)) = 0` for `η = ±1`.

As in `sheetPsi_H0_W0`: the first offer vanishes (`first_offer_neighbour_W0`), the conjugate field vanishes on the zero strip at the image
point `Z(x)` of `x = (1 − n_q + d_q, −η − n_q − d_q)` (`hS.1`), and the harmonic grid value at `x` is explicit. With `n_q + d_q = 2b`
the harmonic numerator is `x₁² + 2x₁x₂ − x₂² − 2x₂` with `x₁ = 1 + 2b − 2n_q`, `x₂ = −η − 2b`, and the sum `Ψ` closes to zero. -/

namespace FLatticePaper.H0Neigh

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.PsiCalibration

theorem sheetPsi_H0_neighbour_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW0 : (frameAt word).eps = -1) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    sheetPsi word (FLatticePaper.Induction.hFirst + (0, -η)) = 0 := by
  have hrel := w0_relation word hW0
  obtain ⟨b, hb⟩ : ∃ b : ℤ, (frameAt word).parents.even.num + (frameAt word).parents.even.den = 2 * b := by
    have hev : ((frameAt word).parents.even.num + (frameAt word).parents.even.den) % 2 = 0 :=
      (frameAt word).valid.even_parity
    exact ⟨((frameAt word).parents.even.num + (frameAt word).parents.even.den) / 2, by omega⟩
  have hdq : (frameAt word).parents.even.den = 2 * b - (frameAt word).parents.even.num := by omega
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  obtain ⟨c1, c2, c3, c4, -⟩ := (frameAt (conjWord word)).child_facts
  have hS := hSE.packet.strips
  have hA := FLatticePaper.FirstOfferGrade.first_offer_neighbour_W0 h hSE hW0 (FLatticePaper.PsiMonoOffset.hFirst_mem_freeH (frameAt word)) hη
  rw [ChildFrame.prescribedH_hFirst] at hA
  -- the zero strip at the image point of the neighbour
  have hzero : standardField (conjWord word)
      (i3Z (1 - (frameAt word).parents.even.num + (frameAt word).parents.even.den,
        -η - (frameAt word).parents.even.num - (frameAt word).parents.even.den)) = 0 := by
    apply hS.1
    · simp only [tGrade_conj word h, hcd]
      unfold i3Z
      simp only
      rcases hη with rfl | rfl <;> nlinarith [hrel, c1, c2, c3, c4]
    · simp only [tGrade_conj word h, hcd, hcn]
      unfold i3Z
      simp only
      rcases hη with rfl | rfl <;> nlinarith [hrel, c1, c2, c3, c4]
  have e1 : FLatticePaper.Induction.hFirst + (0, -η) - ((frameAt word).parents.even.den, (frameAt word).parents.even.num) =
      (1 - (frameAt word).parents.even.den, -η - (frameAt word).parents.even.num) := by
    ext <;> simp [FLatticePaper.Induction.hFirst]
  have e2 : (1 - (frameAt word).parents.even.den, -η - (frameAt word).parents.even.num) -
      ((frameAt word).parents.even.num - 2 * (frameAt word).parents.even.den, (frameAt word).parents.even.den) =
      (1 - (frameAt word).parents.even.num + (frameAt word).parents.even.den,
        -η - (frameAt word).parents.even.num - (frameAt word).parents.even.den) := by
    ext <;> simp
    ring
  have hT : (frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den -
      (frameAt word).parents.even.num = 2 * (2 * b ^ 2 - (frameAt word).parents.even.num ^ 2 - b) := by
    unfold Fraction.periodDenominator
    rw [hdq]
    ring
  have hnum : (1 - (frameAt word).parents.even.num + (frameAt word).parents.even.den) ^ 2 +
      2 * (1 - (frameAt word).parents.even.num + (frameAt word).parents.even.den) *
        (-η - (frameAt word).parents.even.num - (frameAt word).parents.even.den) -
      (-η - (frameAt word).parents.even.num - (frameAt word).parents.even.den) ^ 2 -
      2 * (-η - (frameAt word).parents.even.num - (frameAt word).parents.even.den) -
      ((1 - (frameAt word).parents.even.num + (frameAt word).parents.even.den) +
        (-η - (frameAt word).parents.even.num - (frameAt word).parents.even.den)) % 2 =
      4 * (-((frameAt word).parents.even.num + η * (frameAt word).parents.even.den +
        (2 * b ^ 2 - (frameAt word).parents.even.num ^ 2 - b))) := by
    have hpar : ((1 - (frameAt word).parents.even.num + (frameAt word).parents.even.den) +
        (-η - (frameAt word).parents.even.num - (frameAt word).parents.even.den)) % 2 = 0 := by
      rcases hη with rfl | rfl <;> omega
    rw [hpar, hdq]
    rcases hη with rfl | rfl <;> ring
  unfold sheetPsi
  rw [hA]
  unfold ChildFrame.sheetC
  rw [sheetShift_W0 word hW0, sheetOffset_W0 word hW0, sheetConstant_W0 word hW0, e1, e2]
  unfold FqW
  rw [quarterTurnField_apply, hzero, harmonicGrid_eq_of_numerator _ _ _ hnum]
  unfold ChildFrame.siblingSlope
  rw [hT]
  simp only []
  rw [hdq]
  rcases hη with rfl | rfl <;> ring_nf <;> omega

end FLatticePaper.H0Neigh
