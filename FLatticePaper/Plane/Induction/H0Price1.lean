import FLatticePaper.Plane.Induction.H0Phase1
import FLatticePaper.Plane.Induction.PhaseOnePrice
import FLatticePaper.Plane.Induction.W1BottomValue
import FLatticePaper.Plane.Induction.PsiMonoOffset

/-! The phase-one price at the prescribed neighbours of `H_0`: `P(H_0 + prescribedH η H_0) = P(H_0) = c_0`.

`price_W1` at `z = H_0 + prescribedH η H_0` gives `c_0 − 1 − min 0 (Ψ(reflH z) − 1)`, and `Ψ(reflH z) = 0` (`H0Phase1`) makes the
minimum `−1`, so the price is `c_0`; `price_hFirst` gives `P(H_0) = c_0`. -/

namespace FLatticePaper.H0Price1

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.PriceInputs
  FLatticePaper.Induction.TipVertex

theorem A_H0_neighbour {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (η : ℤ) (hη : η = 1 ∨ η = -1) (hN2 : η = 1 ∨ 2 ≤ (frameAt word).parents.odd.num) :
    (frameAt word).sheetA (FqW word) (FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η))) = 0 := by
  have hz : FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η)) =
      ((frameAt word).child.den, (frameAt word).child.num - 1 + η) := by
    unfold FLatticePaper.ArcPsi.reflH FLatticePaper.Induction.hFirst
    ext <;> simp
  rw [hz]
  obtain ⟨-, -, -, -, -, hn_eq, hd_eq, -, -⟩ := FLatticePaper.PriceInputs.pdata h
  rw [hd_eq, hn_eq]
  exact FLatticePaper.H0Phase1.A_part h hSE hW1 η hη hN2

theorem price_H0_neighbour_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (η : ℤ) (hη : η = 1 ∨ η = -1) (hN2 : η = 1 ∨ 2 ≤ (frameAt word).parents.odd.num) :
    (frameAt word).price (standardField word) (FLatticePaper.Induction.hFirst + (0, -η)) =
      (frameAt word).price (standardField word) FLatticePaper.Induction.hFirst := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := FLatticePaper.PriceInputs.pdata h
  have hpk := packet_of_strong h hSE
  have hF0 := FLatticePaper.PsiMonoOffset.hFirst_mem_freeH (frameAt word)
  have hz0 := FLatticePaper.FreeHPrice.neighbour_F_zero (frameAt word) hpk.strips hF0 hη
  rw [ChildFrame.prescribedH_hFirst] at hz0
  have hR := refl_tip (frameAt word) (standardField word) hpk (FLatticePaper.Induction.hFirst + (0, -η))
  have hA0 := A_H0_neighbour h hSE hW1 η hη hN2
  have hcl := FLatticePaper.TipReflect.tip_closed_reflH_W1 (frameAt word) hN1 hND hD2 hnq hdq hn_eq hd_eq heps hW1 hF0 hη
  have hFV := standardField_eq_sheetMin_of_strong h hSE hcl
  have hP := FLatticePaper.EHPrice.price_W1 h hSE hW1 (FLatticePaper.Induction.hFirst + (0, -η)) hz0 hR hA0 hFV
  have hPsi := FLatticePaper.H0Phase1.sheetPsi_H0_refl_W1 h hSE hW1 η hη hN2
  have hH : (frameAt word).price (standardField word) FLatticePaper.Induction.hFirst = (frameAt word).cutPrice :=
    FLatticePaper.W1BottomValue.price_hFirst h hSE
  rw [hP, hPsi, hH]
  norm_num

end FLatticePaper.H0Price1
