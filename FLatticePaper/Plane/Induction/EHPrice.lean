import FLatticePaper.Plane.Induction.ArcPsi
import FLatticePaper.Plane.Induction.W0Sheets
import FLatticePaper.Plane.Induction.ZoneI1

/-! # The E_H identity and the price `P = c₀ − E_H` in both phases (task 118, H_PRICE)

With `F = standardField word`, `Fq = quarterTurnField (standardField (conjWord word))`, `V_p = tipVertex`, `a_p·x = N x₁ − D x₂`:

* `sheetA_add_tip`: `A(z + V_p) = a_p·(z − lv) + s` when `A(z) = 0` (`quarterTurnField_add_tipVertex`, `harmonicGrid_add_tipVertex`).
* `sheetPsi_add_tip_W0/W1`: `Ψ(z + V_p) = Ψ(z) − 1` (an integer identity, `ε = ±1`).
* `E_W0`, `E_W1`: `F(z + V_p) − a_p·z − s = (1 − W) + min(0, Ψ(z) − 1)`, from `F(z + V_p) = min(A, C)(z + V_p)`.
* `price_W0`, `price_W1`: `P(z) = c₀ − E_H` (W1 through `w = reflH word z`, with `F(z − V_p) = F(w + V_p)`).

Named inputs: `F z = 0` and `A z = 0` on the trace; the sheet-minimum agreement `F y = sheetMin y` at the deck points `y = z + V_p`
(W0) and `y = w + V_p` (W1); the reflection `F(z − V_p) = F(w + V_p)` (W1). The values of `Ψ` are not used. -/

namespace FLatticePaper.EHPrice

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet
open FLatticePaper.Induction.TipVertex FLatticePaper.Induction.W0Sheets FLatticePaper.PsiCalibration

/-- The parent slope of the price: `a_p · x = N x₁ − D x₂`. -/
def aPar (frame : ChildFrame) (x : Site) : ℤ :=
  frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2

/-- The constant of the tip-vertex translation exists: `N + D + T_p` is even (`D(D+1)` and `N(N−1)` are even). -/
theorem exists_const (frame : ChildFrame) : ∃ s : ℤ,
    2 * s = (-frame.parents.odd.num) + (-frame.parents.odd.den) -
      ((-frame.parents.odd.den) ^ 2 + 2 * (-frame.parents.odd.den) * (-frame.parents.odd.num) -
        (-frame.parents.odd.num) ^ 2) := by
  obtain ⟨a, ha⟩ := Int.even_mul_succ_self frame.parents.odd.den
  obtain ⟨b, hb⟩ := Int.even_mul_pred_self frame.parents.odd.num
  refine ⟨-(a - b + frame.parents.odd.den * frame.parents.odd.num), ?_⟩
  linear_combination ha - hb

/-- **The sheet A on the tip.** If `A(z) = 0` then `A(z + V_p) = a_p·(z − lv) + s`. -/
theorem sheetA_add_tip {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (z : Site) (s : ℤ)
    (hs : 2 * s = (-(frameAt word).parents.odd.num) + (-(frameAt word).parents.odd.den) -
      ((-(frameAt word).parents.odd.den) ^ 2 + 2 * (-(frameAt word).parents.odd.den) * (-(frameAt word).parents.odd.num) -
        (-(frameAt word).parents.odd.num) ^ 2))
    (hA0 : (frameAt word).sheetA (FqW word) z = 0) :
    (frameAt word).sheetA (FqW word) (z + tipVertex (frameAt word)) =
      aPar (frameAt word) (z - (frameAt word).sheetShift) + s := by
  have e : z + tipVertex (frameAt word) - (frameAt word).sheetShift =
      (z - (frameAt word).sheetShift) + tipVertex (frameAt word) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  unfold ChildFrame.sheetA at hA0 ⊢
  unfold FqW at hA0 ⊢
  rw [e, quarterTurnField_add_tipVertex h hSE, harmonicGrid_add_tipVertex (frameAt word) _ s hs, hA0]
  unfold aPar
  ring

/-- The quarter turn along the tip: `Fq (y + V_p) = Fq y + a_p·y + s`. -/
theorem fq_add_tip {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (s : ℤ)
    (hs : 2 * s = (-(frameAt word).parents.odd.num) + (-(frameAt word).parents.odd.den) -
      ((-(frameAt word).parents.odd.den) ^ 2 + 2 * (-(frameAt word).parents.odd.den) * (-(frameAt word).parents.odd.num) -
        (-(frameAt word).parents.odd.num) ^ 2)) (y : Site) :
    FqW word (y + tipVertex (frameAt word)) = FqW word y + aPar (frameAt word) y + s := by
  unfold FqW
  rw [quarterTurnField_add_tipVertex h hSE, harmonicGrid_add_tipVertex (frameAt word) y s hs]
  unfold aPar
  ring

/-- The sheet C shifts along the tip: the two arguments move by `V_p` together. -/
theorem psi_shift_formula {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (s : ℤ)
    (hs : 2 * s = (-(frameAt word).parents.odd.num) + (-(frameAt word).parents.odd.den) -
      ((-(frameAt word).parents.odd.den) ^ 2 + 2 * (-(frameAt word).parents.odd.den) * (-(frameAt word).parents.odd.num) -
        (-(frameAt word).parents.odd.num) ^ 2))
    (z lv e : Site) (cE : ℤ) :
    FqW word (z + tipVertex (frameAt word) - lv - e) +
        (frameAt word).siblingSlope (z + tipVertex (frameAt word) - lv) + cE -
        FqW word (z + tipVertex (frameAt word) - lv) =
      FqW word (z - lv - e) + (frameAt word).siblingSlope (z - lv) + cE - FqW word (z - lv) +
        (aPar (frameAt word) (z - lv - e) - aPar (frameAt word) (z - lv) +
          (frameAt word).siblingSlope (tipVertex (frameAt word))) := by
  have e1 : z + tipVertex (frameAt word) - lv - e = (z - lv - e) + tipVertex (frameAt word) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  have e2 : z + tipVertex (frameAt word) - lv = (z - lv) + tipVertex (frameAt word) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [e1, e2, fq_add_tip h hSE s hs, fq_add_tip h hSE s hs]
  unfold aPar ChildFrame.siblingSlope
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

/-- `Ψ(z + V_p) = Ψ(z) − 1` in phase W0 (`ε = −1`). -/
theorem sheetPsi_add_tip_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW0 : (frameAt word).eps = -1) (z : Site) :
    sheetPsi word (z + tipVertex (frameAt word)) = sheetPsi word z - 1 := by
  obtain ⟨s, hs⟩ := exists_const (frameAt word)
  have hε := ZoneI1.eps_eq (frameAt word)
  have hsh := sheetShift_W0 word hW0
  have hoff := sheetOffset_W0 word hW0
  have hslope : aPar (frameAt word) (z - (frameAt word).sheetShift - (frameAt word).sheetOffset) -
      aPar (frameAt word) (z - (frameAt word).sheetShift) +
        (frameAt word).siblingSlope (tipVertex (frameAt word)) = -1 := by
    rw [hsh, hoff]
    rw [hW0] at hε
    unfold aPar ChildFrame.siblingSlope tipVertex
    simp only [Prod.fst_sub, Prod.snd_sub]
    linear_combination (-1 : ℤ) * hε
  have key := psi_shift_formula h hSE s hs z (frameAt word).sheetShift (frameAt word).sheetOffset
    (frameAt word).sheetConstant
  unfold sheetPsi ChildFrame.sheetC ChildFrame.sheetA
  linarith [key, hslope]

/-- `Ψ(z + V_p) = Ψ(z) − 1` in phase W1 (`ε = +1`). -/
theorem sheetPsi_add_tip_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW1 : (frameAt word).eps = 1) (z : Site) :
    sheetPsi word (z + tipVertex (frameAt word)) = sheetPsi word z - 1 := by
  obtain ⟨s, hs⟩ := exists_const (frameAt word)
  have hε := ZoneI1.eps_eq (frameAt word)
  have hsh := sheetShift_W1 word hW1
  have hoff := sheetOffset_W1 word hW1
  have hslope : aPar (frameAt word) (z - (frameAt word).sheetShift - (frameAt word).sheetOffset) -
      aPar (frameAt word) (z - (frameAt word).sheetShift) +
        (frameAt word).siblingSlope (tipVertex (frameAt word)) = -1 := by
    rw [hsh, hoff]
    rw [hW1] at hε
    unfold aPar ChildFrame.siblingSlope tipVertex
    simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]
    linear_combination hε
  have key := psi_shift_formula h hSE s hs z (frameAt word).sheetShift (frameAt word).sheetOffset
    (frameAt word).sheetConstant
  unfold sheetPsi ChildFrame.sheetC ChildFrame.sheetA
  linarith [key, hslope]

/-- **The E identity in phase W0.** `F(z + V_p) − a_p·z − s = 1 + min(0, Ψ(z) − 1)`. -/
theorem E_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW0 : (frameAt word).eps = -1) (z : Site) (s : ℤ)
    (hs : 2 * s = (-(frameAt word).parents.odd.num) + (-(frameAt word).parents.odd.den) -
      ((-(frameAt word).parents.odd.den) ^ 2 + 2 * (-(frameAt word).parents.odd.den) * (-(frameAt word).parents.odd.num) -
        (-(frameAt word).parents.odd.num) ^ 2))
    (hA0 : (frameAt word).sheetA (FqW word) z = 0)
    (hFV : standardField word (z + tipVertex (frameAt word)) =
      (frameAt word).sheetMin (FqW word) (z + tipVertex (frameAt word))) :
    standardField word (z + tipVertex (frameAt word)) - aPar (frameAt word) z - s =
      1 + min 0 (sheetPsi word z - 1) := by
  have hA := sheetA_add_tip h hSE z s hs hA0
  have hΨ := sheetPsi_add_tip_W0 h hSE hW0 z
  have hC : (frameAt word).sheetC (FqW word) (z + tipVertex (frameAt word)) =
      (frameAt word).sheetA (FqW word) (z + tipVertex (frameAt word)) +
        sheetPsi word (z + tipVertex (frameAt word)) := by
    unfold sheetPsi
    ring
  have hlin : aPar (frameAt word) (z - (frameAt word).sheetShift) = aPar (frameAt word) z + 1 := by
    rw [sheetShift_W0 word hW0]
    have hε := ZoneI1.eps_eq (frameAt word)
    rw [hW0] at hε
    unfold aPar
    simp only [Prod.fst_sub, Prod.snd_sub]
    linear_combination hε
  unfold ChildFrame.sheetMin at hFV
  rw [hFV, hC, hA, hΨ, hlin]
  omega

/-- **The E identity in phase W1.** `F(z + V_p) − a_p·z − s = min(0, Ψ(z) − 1)`. -/
theorem E_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW1 : (frameAt word).eps = 1) (z : Site) (s : ℤ)
    (hs : 2 * s = (-(frameAt word).parents.odd.num) + (-(frameAt word).parents.odd.den) -
      ((-(frameAt word).parents.odd.den) ^ 2 + 2 * (-(frameAt word).parents.odd.den) * (-(frameAt word).parents.odd.num) -
        (-(frameAt word).parents.odd.num) ^ 2))
    (hA0 : (frameAt word).sheetA (FqW word) z = 0)
    (hFV : standardField word (z + tipVertex (frameAt word)) =
      (frameAt word).sheetMin (FqW word) (z + tipVertex (frameAt word))) :
    standardField word (z + tipVertex (frameAt word)) - aPar (frameAt word) z - s =
      min 0 (sheetPsi word z - 1) := by
  have hA := sheetA_add_tip h hSE z s hs hA0
  have hΨ := sheetPsi_add_tip_W1 h hSE hW1 z
  have hC : (frameAt word).sheetC (FqW word) (z + tipVertex (frameAt word)) =
      (frameAt word).sheetA (FqW word) (z + tipVertex (frameAt word)) +
        sheetPsi word (z + tipVertex (frameAt word)) := by
    unfold sheetPsi
    ring
  have hlin : aPar (frameAt word) (z - (frameAt word).sheetShift) = aPar (frameAt word) z := by
    rw [sheetShift_W1 word hW1]
    unfold aPar
    simp only [sub_zero]
  unfold ChildFrame.sheetMin at hFV
  rw [hFV, hC, hA, hΨ, hlin]
  omega

/-- **The price in phase W0**: `P(z) = c₀ − E_H(z)`, with `E_H = 1 + min(0, Ψ − 1)`. -/
theorem price_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW0 : (frameAt word).eps = -1) (z : Site)
    (hz0 : standardField word z = 0)
    (hA0 : (frameAt word).sheetA (FqW word) z = 0)
    (hFV : standardField word (z + tipVertex (frameAt word)) =
      (frameAt word).sheetMin (FqW word) (z + tipVertex (frameAt word))) :
    (frameAt word).price (standardField word) z =
      (frameAt word).cutPrice - (1 + min 0 (sheetPsi word z - 1)) := by
  obtain ⟨s, hs⟩ := exists_const (frameAt word)
  have hE := E_W0 h hSE hW0 z s hs hA0 hFV
  have hpsh : z - (frameAt word).parentShift = z + tipVertex (frameAt word) := by
    unfold ChildFrame.parentShift tipVertex
    rw [hW0]
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
  have hs' : 2 * s = -(frameAt word).parents.odd.num - (frameAt word).parents.odd.den -
      ((frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
        (frameAt word).parents.odd.num ^ 2) := by
    linear_combination hs
  unfold ChildFrame.price ChildFrame.cutPrice ChildFrame.parentSlope
  rw [hpsh, hW0, hz0]
  unfold Fraction.periodDenominator at hs' ⊢
  generalize (frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
    (frameAt word).parents.odd.num ^ 2 = T at hs' ⊢
  unfold aPar at hE
  omega

/-- **The price in phase W1**: `P(z) = c₀ − 1 − E_H(w)` at the reflection `w = reflH word z`, with `E_H(w) = min(0, Ψ(w) − 1)`. -/
theorem price_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW1 : (frameAt word).eps = 1) (z : Site)
    (hz0 : standardField word z = 0)
    (hR : standardField word (z - tipVertex (frameAt word)) =
      standardField word (FLatticePaper.ArcPsi.reflH word z + tipVertex (frameAt word)))
    (hA0w : (frameAt word).sheetA (FqW word) (FLatticePaper.ArcPsi.reflH word z) = 0)
    (hFVw : standardField word (FLatticePaper.ArcPsi.reflH word z + tipVertex (frameAt word)) =
      (frameAt word).sheetMin (FqW word) (FLatticePaper.ArcPsi.reflH word z + tipVertex (frameAt word))) :
    (frameAt word).price (standardField word) z =
      (frameAt word).cutPrice - 1 - min 0 (sheetPsi word (FLatticePaper.ArcPsi.reflH word z) - 1) := by
  obtain ⟨s, hs⟩ := exists_const (frameAt word)
  have hE := E_W1 h hSE hW1 (FLatticePaper.ArcPsi.reflH word z) s hs hA0w hFVw
  have hpsh : z - (frameAt word).parentShift = z - tipVertex (frameAt word) := by
    unfold ChildFrame.parentShift tipVertex
    rw [hW1]
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, one_mul]
  have hs' : 2 * s = -(frameAt word).parents.odd.num - (frameAt word).parents.odd.den -
      ((frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
        (frameAt word).parents.odd.num ^ 2) := by
    linear_combination hs
  -- a_p·(w + z) = N d − D n + N + D = ε + N + D = 1 + N + D
  have hε := ZoneI1.eps_eq (frameAt word)
  rw [hW1] at hε
  have hdn := child_den_eq word
  have hnn := child_num_eq word
  have hw : aPar (frameAt word) (FLatticePaper.ArcPsi.reflH word z) + aPar (frameAt word) z =
      1 + (frameAt word).parents.odd.num + (frameAt word).parents.odd.den := by
    unfold FLatticePaper.ArcPsi.reflH aPar
    rw [hdn, hnn]
    linear_combination (-1 : ℤ) * hε
  unfold ChildFrame.price ChildFrame.cutPrice ChildFrame.parentSlope
  rw [hpsh, hW1, hz0, hR]
  unfold aPar at hE hw
  unfold Fraction.periodDenominator at hs' ⊢
  generalize (frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
    (frameAt word).parents.odd.num ^ 2 = T at hs' ⊢
  omega

end FLatticePaper.EHPrice
