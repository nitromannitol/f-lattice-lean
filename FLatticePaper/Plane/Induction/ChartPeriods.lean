import FLatticePaper.Plane.Induction.SheetCharts
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.Reflection
import FLatticePaper.Plane.Induction.SheetDifference
import FLatticePaper.Plane.Induction.OddStep

/-! Task 66 (2): the sheets translate by the parent's odd kernel.

* `Upar word = (2D, 2N)`, the odd parent's kernel `U_p` (so `shortShift = ε U_p`).
* `quarterTurnField_Upar_period`: the parent field `f = quarterTurnField G` (`G` the conjugate's standard field) is `U_p`-periodic
  with constant `0`. Proof: `f(x) = G(Zx) + h₀(x)`; `Z(x + U_p) = Zx + V_c` with `V_c = (−2N, 2D)` the conjugate's transverse
  (`frameAt_conj_num_den`); the conjugate's packet period gives `G(Zx + V_c) = G(Zx) − tGrade_c(Zx) + c_V` with
  `2 c_V = −(den + num + T)` (`coherentConstantV_eq`); the harmonic correction of `U_p` is `D² + 2DN − N² − N`, and
  `c_V + (D + N) + (D² + 2DN − N² − N) = 0`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The odd parent's kernel `U_p = (2D, 2N)`. -/
abbrev Upar (word : Word) : Site := (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)

theorem harmonicGrid_Upar (word : Word) :
    harmonicGrid (Upar word) = (frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den *
      (frameAt word).parents.odd.num - (frameAt word).parents.odd.num ^ 2 - (frameAt word).parents.odd.num := by
  unfold harmonicGrid Upar
  dsimp only
  have hm : (2 * (frameAt word).parents.odd.den + 2 * (frameAt word).parents.odd.num) % 2 = 0 := by omega
  rw [hm]
  have e : (2 * (frameAt word).parents.odd.den) ^ 2 + 2 * (2 * (frameAt word).parents.odd.den) *
      (2 * (frameAt word).parents.odd.num) - (2 * (frameAt word).parents.odd.num) ^ 2 -
      2 * (2 * (frameAt word).parents.odd.num) - 0 =
      4 * ((frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den *
        (frameAt word).parents.odd.num - (frameAt word).parents.odd.num ^ 2 - (frameAt word).parents.odd.num) := by
    ring
  rw [e, Int.mul_ediv_cancel_left _ (by norm_num)]

theorem quarterTurnField_Upar_period {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    quarterTurnField (standardField (conjWord word)) (x + Upar word) =
      quarterTurnField (standardField (conjWord word)) x := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hV := hSE.packet.periods.2
  rw [(frameAt (conjWord word)).child_modifiedDeck_transverse] at hV
  unfold Fraction.transverseGrade at hV
  rw [hcn, hcd] at hV
  have hcV := (frameAt (conjWord word)).coherentConstantV_eq
  unfold Fraction.periodDenominator at hcV
  rw [hcn, hcd] at hcV
  have hcV' : (frameAt (conjWord word)).coherentConstantV =
      -((frameAt word).parents.odd.den + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num +
        (frameAt word).parents.odd.den ^ 2 - (frameAt word).parents.odd.num ^ 2) := by
    ring_nf at hcV ⊢
    linarith
  have hh0 := harmonicGrid_Upar word
  have hH := harmonicGrid_sub_even (-Upar word) x (by
    simp only [EvenSite, Upar, Prod.fst_neg, Prod.snd_neg]
    omega)
  rw [sub_neg_eq_add, neg_neg] at hH
  have e1 : ((-Upar word).1 + (-Upar word).2) / 2 = -((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) := by
    simp only [Upar, Prod.fst_neg, Prod.snd_neg]
    omega
  have e2 : ((-Upar word).1 - (-Upar word).2) / 2 = -((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
    simp only [Upar, Prod.fst_neg, Prod.snd_neg]
    omega
  rw [e1, e2] at hH
  have hs := hV (-x.2, x.1 - 1)
  have es : (-(x + Upar word).2, (x + Upar word).1 - 1) =
      (-x.2, x.1 - 1) + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num -
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num +
          ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) := by
    unfold Upar
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  rw [quarterTurnField_eq]
  dsimp only
  dsimp only at hs
  rw [es, hs, hH, hcV', hh0]
  ring

end FLatticePaper.Induction
