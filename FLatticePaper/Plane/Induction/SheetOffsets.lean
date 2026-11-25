import FLatticePaper.Plane.Induction.ChartPeriods
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.W1MSheet

/-! Task 72 / Q31 step 2, P3: the two sheet offers at the shifted point `z + X`.

`X = U_p = Upar word` in phase 0 (ε = −1) and `X = U_q` in phase 1 (ε = 1). With `Fp = FqW word` (the quarter-turned conjugate field):
* phase 0: `A(z + U_p) = Fp(z − U_q)` and `C(z + U_p) = Fp(z − V_q) + a_q·z + 2 + sheetConstant`;
* phase 1: `A(z + U_q) = Fp(z + U_q)` and `C(z + U_q) = Fp(z − V_q) + a_q·z + sheetConstant`.
Here `a_q·z = n_q z₁ − d_q z₂` (`siblingSlope`), `U_q = kernel`, `V_q = transverse` of the even parent. -/

namespace FLatticePaper.SheetOffsets

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet

theorem phaseW_neg {word : Word} (hε : (frameAt word).eps = -1) : (frameAt word).phaseW = 0 := by
  unfold ChildFrame.phaseW
  rw [hε]
  norm_num

theorem phaseW_pos {word : Word} (hε : (frameAt word).eps = 1) : (frameAt word).phaseW = 1 := by
  unfold ChildFrame.phaseW
  rw [hε]
  norm_num

/-- The determinant form of `ε`: `ε = N d_q − D n_q`. -/
theorem eps_eq_det {word : Word} :
    (frameAt word).eps = (frameAt word).parents.odd.num * (frameAt word).parents.even.den
      - (frameAt word).parents.odd.den * (frameAt word).parents.even.num := by
  unfold ChildFrame.eps Fraction.det
  ring

/-- **Phase 0, A-offer:** `A(z + U_p) = Fp(z − U_q)`. -/
theorem sheetA_neg {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hε : (frameAt word).eps = -1) (z : Site) :
    (frameAt word).sheetA (FqW word) (z + Upar word) =
      FqW word (z - (frameAt word).parents.even.unmodifiedDeck.kernel) := by
  unfold ChildFrame.sheetA ChildFrame.sheetShift
  rw [phaseW_neg hε, sub_zero, one_smul]
  rw [show z + Upar word - (frameAt word).parents.even.unmodifiedDeck.kernel =
      (z - (frameAt word).parents.even.unmodifiedDeck.kernel) + Upar word by abel]
  exact quarterTurnField_Upar_period h hSE _

/-- The even parent's unmodified deck: kernel `(d_q, n_q)`, transverse `(n_q − d_q, n_q + d_q)`. -/
theorem even_kernel {word : Word} : (frameAt word).parents.even.unmodifiedDeck.kernel =
    ((frameAt word).parents.even.den, (frameAt word).parents.even.num) := rfl

theorem even_transverse {word : Word} : (frameAt word).parents.even.unmodifiedDeck.transverse =
    ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
      (frameAt word).parents.even.num + (frameAt word).parents.even.den) := rfl

/-- **Phase 0, C-offer:** `C(z + U_p) = Fp(z − V_q) + a_q·z + 2 + sheetConstant`. -/
theorem sheetC_neg {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hε : (frameAt word).eps = -1) (z : Site) :
    (frameAt word).sheetC (FqW word) (z + Upar word) =
      FqW word (z - (frameAt word).parents.even.unmodifiedDeck.transverse)
        + ((frameAt word).siblingSlope z + 2) + (frameAt word).sheetConstant := by
  have hdet := eps_eq_det (word := word)
  rw [hε] at hdet
  have hp : FqW word (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den) + Upar word) =
      FqW word (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) :=
    quarterTurnField_Upar_period h hSE _
  unfold ChildFrame.sheetC ChildFrame.sheetShift ChildFrame.sheetOffset ChildFrame.siblingSlope
  rw [phaseW_neg hε, sub_zero, one_smul, hε, even_kernel, even_transverse]
  have e : z + Upar word - ((frameAt word).parents.even.den, (frameAt word).parents.even.num)
      - (((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den) +
        (-1 : ℤ) • ((frameAt word).parents.even.den, (frameAt word).parents.even.num))
      = (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) + Upar word := by
    ext <;> simp <;> ring
  rw [e, hp]
  have key : (frameAt word).parents.even.num * (frameAt word).parents.odd.den
      - (frameAt word).parents.even.den * (frameAt word).parents.odd.num = 1 := by
    linear_combination hdet
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Upar]
  linear_combination 2 * key

/-- **Phase 1, A-offer:** `A(z + U_q) = Fp(z + U_q)` (the shift `sheetShift` vanishes). -/
theorem sheetA_pos {word : Word} (hε : (frameAt word).eps = 1) (z : Site) :
    (frameAt word).sheetA (FqW word) z = FqW word z := by
  unfold ChildFrame.sheetA ChildFrame.sheetShift
  rw [phaseW_pos hε, sub_self, zero_smul, sub_zero]

/-- **Phase 1, C-offer:** `C(z + U_q) = Fp(z − V_q) + a_q·z + sheetConstant`. -/
theorem sheetC_pos {word : Word} (hε : (frameAt word).eps = 1) (z : Site) :
    (frameAt word).sheetC (FqW word) (z + (frameAt word).parents.even.unmodifiedDeck.kernel) =
      FqW word (z - (frameAt word).parents.even.unmodifiedDeck.transverse)
        + (frameAt word).siblingSlope z + (frameAt word).sheetConstant := by
  unfold ChildFrame.sheetC ChildFrame.sheetShift ChildFrame.sheetOffset ChildFrame.siblingSlope
  rw [phaseW_pos hε, sub_self, zero_smul, sub_zero, hε, even_kernel, even_transverse]
  have e : z + ((frameAt word).parents.even.den, (frameAt word).parents.even.num)
      - (((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den) +
        (1 : ℤ) • ((frameAt word).parents.even.den, (frameAt word).parents.even.num))
      = z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den) := by
    ext <;> simp
    ring
  rw [e]
  simp only [Prod.fst_add, Prod.snd_add]
  ring_nf

end FLatticePaper.SheetOffsets
