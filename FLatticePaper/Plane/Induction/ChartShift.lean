import FLatticePaper.Plane.Induction.ChartPeriods
import FLatticePaper.Plane.Induction.SheetCharts
import FLatticePaper.Plane.Induction.Q3Bound
import FLatticePaper.Plane.Induction.Q3Strong
import FLatticePaper.Construction.NominalAgreement

/-! Task 66 (2)(b): the sheets at the shifted points and at the adjacent representative.

With `f = quarterTurnField G`, `G = standardField (conjWord word)`, `σ = shortShift = ε U_p`, `U_q = (d_q, n_q)`,
`e = sheetOffset`, `lv = sheetShift`:
* `sheetA_add_shortShift`: `A(x + σ) = A(x)` (the zero `U_p`-period of `f`);
* `sheetC_add_shortShift`: `C(x + σ) = C(x) − 2` (the sibling slope of `σ` is `−2`);
* `sheetA_sub_eps_Uq`: `A(x − ε U_q) − A(x) = p(x − lv)`, the paragraph-5 price;
* `sheetC_sub_eps_Uq`: `C(x − ε U_q) − A(x) = Ψ(x) + p(x − lv − e)`.
Here `p(y) = pW word y = cutPrice − price(Z y)` (`SheetCharts`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem quarterTurnField_add_shortShift {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    quarterTurnField (standardField (conjWord word)) (x + (frameAt word).shortShift) =
      quarterTurnField (standardField (conjWord word)) x := by
  rcases (frameAt word).eps_unit with he | he
  · have hsh : (frameAt word).shortShift = Upar word := by
      unfold ChildFrame.shortShift Upar
      rw [he]
      ext <;> simp only <;> ring
    rw [hsh]
    exact quarterTurnField_Upar_period h hSE x
  · have hsh : (frameAt word).shortShift = -Upar word := by
      unfold ChildFrame.shortShift Upar
      rw [he]
      ext <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring
    rw [hsh, ← sub_eq_add_neg]
    have h1 := quarterTurnField_Upar_period h hSE (x - Upar word)
    rw [sub_add_cancel] at h1
    exact h1.symm

theorem sheetA_add_shortShift {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (x + (frameAt word).shortShift) =
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) x := by
  unfold ChildFrame.sheetA
  rw [show x + (frameAt word).shortShift - (frameAt word).sheetShift =
      (x - (frameAt word).sheetShift) + (frameAt word).shortShift by abel]
  exact quarterTurnField_add_shortShift h hSE _

theorem sheetC_add_shortShift {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (x + (frameAt word).shortShift) =
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) x - 2 := by
  have hdet := (frameAt word).eps_det_even
  have hsq := (frameAt word).eps_sq_one
  unfold ChildFrame.sheetC
  rw [show x + (frameAt word).shortShift - (frameAt word).sheetShift - (frameAt word).sheetOffset =
      (x - (frameAt word).sheetShift - (frameAt word).sheetOffset) + (frameAt word).shortShift by abel]
  rw [quarterTurnField_add_shortShift h hSE]
  unfold ChildFrame.siblingSlope ChildFrame.shortShift
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  linear_combination (-2 * (frameAt word).eps) * hdet - 2 * hsq

/-- `sheetStep = sheetOffset` (both are `V_q + ε U_q`). -/
theorem sheetStep_eq_sheetOffset (word : Word) : (frameAt word).sheetStep = (frameAt word).sheetOffset := by
  rw [FLatticePaper.Construction.sheetOffset_eq]
  rfl

/-- The adjacent offer at the even representative `x − ε U_q`: `A(x − εU_q) − A(x) = p(x − l_v)`. -/
theorem sheetA_sub_eps_Uq {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word)))
        (x - ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num)) -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) x =
    pW word (x - (frameAt word).sheetShift) := by
  have h5 := paragraph5_field_identity_of_strong h hSE (x - (frameAt word).sheetShift)
  simp only [neg_mul] at h5
  unfold ChildFrame.sheetA pW
  unfold zTurn
  have e : x - ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num) -
      (frameAt word).sheetShift = (x - (frameAt word).sheetShift) +
        (-((frameAt word).eps * (frameAt word).parents.even.den), -((frameAt word).eps * (frameAt word).parents.even.num)) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
  rw [e]
  linarith

/-- The adjacent offer of the sheet `C` at `x − ε U_q`: `C(x − εU_q) − A(x) = Ψ(x) + p(x − l_v − e)`. -/
theorem sheetC_sub_eps_Uq {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    (frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))
        (x - ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num)) -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) x =
    sheetDiffW word x + pW word (x - (frameAt word).sheetShift - (frameAt word).sheetOffset) := by
  have h5 := paragraph5_field_identity_of_strong h hSE (x - (frameAt word).sheetShift - (frameAt word).sheetOffset)
  simp only [neg_mul] at h5
  have hsib : (frameAt word).siblingSlope
      (x - ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num) -
        (frameAt word).sheetShift) = (frameAt word).siblingSlope (x - (frameAt word).sheetShift) := by
    unfold ChildFrame.siblingSlope
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  unfold sheetDiffW pW ChildFrame.sheetC ChildFrame.sheetA
  unfold zTurn
  have e : x - ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num) -
      (frameAt word).sheetShift - (frameAt word).sheetOffset =
      (x - (frameAt word).sheetShift - (frameAt word).sheetOffset) +
        (-((frameAt word).eps * (frameAt word).parents.even.den), -((frameAt word).eps * (frameAt word).parents.even.num)) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
  rw [e, hsib]
  linarith

end FLatticePaper.Induction
