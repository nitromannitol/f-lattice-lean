import FLatticePaper.Plane.Induction.HtopCross
import FLatticePaper.Plane.Induction.OppAlg

/-! # The sheet `C` at the kernel translate of an opposite site (`ε = +1`)

For `ε = +1` (so `W = 1`, `lv = 0`, `e = V_q + U_q`), the sheet is `C(w) = F_p(w − e) + a_q·w + c_e`. At `w = y + K` with
`K = (d, n)` the kernel of the child:

* `w − e = (y − V_q) + 2 Up`, with `Up = (odd.den, odd.num)`, since `K − U_q = 2 Up`;
* `F_p` is `2 Up`-periodic (`qtf_two_up`: the conjugate's transverse period, the harmonic shift `harmonic_shift_2Up` and the
  conjugate constant cancel);
* so `C(y + K) = F_p(y − V_q) + a_q·(y + K) + c_e`, and `F_p(y − V_q) = h₀(y − V_q)` is the hypothesis `hwin`
  (the parent window, see `OppParent`);
* the identity `h0_identity_plus` turns `h₀(y − V_q) + a_q·(y + K) + c_e` into `h₀(y)`. -/

namespace FLatticePaper.OppKernel

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.HtopCross FLatticePaper.OppAlg

/-- The parent quarter turn of the conjugate is invariant under the shift `2 Up`. -/
theorem qtf_two_up {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (w : Site) :
    quarterTurnField (standardField (conjWord word))
        (w + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)) =
      quarterTurnField (standardField (conjWord word)) w := by
  obtain ⟨-, hT, hVc, -⟩ := cross_common h hSE
  have hV : (frameAt (conjWord word)).coherentConstantV =
      -(((frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
        (frameAt word).parents.odd.num ^ 2) + (frameAt word).parents.odd.den) := by
    linarith
  rw [qtf_eq, qtf_eq]
  have hsite : (-(w + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)).2,
      (w + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)).1 - 1) =
      (-w.2, w.1 - 1) + (((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) -
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
        ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) +
          ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) := by
    ext <;> simp <;> ring
  have hh : harmonicGrid (w + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)) =
      harmonicGrid w + ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * w.1 +
        ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * w.2 +
        ((frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
          (frameAt word).parents.odd.num ^ 2 - (frameAt word).parents.odd.num) :=
    harmonic_shift_2Up w.1 w.2 (frameAt word).parents.odd.den (frameAt word).parents.odd.num
  rw [hsite, hT, hh]
  dsimp only
  linear_combination hV

/-- **The kernel translate of an opposite site, `ε = +1`.** `C(y + K) = h₀(y)`, given the parent window at `y − V_q`. -/
theorem sheetC_kernel_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hε : (frameAt word).eps = 1) (y : Site)
    (hwin : quarterTurnField (standardField (conjWord word))
        (y - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) =
      harmonicGrid (y - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den))) :
    (frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))
        (y + (frameAt word).child.modifiedDeck.kernel) = harmonicGrid y := by
  have hn := FLatticePaper.Induction.ZoneI1.child_num_eq (frameAt word)
  have hd := FLatticePaper.Induction.ZoneI1.child_den_eq (frameAt word)
  have hdet : (frameAt word).parents.odd.num * (frameAt word).parents.even.den -
      (frameAt word).parents.odd.den * (frameAt word).parents.even.num = 1 := by
    have := FLatticePaper.SheetOffsets.eps_eq_det (word := word)
    rw [hε] at this
    omega
  have hW : (frameAt word).phaseW = 1 := by
    unfold ChildFrame.phaseW
    rw [hε]
    norm_num
  have hnq : (frameAt word).parents.even.num % 2 = 1 := by
    obtain ⟨hnO, -⟩ := (frameAt word).child_odd
    omega
  have hdq : (frameAt word).parents.even.den % 2 = 1 := by
    obtain ⟨-, hdO⟩ := (frameAt word).child_odd
    omega
  have hce := sheetConstant_twice word 1 hW (Or.inr rfl) ⟨hnq, hdq⟩
  have key : harmonicGrid (y - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
        (frameAt word).parents.even.num + (frameAt word).parents.even.den)) +
      (frameAt word).parents.even.num * (y.1 + (2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den)) -
      (frameAt word).parents.even.den * (y.2 + (2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num)) +
      (frameAt word).sheetConstant = harmonicGrid y :=
    h0_identity_plus (N := (frameAt word).parents.odd.num) (D := (frameAt word).parents.odd.den)
      (nq := (frameAt word).parents.even.num) (dq := (frameAt word).parents.even.den)
      (y1 := y.1) (y2 := y.2) (ce := (frameAt word).sheetConstant) hdet (by linarith [hce])
  have hK := ChildFrame.child_modifiedDeck_kernel (frameAt word)
  have hsh : (frameAt word).sheetShift = 0 := by
    unfold ChildFrame.sheetShift
    rw [hW]
    simp
  have hof : (frameAt word).sheetOffset =
      ((frameAt word).parents.even.num, 2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den) := by
    unfold ChildFrame.sheetOffset
    rw [hε]
    simp only [Fraction.unmodifiedDeck, one_smul]
    ext
    · simp
    · simp
      ring
  unfold ChildFrame.sheetC
  rw [hK, hsh, sub_zero, hof]
  have e1 : y + ((frameAt word).child.den, (frameAt word).child.num) -
      ((frameAt word).parents.even.num, 2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den) =
      (y - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) +
        (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> linarith [hn, hd]
  rw [e1, qtf_two_up h hSE, hwin]
  unfold ChildFrame.siblingSlope
  simp only [Prod.fst_add, Prod.snd_add]
  linear_combination key + (frameAt word).parents.even.num * hd - (frameAt word).parents.even.den * hn

/-- **The sheet at an opposite site, `ε = −1`.** For `ε = −1` (so `W = 0`, `lv = U_q`, `e = V_q − U_q`), the sheet at `y` is
`h₀(y)`, given the parent window at `y − V_q`. No period is needed: `z − lv − e = y − V_q` exactly. -/
theorem sheetC_minus_at_y {word : Word} (hε : (frameAt word).eps = -1) (y : Site)
    (hwin : quarterTurnField (standardField (conjWord word))
        (y - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) =
      harmonicGrid (y - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den))) :
    (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) y = harmonicGrid y := by
  have hn := FLatticePaper.Induction.ZoneI1.child_num_eq (frameAt word)
  have hd := FLatticePaper.Induction.ZoneI1.child_den_eq (frameAt word)
  have hW : (frameAt word).phaseW = 0 := by
    unfold ChildFrame.phaseW
    rw [hε]
    norm_num
  have hnq : (frameAt word).parents.even.num % 2 = 1 := by
    obtain ⟨hnO, -⟩ := (frameAt word).child_odd
    omega
  have hdq : (frameAt word).parents.even.den % 2 = 1 := by
    obtain ⟨-, hdO⟩ := (frameAt word).child_odd
    omega
  have hce := sheetConstant_twice word 0 hW (Or.inl rfl) ⟨hnq, hdq⟩
  have key := h0_identity_minus (frameAt word).parents.even.num (frameAt word).parents.even.den y.1 y.2
    (frameAt word).sheetConstant (by linarith [hce])
  have hsh : (frameAt word).sheetShift =
      ((frameAt word).parents.even.den, (frameAt word).parents.even.num) := by
    unfold ChildFrame.sheetShift
    rw [hW]
    simp [Fraction.unmodifiedDeck]
  have hof : (frameAt word).sheetOffset =
      ((frameAt word).parents.even.num - 2 * (frameAt word).parents.even.den, (frameAt word).parents.even.den) := by
    unfold ChildFrame.sheetOffset
    rw [hε]
    simp only [Fraction.unmodifiedDeck, neg_smul, one_smul, Prod.mk_add_mk, Prod.neg_mk, Prod.mk.injEq]
    constructor <;> ring
  unfold ChildFrame.sheetC
  rw [hsh, hof]
  have e1 : y - ((frameAt word).parents.even.den, (frameAt word).parents.even.num) -
      ((frameAt word).parents.even.num - 2 * (frameAt word).parents.even.den, (frameAt word).parents.even.den) =
      y - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den) := by
    ext
    · simp only [Prod.fst_sub]
      ring
    · simp only [Prod.snd_sub]
      ring
  rw [e1, hwin]
  unfold ChildFrame.siblingSlope
  simp only [Prod.fst_sub, Prod.snd_sub]
  linear_combination key

end FLatticePaper.OppKernel
