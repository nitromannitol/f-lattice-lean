import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.Q3Paragraph8
import FLatticePaper.Plane.Induction.MatchedPolicy
import FLatticePaper.Plane.Induction.ShortPassages

/-! Task 72 (case (b), link 2): the conjugate coordinates at the old root `zTurn x`, and the H-web of a free conjugate V site.

* `conj_tGrade_zTurn`, `conj_sGrade_zTurn`: the conjugate grades at `zTurn x` are linear in the parent coordinates,
  `t_c(zTurn x) = L_p − s_p(x)` and `s_c(zTurn x) = 2 (t_p(x) − n_p)`, with `L_p = d_p + n_p`.
* `conj_freeV_hweb`: a free conjugate V site `zTurn x + combine i j` gives `HRootWeb (t_p x + i T_p)`.
* `H_translate_drop_excluded`: the drop `a(x) = 1, a(y) = 0` is impossible when both `x` and `y` translate to the zero strip by the
  same vector `−i V_p`, since the translation shifts `a` by the same constant at both points. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper ShortPassages

/-- The parent period `T_p = d_p² + 2 d_p n_p − n_p²` of the odd parent. -/
def oddParentPeriod (frame : ChildFrame) : ℤ :=
  frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2

/-- The conjugate `t`-grade at the old root: `t_c(zTurn x) = (d_p + n_p) − s_p(x)`. -/
theorem conj_tGrade_zTurn {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x : Site) :
    (frameAt (conjWord word)).tGrade (zTurn x) =
      (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - (frameAt word).parentSGrade x := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hn, hd⟩ := conj_child_num_den hc
  simp only [ChildFrame.tGrade, ChildFrame.parentSGrade, zTurn]
  rw [hn, hd]
  ring

/-- The conjugate `s`-grade at the old root: `s_c(zTurn x) = 2 (t_p(x) − n_p)`. -/
theorem conj_sGrade_zTurn {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x : Site) :
    (frameAt (conjWord word)).sGrade (zTurn x) =
      2 * ((frameAt word).parentTGrade x - (frameAt word).parents.odd.num) := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hn, hd⟩ := conj_child_num_den hc
  simp only [ChildFrame.sGrade, ChildFrame.parentTGrade, zTurn]
  rw [hn, hd]
  ring

/-- The conjugate period is twice the parent period: `T_c = 2 T_p`. -/
theorem conj_periodDenominator {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).child.periodDenominator = 2 * oddParentPeriod (frameAt word) := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hn, hd⟩ := conj_child_num_den hc
  rw [(period_facts (frameAt (conjWord word))).1, hn, hd]
  unfold oddParentPeriod
  ring

/-- **A free conjugate V site gives the H-web of the translated parent root.** The conjugate `s`-grade of
`zTurn x + combine i j` is `2 (t_p x + i T_p − n_p)`, and the conjugate V spectrum in that variable is `HRootWeb`. -/
theorem conj_freeV_hweb {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {x : Site} {i j : ℤ}
    (hf : zTurn x + (frameAt (conjWord word)).child.modifiedDeck.combine i j ∈ (frameAt (conjWord word)).freeV) :
    HRootWeb (frameAt word).parents.odd.num (frameAt word).parents.odd.den
      ((frameAt word).parentTGrade x + i * oddParentPeriod (frameAt word)) := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hn, hd⟩ := conj_child_num_den hc
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hf
  obtain ⟨-, -, hvs⟩ := hf
  rw [sGrade_add_combine, conj_sGrade_zTurn h, conj_periodDenominator h] at hvs
  have key : 2 * ((frameAt word).parentTGrade x - (frameAt word).parents.odd.num) +
      i * (2 * oddParentPeriod (frameAt word)) =
      2 * ((frameAt word).parentTGrade x + i * oddParentPeriod (frameAt word) - (frameAt word).parents.odd.num) := by
    ring
  rw [key] at hvs
  unfold ChildFrame.vSpectrum at hvs
  rw [hn, hd] at hvs
  generalize (frameAt word).parentTGrade x + i * oddParentPeriod (frameAt word) = u at hvs ⊢
  unfold HRootWeb
  omega

/-- The parent `t`-grade of the vertical translate `−i V_p` is `t_p x + i T_p`. -/
theorem parentTGrade_translate_V (frame : ChildFrame) (x : Site) (i : ℤ) :
    frame.parentTGrade (x + (0 * (2 * frame.parents.odd.den) + -i * (frame.parents.odd.num - frame.parents.odd.den),
      0 * (2 * frame.parents.odd.num) + -i * (frame.parents.odd.num + frame.parents.odd.den))) =
      frame.parentTGrade x + i * oddParentPeriod frame := by
  unfold ChildFrame.parentTGrade oddParentPeriod
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- **A zero strip gives a zero jump.** The two arguments of the star lie in `1 − D ≤ t_p ≤ N + 2D − 1`. -/
theorem jumpA_zero_of_strip {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site)
    (hlo : 1 - (frameAt word).parents.odd.den ≤ (frameAt word).parentTGrade x)
    (hhi : (frameAt word).parentTGrade x + 1 ≤ (frameAt word).parents.odd.num + 2 * (frameAt word).parents.odd.den - 1) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 0 := by
  have hsh := parentTGrade_add_eps_uq (frameAt word) x
  have hx := zeroStrip_of_strong h hSE x hlo (by omega)
  have hx' := zeroStrip_of_strong h hSE
    (x + ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num))
    (by rw [hsh]; omega) (by rw [hsh]; omega)
  unfold jumpA
  rw [hx', hx]
  norm_num

/-- **The H-drop at the translate is impossible.** Translating `x` and `y` by the same `−i V_p`, the jump shifts by the same
constant, so `a(x) = a(y)`; the H-web at `x` gives the zero strip at its translate, and the zero strip at `y` gives the zero
jump there. The neighbour zero strip `hsy` is the remaining input. -/
theorem H_translate_drop_excluded {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {x y : Site} {i : ℤ}
    (hx : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1)
    (hy : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) y = 0)
    (hwx : HRootWeb (frameAt word).parents.odd.num (frameAt word).parents.odd.den
      ((frameAt word).parentTGrade x + i * oddParentPeriod (frameAt word)))
    (hsy : 1 - (frameAt word).parents.odd.den ≤ (frameAt word).parentTGrade y + i * oddParentPeriod (frameAt word) ∧
      (frameAt word).parentTGrade y + i * oddParentPeriod (frameAt word) + 1 ≤
        (frameAt word).parents.odd.num + 2 * (frameAt word).parents.odd.den - 1) : False := by
  have hN := frameAt_odd_num_pos h
  obtain ⟨-, -, hNle⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hND : (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den := by omega
  have hA : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (x +
      (0 * (2 * (frameAt word).parents.odd.den) + -i * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        0 * (2 * (frameAt word).parents.odd.num) + -i * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x + -i :=
    aVal_translate_UV h hSE 0 (-i) x
  have hB : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (y +
      (0 * (2 * (frameAt word).parents.odd.den) + -i * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        0 * (2 * (frameAt word).parents.odd.num) + -i * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) y + -i :=
    aVal_translate_UV h hSE 0 (-i) y
  have zA := jumpA_zero_of_strip h hSE _
    (by rw [parentTGrade_translate_V]; exact (web_args_in_strip hN hND hwx).1)
    (by rw [parentTGrade_translate_V]; exact (web_args_in_strip hN hND hwx).2)
  have zB := jumpA_zero_of_strip h hSE _
    (by rw [parentTGrade_translate_V]; exact hsy.1)
    (by rw [parentTGrade_translate_V]; exact hsy.2)
  rw [hA, hx] at zA
  rw [hB, hy] at zB
  omega

end FLatticePaper.Induction
