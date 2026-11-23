import FLatticePaper.Plane.Induction.Q3Field

/-! Task 59, paragraph 8 (the native old H star): both arguments of `a` vanish by the zero strip.

With `f = quarterTurnField (standardField (conjWord word))` and `a(x) = f(x + ε U_q) − f(x)`:
* the zero strip (`StrongEstimates.zeroStripInterval`): `f(x) = 0` whenever `1 − D ≤ t_p(x) ≤ N + 2D − 1`, where `N, D`
  are the parents of the word (`parentN_conjWord`, `parentD_conjWord`: the conjugate child is `(D−N, D+N)`);
* `t_p(x + ε U_q) = t_p(x) + 1` (`parentTGrade_add_eps_uq`, from `N d_q − D n_q = ε` and `ε² = 1`);
* the old H roots have `t_p` in the ParentWeb value set: the named hypothesis `HRootWeb` (category (iv), the regular floor
  step of the web is not yet proved; the exceptional values are in `ParentWeb.lean`).
Then `t_p(x)` and `t_p(x) + 1` both lie in the strip, so `a(x) = 0`.

The V-star part of paragraph 8 (`a ∈ {0,1}` and the `j = 0` translate) is not formalized here: it uses the monotone V path
and the translate index of `d_f`, which are not in the interface. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem parentN_conjWord {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    parentN (conjWord word) = (frameAt word).parents.odd.num := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hn, hd⟩ := conj_child_num_den hc
  unfold parentN
  rw [hn, hd]
  omega

theorem parentD_conjWord {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    parentD (conjWord word) = (frameAt word).parents.odd.den := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hn, hd⟩ := conj_child_num_den hc
  unfold parentD
  rw [hn, hd]
  omega

/-- The zero strip of the quarter-turned earlier field, in the parent transverse coordinate `t_p`. -/
theorem zeroStrip_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site)
    (h1 : 1 - (frameAt word).parents.odd.den ≤ (frameAt word).parentTGrade x)
    (h2 : (frameAt word).parentTGrade x ≤ (frameAt word).parents.odd.num + 2 * (frameAt word).parents.odd.den - 1) :
    quarterTurnField (standardField (conjWord word)) x = 0 := by
  have hN := parentN_conjWord h
  have hD := parentD_conjWord h
  have hz := hSE.zeroStripInterval x
  rw [hN, hD] at hz
  unfold ChildFrame.parentTGrade at h1 h2
  exact hz h1 h2

/-- `t_p(x + ε U_q) = t_p(x) + 1`, with `U_q = (d_q, n_q)` the even parent's kernel. -/
theorem parentTGrade_add_eps_uq (frame : ChildFrame) (x : Site) :
    frame.parentTGrade (x + (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num)) =
      frame.parentTGrade x + 1 := by
  have hdet := frame.eps_det_even
  have hε := frame.eps_sq_one
  unfold ChildFrame.parentTGrade
  simp only [Prod.fst_add, Prod.snd_add]
  linear_combination frame.eps * hdet + hε

/-- The H-root web values of `t_p` (ParentWeb): regular even `[1, N+D−1]`, exceptional even `{0, N+D}`, odd `[N, D]`,
exceptional odd `{D+1}`. Named hypothesis for the old H roots (category (iv)). -/
def HRootWeb (N D t : ℤ) : Prop :=
  (1 ≤ t ∧ t ≤ N + D - 1) ∨ t = 0 ∨ t = N + D ∨ (N ≤ t ∧ t ≤ D) ∨ t = D + 1

theorem web_args_in_strip {N D t : ℤ} (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hw : HRootWeb N D t) :
    1 - D ≤ t ∧ t + 1 ≤ N + 2 * D - 1 := by
  unfold HRootWeb at hw
  omega

/-- Paragraph 8 (H star): both arguments of `a` vanish, so `a(x) = 0`, at an old H root. -/
theorem H_root_a_eq_zero {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site)
    (hweb : HRootWeb (frameAt word).parents.odd.num (frameAt word).parents.odd.den ((frameAt word).parentTGrade x)) :
    quarterTurnField (standardField (conjWord word))
        (x + ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num)) -
      quarterTurnField (standardField (conjWord word)) x = 0 := by
  have hN := frameAt_odd_num_pos h
  obtain ⟨-, -, hNle⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hND : (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den := by omega
  obtain ⟨hlo, hhi⟩ := web_args_in_strip hN hND hweb
  have hsh := parentTGrade_add_eps_uq (frameAt word) x
  have hx := zeroStrip_of_strong h hSE x hlo (by omega)
  have hx' := zeroStrip_of_strong h hSE
    (x + ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num))
    (by rw [hsh]; omega) (by rw [hsh]; omega)
  rw [hx', hx]
  norm_num

end FLatticePaper.Induction
