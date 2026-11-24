import FLatticePaper.Plane.Induction.ConjFreeRoot
import FLatticePaper.Plane.Induction.EvenWindow

/-! Task 72 (hNegTie, the translate case of the free V root).

A free conjugate V translate `zTurn x + combine i j` of a jump-one site `x` is impossible when `x` has a parity input `y` with jump `0`.

* `parentTGrade_uv`, `zTurn_add_uv`: the word translate `λ = jU − iV` (the `aVal_translate_UV` vector) moves `t_p` by `iT` and the
  conjugate point `zTurn` by `combine i j`.
* `incomingNeg_add_even`, `incomingPos_add_even`: the parity inputs are translation-equivariant under the deck (even sum).
* `jumpA_input_of_freeV`: at a free conjugate V site `zTurn x` (sharp band `1 ≤ t_p x ≤ N + D − 1`), each parity input `y` has jump `0`:
  the odd inputs lie in the zero strip (`jumpA_zero_of_strip`), the even inputs in the extended even window (`jumpA_zero_of_even_window`).
* `negTie_translate_V_false`: the root translate has jump `0` (`H_root_a_eq_zero`), so `i = 1` (`aVal_translate_UV` shifts by `−i`);
  the input translate has jump `0` by `jumpA_input_of_freeV`, so `i = 0`. Contradiction. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem parentTGrade_uv (frame : ChildFrame) (x : Site) (k m : ℤ) :
    frame.parentTGrade (x + (k * (2 * frame.parents.odd.den) + m * (frame.parents.odd.num - frame.parents.odd.den),
      k * (2 * frame.parents.odd.num) + m * (frame.parents.odd.num + frame.parents.odd.den))) =
      frame.parentTGrade x - m * oddParentPeriod frame := by
  unfold ChildFrame.parentTGrade oddParentPeriod
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem zTurn_add_uv {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x : Site) (i j : ℤ) :
    zTurn (x + (j * (2 * (frameAt word).parents.odd.den) + -i * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
      j * (2 * (frameAt word).parents.odd.num) + -i * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) =
      zTurn x + (frameAt (conjWord word)).child.modifiedDeck.combine i j := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hn, hd⟩ := conj_child_num_den hc
  rw [ChildFrame.child_modifiedDeck_combine, hn, hd]
  unfold zTurn
  ext <;> simp <;> ring

theorem incomingNeg_add_even (x v : Site) (hv : (v.1 + v.2) % 2 = 0) :
    incomingNeg (x + v) = incomingNeg x + v := by
  unfold incomingNeg EvenSite
  simp only [Prod.fst_add, Prod.snd_add] at *
  split_ifs <;> first | (exfalso; omega) | (ext <;> simp; ring)

theorem incomingPos_add_even (x v : Site) (hv : (v.1 + v.2) % 2 = 0) :
    incomingPos (x + v) = incomingPos x + v := by
  unfold incomingPos EvenSite
  simp only [Prod.fst_add, Prod.snd_add] at *
  split_ifs <;> first | (exfalso; omega) | (ext <;> simp; ring)

/-- **The parity inputs of a free conjugate V site have jump `0`.** -/
theorem jumpA_input_of_freeV {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word)) {x : Site}
    (hf : zTurn x ∈ (frameAt (conjWord word)).freeV) {y : Site}
    (hy : y = incomingNeg x ∨ y = incomingPos x) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) y = 0 := by
  have hf' : zTurn x + (frameAt (conjWord word)).child.modifiedDeck.combine 0 0 ∈
      (frameAt (conjWord word)).freeV := by
    rw [ChildFrame.combine_zero_zero]
    simpa using hf
  obtain ⟨hb1, hb2⟩ := conj_freeV_band h hf'
  simp only [zero_mul, add_zero] at hb1 hb2
  have hN := frameAt_odd_num_pos h
  obtain ⟨-, -, hNle⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hND : (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den := by omega
  by_cases hEx : EvenSite x
  · -- even `x`: the inputs are odd, horizontal, the parent height moves by `±N`; the zero strip applies
    simp only [incomingNeg, incomingPos, if_pos hEx] at hy
    rcases hy with rfl | rfl
    · have e1 : (frameAt word).parentTGrade (x.1 - 1, x.2) =
          (frameAt word).parentTGrade x - (frameAt word).parents.odd.num := by
        unfold ChildFrame.parentTGrade; ring
      exact jumpA_zero_of_strip h hSE _ (by rw [e1]; omega) (by rw [e1]; omega)
    · have e1 : (frameAt word).parentTGrade (x.1 + 1, x.2) =
          (frameAt word).parentTGrade x + (frameAt word).parents.odd.num := by
        unfold ChildFrame.parentTGrade; ring
      exact jumpA_zero_of_strip h hSE _ (by rw [e1]; omega) (by rw [e1]; omega)
  · -- odd `x`: the inputs are even, vertical, the parent height moves by `±D`; the extended even window applies
    simp only [incomingNeg, incomingPos, if_neg hEx] at hy
    rcases hy with rfl | rfl
    · have ev : EvenSite (x.1, x.2 - 1) := by
        unfold EvenSite at *
        simp only at *
        omega
      have e1 : (frameAt word).parentTGrade (x.1, x.2 - 1) =
          (frameAt word).parentTGrade x + (frameAt word).parents.odd.den := by
        unfold ChildFrame.parentTGrade; ring
      exact jumpA_zero_of_even_window h hSE hpar _ ev (by rw [e1]; omega) (by rw [e1]; omega)
        (by rw [e1]; omega) (by rw [e1]; omega)
    · have ev : EvenSite (x.1, x.2 + 1) := by
        unfold EvenSite at *
        simp only at *
        omega
      have e1 : (frameAt word).parentTGrade (x.1, x.2 + 1) =
          (frameAt word).parentTGrade x - (frameAt word).parents.odd.den := by
        unfold ChildFrame.parentTGrade; ring
      exact jumpA_zero_of_even_window h hSE hpar _ ev (by rw [e1]; omega) (by rw [e1]; omega)
        (by rw [e1]; omega) (by rw [e1]; omega)

/-- **The free V translate of a jump-one site is impossible when it has a jump-zero parity input.** -/
theorem negTie_translate_V_false {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    {x y : Site} {i j : ℤ}
    (hx : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1)
    (hy : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) y = 0)
    (hyx : y = incomingNeg x ∨ y = incomingPos x)
    (hf : zTurn x + (frameAt (conjWord word)).child.modifiedDeck.combine i j ∈ (frameAt (conjWord word)).freeV) :
    False := by
  set lam : Site := (j * (2 * (frameAt word).parents.odd.den) + -i * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
      j * (2 * (frameAt word).parents.odd.num) + -i * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) with hlam
  have hf' : zTurn (x + lam) ∈ (frameAt (conjWord word)).freeV := by
    have hzT : zTurn (x + lam) = zTurn x + (frameAt (conjWord word)).child.modifiedDeck.combine i j :=
      zTurn_add_uv h x i j
    rw [hzT]
    exact hf
  have hev : (lam.1 + lam.2) % 2 = 0 := by
    have e : lam.1 + lam.2 = 2 * (j * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) -
        i * (frameAt word).parents.odd.num) := by
      rw [hlam]
      ring
    rw [e]
    omega
  have hyl : y + lam = incomingNeg (x + lam) ∨ y + lam = incomingPos (x + lam) := by
    rcases hyx with rfl | rfl
    · left; rw [incomingNeg_add_even _ _ hev]
    · right; rw [incomingPos_add_even _ _ hev]
  have hyz : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (y + lam) = 0 :=
    jumpA_input_of_freeV h hSE hpar hf' hyl
  have hf0 : zTurn (x + lam) + (frameAt (conjWord word)).child.modifiedDeck.combine 0 0 ∈
      (frameAt (conjWord word)).freeV := by
    rw [ChildFrame.combine_zero_zero]
    simpa using hf'
  have hweb := conj_freeV_hweb h hf0
  simp only [zero_mul, add_zero] at hweb
  have hroot : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (x + lam) = 0 :=
    H_root_a_eq_zero h hSE _ hweb
  have hA : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (x + lam) =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x + -i :=
    aVal_translate_UV h hSE j (-i) x
  have hB : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (y + lam) =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) y + -i :=
    aVal_translate_UV h hSE j (-i) y
  omega

end FLatticePaper.Induction
