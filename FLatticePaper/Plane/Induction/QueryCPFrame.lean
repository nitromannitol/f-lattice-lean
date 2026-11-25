import FLatticePaper.Plane.Induction.QueryCP
import FLatticePaper.Plane.Induction.QueryGrade
import FLatticePaper.Plane.Induction.TpFrame
import FLatticePaper.Plane.Induction.ParentGradeKernel

/-! Task w3, step 1(b)(C): the representative of the transport query is in the conjugate's closed polygon (frame level). -/

namespace FLatticePaper.QueryCPFrame

open Farey FLatticePaper FLatticePaper.Induction

/-- The conjugate's period denominator is `2 T_p`, with `T_p = D² + 2DN − N²` (the odd parent). -/
theorem conj_periodDenominator {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).child.periodDenominator =
      2 * ((frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
        (frameAt word).parents.odd.num ^ 2) := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  unfold Fraction.periodDenominator
  rw [hcn, hcd]
  ring

/-- **The representative of an odd-x query is even:** `x` odd, `N ≤ t_p(x) ≤ D`, then `rep` lies in the conjugate's even window. -/
theorem rep_mem_of_odd {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x : ℤ × ℤ) (m i : ℤ)
    (hk : x.1 - 1 = 2 * (frameAt word).parents.odd.den * m + i) (hi0 : 0 ≤ i)
    (hi1 : i < 2 * (frameAt word).parents.odd.den) (hxo : ¬ EvenSite x)
    (hN : 1 ≤ (frameAt word).parents.odd.num) (hND : (frameAt word).parents.odd.num < (frameAt word).parents.odd.den)
    (htp0 : (frameAt word).parents.odd.num ≤ (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2)
    (htp1 : (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2 ≤ (frameAt word).parents.odd.den) :
    ((-x.2 + 2 * (frameAt word).parents.odd.num * m, i) : ℤ × ℤ) ∈ (frameAt (conjWord word)).closedPolygon := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  set N := (frameAt word).parents.odd.num with hNdef
  set D := (frameAt word).parents.odd.den with hDdef
  have hper := conj_periodDenominator h
  rw [← hNdef, ← hDdef] at hper
  have hpar : EvenSite ((-x.2 + 2 * N * m, i) : ℤ × ℤ) := by
    unfold EvenSite
    have e : (-x.2 + 2 * N * m) + i = (x.1 - x.2 - 1) + 2 * (m * (N - D)) := by
      linear_combination (-1 : ℤ) * hk
    simp only
    rw [e]
    unfold EvenSite at hxo
    generalize m * (N - D) = c
    omega
  have hT := QueryCP.key_tprime N D x.1 x.2 m i hk
  have hS := QueryCP.key_sprime N D x.1 x.2 m i hk
  have hw := QueryCP.even_window N D (N * x.1 - D * x.2) i
    ((D - N) * (-x.2 + 2 * N * m) - (D + N) * i) hN hND hi0 hi1 htp0 htp1 hT
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq]
  rw [if_pos hpar]
  unfold ChildFrame.tGrade ChildFrame.sGrade
  simp only
  rw [hcn, hcd, hper]
  refine ⟨by linarith [hw.1], by linarith [hw.2], by nlinarith, by nlinarith⟩

/-- **The representative of an even-x query is odd:** `x` even, `1 ≤ t_p(x) ≤ r`, then `rep` lies in the conjugate's odd window. -/
theorem rep_mem_of_even {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x : ℤ × ℤ) (m i : ℤ)
    (hk : x.1 - 1 = 2 * (frameAt word).parents.odd.den * m + i) (hi0 : 0 ≤ i)
    (hi1 : i < 2 * (frameAt word).parents.odd.den) (hxe : EvenSite x)
    (hN : 1 ≤ (frameAt word).parents.odd.num) (hND : (frameAt word).parents.odd.num < (frameAt word).parents.odd.den)
    (htp0 : 1 ≤ (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2)
    (htp1 : (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2 ≤
      (frameAt word).parents.odd.den + (frameAt word).parents.odd.num) :
    ((-x.2 + 2 * (frameAt word).parents.odd.num * m, i) : ℤ × ℤ) ∈ (frameAt (conjWord word)).closedPolygon := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  set N := (frameAt word).parents.odd.num with hNdef
  set D := (frameAt word).parents.odd.den with hDdef
  have hper := conj_periodDenominator h
  rw [← hNdef, ← hDdef] at hper
  have hpar : ¬ EvenSite ((-x.2 + 2 * N * m, i) : ℤ × ℤ) := by
    unfold EvenSite at hxe ⊢
    have e : (-x.2 + 2 * N * m) + i = (x.1 - x.2 - 1) + 2 * (m * (N - D)) := by
      linear_combination (-1 : ℤ) * hk
    simp only
    rw [e]
    generalize m * (N - D) = c
    omega
  have hT := QueryCP.key_tprime N D x.1 x.2 m i hk
  have hS := QueryCP.key_sprime N D x.1 x.2 m i hk
  have hw := QueryCP.odd_window N D (N * x.1 - D * x.2) i
    ((D - N) * (-x.2 + 2 * N * m) - (D + N) * i) hN hND hi0 hi1 htp0 htp1 hT
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq]
  rw [if_neg hpar]
  unfold ChildFrame.tGrade ChildFrame.sGrade
  simp only
  rw [hcn, hcd, hper]
  refine ⟨by linarith [hw.1], by linarith [hw.2], by nlinarith, by nlinarith⟩

/-- **The exit of the representative:** `rep − (1, 0)` leaves the conjugate's closed polygon, when `t_p(x) ≤ D` for odd `x`
or `t_p(x) ≤ r − 1` for even `x` (the window of the query). -/
theorem exit_of_rep {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x : ℤ × ℤ) (m i : ℤ)
    (hk : x.1 - 1 = 2 * (frameAt word).parents.odd.den * m + i)
    (hexit : (¬ EvenSite x ∧ (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2 ≤
        (frameAt word).parents.odd.den) ∨
      (EvenSite x ∧ (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2 ≤
        (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1)) :
    ((-x.2 + 2 * (frameAt word).parents.odd.num * m - 1, i) : ℤ × ℤ) ∉ (frameAt (conjWord word)).closedPolygon := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  set N := (frameAt word).parents.odd.num with hNdef
  set D := (frameAt word).parents.odd.den with hDdef
  have hper := conj_periodDenominator h
  rw [← hNdef, ← hDdef] at hper
  have hT := QueryCP.key_sprime N D x.1 x.2 m i hk
  intro hmem
  unfold ChildFrame.closedPolygon at hmem
  simp only [Set.mem_setOf_eq] at hmem
  unfold ChildFrame.sGrade at hmem
  simp only [hcn, hcd] at hmem
  rcases hexit with ⟨hxo, htp⟩ | ⟨hxe, htp⟩
  · -- x odd: the representative is even, its neighbour is odd
    have hpar : ¬ EvenSite ((-x.2 + 2 * N * m - 1, i) : ℤ × ℤ) := by
      unfold EvenSite at hxo ⊢
      have e : (-x.2 + 2 * N * m - 1 + i) = (x.1 - x.2 - 1) + 2 * (m * (N - D)) - 1 := by
        linear_combination (-1 : ℤ) * hk
      rw [e]
      generalize m * (N - D) = c
      omega
    rw [if_neg hpar] at hmem
    unfold ChildFrame.tGrade at hmem
    have hs := hmem.2.2.1
    nlinarith
  · have hpar : EvenSite ((-x.2 + 2 * N * m - 1, i) : ℤ × ℤ) := by
      unfold EvenSite at hxe ⊢
      have e : (-x.2 + 2 * N * m - 1 + i) = (x.1 - x.2 - 1) + 2 * (m * (N - D)) - 1 := by
        linear_combination (-1 : ℤ) * hk
      rw [e]
      generalize m * (N - D) = c
      omega
    rw [if_pos hpar] at hmem
    have hs := hmem.2.2.1
    nlinarith

/-- **The H-form:** `x` even with `t_p(x) = r = D + N` gives `x − I = 2m (D, N)`, so `Z x = (1, 0) + m V'` and its ordinate is
`m L' = 2 D m`. The coprimality `N, D` and `D + N` odd are the parent facts. -/
theorem hform_of_tp (N D : ℤ) (x : ℤ × ℤ) (hcop : IsCoprime N D) (hN : N ≠ 0) (hodd : (D + N) % 2 = 1)
    (hxe : (x.1 + x.2) % 2 = 0) (htp : N * x.1 - D * x.2 = D + N) :
    ∃ m : ℤ, x.1 - 1 = 2 * D * m ∧ x.2 + 1 = 2 * N * m := by
  obtain ⟨k, hk1, hk2⟩ := FLatticePaper.ParentGradeKernel.vp_multiple N (-D) (x.1 - 1) (x.2 + 1) hcop.neg_right hN
    (by linear_combination htp)
  have hsum : x.1 + x.2 = (D + N) * k := by
    rw [show x.1 = (x.1 - 1) + 1 by ring, show x.2 = (x.2 + 1) - 1 by ring]
    linear_combination hk1 + hk2
  obtain ⟨c, hc | hc⟩ := Int.even_or_odd' k
  · refine ⟨c, ?_, ?_⟩
    · rw [hk1]; subst hc; ring
    · rw [hk2]; subst hc; ring
  · exfalso
    have e : x.1 + x.2 = 2 * (c * (D + N)) + (D + N) := by
      rw [hsum, hc]; ring
    generalize c * (D + N) = q at e
    omega

end FLatticePaper.QueryCPFrame
