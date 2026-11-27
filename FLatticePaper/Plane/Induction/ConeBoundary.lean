import FLatticePaper.Plane.Induction.ConeFaceArith
import FLatticePaper.Plane.Induction.ConeRoot
import FLatticePaper.Plane.Induction.Q3Exit
import FLatticePaper.Plane.Induction.Sheets
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.OddAxialRank

/-! # The closed-boundary inputs of a cone point (the face classification, frame form)

For an open cone point `x` of the cone of an odd free base `z`, every input `i` of `x` that is not open lies on one of two
faces: an even input has `tGrade i ≥ 2` (the H-cut), and an odd input has `sGrade i ≥ T + 2 − d + n` (the V-cut). The arithmetic is
in `FLatticePaper.ConeFaceArith`; this file unfolds the frame predicates. -/

namespace FLatticePaper.ConeBoundary

open FLatticePaper FLatticePaper.Induction FLatticePaper.ConeFaceArith

theorem periodDenominator_eq (frame : ChildFrame) :
    frame.child.periodDenominator =
      frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num := by
  unfold Farey.Fraction.periodDenominator
  ring

/-- Odd open point of the cone: its inputs are even; the even input `x - (0,1)` lies on the H side. -/
theorem even_input_H (frame : ChildFrame) {z x i : Site} (hz1 : 2 ≤ z.1)
    (hzt : frame.child.num + 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den - 2)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    {K : ℕ} (hx : frame.openRect x) (hcone : CapRay.ConeRoot z K x)
    (hi : i = incomingNeg x ∨ i = incomingPos x) (hiE : EvenSite i) (hiopen : ¬ frame.openRect i) :
    2 ≤ frame.tGrade i := by
  have hxo : ¬ EvenSite x := by
    intro hxe
    have hxe' : (x.1 + x.2) % 2 = 0 := hxe
    rcases hi with rfl | rfl
    · unfold incomingNeg at hiE
      rw [if_pos hxe] at hiE
      unfold EvenSite at hiE
      omega
    · unfold incomingPos at hiE
      rw [if_pos hxe] at hiE
      unfold EvenSite at hiE
      omega
  have hxo' : (x.1 + x.2) % 2 = 1 := by
    unfold EvenSite at hxo; omega
  obtain ⟨hn2, hd2⟩ := frame.child_odd
  have hcop : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  have hT := periodDenominator_eq frame
  have hopen := hx
  unfold ChildFrame.openRect at hopen
  rw [if_neg hxo] at hopen
  simp only [ChildFrame.tGrade, ChildFrame.sGrade] at hopen
  obtain ⟨hO1, hO2, hO3, hO4⟩ := hopen
  have hzt2 : frame.child.num * z.1 - frame.child.den * z.2 ≤ frame.child.den - 2 := hzt.2
  have hsz := base_s (n := frame.child.num) (d := frame.child.den) (T := frame.child.periodDenominator)
    hT hn1 hnd hz1 hzt2
  obtain ⟨hh, _, _, hodd⟩ := hcone
  have hha : x.2 - z.2 ≤ x.1 - z.1 := hodd hxo
  rcases hi with rfl | rfl
  · have hneg : incomingNeg x = (x.1, x.2 - 1) := by unfold incomingNeg; rw [if_neg hxo]
    rw [hneg] at hiE hiopen ⊢
    by_contra hlt
    push Not at hlt
    apply hiopen
    unfold ChildFrame.openRect
    rw [if_pos hiE]
    simp only [ChildFrame.tGrade, ChildFrame.sGrade] at hlt ⊢
    obtain ⟨g1, g2, g3⟩ := face_odd_neg hn1 hnd hsz hh hha hO1 hO4
    refine ⟨by linarith [g1], hlt, by linarith [g2], by linarith [g3]⟩
  · have hpos : incomingPos x = (x.1, x.2 + 1) := by unfold incomingPos; rw [if_neg hxo]
    rw [hpos] at hiE hiopen ⊢
    by_contra hlt
    push Not at hlt
    apply hiopen
    unfold ChildFrame.openRect
    rw [if_pos hiE]
    simp only [ChildFrame.tGrade, ChildFrame.sGrade] at hlt ⊢
    have hpa : x.2 - z.2 ≤ x.1 - z.1 := hha
    obtain ⟨g1, g2, g3⟩ := face_odd_pos hT hn1 hnd hn2 hd2 hcop hzt.1 hsz hh hpa hxo' hO1 hO2 hO3 hO4
    refine ⟨by linarith [g1], hlt, by linarith [g2], by linarith [g3]⟩

/-- An odd closed-boundary input of an open cone point is `x + (1,0)` at an even `x`, on the V-cut `sGrade ≥ T + 2 − d + n`. -/
theorem odd_input_V (frame : ChildFrame) {z x i : Site} (hz1 : 2 ≤ z.1)
    (hzt : frame.child.num + 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den - 2)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    {K : ℕ} (hx : frame.openRect x) (hcone : CapRay.ConeRoot z K x)
    (hi : i = incomingNeg x ∨ i = incomingPos x) (hiO : ¬ EvenSite i) (hiopen : ¬ frame.openRect i) :
    i = incomingPos x ∧ frame.child.periodDenominator + 2 - frame.child.den + frame.child.num ≤ frame.sGrade i := by
  have hxe : EvenSite x := by
    by_contra hxo
    rcases hi with rfl | rfl
    · unfold incomingNeg at hiO
      rw [if_neg hxo] at hiO
      exact hiO (show (x.1 + (x.2 - 1)) % 2 = 0 by
        have := hxo; unfold EvenSite at this; omega)
    · unfold incomingPos at hiO
      rw [if_neg hxo] at hiO
      exact hiO (show (x.1 + (x.2 + 1)) % 2 = 0 by
        have := hxo; unfold EvenSite at this; omega)
  have hxe' : (x.1 + x.2) % 2 = 0 := hxe
  obtain ⟨hn2, hd2⟩ := frame.child_odd
  have hcop : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  have hT := periodDenominator_eq frame
  have hzt2 : frame.child.num * z.1 - frame.child.den * z.2 ≤ frame.child.den - 2 := hzt.2
  have hzt1 : frame.child.num + 2 ≤ frame.child.num * z.1 - frame.child.den * z.2 := hzt.1
  have hsz := base_s (n := frame.child.num) (d := frame.child.den) (T := frame.child.periodDenominator)
    hT hn1 hnd hz1 hzt2
  have hopen := hx
  unfold ChildFrame.openRect at hopen
  rw [if_pos hxe] at hopen
  simp only [ChildFrame.tGrade, ChildFrame.sGrade] at hopen
  obtain ⟨hO1, hO2, hO3, hO4⟩ := hopen
  obtain ⟨hh, _, hodd_e, _⟩ := hcone
  have ha : x.2 - z.2 - 1 ≤ x.1 - z.1 := hodd_e hxe
  rcases hi with rfl | rfl
  · exfalso
    have hneg : incomingNeg x = (x.1 - 1, x.2) := by unfold incomingNeg; rw [if_pos hxe]
    rw [hneg] at hiopen
    apply hiopen
    unfold ChildFrame.openRect
    rw [if_neg (show ¬ EvenSite (x.1 - 1, x.2) from
      fun h => by have h' : (x.1 - 1 + x.2) % 2 = 0 := h; omega)]
    simp only [ChildFrame.tGrade, ChildFrame.sGrade]
    obtain ⟨g1, g2, g3, g4⟩ := face_even_neg hT hn1 hnd hzt1 hsz hh ha hO4 hO2
    exact ⟨g1, g2, g3, g4⟩
  · refine ⟨rfl, ?_⟩
    have hpos : incomingPos x = (x.1 + 1, x.2) := by unfold incomingPos; rw [if_pos hxe]
    rw [hpos] at hiopen ⊢
    by_contra hlt
    push Not at hlt
    apply hiopen
    unfold ChildFrame.openRect
    rw [if_neg (show ¬ EvenSite (x.1 + 1, x.2) from
      fun h => by have h' : (x.1 + 1 + x.2) % 2 = 0 := h; omega)]
    simp only [ChildFrame.tGrade, ChildFrame.sGrade] at hlt ⊢
    obtain ⟨g1, g2, g3⟩ := face_even_pos hT hn1 hnd hn2 hd2 hcop hxe' hO1 hO2 hO3 hO4
    exact ⟨g1, g2, g3, hlt⟩

theorem odd_input_even_x {x i : Site} (hi : i = incomingNeg x ∨ i = incomingPos x) (hiO : ¬ EvenSite i) :
    EvenSite x := by
  by_contra hxo
  rcases hi with rfl | rfl
  · unfold incomingNeg at hiO
    rw [if_neg hxo] at hiO
    exact hiO (show (x.1 + (x.2 - 1)) % 2 = 0 by
      have := hxo; unfold EvenSite at this; omega)
  · unfold incomingPos at hiO
    rw [if_neg hxo] at hiO
    exact hiO (show (x.1 + (x.2 + 1)) % 2 = 0 by
      have := hxo; unfold EvenSite at this; omega)

/-- An even closed-boundary input of an open cone point is a chain site `hpath k` with `z.1 ≤ k < d`. -/
theorem H_label (frame : ChildFrame) {z x i : Site} (hz1 : 2 ≤ z.1)
    (hzt : frame.child.num + 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den - 2)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    {K : ℕ} (hx : frame.openRect x) (hcone : CapRay.ConeRoot z K x)
    (hi : i = incomingNeg x ∨ i = incomingPos x) (hiE : EvenSite i) (hiC : i ∈ frame.closedPolygon)
    (hiopen : ¬ frame.openRect i) :
    ∃ k : ℕ, z.1 ≤ (k : ℤ) ∧ (k : ℤ) < frame.child.den ∧ i = HChain.hpath frame k := by
  have h2 := even_input_H frame hz1 hzt hn1 hnd hx hcone hi hiE hiopen
  have hxo : ¬ EvenSite x := by
    intro hxe
    have hi' : ¬ EvenSite i := by
      rcases hi with rfl | rfl
      · unfold incomingNeg; rw [if_pos hxe]; unfold EvenSite at hxe ⊢; omega
      · unfold incomingPos; rw [if_pos hxe]; unfold EvenSite at hxe ⊢; omega
    exact hi' hiE
  have hxo' : (x.1 + x.2) % 2 = 1 := by unfold EvenSite at hxo; omega
  have hi1 : i.1 = x.1 := by
    rcases hi with rfl | rfl
    · unfold incomingNeg; rw [if_neg hxo]
    · unfold incomingPos; rw [if_neg hxo]
  have hcx := hcone.2.2.2 hxo
  have hh := hcone.1
  have hfree : i ∈ frame.freeH := by
    refine ⟨hiC, ?_, ?_⟩
    · intro hc
      have hiE' : (i.1 + i.2) % 2 = 0 := hiE
      have hcO : ¬ EvenSite (i.1, i.2 - 1) := by
        intro h; have h' : (i.1 + (i.2 - 1)) % 2 = 0 := h; omega
      unfold ChildFrame.closedPolygon at hc
      simp only [Set.mem_setOf_eq] at hc
      rw [if_neg hcO] at hc
      have ht := hc.2.1
      simp only [ChildFrame.tGrade] at ht h2
      have key : frame.child.num * i.1 - frame.child.den * (i.2 - 1)
          = (frame.child.num * i.1 - frame.child.den * i.2) + frame.child.den := by ring
      linarith
    · have hiE' : (i.1 + i.2) % 2 = 0 := hiE
      obtain ⟨t2, ht2⟩ : ∃ k, frame.tGrade i = 2 * k := by
        obtain ⟨k, hk⟩ := t_par_even (n := frame.child.num) (d := frame.child.den) (x1 := i.1) (x2 := i.2)
          (frame.child_odd.1) (frame.child_odd.2) hiE'
        exact ⟨k, hk⟩
      unfold ChildFrame.hSpectrum
      left
      have hC := hiC
      unfold ChildFrame.closedPolygon at hC
      simp only [Set.mem_setOf_eq] at hC
      rw [if_pos hiE] at hC
      refine ⟨by omega, h2, ?_⟩
      linarith [hC.2.1]
  obtain ⟨k, hk1, hk2⟩ := HChain.freeH_eq_hpath_of_mem frame hfree
  refine ⟨k, ?_, hk1, hk2⟩
  have hf := RowPair.hpath_fst frame k
  rw [← hk2, hi1] at hf
  have hcx' : x.1 - z.1 ≥ 1 := by omega
  omega

/-- An odd closed-boundary input of an open cone point is `vpath k + U` with `k = x.2 − n`. -/
theorem V_label (frame : ChildFrame) {z x i : Site} (hz1 : 2 ≤ z.1)
    (hzt : frame.child.num + 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den - 2)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    {K : ℕ} (hx : frame.openRect x) (hcone : CapRay.ConeRoot z K x)
    (hi : i = incomingNeg x ∨ i = incomingPos x) (hiO : ¬ EvenSite i) (hiC : i ∈ frame.closedPolygon)
    (hiopen : ¬ frame.openRect i) :
    ∃ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num ∧ (k : ℤ) = x.2 - frame.child.num ∧
      i = VChain.vpath frame k + RowAt.Uvec frame := by
  obtain ⟨hpos, hV⟩ := odd_input_V frame hz1 hzt hn1 hnd hx hcone hi hiO hiopen
  have hxe := odd_input_even_x hi hiO
  have hipos : i = (x.1 + 1, x.2) := by
    rw [hpos]; unfold incomingPos; rw [if_pos hxe]
  subst hipos
  obtain ⟨hn2, hd2⟩ := frame.child_odd
  have hT := periodDenominator_eq frame
  have hT0 : 0 ≤ frame.child.periodDenominator := by
    rw [hT]; nlinarith [mul_le_mul_of_nonneg_right hnd (show (0:ℤ) ≤ frame.child.num by linarith),
      mul_self_nonneg frame.child.num]
  have hOx := hx
  unfold ChildFrame.openRect at hOx
  rw [if_pos hxe] at hOx
  simp only [ChildFrame.tGrade, ChildFrame.sGrade] at hOx
  obtain ⟨_, _, _, hO4⟩ := hOx
  have hC := hiC
  unfold ChildFrame.closedPolygon at hC
  simp only [Set.mem_setOf_eq] at hC
  rw [if_neg hiO] at hC
  simp only [ChildFrame.tGrade, ChildFrame.sGrade] at hC
  simp only [ChildFrame.sGrade] at hV
  have hu : (x.1 + 1 - frame.child.den, x.2 - frame.child.num) ∈ frame.freeV := by
    unfold ChildFrame.freeV
    rw [Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · unfold ChildFrame.closedPolygon
      simp only [Set.mem_setOf_eq]
      rw [if_neg (show ¬ EvenSite (x.1 + 1 - frame.child.den, x.2 - frame.child.num) from fun h => by
        have h' : (x.1 + 1 - frame.child.den + (x.2 - frame.child.num)) % 2 = 0 := h
        have hxo : (x.1 + x.2) % 2 = 0 := hxe
        omega)]
      simp only [ChildFrame.tGrade, ChildFrame.sGrade]
      obtain ⟨c1, c2, _, c4⟩ := hC
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · intro hc
      unfold ChildFrame.closedPolygon at hc
      simp only [Set.mem_setOf_eq] at hc
      split_ifs at hc with hEv
      · simp only [ChildFrame.sGrade] at hc
        obtain ⟨_, _, h3, _⟩ := hc
        linarith
      · apply hEv
        show (x.1 + 1 - frame.child.den - 1 + (x.2 - frame.child.num)) % 2 = 0
        have hxo : (x.1 + x.2) % 2 = 0 := hxe
        omega
    · unfold ChildFrame.vSpectrum
      simp only [ChildFrame.sGrade]
      obtain ⟨k, hk⟩ := s_par (x1 := x.1 + 1 - frame.child.den) (x2 := x.2 - frame.child.num) hn2 hd2
      refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
      · rw [hk]; omega
      · linarith
      · linarith
  have hfv := VChain.freeV_eq_vpath_of_mem frame hu
  obtain ⟨k, hk, hkeq⟩ := hfv
  have e1 := congrArg Prod.fst hkeq
  have e2 := congrArg Prod.snd hkeq
  rw [VChain.vpath_ord] at e2
  simp only at e1 e2
  refine ⟨k, hk, by linarith, ?_⟩
  have hvk := VChain.vpath_ord frame k
  exact Prod.ext (show x.1 + 1 = (VChain.vpath frame k).1 + frame.child.den by linarith)
    (show x.2 = (VChain.vpath frame k).2 + frame.child.num by linarith)

/-- **The V index bound** (`hVr`): at a V-face boundary input `x + (1,0)` of an even open cone point, the V index
`x.2 − n` lies in `[1, r]` with `r = odd.den + odd.num` (the word's break), for the minimal cone height `n K ≤ d + 3n − 2`. -/
theorem V_index (frame : ChildFrame) {z x : Site} (hz1 : 2 ≤ z.1) (hzd : z.1 < frame.child.den)
    (hzt : frame.child.num + 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den - 2)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    (hNo : 1 ≤ frame.parents.odd.num) {K : ℕ}
    (hKu : frame.child.num * (K : ℤ) ≤ frame.child.den + 3 * frame.child.num - 2)
    (hx : frame.openRect x) (hcone : CapRay.ConeRoot z K x) (hxe : EvenSite x)
    (hiopen : ¬ frame.openRect (incomingPos x)) :
    1 ≤ x.2 - frame.child.num ∧ x.2 - frame.child.num ≤ frame.parents.odd.den + frame.parents.odd.num := by
  have hxe' : (x.1 + x.2) % 2 = 0 := hxe
  have hiO : ¬ EvenSite (incomingPos x) := by
    unfold incomingPos
    rw [if_pos hxe]
    intro h
    have h' : (x.1 + 1 + x.2) % 2 = 0 := h
    omega
  have hV := (odd_input_V frame hz1 hzt hn1 hnd hx hcone (Or.inr rfl) hiO hiopen).2
  obtain ⟨hn2, hd2⟩ := frame.child_odd
  have hT := periodDenominator_eq frame
  have hVs : frame.child.periodDenominator + 2 - frame.child.den + frame.child.num ≤
      (frame.child.den + frame.child.num) * (x.1 + 1) + (frame.child.den - frame.child.num) * x.2 := by
    unfold incomingPos at hV
    rw [if_pos hxe] at hV
    simp only [ChildFrame.sGrade] at hV
    linarith
  have hOx := hx
  unfold ChildFrame.openRect at hOx
  rw [if_pos hxe] at hOx
  simp only [ChildFrame.tGrade, ChildFrame.sGrade] at hOx
  obtain ⟨_, hOt2, _, hO4⟩ := hOx
  obtain ⟨k, hk⟩ := ConeFaceArith.t_par_even hn2 hd2 hxe'
  have hk2 : 2 * k < 2 := by linarith
  have hk0 : k ≤ 0 := by omega
  have ht0 : frame.child.num * x.1 - frame.child.den * x.2 ≤ 0 := by linarith
  have hzt2 : frame.child.num * z.1 - frame.child.den * z.2 ≤ frame.child.den - 2 := hzt.2
  have hzt1 : frame.child.num + 2 ≤ frame.child.num * z.1 - frame.child.den * z.2 := hzt.1
  have hz2 : z.2 ≤ frame.child.num - 1 := by
    have hzd' : z.1 ≤ frame.child.den - 1 := by omega
    have hA : frame.child.num * z.1 ≤ frame.child.num * (frame.child.den - 1) :=
      mul_le_mul_of_nonneg_left hzd' (by linarith)
    have hB : frame.child.den * z.2 < frame.child.den * frame.child.num := by nlinarith
    have hC := lt_of_mul_lt_mul_left hB (by linarith)
    omega
  have hcx := hcone.2.1
  have heps := frame.eps_eq
  have heu := frame.eps_unit
  have hr := nr_ge_arith heps (by rcases heu with h | h <;> omega) hNo
    (show (0:ℤ) ≤ frame.child.den + frame.child.num by linarith)
  have hup := V_up_arith (n := frame.child.num) (d := frame.child.den) (K := (K : ℤ)) (z2 := z.2) (x2 := x.2)
    (r := frame.parents.odd.den + frame.parents.odd.num) (by linarith) hz2 (by linarith [hcx]) hKu hr
  refine ⟨?_, hup⟩
  by_contra hlow
  push Not at hlow
  have hk' : x.2 ≤ frame.child.num := by omega
  exact ConeFaceArith.V_low_arith hT hn1 hnd hn2 hd2 hxe' ht0 hO4 hVs hk'

/-- **hG from the faces (rank 4 form).** Every closed-boundary non-open input of an open cone point of the base `z` is an earlier
label translated by `U`: an even input is `hpath k` with `z.1 ≤ k < d` (the H labels after `z`), an odd input is `vpath k + U` with
`1 ≤ k ≤ brk` (the V labels `V_1..V_brk` of the minus row, before every H label). The earlier sets are the row data `hEH`, `hEV`;
the V index bound is `V_index`, for the minimal cone height `n K ≤ d + 3n − 2`. -/
theorem hG_of_faces (frame : ChildFrame) {z : Site} {K : ℕ} (hz1 : 2 ≤ z.1) (hzd : z.1 < frame.child.den)
    (hzt : frame.child.num + 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den - 2)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    (hNo : 1 ≤ frame.parents.odd.num)
    (hKu : frame.child.num * (K : ℤ) ≤ frame.child.den + 3 * frame.child.num - 2)
    (Eset : Set Site)
    (hEH : ∀ k : ℕ, z.1 ≤ (k : ℤ) → (k : ℤ) < frame.child.den →
      HChain.hpath frame k - RowAt.Uvec frame ∈ Eset)
    (hEV : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num → 1 ≤ (k : ℤ) →
      (k : ℤ) ≤ frame.parents.odd.den + frame.parents.odd.num → VChain.vpath frame k ∈ Eset) :
    ∀ x i : Site, (frame.openRect x ∧ CapRay.ConeRoot z K x) → (i = incomingNeg x ∨ i = incomingPos x) →
      i ∈ frame.closedPolygon → ¬ frame.openRect i → ∃ e ∈ Eset, i = e + RowAt.Uvec frame := by
  rintro x i ⟨hx, hcone⟩ hi hiC hiopen
  by_cases hiE : EvenSite i
  · obtain ⟨k, hk1, hk2, hk⟩ := H_label frame hz1 hzt hn1 hnd hx hcone hi hiE hiC hiopen
    exact ⟨_, hEH k hk1 hk2, by rw [hk, sub_add_cancel]⟩
  · obtain ⟨k, hkL, hkx, hki⟩ := V_label frame hz1 hzt hn1 hnd hx hcone hi hiE hiC hiopen
    have hxe := odd_input_even_x hi hiE
    obtain ⟨hpos, _⟩ := odd_input_V frame hz1 hzt hn1 hnd hx hcone hi hiE hiopen
    rw [hpos] at hiopen
    obtain ⟨hr1, hr2⟩ := V_index frame hz1 hzd hzt hn1 hnd hNo hKu hx hcone hxe hiopen
    have hk1 : (1 : ℤ) ≤ (k : ℤ) := by omega
    have hk2 : (k : ℤ) ≤ frame.parents.odd.den + frame.parents.odd.num := by omega
    exact ⟨_, hEV k hkL hk1 hk2, hki⟩

end FLatticePaper.ConeBoundary
