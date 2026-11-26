import FLatticePaper.Plane.Induction.FaceWitness
import FLatticePaper.Plane.Induction.FreeOrbit
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.FreeClosure

/-! # Two witness pairs cannot coexist (the grade part of the witness dichotomy)

A bottom witness (a free H point `u` within king distance 1 of `c`) and a top witness (`v` within distance 1 with `v - V` free H)
cannot coexist: `t(v - V) = t(v) + T` and both free H points have `1 ≤ t ≤ L - 1`, while `|t(v) - t(u)| ≤ 2L`. A left witness
(free V point `u`) and a right witness (`v - K` free V) cannot coexist for `n ≥ 3`: `s(v - K) = s(v) - T` and `|s(v) - s(u)| ≤ 4d`,
while free V points have `2 - d + n ≤ s ≤ L - 2`. -/

namespace FLatticePaper.WitnessPairs

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FaceWitness

theorem not_bottom_top (frame : ChildFrame) {c : Site} (hB : BottomWit frame c) (hT : TopWit frame c) : False := by
  obtain ⟨u, hu1, hu2, huF⟩ := hB
  obtain ⟨v, hv1, hv2, hvF⟩ := hT
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hTpos := periodDenominator_pos frame
  obtain ⟨hu1a, hu1b⟩ := abs_le.mp hu1
  obtain ⟨hu2a, hu2b⟩ := abs_le.mp hu2
  obtain ⟨hv1a, hv1b⟩ := abs_le.mp hv1
  obtain ⟨hv2a, hv2b⟩ := abs_le.mp hv2
  have htr : frame.child.modifiedDeck.transverse = (frame.child.num - frame.child.den, frame.child.num + frame.child.den) :=
    ChildFrame.child_modifiedDeck_transverse frame
  have htu := FLatticePaper.FreeOrbit.freeH_t_range frame huF
  have htv := FLatticePaper.FreeOrbit.freeH_t_range frame hvF
  have htsub : frame.tGrade (v - frame.child.modifiedDeck.transverse) = frame.tGrade v + frame.child.periodDenominator := by
    rw [htr]
    unfold ChildFrame.tGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [hTd]
    ring
  have hd1lo : -2 ≤ v.1 - u.1 := by omega
  have hd1hi : v.1 - u.1 ≤ 2 := by omega
  have hd2lo : -2 ≤ v.2 - u.2 := by omega
  have hd2hi : v.2 - u.2 ≤ 2 := by omega
  have p1 : frame.child.num * (-2) ≤ frame.child.num * (v.1 - u.1) := mul_le_mul_of_nonneg_left hd1lo hn0.le
  have p2 : frame.child.num * (v.1 - u.1) ≤ frame.child.num * 2 := mul_le_mul_of_nonneg_left hd1hi hn0.le
  have p3 : frame.child.den * (v.2 - u.2) ≤ frame.child.den * 2 := mul_le_mul_of_nonneg_left hd2hi (by omega)
  have p4 : frame.child.den * (-2) ≤ frame.child.den * (v.2 - u.2) := mul_le_mul_of_nonneg_left hd2lo (by omega)
  have htvu : frame.tGrade v - frame.tGrade u =
      frame.child.num * (v.1 - u.1) - frame.child.den * (v.2 - u.2) := by
    unfold ChildFrame.tGrade; ring
  have hbig : 3 * (frame.child.num + frame.child.den) - 2 < frame.child.periodDenominator := by
    rw [hTd]; nlinarith
  -- t(v - V) - t(u) = t(v) - t(u) + T lies in [T - 2L, L - 2] by the t-range of the two free H points
  have hlo : frame.child.periodDenominator - 2 * (frame.child.num + frame.child.den) ≤
      frame.tGrade (v - frame.child.modifiedDeck.transverse) - frame.tGrade u := by
    rw [htsub]; linarith
  omega

theorem not_left_right (frame : ChildFrame) (hn3 : 3 ≤ frame.child.num) {c : Site}
    (hL : LeftWit frame c) (hR : RightWit frame c) : False := by
  obtain ⟨u, hu1, hu2, huF⟩ := hL
  obtain ⟨v, hv1, hv2, hvF⟩ := hR
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hTpos := periodDenominator_pos frame
  obtain ⟨hu1a, hu1b⟩ := abs_le.mp hu1
  obtain ⟨hu2a, hu2b⟩ := abs_le.mp hu2
  obtain ⟨hv1a, hv1b⟩ := abs_le.mp hv1
  obtain ⟨hv2a, hv2b⟩ := abs_le.mp hv2
  have hk : frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) := ChildFrame.child_modifiedDeck_kernel frame
  have hsu := FLatticePaper.FreeOrbit.freeV_s_range frame huF
  have hsv := FLatticePaper.FreeOrbit.freeV_s_range frame hvF
  have hssub : frame.sGrade (v - frame.child.modifiedDeck.kernel) = frame.sGrade v - frame.child.periodDenominator := by
    rw [hk]
    unfold ChildFrame.sGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [hTd]
    ring
  have hd1lo : -2 ≤ v.1 - u.1 := by omega
  have hd1hi : v.1 - u.1 ≤ 2 := by omega
  have hd2lo : -2 ≤ v.2 - u.2 := by omega
  have hd2hi : v.2 - u.2 ≤ 2 := by omega
  have q1 : (frame.child.den + frame.child.num) * (-2) ≤ (frame.child.den + frame.child.num) * (v.1 - u.1) :=
    mul_le_mul_of_nonneg_left hd1lo (by omega)
  have q2 : (frame.child.den + frame.child.num) * (v.1 - u.1) ≤ (frame.child.den + frame.child.num) * 2 :=
    mul_le_mul_of_nonneg_left hd1hi (by omega)
  have q3 : (frame.child.den - frame.child.num) * (-2) ≤ (frame.child.den - frame.child.num) * (v.2 - u.2) :=
    mul_le_mul_of_nonneg_left hd2lo (by omega)
  have q4 : (frame.child.den - frame.child.num) * (v.2 - u.2) ≤ (frame.child.den - frame.child.num) * 2 :=
    mul_le_mul_of_nonneg_left hd2hi (by omega)
  have hsvu : frame.sGrade v - frame.sGrade u =
      (frame.child.den + frame.child.num) * (v.1 - u.1) + (frame.child.den - frame.child.num) * (v.2 - u.2) := by
    unfold ChildFrame.sGrade; ring
  have hbig : 6 * frame.child.den - 4 < frame.child.periodDenominator := by
    rw [hTd]; nlinarith
  -- s(v - K) - s(u) = s(v) - s(u) - T lies in [-(2d-4), 4d - T] by the s-range of the two free V points
  have hlo : -(2 * frame.child.den - 4) ≤ frame.sGrade (v - frame.child.modifiedDeck.kernel) - frame.sGrade u := by
    linarith [hsu.1, hsv.2]
  have hhi : frame.sGrade (v - frame.child.modifiedDeck.kernel) - frame.sGrade u ≤ 4 * frame.child.den - frame.child.periodDenominator := by
    rw [hssub]; nlinarith
  omega

end FLatticePaper.WitnessPairs
