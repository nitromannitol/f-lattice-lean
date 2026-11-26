import FLatticePaper.Construction.PureRankPlus4

-- PureRankPlus5: part 5 of 7; declarations from gateP_int_odd_right_down_im1_j1 to gateP_top_odd_im2_j0.
namespace FLatticePaper.PureRank
open Classical

set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 1)) :
    valPlus d (shiftP d (x, y - 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 (-1))) :
    valPlus d (shiftP d (x, y - 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 0)) :
    valPlus d (shiftP d (x, y - 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 1)) :
    valPlus d (shiftP d (x, y - 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 (-1))) :
    valPlus d (shiftP d (x, y - 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 0)) :
    valPlus d (shiftP d (x, y - 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 1)) :
    valPlus d (shiftP d (x, y - 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 (-1))) :
    valPlus d (shiftP d (x, y - 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 0)) :
    valPlus d (shiftP d (x, y - 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 1)) :
    valPlus d (shiftP d (x, y - 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (h4 : x + y ≠ d + 2) (hx1 : 1 ≤ x) (hodd : (x + y) % 2 = 1) (r : ℤ) (hr : RankOfP d (x, y - 1) r) :
    r < valPlus d (x, y) := by
  rw [valPlus_int_right d x y hf hx1]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_int_odd_right_down_im2_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_im2_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_im2_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_im1_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_im1_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_im1_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i0_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i0_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i0_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i1_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i1_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i1_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i2_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i2_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i2_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_im2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-2) (-1))) :
    valPlus d (shiftP d (x, y + 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_im2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-2) 0)) :
    valPlus d (shiftP d (x, y + 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_im2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-2) 1)) :
    valPlus d (shiftP d (x, y + 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_im1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-1) (-1))) :
    valPlus d (shiftP d (x, y + 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_im1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-1) 0)) :
    valPlus d (shiftP d (x, y + 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-1) 1)) :
    valPlus d (shiftP d (x, y + 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 0 (-1))) :
    valPlus d (shiftP d (x, y + 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 0 0)) :
    valPlus d (shiftP d (x, y + 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 0 1)) :
    valPlus d (shiftP d (x, y + 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 1 (-1))) :
    valPlus d (shiftP d (x, y + 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 1 0)) :
    valPlus d (shiftP d (x, y + 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 1 1)) :
    valPlus d (shiftP d (x, y + 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 2 (-1))) :
    valPlus d (shiftP d (x, y + 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 2 0)) :
    valPlus d (shiftP d (x, y + 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 2 1)) :
    valPlus d (shiftP d (x, y + 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (h4 : x + y ≠ d + 2) (hx1 : 1 ≤ x) (hodd : (x + y) % 2 = 1) (r : ℤ) (hr : RankOfP d (x, y + 1) r) :
    r < valPlus d (x, y) := by
  rw [valPlus_int_right d x y hf hx1]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_int_odd_right_up_im2_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_im2_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_im2_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_im1_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_im1_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_im1_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i0_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i0_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i0_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i1_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i1_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i1_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i2_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i2_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i2_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_top_even_im2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) (-2) (-1))) :
    valPlus d (shiftP d (x - 1, d + 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_im2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) (-2) 0)) :
    valPlus d (shiftP d (x - 1, d + 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_im2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) (-2) 1)) :
    valPlus d (shiftP d (x - 1, d + 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_im1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) (-1) (-1))) :
    valPlus d (shiftP d (x - 1, d + 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_im1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) (-1) 0)) :
    valPlus d (shiftP d (x - 1, d + 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_im1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) (-1) 1)) :
    valPlus d (shiftP d (x - 1, d + 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i0_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 0 (-1))) :
    valPlus d (shiftP d (x - 1, d + 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i0_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 0 0)) :
    valPlus d (shiftP d (x - 1, d + 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i0_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 0 1)) :
    valPlus d (shiftP d (x - 1, d + 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 1 (-1))) :
    valPlus d (shiftP d (x - 1, d + 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 1 0)) :
    valPlus d (shiftP d (x - 1, d + 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 1 1)) :
    valPlus d (shiftP d (x - 1, d + 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 2 (-1))) :
    valPlus d (shiftP d (x - 1, d + 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 2 0)) :
    valPlus d (shiftP d (x - 1, d + 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 2 1)) :
    valPlus d (shiftP d (x - 1, d + 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0) (hev : x % 2 = 0) (r : ℤ) (hr : RankOfP d (x - 1, d + 1) r) :
    r < 2 * x + 4 * d - 4 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_top_even_im2_jm1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_im2_j0 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_im2_j1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_im1_jm1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_im1_j0 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_im1_j1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i0_jm1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i0_j0 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i0_j1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i1_jm1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i1_j0 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i1_j1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i2_jm1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i2_j0 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i2_j1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_im2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) (-2) (-1))) :
    valPlus d (shiftP d (x, d) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_im2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) (-2) 0)) :
    valPlus d (shiftP d (x, d) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


