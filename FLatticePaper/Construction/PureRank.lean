import FLatticePaper.Construction.PureRank4

-- PureRank: part 5 of 5; declarations from gate_int_odd_left_up_a1_1 to gate_fifth.
namespace FLatticePaper.PureRank
open Classical

theorem gate_int_odd_left_up_a1_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 1 1)) :
    valMinus d (shiftP d (x, y + 1) 1 1) - 1 * (2 * d) + 1 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_a2_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 2 (-1))) :
    valMinus d (shiftP d (x, y + 1) 2 (-1)) - 2 * (2 * d) + (-1) * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_a2_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 2 0)) :
    valMinus d (shiftP d (x, y + 1) 2 0) - 2 * (2 * d) + 0 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_a2_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 2 1)) :
    valMinus d (shiftP d (x, y + 1) 2 1) - 2 * (2 * d) + 1 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (hx : x ≤ 0) (hodd : (x + y) % 2 = 1)
    (r : ℤ) (hr : RankOf d (x, y + 1) r) : r < valMinus d (x, y) := by
  rw [valMinus_int_left d x y hf hx]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  have hnV : ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) := by
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hf
    omega
  clear hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gate_int_odd_left_up_am2_m1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_am2_0 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_am2_1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_am1_m1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_am1_0 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_am1_1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_a0_m1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_a0_0 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_a0_1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_a1_m1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_a1_0 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_a1_1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_a2_m1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_a2_0 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_up_a2_1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep


theorem gate_int_odd_right_down_am2_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) (-1))) :
    valMinus d (shiftP d (x, y - 1) (-2) (-1)) - (-2) * (2 * d) + (-1) * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_am2_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) 0)) :
    valMinus d (shiftP d (x, y - 1) (-2) 0) - (-2) * (2 * d) + 0 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_am2_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) 1)) :
    valMinus d (shiftP d (x, y - 1) (-2) 1) - (-2) * (2 * d) + 1 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_am1_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) (-1))) :
    valMinus d (shiftP d (x, y - 1) (-1) (-1)) - (-1) * (2 * d) + (-1) * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_am1_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 0)) :
    valMinus d (shiftP d (x, y - 1) (-1) 0) - (-1) * (2 * d) + 0 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem gate_int_odd_right_down_am1_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 1)) :
    valMinus d (shiftP d (x, y - 1) (-1) 1) - (-1) * (2 * d) + 1 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_a0_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 (-1))) :
    valMinus d (shiftP d (x, y - 1) 0 (-1)) - 0 * (2 * d) + (-1) * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_a0_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 0)) :
    valMinus d (shiftP d (x, y - 1) 0 0) - 0 * (2 * d) + 0 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_a0_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 1)) :
    valMinus d (shiftP d (x, y - 1) 0 1) - 0 * (2 * d) + 1 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_a1_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 (-1))) :
    valMinus d (shiftP d (x, y - 1) 1 (-1)) - 1 * (2 * d) + (-1) * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_a1_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 0)) :
    valMinus d (shiftP d (x, y - 1) 1 0) - 1 * (2 * d) + 0 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_a1_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 1)) :
    valMinus d (shiftP d (x, y - 1) 1 1) - 1 * (2 * d) + 1 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_a2_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 (-1))) :
    valMinus d (shiftP d (x, y - 1) 2 (-1)) - 2 * (2 * d) + (-1) * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_a2_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 0)) :
    valMinus d (shiftP d (x, y - 1) 2 0) - 2 * (2 * d) + 0 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down_a2_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 2 ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 1)) :
    valMinus d (shiftP d (x, y - 1) 2 1) - 2 * (2 * d) + 1 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_right_down (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (h4 : x + y ≠ d + 2) (hx : 1 ≤ x) (hodd : (x + y) % 2 = 1)
    (r : ℤ) (hr : RankOf d (x, y - 1) r) : r < valMinus d (x, y) := by
  rw [valMinus_int_right d x y hf hx (by omega)]
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
  · exact gate_int_odd_right_down_am2_m1 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_am2_0 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_am2_1 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_am1_m1 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_am1_0 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_am1_1 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_a0_m1 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_a0_0 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_a0_1 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_a1_m1 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_a1_0 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_a1_1 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_a2_m1 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_a2_0 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_right_down_a2_1 d x y ⟨hd, hdodd, hy, h4, hx, hodd, hb1, hb2, hb3, hb4, hb5⟩ hrep

set_option maxHeartbeats 400000 in
/-- Odd interior point on the right: the neighbour `(x, y+1)` has every rank below the point's. -/
theorem gate_int_odd_right_up (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (hx : 1 ≤ x) (hodd : (x + y) % 2 = 1)
    (r : ℤ) (hr : RankOf d (x, y + 1) r) : r < valMinus d (x, y) := by
  rw [valMinus_int_right d x y hf hx (by omega)]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hn
  gate_tac

set_option maxHeartbeats 400000 in
/-- The top row point `(x, d+1)` with `x` even, `x ≤ 0`: its neighbour `(x−1, d+1)` has every rank below `2x − 4`. -/
theorem gate_top_even (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0)
    (hev : x % 2 = 0) (r : ℤ) (hr : RankOf d (x - 1, d + 1) r) : r < 2 * x - 4 := by
  gate_tac

set_option maxHeartbeats 400000 in
/-- The top row point `(x, d+1)` with `x` odd, `x ≤ 0`: its neighbour `(x, d)` has every rank below `2x − 3`. -/
theorem gate_top_odd (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0)
    (hod : x % 2 = 1) (r : ℤ) (hr : RankOf d (x, d) r) : r < 2 * x - 3 := by
  gate_tac

set_option maxHeartbeats 400000 in
/-- The top row point `(1, d+1)`: its upper neighbour `(1, d+2)` has every rank below `−1`. -/
theorem gate_top_one (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (r : ℤ) (hr : RankOf d (1, d + 2) r) :
    r < -1 := by
  gate_tac

set_option maxHeartbeats 400000 in
/-- The corner `(2, d+1)`: its left neighbour `(1, d+1)` has every rank below `0`. -/
theorem gate_corner (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (r : ℤ) (hr : RankOf d (1, d + 1) r) :
    r < 0 := by
  gate_tac

set_option maxHeartbeats 400000 in
/-- The anti-diagonal point `(x, d+2−x)` with `2 ≤ x ≤ d`: its upper neighbour has every rank below `2x − 3`. -/
theorem gate_anti (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx2 : 2 ≤ x) (hxd : x ≤ d) (r : ℤ)
    (hr : RankOf d (x, d + 3 - x) r) : r < 2 * x - 3 := by
  gate_tac

set_option maxHeartbeats 400000 in
/-- The point `(d, 1)`: its left neighbour `(d−1, 1)` has every rank below `2d`. -/
theorem gate_fifth (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (r : ℤ) (hr : RankOf d (d - 1, 1) r) :
    r < 2 * d := by
  gate_tac

end FLatticePaper.PureRank

