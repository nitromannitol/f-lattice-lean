import FLatticePaper.Construction.PureRank3

-- PureRank4: part 4 of 5; declarations from gate_int_one_diag_left to gate_int_odd_left_up_a1_0.
namespace FLatticePaper.PureRank
open Classical

set_option maxHeartbeats 400000 in
/-- The point `(1, d)` (on the diagonal): its left neighbour `(0, d)` has every rank below `2`. -/
theorem gate_int_one_diag_left (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1)
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (hx1 : x = 1) (hdiag : x + y = d + 1)
    (r : ℤ) (hr : RankOf d (x - 1, y) r) : r < valMinus d (x, y) := by
  rw [valMinus_int_diag d x y hf (by omega) hdiag]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hf hdiag
  gate_tac


theorem gate_int_odd_left_down_am2_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) (-1))) :
    valMinus d (shiftP d (x, y - 1) (-2) (-1)) - (-2) * (2 * d) + (-1) * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_am2_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) 0)) :
    valMinus d (shiftP d (x, y - 1) (-2) 0) - (-2) * (2 * d) + 0 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem gate_int_odd_left_down_am2_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) 1)) :
    valMinus d (shiftP d (x, y - 1) (-2) 1) - (-2) * (2 * d) + 1 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_am1_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) (-1))) :
    valMinus d (shiftP d (x, y - 1) (-1) (-1)) - (-1) * (2 * d) + (-1) * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_am1_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 0)) :
    valMinus d (shiftP d (x, y - 1) (-1) 0) - (-1) * (2 * d) + 0 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_am1_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 1)) :
    valMinus d (shiftP d (x, y - 1) (-1) 1) - (-1) * (2 * d) + 1 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_a0_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 (-1))) :
    valMinus d (shiftP d (x, y - 1) 0 (-1)) - 0 * (2 * d) + (-1) * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_a0_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 0)) :
    valMinus d (shiftP d (x, y - 1) 0 0) - 0 * (2 * d) + 0 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_a0_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 1)) :
    valMinus d (shiftP d (x, y - 1) 0 1) - 0 * (2 * d) + 1 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_a1_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 (-1))) :
    valMinus d (shiftP d (x, y - 1) 1 (-1)) - 1 * (2 * d) + (-1) * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_a1_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 0)) :
    valMinus d (shiftP d (x, y - 1) 1 0) - 1 * (2 * d) + 0 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_a1_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 1)) :
    valMinus d (shiftP d (x, y - 1) 1 1) - 1 * (2 * d) + 1 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_a2_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 (-1))) :
    valMinus d (shiftP d (x, y - 1) 2 (-1)) - 2 * (2 * d) + (-1) * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_a2_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 0)) :
    valMinus d (shiftP d (x, y - 1) 2 0) - 2 * (2 * d) + 0 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down_a2_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 1)) :
    valMinus d (shiftP d (x, y - 1) 2 1) - 2 * (2 * d) + 1 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_down (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (hx : x ≤ 0) (hodd : (x + y) % 2 = 1)
    (r : ℤ) (hr : RankOf d (x, y - 1) r) : r < valMinus d (x, y) := by
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
  · exact gate_int_odd_left_down_am2_m1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_am2_0 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_am2_1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_am1_m1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_am1_0 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_am1_1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_a0_m1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_a0_0 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_a0_1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_a1_m1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_a1_0 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_a1_1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_a2_m1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_a2_0 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_odd_left_down_a2_1 d x y ⟨hd, hdodd, hy, hx, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep


theorem gate_int_odd_left_up_am2_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-2) (-1))) :
    valMinus d (shiftP d (x, y + 1) (-2) (-1)) - (-2) * (2 * d) + (-1) * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_am2_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-2) 0)) :
    valMinus d (shiftP d (x, y + 1) (-2) 0) - (-2) * (2 * d) + 0 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_am2_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-2) 1)) :
    valMinus d (shiftP d (x, y + 1) (-2) 1) - (-2) * (2 * d) + 1 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_am1_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-1) (-1))) :
    valMinus d (shiftP d (x, y + 1) (-1) (-1)) - (-1) * (2 * d) + (-1) * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_am1_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-1) 0)) :
    valMinus d (shiftP d (x, y + 1) (-1) 0) - (-1) * (2 * d) + 0 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_am1_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-1) 1)) :
    valMinus d (shiftP d (x, y + 1) (-1) 1) - (-1) * (2 * d) + 1 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_a0_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 0 (-1))) :
    valMinus d (shiftP d (x, y + 1) 0 (-1)) - 0 * (2 * d) + (-1) * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_a0_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 0 0)) :
    valMinus d (shiftP d (x, y + 1) 0 0) - 0 * (2 * d) + 0 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_a0_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 0 1)) :
    valMinus d (shiftP d (x, y + 1) 0 1) - 0 * (2 * d) + 1 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_a1_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 1 (-1))) :
    valMinus d (shiftP d (x, y + 1) 1 (-1)) - 1 * (2 * d) + (-1) * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_odd_left_up_a1_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 1 0)) :
    valMinus d (shiftP d (x, y + 1) 1 0) - 1 * (2 * d) + 0 * (2 * (d + 1)) < 2 * x - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

