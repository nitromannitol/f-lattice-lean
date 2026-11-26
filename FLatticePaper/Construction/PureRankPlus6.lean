import FLatticePaper.Construction.PureRankPlus5

-- PureRankPlus6: part 6 of 7; declarations from gateP_top_odd_im2_j1 to gateP_anti_im2_j0.
namespace FLatticePaper.PureRank
open Classical

set_option maxHeartbeats 400000 in
theorem gateP_top_odd_im2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) (-2) 1)) :
    valPlus d (shiftP d (x, d) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_im1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) (-1) (-1))) :
    valPlus d (shiftP d (x, d) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_im1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) (-1) 0)) :
    valPlus d (shiftP d (x, d) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_im1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) (-1) 1)) :
    valPlus d (shiftP d (x, d) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i0_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 0 (-1))) :
    valPlus d (shiftP d (x, d) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i0_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 0 0)) :
    valPlus d (shiftP d (x, d) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i0_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 0 1)) :
    valPlus d (shiftP d (x, d) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 1 (-1))) :
    valPlus d (shiftP d (x, d) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 1 0)) :
    valPlus d (shiftP d (x, d) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 1 1)) :
    valPlus d (shiftP d (x, d) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 2 (-1))) :
    valPlus d (shiftP d (x, d) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 2 0)) :
    valPlus d (shiftP d (x, d) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 2 1)) :
    valPlus d (shiftP d (x, d) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0) (hod : x % 2 = 1) (r : ℤ) (hr : RankOfP d (x, d) r) :
    r < 2 * x + 4 * d - 3 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_top_odd_im2_jm1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_im2_j0 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_im2_j1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_im1_jm1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_im1_j0 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_im1_j1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i0_jm1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i0_j0 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i0_j1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i1_jm1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i1_j0 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i1_j1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i2_jm1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i2_j0 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i2_j1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_top_one_im2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) (-2) (-1))) :
    valPlus d (shiftP d (1, d) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_im2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) (-2) 0)) :
    valPlus d (shiftP d (1, d) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_im2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) (-2) 1)) :
    valPlus d (shiftP d (1, d) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_im1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) (-1) (-1))) :
    valPlus d (shiftP d (1, d) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_im1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) (-1) 0)) :
    valPlus d (shiftP d (1, d) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_im1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) (-1) 1)) :
    valPlus d (shiftP d (1, d) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i0_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 0 (-1))) :
    valPlus d (shiftP d (1, d) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i0_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 0 0)) :
    valPlus d (shiftP d (1, d) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i0_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 0 1)) :
    valPlus d (shiftP d (1, d) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 1 (-1))) :
    valPlus d (shiftP d (1, d) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 1 0)) :
    valPlus d (shiftP d (1, d) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 1 1)) :
    valPlus d (shiftP d (1, d) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 2 (-1))) :
    valPlus d (shiftP d (1, d) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 2 0)) :
    valPlus d (shiftP d (1, d) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 2 1)) :
    valPlus d (shiftP d (1, d) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (r : ℤ) (hr : RankOfP d (1, d) r) :
    r < 4 * d - 1 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_top_one_im2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_im2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_im2_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_im1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_im1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_im1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i0_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i0_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i0_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i2_j1 d ⟨hd, hdodd⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_corner_im2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) (-2) (-1))) :
    valPlus d (shiftP d (1, d + 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_im2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) (-2) 0)) :
    valPlus d (shiftP d (1, d + 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_im2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) (-2) 1)) :
    valPlus d (shiftP d (1, d + 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_im1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) (-1) (-1))) :
    valPlus d (shiftP d (1, d + 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_im1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) (-1) 0)) :
    valPlus d (shiftP d (1, d + 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_im1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) (-1) 1)) :
    valPlus d (shiftP d (1, d + 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i0_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 0 (-1))) :
    valPlus d (shiftP d (1, d + 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i0_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 0 0)) :
    valPlus d (shiftP d (1, d + 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i0_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 0 1)) :
    valPlus d (shiftP d (1, d + 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 1 (-1))) :
    valPlus d (shiftP d (1, d + 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 1 0)) :
    valPlus d (shiftP d (1, d + 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 1 1)) :
    valPlus d (shiftP d (1, d + 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 2 (-1))) :
    valPlus d (shiftP d (1, d + 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 2 0)) :
    valPlus d (shiftP d (1, d + 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 2 1)) :
    valPlus d (shiftP d (1, d + 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (r : ℤ) (hr : RankOfP d (1, d + 1) r) :
    r < 4 * d := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_corner_im2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_im2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_im2_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_im1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_im1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_im1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i0_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i0_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i0_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i2_j1 d ⟨hd, hdodd⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_anti_im2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) (-1))) :
    valPlus d (shiftP d (x, y - 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_im2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) 0)) :
    valPlus d (shiftP d (x, y - 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


