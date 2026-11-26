import FLatticePaper.Construction.PureRankPlus6

-- PureRankPlus: part 7 of 7; declarations from gateP_anti_im2_j1 to gateP_fifth.
namespace FLatticePaper.PureRank
open Classical

set_option maxHeartbeats 400000 in
theorem gateP_anti_im2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) 1)) :
    valPlus d (shiftP d (x, y - 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_im1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) (-1))) :
    valPlus d (shiftP d (x, y - 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_im1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 0)) :
    valPlus d (shiftP d (x, y - 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 1)) :
    valPlus d (shiftP d (x, y - 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 0 (-1))) :
    valPlus d (shiftP d (x, y - 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 0 0)) :
    valPlus d (shiftP d (x, y - 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 0 1)) :
    valPlus d (shiftP d (x, y - 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 1 (-1))) :
    valPlus d (shiftP d (x, y - 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 1 0)) :
    valPlus d (shiftP d (x, y - 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 1 1)) :
    valPlus d (shiftP d (x, y - 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 2 (-1))) :
    valPlus d (shiftP d (x, y - 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 2 0)) :
    valPlus d (shiftP d (x, y - 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 2 1)) :
    valPlus d (shiftP d (x, y - 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hs : x + y = d + 2) (hx2 : 2 ≤ x) (hxd : x ≤ d) (hyd : y ≤ d) (r : ℤ) (hr : RankOfP d (x, y - 1) r) :
    r < 4 * d + 1 - 2 * x := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_anti_im2_jm1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_im2_j0 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_im2_j1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_im1_jm1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_im1_j0 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_im1_j1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i0_jm1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i0_j0 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i0_j1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i1_jm1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i1_j0 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i1_j1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i2_jm1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i2_j0 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i2_j1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_fifth_im2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) (-2) (-1))) :
    valPlus d (shiftP d (d + 1, 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_im2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) (-2) 0)) :
    valPlus d (shiftP d (d + 1, 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_im2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) (-2) 1)) :
    valPlus d (shiftP d (d + 1, 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_im1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) (-1) (-1))) :
    valPlus d (shiftP d (d + 1, 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_im1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) (-1) 0)) :
    valPlus d (shiftP d (d + 1, 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_im1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) (-1) 1)) :
    valPlus d (shiftP d (d + 1, 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i0_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 0 (-1))) :
    valPlus d (shiftP d (d + 1, 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i0_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 0 0)) :
    valPlus d (shiftP d (d + 1, 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i0_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 0 1)) :
    valPlus d (shiftP d (d + 1, 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 1 (-1))) :
    valPlus d (shiftP d (d + 1, 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 1 0)) :
    valPlus d (shiftP d (d + 1, 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 1 1)) :
    valPlus d (shiftP d (d + 1, 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 2 (-1))) :
    valPlus d (shiftP d (d + 1, 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 2 0)) :
    valPlus d (shiftP d (d + 1, 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 2 1)) :
    valPlus d (shiftP d (d + 1, 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (r : ℤ) (hr : RankOfP d (d + 1, 1) r) :
    r < 2 * d := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_fifth_im2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_im2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_im2_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_im1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_im1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_im1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i0_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i0_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i0_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i2_j1 d ⟨hd, hdodd⟩ hrep


end FLatticePaper.PureRank

