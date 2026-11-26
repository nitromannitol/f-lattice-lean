import FLatticePaper.Construction.PureRankPlus1

-- PureRankPlus2: part 2 of 7; declarations from gateP_Vlast_im1_j1 to gateP_int_left_even_i1_j0.
namespace FLatticePaper.PureRank
open Classical

theorem gateP_Vlast_im1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) (-1) 1)) :
    valPlus d (shiftP d (1 - d, d) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i0_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 0 (-1))) :
    valPlus d (shiftP d (1 - d, d) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i0_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 0 0)) :
    valPlus d (shiftP d (1 - d, d) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i0_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 0 1)) :
    valPlus d (shiftP d (1 - d, d) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 1 (-1))) :
    valPlus d (shiftP d (1 - d, d) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 1 0)) :
    valPlus d (shiftP d (1 - d, d) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 1 1)) :
    valPlus d (shiftP d (1 - d, d) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 2 (-1))) :
    valPlus d (shiftP d (1 - d, d) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 2 0)) :
    valPlus d (shiftP d (1 - d, d) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 2 1)) :
    valPlus d (shiftP d (1 - d, d) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- The point `(2−d, d)`: its prescribed target `(1−d, d)` has every plus rank below `2d`. -/
theorem gateP_Vlast (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (r : ℤ) (hr : RankOfP d (1 - d, d) r) :
    r < 2 * d := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_Vlast_im2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_im2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_im2_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_im1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_im1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_im1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i0_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i0_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i0_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i2_j1 d ⟨hd, hdodd⟩ hrep

theorem gateP_H_odd_im2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) (-2) (-1))) :
    valPlus d (shiftP d (x, -1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_im2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) (-2) 0)) :
    valPlus d (shiftP d (x, -1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_im2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) (-2) 1)) :
    valPlus d (shiftP d (x, -1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_im1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) (-1) (-1))) :
    valPlus d (shiftP d (x, -1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_im1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) (-1) 0)) :
    valPlus d (shiftP d (x, -1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_im1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) (-1) 1)) :
    valPlus d (shiftP d (x, -1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem gateP_H_odd_i0_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 0 (-1))) :
    valPlus d (shiftP d (x, -1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i0_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 0 0)) :
    valPlus d (shiftP d (x, -1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i0_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 0 1)) :
    valPlus d (shiftP d (x, -1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 1 (-1))) :
    valPlus d (shiftP d (x, -1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 1 0)) :
    valPlus d (shiftP d (x, -1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 1 1)) :
    valPlus d (shiftP d (x, -1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 2 (-1))) :
    valPlus d (shiftP d (x, -1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 2 0)) :
    valPlus d (shiftP d (x, -1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 2 1)) :
    valPlus d (shiftP d (x, -1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- Free odd `(x, 0)`, `1 ≤ x ≤ d`: its prescribed target `(x, −1)` has every plus rank below `2x − 3`. -/
theorem gateP_H_odd (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 1 ≤ x) (hxd : x ≤ d) (hod : x % 2 = 1) (r : ℤ) (hr : RankOfP d (x, -1) r) :
    r < 2 * x - 3 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_H_odd_im2_jm1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_im2_j0 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_im2_j1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_im1_jm1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_im1_j0 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_im1_j1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i0_jm1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i0_j0 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i0_j1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i1_jm1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i1_j0 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i1_j1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i2_jm1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i2_j0 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i2_j1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep

theorem gateP_V_odd_im2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) (-2) (-1))) :
    valPlus d (shiftP d (x, -x) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_im2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) (-2) 0)) :
    valPlus d (shiftP d (x, -x) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_im2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) (-2) 1)) :
    valPlus d (shiftP d (x, -x) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_im1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) (-1) (-1))) :
    valPlus d (shiftP d (x, -x) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_im1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) (-1) 0)) :
    valPlus d (shiftP d (x, -x) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_im1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) (-1) 1)) :
    valPlus d (shiftP d (x, -x) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i0_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 0 (-1))) :
    valPlus d (shiftP d (x, -x) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i0_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 0 0)) :
    valPlus d (shiftP d (x, -x) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i0_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 0 1)) :
    valPlus d (shiftP d (x, -x) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 1 (-1))) :
    valPlus d (shiftP d (x, -x) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 1 0)) :
    valPlus d (shiftP d (x, -x) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 1 1)) :
    valPlus d (shiftP d (x, -x) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 2 (-1))) :
    valPlus d (shiftP d (x, -x) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 2 0)) :
    valPlus d (shiftP d (x, -x) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 2 1)) :
    valPlus d (shiftP d (x, -x) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- Free odd `(x, 1−x)`, `2−d ≤ x ≤ 0`: its prescribed target `(x, −x)` has every plus rank below `1 − 2x`. -/
theorem gateP_V_odd (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx0 : x ≤ 0) (r : ℤ) (hr : RankOfP d (x, -x) r) :
    r < 1 - 2 * x := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_V_odd_im2_jm1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_im2_j0 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_im2_j1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_im1_jm1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_im1_j0 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_im1_j1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i0_jm1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i0_j0 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i0_j1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i1_jm1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i1_j0 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i1_j1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i2_jm1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i2_j0 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i2_j1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep


/-! ## The interior and boundary plus gates (step (ii), plus sources) -/

set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_im2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-2) (-1))) :
    valPlus d (shiftP d (x - 1, y) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_im2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-2) 0)) :
    valPlus d (shiftP d (x - 1, y) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_im2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-2) 1)) :
    valPlus d (shiftP d (x - 1, y) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_im1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-1) (-1))) :
    valPlus d (shiftP d (x - 1, y) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_im1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-1) 0)) :
    valPlus d (shiftP d (x - 1, y) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-1) 1)) :
    valPlus d (shiftP d (x - 1, y) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 0 (-1))) :
    valPlus d (shiftP d (x - 1, y) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 0 0)) :
    valPlus d (shiftP d (x - 1, y) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 0 1)) :
    valPlus d (shiftP d (x - 1, y) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 1 (-1))) :
    valPlus d (shiftP d (x - 1, y) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 1 0)) :
    valPlus d (shiftP d (x - 1, y) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


