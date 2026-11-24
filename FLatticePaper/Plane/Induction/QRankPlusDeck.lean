import FLatticePaper.Construction.PureRankPlusWhite
import FLatticePaper.Plane.Induction.QRankDeck

/-!
# Deck consistency of `qRankP` on native pairs (task 118, W1 base; bridge (1) for eta = -1)

The plus analogue of `QRankDeck`: `qRankP_fam` classifies a native point into nine families with the explicit value of
`qRankP` (by `valPlus` branch lemmas `vP_H`, `vP_V`, `vP_L1`, `vP_L2`, `vP_R`), and the four unit-shift identities
`qRankP_shift_U`, `qRankP_shift_negU`, `qRankP_shift_V`, `qRankP_shift_negV` hold on native pairs (characters `2d` for
`U` and `2(d+1)` for `V`, opposite to the minus side).
-/

namespace FLatticePaper.QRankPlusDeck

open FLatticePaper.PureRank FLatticePaper.QRankDeck

theorem vP_H (d x y : ℤ) (h : y = 0 ∧ 1 ≤ x ∧ x ≤ d) : valPlus d (x, y) = 2 * x + (x + y) % 2 - 4 := by
  dsimp only [valPlus]
  rw [if_pos (show IsHc d (x, y) from ⟨h.1, h.2.1, h.2.2⟩)]

theorem vP_V (d x y : ℤ) (hH : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d))
    (hV : (x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) :
    valPlus d (x, y) = 2 * y - (x + y) % 2 := by
  dsimp only [valPlus]
  rw [if_neg (show ¬ IsHc d (x, y) from fun h => hH ⟨h.1, h.2.1, h.2.2⟩),
    if_pos ((isVc_iff d x y).mpr hV)]

theorem vP_L1 (d x y : ℤ) (hH : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d))
    (hV : ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d))) (hx : x ≤ 0) (hs : x + y = 2) :
    valPlus d (x, y) = 2 * y := by
  dsimp only [valPlus]
  rw [if_neg (show ¬ IsHc d (x, y) from fun h => hH ⟨h.1, h.2.1, h.2.2⟩),
    if_neg (fun h => hV ((isVc_iff d x y).mp h)), if_pos (show x ≤ 0 ∧ x + y = 2 from ⟨hx, hs⟩)]

theorem vP_L2 (d x y : ℤ) (hH : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d))
    (hV : ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d))) (hx : x ≤ 0) (hs : ¬ (x + y = 2)) :
    valPlus d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2 := by
  dsimp only [valPlus]
  rw [if_neg (show ¬ IsHc d (x, y) from fun h => hH ⟨h.1, h.2.1, h.2.2⟩),
    if_neg (fun h => hV ((isVc_iff d x y).mp h)), if_neg (fun h => hs h.2), if_pos hx]

theorem vP_R (d x y : ℤ) (hH : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d))
    (hV : ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d))) (hx : ¬ x ≤ 0) :
    valPlus d (x, y) = 4 * d - 2 * x + (x + y) % 2 := by
  dsimp only [valPlus]
  rw [if_neg (show ¬ IsHc d (x, y) from fun h => hH ⟨h.1, h.2.1, h.2.2⟩),
    if_neg (fun h => hV ((isVc_iff d x y).mp h)), if_neg (fun h => hx h.1), if_neg hx]

theorem qRankP_fam (d x y : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) :
    (y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) ∨
    (¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧
      qRankP d (x, y) = 2 * y - (x + y) % 2) ∨
    (¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧
      y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧
      qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) ∨
    (¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧
      ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) ∨
    (¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧
      ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧
      x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) ∨
    (¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧
      ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧
      x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) ∨
    (¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧
      ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧
      x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) ∨
    (¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧
      ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧
      x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) ∨
    (¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧
      ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧
      ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) := by
  have hn' := hn
  unfold NativeP at hn'
  by_cases hH : y = 0 ∧ 1 ≤ x ∧ x ≤ d
  · refine Or.inl ⟨hH.1, hH.2.1, hH.2.2, ?_⟩
    unfold qRankP
    dsimp only
    rw [if_pos (show IsFreeP d (x, y) from Or.inl ((isHc_iff d x y).mpr hH))]
    exact vP_H d x y hH
  by_cases hV : (x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)
  · refine Or.inr (Or.inl ⟨hH, hV, ?_⟩)
    unfold qRankP
    dsimp only
    rw [if_pos (show IsFreeP d (x, y) from Or.inr ((isVc_iff d x y).mpr hV))]
    exact vP_V d x y hH hV
  have hfree : ¬ IsFreeP d (x, y) := fun h =>
    h.elim (fun h' => hH ((isHc_iff d x y).mp h')) (fun h' => hV ((isVc_iff d x y).mp h'))
  by_cases hT : y = d + 1 ∧ x ≤ 1
  · have hb : 2 - d ≤ x := by
      rcases hn' with hb | h0 | h0
      · omega
      · simp only [Prod.mk.injEq] at h0
        exact absurd (Or.inl ⟨h0.1, h0.2⟩) hV
      · simp only [Prod.mk.injEq] at h0
        omega
    refine Or.inr (Or.inr (Or.inl ⟨hH, hV, hT.1, hT.2, hb, ?_⟩))
    unfold qRankP
    dsimp only
    rw [if_neg hfree, if_pos hT, vP_H d (x + d - 1) 0 ⟨rfl, by omega, by omega⟩]
  by_cases hC : x = 2 ∧ y = d + 1
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hH, hV, hT, hC.1, hC.2, ?_⟩)))
    unfold qRankP
    dsimp only
    rw [if_neg hfree, if_neg hT, if_pos (show (x, y) = (2, d + 1) from Prod.ext hC.1 hC.2),
      vP_V d (2 - d) d (by omega) (Or.inr (Or.inr ⟨rfl, rfl⟩))]
    omega
  by_cases hA : x + y = d + 2
  · have hb2 : 2 ≤ x ∧ x ≤ d := by
      rcases hn' with hb | h0 | h0
      · omega
      · simp only [Prod.mk.injEq] at h0
        omega
      · simp only [Prod.mk.injEq] at h0
        exact absurd ⟨h0.1, h0.2⟩ hC
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hH, hV, hT, hC, hA, hb2.1, hb2.2, ?_⟩))))
    unfold qRankP
    dsimp only
    rw [if_neg hfree, if_neg hT, if_neg (fun h => hC (by simp only [Prod.mk.injEq] at h; exact ⟨h.1, h.2⟩)),
      if_pos hA, vP_V d (x - d) (y - 1) (by omega) (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))]
    omega
  by_cases hD : x = d ∧ y = 1
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hH, hV, hT, hC, hA, hD.1, hD.2, ?_⟩)))))
    unfold qRankP
    dsimp only
    rw [if_neg hfree, if_neg hT, if_neg (fun h => hC (by simp only [Prod.mk.injEq] at h; exact ⟨h.1, h.2⟩)),
      if_neg hA, if_pos (show (x, y) = (d, 1) from Prod.ext hD.1 hD.2),
      vP_V d 0 0 (by omega) (Or.inl ⟨rfl, rfl⟩)]
    omega
  by_cases hlf : x ≤ 0
  · by_cases hs : x + y = 2
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hH, hV, hT, hC, hA, hD, hlf, hs, ?_⟩))))))
      unfold qRankP
      dsimp only
      rw [if_neg hfree, if_neg hT, if_neg (fun h => hC (by simp only [Prod.mk.injEq] at h; exact ⟨h.1, h.2⟩)),
        if_neg hA, if_neg (fun h => hD (by simp only [Prod.mk.injEq] at h; exact ⟨h.1, h.2⟩))]
      exact vP_L1 d x y hH hV hlf hs
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hH, hV, hT, hC, hA, hD, hlf, hs, ?_⟩)))))))
      unfold qRankP
      dsimp only
      rw [if_neg hfree, if_neg hT, if_neg (fun h => hC (by simp only [Prod.mk.injEq] at h; exact ⟨h.1, h.2⟩)),
        if_neg hA, if_neg (fun h => hD (by simp only [Prod.mk.injEq] at h; exact ⟨h.1, h.2⟩))]
      exact vP_L2 d x y hH hV hlf hs
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hH, hV, hT, hC, hA, hD, hlf, ?_⟩)))))))
    unfold qRankP
    dsimp only
    rw [if_neg hfree, if_neg hT, if_neg (fun h => hC (by simp only [Prod.mk.injEq] at h; exact ⟨h.1, h.2⟩)),
      if_neg hA, if_neg (fun h => hD (by simp only [Prod.mk.injEq] at h; exact ⟨h.1, h.2⟩))]
    exact vP_R d x y hH hV hlf

set_option maxHeartbeats 400000 in
theorem shP_U_1_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (_hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_1_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_1_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_1_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_1_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_1_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_1_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_1_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_1_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_2_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_2_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_2_3 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_2_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_2_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_2_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_2_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_2_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_2_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_3_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_3_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_3_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_3_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_3_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_3_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_3_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_3_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_3_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_4_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_4_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_4_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_4_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_4_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_4_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_4_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_4_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_4_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_5_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_5_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_5_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_5_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_5_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_5_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_5_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_5_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_5_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_6_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (_hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_6_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_6_3 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_6_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_6_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_6_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_6_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_6_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_6_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_7_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (_hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_7_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_7_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_7_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_7_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_7_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_7_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_7_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_7_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_8_1 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_8_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_8_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_8_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_8_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_8_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_8_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_8_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_8_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_9_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_9_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_9_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_9_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_9_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_9_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_9_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_9_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_U_9_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + d) (hv : v = y + 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem qRankP_shift_U (d x y : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hn' : NativeP d (x + d, y + 1)) : qRankP d (x + d, y + 1) = qRankP d (x, y) + 2 * d := by
  have h1 := qRankP_fam d x y hd3 hdodd hn
  have h2 := qRankP_fam d (x + d) (y + 1) hd3 hdodd hn'
  rcases h1 with h1_0 | h1_1 | h1_2 | h1_3 | h1_4 | h1_5 | h1_6 | h1_7 | h1_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_U_1_1 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_0
    · exact shP_U_1_2 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_1
    · exact shP_U_1_3 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_2
    · exact shP_U_1_4 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_3
    · exact shP_U_1_5 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_4
    · exact shP_U_1_6 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_5
    · exact shP_U_1_7 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_6
    · exact shP_U_1_8 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_7
    · exact shP_U_1_9 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_U_2_1 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_0
    · exact shP_U_2_2 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_1
    · exact shP_U_2_3 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_2
    · exact shP_U_2_4 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_3
    · exact shP_U_2_5 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_4
    · exact shP_U_2_6 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_5
    · exact shP_U_2_7 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_6
    · exact shP_U_2_8 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_7
    · exact shP_U_2_9 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_U_3_1 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_0
    · exact shP_U_3_2 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_1
    · exact shP_U_3_3 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_2
    · exact shP_U_3_4 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_3
    · exact shP_U_3_5 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_4
    · exact shP_U_3_6 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_5
    · exact shP_U_3_7 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_6
    · exact shP_U_3_8 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_7
    · exact shP_U_3_9 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_U_4_1 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_0
    · exact shP_U_4_2 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_1
    · exact shP_U_4_3 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_2
    · exact shP_U_4_4 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_3
    · exact shP_U_4_5 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_4
    · exact shP_U_4_6 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_5
    · exact shP_U_4_7 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_6
    · exact shP_U_4_8 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_7
    · exact shP_U_4_9 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_U_5_1 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_0
    · exact shP_U_5_2 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_1
    · exact shP_U_5_3 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_2
    · exact shP_U_5_4 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_3
    · exact shP_U_5_5 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_4
    · exact shP_U_5_6 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_5
    · exact shP_U_5_7 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_6
    · exact shP_U_5_8 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_7
    · exact shP_U_5_9 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_U_6_1 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_0
    · exact shP_U_6_2 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_1
    · exact shP_U_6_3 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_2
    · exact shP_U_6_4 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_3
    · exact shP_U_6_5 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_4
    · exact shP_U_6_6 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_5
    · exact shP_U_6_7 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_6
    · exact shP_U_6_8 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_7
    · exact shP_U_6_9 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_U_7_1 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_0
    · exact shP_U_7_2 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_1
    · exact shP_U_7_3 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_2
    · exact shP_U_7_4 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_3
    · exact shP_U_7_5 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_4
    · exact shP_U_7_6 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_5
    · exact shP_U_7_7 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_6
    · exact shP_U_7_8 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_7
    · exact shP_U_7_9 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_U_8_1 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_0
    · exact shP_U_8_2 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_1
    · exact shP_U_8_3 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_2
    · exact shP_U_8_4 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_3
    · exact shP_U_8_5 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_4
    · exact shP_U_8_6 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_5
    · exact shP_U_8_7 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_6
    · exact shP_U_8_8 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_7
    · exact shP_U_8_9 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_U_9_1 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_0
    · exact shP_U_9_2 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_1
    · exact shP_U_9_3 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_2
    · exact shP_U_9_4 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_3
    · exact shP_U_9_5 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_4
    · exact shP_U_9_6 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_5
    · exact shP_U_9_7 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_6
    · exact shP_U_9_8 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_7
    · exact shP_U_9_9 d x y (x + d) (y + 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_8

set_option maxHeartbeats 400000 in
theorem shP_negU_1_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (_hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_1_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_1_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_1_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_1_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_1_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_1_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_1_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_1_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_2_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_2_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_2_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_2_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_2_5 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_2_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_2_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_2_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_2_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_3_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_3_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_3_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_3_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_3_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_3_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_3_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_3_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_3_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_4_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_4_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_4_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_4_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_4_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_4_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_4_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_4_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_4_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_5_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_5_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_5_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_5_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_5_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_5_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_5_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_5_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_5_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_6_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_6_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_6_3 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_6_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_6_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_6_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_6_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_6_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_6_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_7_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (_hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_7_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_7_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_7_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_7_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_7_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_7_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_7_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_7_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_8_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_8_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_8_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_8_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_8_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_8_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_8_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_8_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_8_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_9_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_9_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_9_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_9_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_9_5 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_9_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_9_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_9_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negU_9_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - d) (hv : v = y - 1)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * d := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem qRankP_shift_negU (d x y : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hn' : NativeP d (x - d, y - 1)) : qRankP d (x - d, y - 1) = qRankP d (x, y) - 2 * d := by
  have h1 := qRankP_fam d x y hd3 hdodd hn
  have h2 := qRankP_fam d (x - d) (y - 1) hd3 hdodd hn'
  rcases h1 with h1_0 | h1_1 | h1_2 | h1_3 | h1_4 | h1_5 | h1_6 | h1_7 | h1_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negU_1_1 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_0
    · exact shP_negU_1_2 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_1
    · exact shP_negU_1_3 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_2
    · exact shP_negU_1_4 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_3
    · exact shP_negU_1_5 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_4
    · exact shP_negU_1_6 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_5
    · exact shP_negU_1_7 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_6
    · exact shP_negU_1_8 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_7
    · exact shP_negU_1_9 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_0 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negU_2_1 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_0
    · exact shP_negU_2_2 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_1
    · exact shP_negU_2_3 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_2
    · exact shP_negU_2_4 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_3
    · exact shP_negU_2_5 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_4
    · exact shP_negU_2_6 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_5
    · exact shP_negU_2_7 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_6
    · exact shP_negU_2_8 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_7
    · exact shP_negU_2_9 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_1 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negU_3_1 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_0
    · exact shP_negU_3_2 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_1
    · exact shP_negU_3_3 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_2
    · exact shP_negU_3_4 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_3
    · exact shP_negU_3_5 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_4
    · exact shP_negU_3_6 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_5
    · exact shP_negU_3_7 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_6
    · exact shP_negU_3_8 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_7
    · exact shP_negU_3_9 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_2 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negU_4_1 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_0
    · exact shP_negU_4_2 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_1
    · exact shP_negU_4_3 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_2
    · exact shP_negU_4_4 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_3
    · exact shP_negU_4_5 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_4
    · exact shP_negU_4_6 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_5
    · exact shP_negU_4_7 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_6
    · exact shP_negU_4_8 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_7
    · exact shP_negU_4_9 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_3 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negU_5_1 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_0
    · exact shP_negU_5_2 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_1
    · exact shP_negU_5_3 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_2
    · exact shP_negU_5_4 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_3
    · exact shP_negU_5_5 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_4
    · exact shP_negU_5_6 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_5
    · exact shP_negU_5_7 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_6
    · exact shP_negU_5_8 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_7
    · exact shP_negU_5_9 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_4 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negU_6_1 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_0
    · exact shP_negU_6_2 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_1
    · exact shP_negU_6_3 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_2
    · exact shP_negU_6_4 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_3
    · exact shP_negU_6_5 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_4
    · exact shP_negU_6_6 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_5
    · exact shP_negU_6_7 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_6
    · exact shP_negU_6_8 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_7
    · exact shP_negU_6_9 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_5 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negU_7_1 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_0
    · exact shP_negU_7_2 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_1
    · exact shP_negU_7_3 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_2
    · exact shP_negU_7_4 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_3
    · exact shP_negU_7_5 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_4
    · exact shP_negU_7_6 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_5
    · exact shP_negU_7_7 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_6
    · exact shP_negU_7_8 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_7
    · exact shP_negU_7_9 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_6 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negU_8_1 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_0
    · exact shP_negU_8_2 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_1
    · exact shP_negU_8_3 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_2
    · exact shP_negU_8_4 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_3
    · exact shP_negU_8_5 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_4
    · exact shP_negU_8_6 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_5
    · exact shP_negU_8_7 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_6
    · exact shP_negU_8_8 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_7
    · exact shP_negU_8_9 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_7 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negU_9_1 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_0
    · exact shP_negU_9_2 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_1
    · exact shP_negU_9_3 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_2
    · exact shP_negU_9_4 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_3
    · exact shP_negU_9_5 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_4
    · exact shP_negU_9_6 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_5
    · exact shP_negU_9_7 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_6
    · exact shP_negU_9_8 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_7
    · exact shP_negU_9_9 d x y (x - d) (y - 1) hd3 hdodd hn hn' rfl rfl h1_8 h2_8

set_option maxHeartbeats 400000 in
theorem shP_V_1_1 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_1_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_1_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_1_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_1_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_1_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_1_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_1_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_1_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_2_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_2_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_2_3 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_2_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_2_5 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_2_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_2_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_2_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_2_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_3_1 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_3_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_3_3 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_3_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_3_5 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_3_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_3_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_3_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_3_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_4_1 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_4_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_4_3 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_4_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_4_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_4_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_4_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_4_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_4_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_5_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_5_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_5_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_5_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_5_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_5_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_5_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_5_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_5_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_6_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_6_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_6_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_6_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_6_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_6_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_6_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_6_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_6_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_7_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_7_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_7_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_7_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_7_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_7_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_7_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_7_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_7_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_8_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_8_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_8_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_8_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_8_5 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_8_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_8_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_8_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_8_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_9_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_9_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_9_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  obtain ⟨hH1, -, -, -, -, -, hx1, e1⟩ := h1
  obtain ⟨-, -, t1, t2, t3, e2⟩ := h2
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_9_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_9_5 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_9_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_9_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_9_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_V_9_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x + 1 - d) (hv : v = y + 1 + d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) + 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem qRankP_shift_V (d x y : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hn' : NativeP d (x + 1 - d, y + 1 + d)) : qRankP d (x + 1 - d, y + 1 + d) = qRankP d (x, y) + 2 * (d + 1) := by
  have h1 := qRankP_fam d x y hd3 hdodd hn
  have h2 := qRankP_fam d (x + 1 - d) (y + 1 + d) hd3 hdodd hn'
  rcases h1 with h1_0 | h1_1 | h1_2 | h1_3 | h1_4 | h1_5 | h1_6 | h1_7 | h1_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_V_1_1 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_0 h2_0
    · exact shP_V_1_2 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_0 h2_1
    · exact shP_V_1_3 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_0 h2_2
    · exact shP_V_1_4 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_0 h2_3
    · exact shP_V_1_5 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_0 h2_4
    · exact shP_V_1_6 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_0 h2_5
    · exact shP_V_1_7 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_0 h2_6
    · exact shP_V_1_8 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_0 h2_7
    · exact shP_V_1_9 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_0 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_V_2_1 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_1 h2_0
    · exact shP_V_2_2 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_1 h2_1
    · exact shP_V_2_3 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_1 h2_2
    · exact shP_V_2_4 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_1 h2_3
    · exact shP_V_2_5 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_1 h2_4
    · exact shP_V_2_6 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_1 h2_5
    · exact shP_V_2_7 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_1 h2_6
    · exact shP_V_2_8 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_1 h2_7
    · exact shP_V_2_9 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_1 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_V_3_1 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_2 h2_0
    · exact shP_V_3_2 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_2 h2_1
    · exact shP_V_3_3 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_2 h2_2
    · exact shP_V_3_4 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_2 h2_3
    · exact shP_V_3_5 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_2 h2_4
    · exact shP_V_3_6 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_2 h2_5
    · exact shP_V_3_7 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_2 h2_6
    · exact shP_V_3_8 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_2 h2_7
    · exact shP_V_3_9 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_2 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_V_4_1 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_3 h2_0
    · exact shP_V_4_2 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_3 h2_1
    · exact shP_V_4_3 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_3 h2_2
    · exact shP_V_4_4 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_3 h2_3
    · exact shP_V_4_5 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_3 h2_4
    · exact shP_V_4_6 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_3 h2_5
    · exact shP_V_4_7 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_3 h2_6
    · exact shP_V_4_8 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_3 h2_7
    · exact shP_V_4_9 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_3 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_V_5_1 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_4 h2_0
    · exact shP_V_5_2 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_4 h2_1
    · exact shP_V_5_3 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_4 h2_2
    · exact shP_V_5_4 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_4 h2_3
    · exact shP_V_5_5 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_4 h2_4
    · exact shP_V_5_6 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_4 h2_5
    · exact shP_V_5_7 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_4 h2_6
    · exact shP_V_5_8 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_4 h2_7
    · exact shP_V_5_9 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_4 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_V_6_1 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_5 h2_0
    · exact shP_V_6_2 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_5 h2_1
    · exact shP_V_6_3 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_5 h2_2
    · exact shP_V_6_4 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_5 h2_3
    · exact shP_V_6_5 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_5 h2_4
    · exact shP_V_6_6 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_5 h2_5
    · exact shP_V_6_7 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_5 h2_6
    · exact shP_V_6_8 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_5 h2_7
    · exact shP_V_6_9 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_5 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_V_7_1 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_6 h2_0
    · exact shP_V_7_2 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_6 h2_1
    · exact shP_V_7_3 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_6 h2_2
    · exact shP_V_7_4 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_6 h2_3
    · exact shP_V_7_5 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_6 h2_4
    · exact shP_V_7_6 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_6 h2_5
    · exact shP_V_7_7 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_6 h2_6
    · exact shP_V_7_8 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_6 h2_7
    · exact shP_V_7_9 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_6 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_V_8_1 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_7 h2_0
    · exact shP_V_8_2 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_7 h2_1
    · exact shP_V_8_3 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_7 h2_2
    · exact shP_V_8_4 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_7 h2_3
    · exact shP_V_8_5 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_7 h2_4
    · exact shP_V_8_6 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_7 h2_5
    · exact shP_V_8_7 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_7 h2_6
    · exact shP_V_8_8 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_7 h2_7
    · exact shP_V_8_9 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_7 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_V_9_1 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_8 h2_0
    · exact shP_V_9_2 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_8 h2_1
    · exact shP_V_9_3 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_8 h2_2
    · exact shP_V_9_4 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_8 h2_3
    · exact shP_V_9_5 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_8 h2_4
    · exact shP_V_9_6 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_8 h2_5
    · exact shP_V_9_7 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_8 h2_6
    · exact shP_V_9_8 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_8 h2_7
    · exact shP_V_9_9 d x y (x + 1 - d) (y + 1 + d) hd3 hdodd hn hn' rfl rfl h1_8 h2_8

set_option maxHeartbeats 400000 in
theorem shP_negV_1_1 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_1_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_1_3 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_1_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_1_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_1_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_1_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_1_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_1_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : y = 0 ∧ 1 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * x + (x + y) % 2 - 4) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_2_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_2_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_2_3 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_2_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_2_5 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_2_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_2_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_2_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_2_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ qRankP d (x, y) = 2 * y - (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_3_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_3_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_3_3 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_3_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_3_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_3_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_3_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_3_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_3_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ y = d + 1 ∧ x ≤ 1 ∧ 2 - d ≤ x ∧ qRankP d (x, y) = 2 * (x + d - 1) + (x + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_4_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_4_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_4_3 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_4_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_4_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_4_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_4_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_4_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_4_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ x = 2 ∧ y = d + 1 ∧ qRankP d (x, y) = 4 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_5_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_5_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_5_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_5_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_5_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_5_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_5_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_5_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_5_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ qRankP d (x, y) = 2 * y - 3 + 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_6_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_6_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_6_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_6_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_6_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_6_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_6_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_6_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_6_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ x = d ∧ y = 1 ∧ qRankP d (x, y) = 2 * d) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_7_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_7_2 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_7_3 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_7_4 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_7_5 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_7_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_7_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_7_8 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_7_9 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ x + y = 2 ∧ qRankP d (x, y) = 2 * y) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_8_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_8_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_8_3 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_8_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_8_5 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_8_6 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_8_7 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_8_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_8_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ x ≤ 0 ∧ ¬ (x + y = 2) ∧ qRankP d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_9_1 (d x y u v : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : v = 0 ∧ 1 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * u + (u + v) % 2 - 4) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_9_2 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ qRankP d (u, v) = 2 * v - (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_9_3 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ v = d + 1 ∧ u ≤ 1 ∧ 2 - d ≤ u ∧ qRankP d (u, v) = 2 * (u + d - 1) + (u + d - 1 + 0) % 2 - 4 + 2 * (d + 1)) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_9_4 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ u = 2 ∧ v = d + 1 ∧ qRankP d (u, v) = 4 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_9_5 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ u + v = d + 2 ∧ 2 ≤ u ∧ u ≤ d ∧ qRankP d (u, v) = 2 * v - 3 + 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_9_6 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ u = d ∧ v = 1 ∧ qRankP d (u, v) = 2 * d) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_9_7 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ u + v = 2 ∧ qRankP d (u, v) = 2 * v) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_9_8 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ u ≤ 0 ∧ ¬ (u + v = 2) ∧ qRankP d (u, v) = 2 * u + 4 * d - 4 + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem shP_negV_9_9 (d x y u v : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hn' : NativeP d (u, v))
    (hu : u = x - 1 + d) (hv : v = y - 1 - d)
    (h1 : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∧ ¬ ((x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨ (x = 2 - d ∧ y = d)) ∧ ¬ (y = d + 1 ∧ x ≤ 1) ∧ ¬ (x = 2 ∧ y = d + 1) ∧ ¬ (x + y = d + 2) ∧ ¬ (x = d ∧ y = 1) ∧ ¬ (x ≤ 0) ∧ qRankP d (x, y) = 4 * d - 2 * x + (x + y) % 2) (h2 : ¬ (v = 0 ∧ 1 ≤ u ∧ u ≤ d) ∧ ¬ ((u = 0 ∧ v = 0) ∨ (u + v = 1 ∧ 1 ≤ v ∧ v < d) ∨ (u = 2 - d ∧ v = d)) ∧ ¬ (v = d + 1 ∧ u ≤ 1) ∧ ¬ (u = 2 ∧ v = d + 1) ∧ ¬ (u + v = d + 2) ∧ ¬ (u = d ∧ v = 1) ∧ ¬ (u ≤ 0) ∧ qRankP d (u, v) = 4 * d - 2 * u + (u + v) % 2) : qRankP d (u, v) = qRankP d (x, y) - 2 * (d + 1) := by
  obtain ⟨-, -, -, hC1, -, -, hx1, e1⟩ := h1
  obtain ⟨k1, -, -, -, -, -, k6, e2⟩ := h2
  have _r1 := hn
  have _r2 := hn'
  have _r3 := hu
  have _r4 := hv
  unfold NativeP at hn hn'
  simp only [Prod.mk.injEq] at hn hn'
  omega

set_option maxHeartbeats 400000 in
theorem qRankP_shift_negV (d x y : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hn' : NativeP d (x - 1 + d, y - 1 - d)) : qRankP d (x - 1 + d, y - 1 - d) = qRankP d (x, y) - 2 * (d + 1) := by
  have h1 := qRankP_fam d x y hd3 hdodd hn
  have h2 := qRankP_fam d (x - 1 + d) (y - 1 - d) hd3 hdodd hn'
  rcases h1 with h1_0 | h1_1 | h1_2 | h1_3 | h1_4 | h1_5 | h1_6 | h1_7 | h1_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negV_1_1 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_0 h2_0
    · exact shP_negV_1_2 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_0 h2_1
    · exact shP_negV_1_3 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_0 h2_2
    · exact shP_negV_1_4 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_0 h2_3
    · exact shP_negV_1_5 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_0 h2_4
    · exact shP_negV_1_6 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_0 h2_5
    · exact shP_negV_1_7 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_0 h2_6
    · exact shP_negV_1_8 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_0 h2_7
    · exact shP_negV_1_9 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_0 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negV_2_1 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_1 h2_0
    · exact shP_negV_2_2 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_1 h2_1
    · exact shP_negV_2_3 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_1 h2_2
    · exact shP_negV_2_4 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_1 h2_3
    · exact shP_negV_2_5 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_1 h2_4
    · exact shP_negV_2_6 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_1 h2_5
    · exact shP_negV_2_7 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_1 h2_6
    · exact shP_negV_2_8 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_1 h2_7
    · exact shP_negV_2_9 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_1 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negV_3_1 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_2 h2_0
    · exact shP_negV_3_2 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_2 h2_1
    · exact shP_negV_3_3 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_2 h2_2
    · exact shP_negV_3_4 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_2 h2_3
    · exact shP_negV_3_5 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_2 h2_4
    · exact shP_negV_3_6 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_2 h2_5
    · exact shP_negV_3_7 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_2 h2_6
    · exact shP_negV_3_8 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_2 h2_7
    · exact shP_negV_3_9 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_2 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negV_4_1 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_3 h2_0
    · exact shP_negV_4_2 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_3 h2_1
    · exact shP_negV_4_3 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_3 h2_2
    · exact shP_negV_4_4 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_3 h2_3
    · exact shP_negV_4_5 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_3 h2_4
    · exact shP_negV_4_6 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_3 h2_5
    · exact shP_negV_4_7 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_3 h2_6
    · exact shP_negV_4_8 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_3 h2_7
    · exact shP_negV_4_9 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_3 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negV_5_1 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_4 h2_0
    · exact shP_negV_5_2 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_4 h2_1
    · exact shP_negV_5_3 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_4 h2_2
    · exact shP_negV_5_4 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_4 h2_3
    · exact shP_negV_5_5 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_4 h2_4
    · exact shP_negV_5_6 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_4 h2_5
    · exact shP_negV_5_7 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_4 h2_6
    · exact shP_negV_5_8 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_4 h2_7
    · exact shP_negV_5_9 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_4 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negV_6_1 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_5 h2_0
    · exact shP_negV_6_2 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_5 h2_1
    · exact shP_negV_6_3 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_5 h2_2
    · exact shP_negV_6_4 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_5 h2_3
    · exact shP_negV_6_5 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_5 h2_4
    · exact shP_negV_6_6 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_5 h2_5
    · exact shP_negV_6_7 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_5 h2_6
    · exact shP_negV_6_8 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_5 h2_7
    · exact shP_negV_6_9 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_5 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negV_7_1 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_6 h2_0
    · exact shP_negV_7_2 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_6 h2_1
    · exact shP_negV_7_3 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_6 h2_2
    · exact shP_negV_7_4 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_6 h2_3
    · exact shP_negV_7_5 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_6 h2_4
    · exact shP_negV_7_6 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_6 h2_5
    · exact shP_negV_7_7 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_6 h2_6
    · exact shP_negV_7_8 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_6 h2_7
    · exact shP_negV_7_9 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_6 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negV_8_1 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_7 h2_0
    · exact shP_negV_8_2 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_7 h2_1
    · exact shP_negV_8_3 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_7 h2_2
    · exact shP_negV_8_4 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_7 h2_3
    · exact shP_negV_8_5 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_7 h2_4
    · exact shP_negV_8_6 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_7 h2_5
    · exact shP_negV_8_7 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_7 h2_6
    · exact shP_negV_8_8 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_7 h2_7
    · exact shP_negV_8_9 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_7 h2_8
  · rcases h2 with h2_0 | h2_1 | h2_2 | h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8
    · exact shP_negV_9_1 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_8 h2_0
    · exact shP_negV_9_2 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_8 h2_1
    · exact shP_negV_9_3 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_8 h2_2
    · exact shP_negV_9_4 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_8 h2_3
    · exact shP_negV_9_5 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_8 h2_4
    · exact shP_negV_9_6 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_8 h2_5
    · exact shP_negV_9_7 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_8 h2_6
    · exact shP_negV_9_8 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_8 h2_7
    · exact shP_negV_9_9 d x y (x - 1 + d) (y - 1 - d) hd3 hdodd hn hn' rfl rfl h1_8 h2_8

end FLatticePaper.QRankPlusDeck
