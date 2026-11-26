import FLatticePaper.Plane.Induction.AlignedClassGrade
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Defs

/-! # The aligned classification in grades, eps = -1

Target `R - (1,1) = (n, 2n+d-2)`: grades `(-T+2d, T-2d+2n)`. The aligned witness is the kernel-shifted free V point (grades
`(t_v, s_v - T)`). The box is `u = t - (-T+2d) in [-(d-1), 2n-1]`, `w = s - (T-2d+2n) in [-(d+n)+2, 2(d-n)-2]`. The survivors of the box
are the target, `(0,-1)` (excluded by the missing top witness) and `(1,0)` (excluded by strictness). -/

namespace FLatticePaper.AlignedClassGradeMinus

open FLatticePaper.AlignedClassGrade

theorem box_minus_mm (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * (-1) - d * (-1)) (s + (d + n) * (-1) + (d - n) * (-1) - T))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -(d - 1) ≤ t - (-T + 2 * d) ∧ t - (-T + 2 * d) ≤ 2 * n - 1 ∧
      -(d + n) + 2 ≤ s - (T - 2 * d + 2 * n) ∧ s - (T - 2 * d + 2 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega
theorem box_minus_mz (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * (-1) - d * 0) (s + (d + n) * (-1) + (d - n) * 0 - T))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -(d - 1) ≤ t - (-T + 2 * d) ∧ t - (-T + 2 * d) ≤ 2 * n - 1 ∧
      -(d + n) + 2 ≤ s - (T - 2 * d + 2 * n) ∧ s - (T - 2 * d + 2 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega
theorem box_minus_mp (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * (-1) - d * 1) (s + (d + n) * (-1) + (d - n) * 1 - T))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -(d - 1) ≤ t - (-T + 2 * d) ∧ t - (-T + 2 * d) ≤ 2 * n - 1 ∧
      -(d + n) + 2 ≤ s - (T - 2 * d + 2 * n) ∧ s - (T - 2 * d + 2 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega
theorem box_minus_zm (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * 0 - d * (-1)) (s + (d + n) * 0 + (d - n) * (-1) - T))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -(d - 1) ≤ t - (-T + 2 * d) ∧ t - (-T + 2 * d) ≤ 2 * n - 1 ∧
      -(d + n) + 2 ≤ s - (T - 2 * d + 2 * n) ∧ s - (T - 2 * d + 2 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega
theorem box_minus_zz (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * 0 - d * 0) (s + (d + n) * 0 + (d - n) * 0 - T))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -(d - 1) ≤ t - (-T + 2 * d) ∧ t - (-T + 2 * d) ≤ 2 * n - 1 ∧
      -(d + n) + 2 ≤ s - (T - 2 * d + 2 * n) ∧ s - (T - 2 * d + 2 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega
theorem box_minus_zp (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * 0 - d * 1) (s + (d + n) * 0 + (d - n) * 1 - T))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -(d - 1) ≤ t - (-T + 2 * d) ∧ t - (-T + 2 * d) ≤ 2 * n - 1 ∧
      -(d + n) + 2 ≤ s - (T - 2 * d + 2 * n) ∧ s - (T - 2 * d + 2 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega
theorem box_minus_pm (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * 1 - d * (-1)) (s + (d + n) * 1 + (d - n) * (-1) - T))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -(d - 1) ≤ t - (-T + 2 * d) ∧ t - (-T + 2 * d) ≤ 2 * n - 1 ∧
      -(d + n) + 2 ≤ s - (T - 2 * d + 2 * n) ∧ s - (T - 2 * d + 2 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega
theorem box_minus_pz (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * 1 - d * 0) (s + (d + n) * 1 + (d - n) * 0 - T))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -(d - 1) ≤ t - (-T + 2 * d) ∧ t - (-T + 2 * d) ≤ 2 * n - 1 ∧
      -(d + n) + 2 ≤ s - (T - 2 * d + 2 * n) ∧ s - (T - 2 * d + 2 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega
theorem box_minus_pp (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * 1 - d * 1) (s + (d + n) * 1 + (d - n) * 1 - T))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -(d - 1) ≤ t - (-T + 2 * d) ∧ t - (-T + 2 * d) ≤ 2 * n - 1 ∧
      -(d + n) + 2 ≤ s - (T - 2 * d + 2 * n) ∧ s - (T - 2 * d + 2 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega

theorem relaxLm {n d T t s : Int}
    (h : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FVG n d T (t + n * i - d * j) (s + (d + n) * i + (d - n) * j - T)) :
    ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FVr n d T (t + n * i - d * j) (s + (d + n) * i + (d - n) * j - T) := by
  obtain ⟨i, j, a, b, c, e, hV⟩ := h
  exact ⟨i, j, a, b, c, e, hV.1, hV.2.2⟩

theorem box_minus_r (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTL : 2 * (d + n) < T) (hT : T % 2 = 0) (hS : SIG n d T t s)
    (hL : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FVr n d T (t + n * i - d * j) (s + (d + n) * i + (d - n) * j - T))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -(d - 1) ≤ t - (-T + 2 * d) ∧ t - (-T + 2 * d) ≤ 2 * n - 1 ∧
      -(d + n) + 2 ≤ s - (T - 2 * d + 2 * n) ∧ s - (T - 2 * d + 2 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i1, j1, hi1a, hi1b, hj1a, hj1b, hL1⟩ := hL
  have hi1' : i1 = -1 ∨ i1 = 0 ∨ i1 = 1 := by omega
  have hj1' : j1 = -1 ∨ j1 = 0 ∨ j1 = 1 := by omega
  rcases hi1' with rfl | rfl | rfl <;> rcases hj1' with rfl | rfl | rfl
  · exact box_minus_mm n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_minus_mz n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_minus_mp n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_minus_zm n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_minus_zz n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_minus_zp n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_minus_pm n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_minus_pz n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_minus_pp n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
/-- The offset `(0,-1)` from the target is excluded by the top witness (full `FHG`). -/
theorem minus_excl_0m1 (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hpt : t = (-T + 2 * d) + n * 0 - d * (-1)) (_hps : s = (T - 2 * d + 2 * n) + (d + n) * 0 + (d - n) * (-1))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHG n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) : False := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FHG, ClG, hSpG] at hT2 <;> omega

/-- **The classification core, eps = -1**: the centre at offset `(p, q)` from `R - (1,1)` is the target only. -/
theorem class_minus_core (n d T t s p q : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTL : 2 * (d + n) < T) (hT : T % 2 = 0) (hTdef : T = d * d + 2 * d * n - n * n)
    (hpt : t = (-T + 2 * d) + n * p - d * q) (hps : s = (T - 2 * d + 2 * n) + (d + n) * p + (d - n) * q)
    (hS : SIG n d T t s)
    (hL : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FVG n d T (t + n * i - d * j) (s + (d + n) * i + (d - n) * j - T))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHG n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    p = 0 ∧ q = 0 := by
  have hbox := box_minus_r n d T t s hn hd hn1 hnd hTL hT hS (relaxLm hL) (relaxT hTop)
  simp only [SIG] at hS
  have hT0 : 0 < T := by omega
  have hkp : T * p = d * (s - (T - 2 * d + 2 * n)) + (d - n) * (t - (-T + 2 * d)) := by
    rw [hps, hpt, hTdef]; ring
  have hkq : T * q = n * (s - (T - 2 * d + 2 * n)) - (d + n) * (t - (-T + 2 * d)) := by
    rw [hps, hpt, hTdef]; ring
  have h1 := mul_le_mul_of_nonneg_left hbox.2.2.2 (show (0:Int) ≤ d by omega)
  have h2 := mul_le_mul_of_nonneg_left hbox.2.1 (show (0:Int) ≤ d - n by omega)
  have h3 := mul_le_mul_of_nonneg_left hbox.2.2.1 (show (0:Int) ≤ d by omega)
  have h4 := mul_le_mul_of_nonneg_left hbox.1 (show (0:Int) ≤ d - n by omega)
  have hp3 : p < 3 := by nlinarith
  have hp4 : -3 < p := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left hbox.2.2.2 (show (0:Int) ≤ n by omega)
  have h6 := mul_le_mul_of_nonneg_left hbox.2.1 (show (0:Int) ≤ d + n by omega)
  have h7 := mul_le_mul_of_nonneg_left hbox.2.2.1 (show (0:Int) ≤ n by omega)
  have h8 := mul_le_mul_of_nonneg_left hbox.1 (show (0:Int) ≤ d + n by omega)
  have hq3 : q < 3 := by nlinarith
  have hq4 : -3 < q := by nlinarith
  clear hkp hkq h1 h2 h3 h4 h5 h6 h7 h8
  have hp2 : -2 ≤ p ∧ p ≤ 2 := by omega
  have hq2 : -2 ≤ q ∧ q ≤ 2 := by omega
  obtain ⟨hpa, hpb⟩ := hp2
  obtain ⟨hqa, hqb⟩ := hq2
  have hpc : p = -2 ∨ p = -1 ∨ p = 0 ∨ p = 1 ∨ p = 2 := by omega
  have hqc : q = -2 ∨ q = -1 ∨ q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hpc with rfl | rfl | rfl | rfl | rfl <;> rcases hqc with rfl | rfl | rfl | rfl | rfl <;>
    first
    | omega
    | exact (minus_excl_0m1 n d T t s hn hd hn1 hnd hTL hT hpt hps hTop).elim

end FLatticePaper.AlignedClassGradeMinus
