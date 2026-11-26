import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Defs

/-! # The aligned classification in grades (eps = +1), the grade-level core

The strict centre `(t, s)` (grades) with an aligned free V witness and a top free H witness lies at the target `V + (2,-1)` (grades
`(-T+2n+d, d+3n)`) or in the explicit set of excluded offsets. The site-level statement, through the inverse identities, is in a
later module. Every offset is a literal, so each case is linear. -/

namespace FLatticePaper.AlignedClassGrade


def ClG (n d T t s : Int) : Prop :=
  (t % 2 = 0 ∧ 2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2 * n) ∨
  (t % 2 = 1 ∧ n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2)

def vSpG (n d s : Int) : Prop :=
  s % 2 = 0 ∧ ((0 ≤ s ∧ s ≤ 2 * n) ∨ (2 - d + n ≤ s ∧ s ≤ d + n - 2))

def hSpG (n d t : Int) : Prop :=
  (t % 2 = 0 ∧ 2 ≤ t ∧ t ≤ d + n - 2) ∨ (t % 2 = 1 ∧ n ≤ t ∧ t ≤ d)

/-- aligned free V at grades (t, s) (with the kernel-shifted `s` already applied) -/
def FVG (n d T t s : Int) : Prop :=
  ClG n d T t s ∧ ¬ ClG n d T (t - n) (s - (d + n)) ∧ vSpG n d s

/-- free H at grades (t, s) -/
def FHG (n d T t s : Int) : Prop :=
  ClG n d T t s ∧ ¬ ClG n d T (t + d) (s - (d - n)) ∧ hSpG n d t

def SIG (n d T t s : Int) : Prop :=
  (t % 2 = 0 ∧ d + n - 2 - T < t ∧ t < 2 ∧ 2 * n < s ∧ s < T) ∨
  (t % 2 = 1 ∧ d - T < t ∧ t < n ∧ d + n - 2 < s ∧ s < T + (2 - d + n))

def FVr (n d T t s : Int) : Prop := ClG n d T t s ∧ vSpG n d s
def FHr (n d T t s : Int) : Prop := ClG n d T t s ∧ hSpG n d t
theorem box_plus_mm (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * (-1) - d * (-1)) (s + (d + n) * (-1) + (d - n) * (-1)))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -2 * n + 1 ≤ t - (-T + 2 * n + d) ∧ t - (-T + 2 * n + d) ≤ d - 1 ∧
      -(d + n) + 2 ≤ s - (d + 3 * n) ∧ s - (d + 3 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega

theorem box_plus_mz (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * (-1) - d * 0) (s + (d + n) * (-1) + (d - n) * 0))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -2 * n + 1 ≤ t - (-T + 2 * n + d) ∧ t - (-T + 2 * n + d) ≤ d - 1 ∧
      -(d + n) + 2 ≤ s - (d + 3 * n) ∧ s - (d + 3 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega

theorem box_plus_mp (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * (-1) - d * 1) (s + (d + n) * (-1) + (d - n) * 1))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -2 * n + 1 ≤ t - (-T + 2 * n + d) ∧ t - (-T + 2 * n + d) ≤ d - 1 ∧
      -(d + n) + 2 ≤ s - (d + 3 * n) ∧ s - (d + 3 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega

theorem box_plus_zm (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * 0 - d * (-1)) (s + (d + n) * 0 + (d - n) * (-1)))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -2 * n + 1 ≤ t - (-T + 2 * n + d) ∧ t - (-T + 2 * n + d) ≤ d - 1 ∧
      -(d + n) + 2 ≤ s - (d + 3 * n) ∧ s - (d + 3 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega

theorem box_plus_zz (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * 0 - d * 0) (s + (d + n) * 0 + (d - n) * 0))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -2 * n + 1 ≤ t - (-T + 2 * n + d) ∧ t - (-T + 2 * n + d) ≤ d - 1 ∧
      -(d + n) + 2 ≤ s - (d + 3 * n) ∧ s - (d + 3 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega

theorem box_plus_zp (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * 0 - d * 1) (s + (d + n) * 0 + (d - n) * 1))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -2 * n + 1 ≤ t - (-T + 2 * n + d) ∧ t - (-T + 2 * n + d) ≤ d - 1 ∧
      -(d + n) + 2 ≤ s - (d + 3 * n) ∧ s - (d + 3 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega

theorem box_plus_pm (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * 1 - d * (-1)) (s + (d + n) * 1 + (d - n) * (-1)))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -2 * n + 1 ≤ t - (-T + 2 * n + d) ∧ t - (-T + 2 * n + d) ≤ d - 1 ∧
      -(d + n) + 2 ≤ s - (d + 3 * n) ∧ s - (d + 3 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega

theorem box_plus_pz (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * 1 - d * 0) (s + (d + n) * 1 + (d - n) * 0))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -2 * n + 1 ≤ t - (-T + 2 * n + d) ∧ t - (-T + 2 * n + d) ≤ d - 1 ∧
      -(d + n) + 2 ≤ s - (d + 3 * n) ∧ s - (d + 3 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega

theorem box_plus_pp (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (_hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hS : SIG n d T t s)
    (hL : FVr n d T (t + n * 1 - d * 1) (s + (d + n) * 1 + (d - n) * 1))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -2 * n + 1 ≤ t - (-T + 2 * n + d) ∧ t - (-T + 2 * n + d) ≤ d - 1 ∧
      -(d + n) + 2 ≤ s - (d + 3 * n) ∧ s - (d + 3 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FVr, FHr, ClG, vSpG, hSpG, SIG] at hS hL hT2 <;> omega

theorem box_plus_r (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTL : 2 * (d + n) < T) (hT : T % 2 = 0) (hS : SIG n d T t s)
    (hL : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FVr n d T (t + n * i - d * j) (s + (d + n) * i + (d - n) * j))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    -2 * n + 1 ≤ t - (-T + 2 * n + d) ∧ t - (-T + 2 * n + d) ≤ d - 1 ∧
      -(d + n) + 2 ≤ s - (d + 3 * n) ∧ s - (d + 3 * n) ≤ 2 * (d - n) - 2 := by
  obtain ⟨i1, j1, hi1a, hi1b, hj1a, hj1b, hL1⟩ := hL
  have hi1' : i1 = -1 ∨ i1 = 0 ∨ i1 = 1 := by omega
  have hj1' : j1 = -1 ∨ j1 = 0 ∨ j1 = 1 := by omega
  rcases hi1' with rfl | rfl | rfl <;> rcases hj1' with rfl | rfl | rfl
  · exact box_plus_mm n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_plus_mz n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_plus_mp n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_plus_zm n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_plus_zz n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_plus_zp n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_plus_pm n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_plus_pz n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop
  · exact box_plus_pp n d T t s hn hd hn1 hnd hTL hT hS hL1 hTop

theorem relaxL {n d T t s : Int}
    (h : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FVG n d T (t + n * i - d * j) (s + (d + n) * i + (d - n) * j)) :
    ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FVr n d T (t + n * i - d * j) (s + (d + n) * i + (d - n) * j) := by
  obtain ⟨i, j, a, b, c, e, hV⟩ := h
  exact ⟨i, j, a, b, c, e, hV.1, hV.2.2⟩

theorem relaxT {n d T t s : Int}
    (h : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHG n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j) := by
  obtain ⟨i, j, a, b, c, e, hH⟩ := h
  exact ⟨i, j, a, b, c, e, hH.1, hH.2.2⟩

/-- The offset `(1,0)` from `V + (2,-1)` is excluded by the aligned witness (full `FVG`). -/
theorem plus_excl_10 (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTL : 2 * (d + n) < T) (hT : T % 2 = 0)
    (hpt : t = (-T + 2 * n + d) + n * 1 - d * 0) (hps : s = (d + 3 * n) + (d + n) * 1 + (d - n) * 0)
    (hL : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FVG n d T (t + n * i - d * j) (s + (d + n) * i + (d - n) * j)) : False := by
  obtain ⟨i1, j1, hi1a, hi1b, hj1a, hj1b, hL1⟩ := hL
  have hi1' : i1 = -1 ∨ i1 = 0 ∨ i1 = 1 := by omega
  have hj1' : j1 = -1 ∨ j1 = 0 ∨ j1 = 1 := by omega
  rcases hi1' with rfl | rfl | rfl <;> rcases hj1' with rfl | rfl | rfl <;>
    simp only [FVG, ClG, vSpG] at hL1 <;> omega

/-- **The classification core, eps = +1**: the centre at offset `(p, q)` from `V + (2,-1)` is the target only. -/
theorem class_plus_core (n d T t s p q : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTL : 2 * (d + n) < T) (hT : T % 2 = 0) (hTdef : T = d * d + 2 * d * n - n * n)
    (hpt : t = (-T + 2 * n + d) + n * p - d * q) (hps : s = (d + 3 * n) + (d + n) * p + (d - n) * q)
    (hS : SIG n d T t s)
    (hL : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FVG n d T (t + n * i - d * j) (s + (d + n) * i + (d - n) * j))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHG n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) :
    p = 0 ∧ q = 0 := by
  have hbox := box_plus_r n d T t s hn hd hn1 hnd hTL hT hS (relaxL hL) (relaxT hTop)
  simp only [SIG] at hS
  have hT0 : 0 < T := by omega
  have hkp : T * p = d * (s - (d + 3 * n)) + (d - n) * (t - (-T + 2 * n + d)) := by
    rw [hps, hpt, hTdef]; ring
  have hkq : T * q = n * (s - (d + 3 * n)) - (d + n) * (t - (-T + 2 * n + d)) := by
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
    | exact (plus_excl_10 n d T t s hn hd hn1 hnd hTL hT hpt hps hL).elim



end FLatticePaper.AlignedClassGrade
