import FLatticePaper.Construction.BaseCaseRecurrence
import FLatticePaper.Tiles.ZeroOneOdometers

/-! # Pilot: the per-tile identity of the odd `3^k` vertical base piece (zero tiles)

For the odd base ladder `d = 2k+2` (k ≥ 1) the paper value `paperLadderValue d` restricted to the zero tile at
`pos_j = (-(j-1), j)`, `1 ≤ j ≤ 2k+1`, is the family value `zeroOdometer (a,b) + (1,-j)·x + j(j+1)/2 - 1`, where `(a,b)` is the
point of the zero tile `T_0 = {(0,0),(0,1),(0,2),(1,0),(1,1),(1,2)}` and `x = pos_j + (a,b)`. The indicator of `A ∪ B` vanishes
on these points, and the `min`/`max` terms are linear in `k`, `j`. -/

namespace FLatticePaper.Tiles.BaseVertPilot

open FLatticePaper.Construction FLatticePaper.Tiles

/-- `(j+b)(j+b+1)/2` in the form used by the identity (`b = 0, 1, 2`). -/
theorem half_zero (j : ℤ) : j * (j + 1) / 2 = j * (j + 1) / 2 := rfl

theorem half_one (j : ℤ) : (j + 1) * (j + 1 + 1) / 2 = j * (j + 1) / 2 + (j + 1) := by
  have h : (j + 1) * (j + 1 + 1) = j * (j + 1) + 2 * (j + 1) := by ring
  rw [h]
  generalize j * (j + 1) = X
  omega

theorem half_two (j : ℤ) : (j + 2) * (j + 2 + 1) / 2 = j * (j + 1) / 2 + (2 * j + 3) := by
  have h : (j + 2) * (j + 2 + 1) = j * (j + 1) + 4 * j + 6 := by ring
  rw [h]
  generalize j * (j + 1) = X
  omega

/-- The value of the odd ladder `d` at the zero-tile points `x = pos_j + (a,b)`, `(a,b)` in the zero tile. -/
theorem ladder_zero_point (k j : ℤ) (hk : 1 ≤ k) (hj1 : 1 ≤ j) (hj : j ≤ 2 * k + 1) (a b : ℤ)
    (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) ∨ (a, b) = (1, 2)) :
    paperLadderValue (2 * k + 2) (-(j - 1) + a, j + b) =
      (if (a, b) = (0, 2) ∨ (a, b) = (1, 2) then -1 else 0) + ((-(j - 1) + a) - j * (j + b)) + (j * (j + 1) / 2 - 1) := by
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hb : 0 ≤ b ∧ b ≤ 2 := by
    rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb2⟩ := hb
  have hnot : (-(j - 1) + a, j + b) ∉ paperLadderA (2 * k + 2) ∪ paperLadderB (2 * k + 2) := by
    rintro (h | h)
    · simp only [paperLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · simp only [paperLadderB, Set.mem_setOf_eq] at h
      omega
  unfold paperLadderValue
  dsimp only
  rw [Set.indicator_of_notMem hnot]
  have e1 : min (-(j - 1) + a - 1) 0 = -(j - 1) + a - 1 := min_eq_left (by omega)
  have e2 : min 0 (2 * k + 2 + 1 - (-(j - 1) + a)) = 0 := min_eq_left (by omega)
  have e3 : max (-(j - 1) + a + (j + b) - (2 * k + 2) - 2) 0 = 0 := max_eq_right (by omega)
  rw [e1, e2, e3]
  have h1 : j * (j + 1) = j * j + j := by ring
  have h2 : j * (j + 2) = j * j + 2 * j := by ring
  have hT2 : 2 * (j * (j + 1) / 2) = j * j + j := by
    rw [Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self j)]
    ring
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
    simp only [add_zero, half_one, half_two, Prod.mk.injEq] <;>
    generalize j * (j + 1) / 2 = T at hT2 ⊢ <;> norm_num <;> linarith [hT2, h1, h2]

/-- The one tile `T_{1/1}` at `(0,0)` of the odd 3^k vertical base piece: the paper ladder value is `oneOdometer` there. -/
theorem ladder_one_point (k : ℤ) (hk : 1 ≤ k) (a b : ℤ)
    (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1)) :
    paperLadderValue (2 * k + 2) (a, b) = oneOdometer (a, b) := by
  rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · unfold paperLadderValue
    dsimp only
    rw [Set.indicator_of_mem (by simp [paperLadderA])]
    norm_num [oneOdometer]
    omega
  · unfold paperLadderValue
    dsimp only
    have hnot : ((0 : ℤ), (1 : ℤ)) ∉ paperLadderA (2 * k + 2) ∪ paperLadderB (2 * k + 2) := by
      rintro (h | h)
      · simp only [paperLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · simp only [paperLadderB, Set.mem_setOf_eq] at h
        omega
    rw [Set.indicator_of_notMem hnot]
    norm_num [oneOdometer]
    omega
  · unfold paperLadderValue
    dsimp only
    have hnot : ((1 : ℤ), (0 : ℤ)) ∉ paperLadderA (2 * k + 2) ∪ paperLadderB (2 * k + 2) := by
      rintro (h | h)
      · simp only [paperLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · simp only [paperLadderB, Set.mem_setOf_eq] at h
        omega
    rw [Set.indicator_of_notMem hnot]
    norm_num [oneOdometer]
    omega
  · unfold paperLadderValue
    dsimp only
    have hnot : ((1 : ℤ), (1 : ℤ)) ∉ paperLadderA (2 * k + 2) ∪ paperLadderB (2 * k + 2) := by
      rintro (h | h)
      · simp only [paperLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · simp only [paperLadderB, Set.mem_setOf_eq] at h
        omega
    rw [Set.indicator_of_notMem hnot]
    norm_num [oneOdometer]
    omega

end FLatticePaper.Tiles.BaseVertPilot
