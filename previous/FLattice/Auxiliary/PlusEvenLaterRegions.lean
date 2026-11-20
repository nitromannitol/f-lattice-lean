import FLattice.Auxiliary.PlusEvenRegions
import FLattice.Auxiliary.PlusEvenPredecessors
import FLattice.Auxiliary.PlusEvenDeficitTable

/-!
# Incoming selections for Regions II, III, and IV

Every selected object is an incoming edge index in `Fin 2`. The count uses
the actual physical deficit. An edge either reaches an earlier region or
has the indicated physical direction in the same region. No rank is
evaluated at a reduced target representative.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

private theorem select_single (η : ℤ) (P : Fin 2 → Prop) (i : Fin 2)
    (hη : η < 1) (hi : P i) :
    ∃ S : Finset (Fin 2), η < (S.card : ℤ) ∧ ∀ j ∈ S, P j := by
  refine ⟨{i}, by simpa only [Finset.card_singleton, Int.natCast_one] using hη, ?_⟩
  intro j hj
  have hji := Finset.mem_singleton.mp hj
  subst j
  exact hi

private theorem select_both (η : ℤ) (P : Fin 2 → Prop)
    (hη : η < 2) (h0 : P 0) (h1 : P 1) :
    ∃ S : Finset (Fin 2), η < (S.card : ℤ) ∧ ∀ j ∈ S, P j := by
  refine ⟨Finset.univ, by simpa using hη, ?_⟩
  intro j _hj
  fin_cases j
  · exact h0
  · exact h1

private theorem deficit_00 {m : Parameter} (c : Cell m) (he : c.e = 0) (hv : c.v = 0) :
    incomingDeficit m c.x c.y =
      if c.r = 0 then 0 else if c.r = 1 then (if c.s = 0 then 1 else 0)
      else if c.r - c.s = 2 then 1 else 0 := by
  simpa [Cell.x, Cell.y, he, hv] using incomingDeficit_00_at_cell m c.r c.s
    c.hr0 c.hrm c.hs0 c.hsm c.hMissing

private theorem deficit_01 {m : Parameter} (c : Cell m) (he : c.e = 0) (hv : c.v = 1) :
    incomingDeficit m c.x c.y =
      if c.r ≤ 1 then (if 1 ≤ c.s then 1 else 0)
      else if c.r - c.s = 1 ∨ c.r - c.s = 3 then 0 else 1 := by
  simpa [Cell.x, Cell.y, he, hv] using incomingDeficit_01_at_cell m c.r c.s
    c.hr0 c.hrm c.hs0 c.hsm c.hMissing

private theorem deficit_10 {m : Parameter} (c : Cell m) (he : c.e = 1) (hv : c.v = 0) :
    incomingDeficit m c.x c.y =
      if c.r = 0 then (if c.s = 0 then 4 else 0)
      else if c.r = 1 then (if 1 ≤ c.s then 1 else 0)
      else if c.r - c.s = 1 ∨ c.r - c.s = 3 then 0 else 1 := by
  simpa [Cell.x, Cell.y, he, hv] using incomingDeficit_10_at_cell m c.r c.s
    c.hr0 c.hrm c.hs0 c.hsm c.hMissing

private theorem deficit_11 {m : Parameter} (c : Cell m) (he : c.e = 1) (hv : c.v = 1) :
    incomingDeficit m c.x c.y =
      if c.r ≤ 1 then 0 else if c.s = m.val - 1 then 1
      else if c.r = m.val + 1 ∧ c.s = m.val - 2 then 0
      else if c.r - c.s = 3 then 1 else 0 := by
  simpa [Cell.x, Cell.y, he, hv] using incomingDeficit_11_at_cell m c.r c.s
    c.hr0 c.hrm c.hs0 c.hsm c.hMissing

/-- Region II selects enough earlier inputs or same-region inputs directed
vertically or to the right. -/
theorem regionII_selected {m : Parameter} (c : Cell m) (hc : regionII c) :
    ∃ S : Finset (Fin 2), incomingDeficit m c.x c.y < (S.card : ℤ) ∧
      ∀ i ∈ S, regionI (incomingCell c i) ∨
        (regionII (incomingCell c i) ∧ (c.e ≠ c.v ∨ i = 1)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have heCases : c.e = 0 ∨ c.e = 1 := by have := c.e.isLt; omega
  have hvCases : c.v = 0 ∨ c.v = 1 := by have := c.v.isLt; omega
  rcases heCases with he | he <;> rcases hvCases with hv | hv
  · have hBounds : 1 ≤ c.r ∧ (c.r - c.s = 1 ∨ 3 ≤ c.r - c.s) := by
      simpa [regionII, he, hv] using hc
    by_cases hLow : c.r = 1 ∧ c.s = 0
    · apply select_both
      · rw [deficit_00 c he hv]
        split_ifs <;> omega
      · obtain ⟨lr, ls, le, lv⟩ := incomingCell_00_left_of_zero c he hv (by omega) (by omega)
        left
        norm_num [regionI, lr, ls, le, lv]
        omega
      · obtain ⟨rr, rs, re, rv⟩ := incomingCell_00_right c he hv
        left
        norm_num [regionI, rr, rs, re, rv]
        omega
    · apply select_single _ _ 1
      · rw [deficit_00 c he hv]
        split_ifs <;> omega
      · obtain ⟨rr, rs, re, rv⟩ := incomingCell_00_right c he hv
        norm_num [regionI, regionII, rr, rs, re, rv]
        omega
  · have hBounds :
        (c.s = m.val - 1 ∧ 1 ≤ c.r ∧ c.r ≤ m.val) ∨
          (3 ≤ c.r - c.s ∧ ¬(c.r = m.val + 1 ∧ c.s = m.val - 2)) := by
      simpa [regionII, he, hv] using hc
    have hDown : regionI (incomingCell c 0) ∨
        (regionII (incomingCell c 0) ∧ (c.e ≠ c.v ∨ (0 : Fin 2) = 1)) := by
      by_cases hTop : c.r = m.val + 1
      · obtain ⟨dr, ds, de, dv⟩ := incomingCell_01_down_top c he hv hTop
        left
        norm_num [regionI, dr, ds, de, dv]
        omega
      · by_cases hEnd : c.r = m.val ∧ c.s = m.val - 1
        · obtain ⟨dr, ds, de, dv⟩ := incomingCell_01_down_penultimate c he hv hEnd.1 hEnd.2
          norm_num [regionI, regionII, dr, ds, de, dv, he, hv]
        · obtain ⟨dr, ds, de, dv⟩ := incomingCell_01_down_inner c he hv (by omega) hEnd
          norm_num [regionI, regionII, dr, ds, de, dv, he, hv]
          omega
    by_cases hThree : c.r - c.s = 3
    · apply select_single _ _ 0
      · rw [deficit_01 c he hv]
        split_ifs <;> omega
      · exact hDown
    · apply select_both
      · rw [deficit_01 c he hv]
        split_ifs <;> omega
      · exact hDown
      · obtain ⟨ur, us, ue, uv⟩ := incomingCell_01_up c he hv
        norm_num [regionI, regionII, ur, us, ue, uv]
        omega
  · have hBounds : 3 ≤ c.r - c.s := by
      simpa [regionII, he, hv] using hc
    have hDown : regionI (incomingCell c 0) ∨
        (regionII (incomingCell c 0) ∧ (c.e ≠ c.v ∨ (0 : Fin 2) = 1)) := by
      obtain ⟨dr, ds, de, dv⟩ := incomingCell_10_down c he hv
      norm_num [regionI, regionII, dr, ds, de, dv, he, hv]
      omega
    by_cases hThree : c.r - c.s = 3
    · apply select_single _ _ 0
      · rw [deficit_10 c he hv]
        split_ifs <;> omega
      · exact hDown
    · apply select_both
      · rw [deficit_10 c he hv]
        split_ifs <;> omega
      · exact hDown
      · obtain ⟨ur, us, ue, uv⟩ := incomingCell_10_up_of_pos c he hv (by omega)
        norm_num [regionI, regionII, ur, us, ue, uv]
        omega
  · have hBounds : (c.r = 0 ∧ c.s = 0) ∨
        (2 ≤ c.r ∧ (c.r - c.s = 2 ∨ 4 ≤ c.r - c.s)) ∨
        (c.s = m.val - 1 ∧ 2 ≤ c.r ∧ c.r ≤ m.val) := by
      simpa [regionII, he, hv] using hc
    by_cases hLast : c.s = m.val - 1
    · apply select_both
      · rw [deficit_11 c he hv]
        split_ifs <;> omega
      · obtain ⟨lr, ls, le, lv⟩ := incomingCell_11_left c he hv
        left
        norm_num [regionI, lr, ls, le, lv]
        omega
      · obtain ⟨rr, rs, re, rv⟩ := incomingCell_11_right_last c he hv hLast
        norm_num [regionI, regionII, rr, rs, re, rv]
        omega
    · apply select_single _ _ 1
      · rw [deficit_11 c he hv]
        split_ifs <;> omega
      · obtain ⟨rr, rs, re, rv⟩ := incomingCell_11_right_inner c he hv (by omega) (by omega)
        norm_num [regionI, regionII, rr, rs, re, rv]
        omega

/-- Both connecting classes select sufficiently many earlier or leftward inputs. -/
theorem regionIII_selected {m : Parameter} (c : Cell m) (hc : regionIII c) :
    ∃ S : Finset (Fin 2), incomingDeficit m c.x c.y < (S.card : ℤ) ∧
      ∀ i ∈ S, regionI (incomingCell c i) ∨ regionII (incomingCell c i) ∨
        (regionIII (incomingCell c i) ∧ (c.e ≠ c.v ∨ i = 0)) := by
  have hm := m.property
  rcases hc with ⟨he, hv, hr, hs⟩ | ⟨he, hv, hr, hs⟩
  · apply select_both
    · rw [deficit_01 c he hv]
      split_ifs <;> omega
    · obtain ⟨dr, ds, de, dv⟩ := incomingCell_01_down_inner c he hv (by omega) (by omega)
      right; right
      constructor
      · simp only [regionIII, dr, ds, de, dv]
        norm_num
        omega
      · left
        rw [he, hv]
        decide
    · obtain ⟨ur, us, ue, uv⟩ := incomingCell_01_up c he hv
      right; left
      simp only [regionII, ur, us, ue, uv]
      norm_num
      omega
  · apply select_single _ _ 0
    · rw [deficit_11 c he hv]
      split_ifs <;> omega
    · obtain ⟨lr, ls, le, lv⟩ := incomingCell_11_left c he hv
      right; left
      simp only [regionII, lr, ls, le, lv]
      norm_num
      omega

/-- Each black-diagonal site selects both incoming indices; same-stage inputs
are vertical or point right. -/
theorem regionIV_selected {m : Parameter} (c : Cell m) (hc : regionIV c) :
    ∃ S : Finset (Fin 2), incomingDeficit m c.x c.y < (S.card : ℤ) ∧
      ∀ i ∈ S, regionI (incomingCell c i) ∨ regionII (incomingCell c i) ∨
        regionIII (incomingCell c i) ∨
        (regionIV (incomingCell c i) ∧ (c.e ≠ c.v ∨ i = 1)) := by
  have hm := m.property
  have heCases : c.e = 0 ∨ c.e = 1 := by have := c.e.isLt; omega
  have hvCases : c.v = 0 ∨ c.v = 1 := by have := c.v.isLt; omega
  rcases heCases with he | he <;> rcases hvCases with hv | hv
  · have hBounds : 2 ≤ c.r ∧ c.r ≤ m.val ∧ c.s = c.r - 2 := by
      simpa [regionIV, hv] using hc
    apply select_both
    · rw [deficit_00 c he hv]
      split_ifs <;> omega
    · right; left
      by_cases hs : c.s = 0
      · obtain ⟨lr, ls, le, lv⟩ := incomingCell_00_left_of_zero c he hv hs (by omega)
        norm_num [regionII, lr, ls, le, lv]
        omega
      · obtain ⟨lr, ls, le, lv⟩ := incomingCell_00_left_of_pos c he hv (by omega)
        norm_num [regionII, lr, ls, le, lv]
        omega
    · obtain ⟨rr, rs, re, rv⟩ := incomingCell_00_right c he hv
      right; right
      norm_num [regionIII, regionIV, rr, rs, re, rv]
      omega
  · have hBounds : 2 ≤ c.r ∧ c.r ≤ m.val - 1 ∧ c.s = c.r - 2 := by
      simpa [regionIV, he, hv] using hc
    apply select_both
    · rw [deficit_01 c he hv]
      split_ifs <;> omega
    · obtain ⟨dr, ds, de, dv⟩ := incomingCell_01_down_inner c he hv (by omega) (by omega)
      right; right; right
      constructor
      · norm_num [regionIV, dr, ds, de, dv]
        omega
      · left
        rw [he, hv]
        decide
    · obtain ⟨ur, us, ue, uv⟩ := incomingCell_01_up c he hv
      right; left
      norm_num [regionII, ur, us, ue, uv]
      omega
  · have hBounds : 2 ≤ c.r ∧ c.r ≤ m.val ∧ c.s = c.r - 2 := by
      simpa [regionIV, hv] using hc
    apply select_both
    · rw [deficit_10 c he hv]
      split_ifs <;> omega
    · obtain ⟨dr, ds, de, dv⟩ := incomingCell_10_down c he hv
      right; right; right
      constructor
      · norm_num [regionIV, dr, ds, de, dv]
        omega
      · left
        rw [he, hv]
        decide
    · obtain ⟨ur, us, ue, uv⟩ := incomingCell_10_up_of_pos c he hv (by omega)
      right; left
      norm_num [regionII, ur, us, ue, uv]
      omega
  · have hBounds : 3 ≤ c.r ∧ c.r ≤ m.val ∧ c.s = c.r - 3 := by
      simpa [regionIV, he, hv] using hc
    apply select_both
    · rw [deficit_11 c he hv]
      split_ifs <;> omega
    · obtain ⟨lr, ls, le, lv⟩ := incomingCell_11_left c he hv
      right; left
      norm_num [regionII, lr, ls, le, lv]
      omega
    · obtain ⟨rr, rs, re, rv⟩ := incomingCell_11_right_inner c he hv (by omega) (by omega)
      right; right; right
      constructor
      · norm_num [regionIV, rr, rs, re, rv]
        omega
      · right
        rfl

end FLattice.Auxiliary.PlusEvenProfile
