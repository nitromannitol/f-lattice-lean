import FLattice.Auxiliary.PlusEvenRegions
import FLattice.Auxiliary.PlusEvenPredecessors
import FLattice.Auxiliary.PlusEvenDeficitTable

/-!
# Selected physical incoming edges of Region I

The selected indices count incoming edges, even if two decoded cells coincide.
Every selected predecessor stays in Region I. Horizontal selections use the
negative (left) edge; vertical selections may use either edge. No rank or
periodicity assumption on an unknown function is used.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

private theorem fin_two_cases (e : Fin 2) : e = 0 ∨ e = 1 := by
  fin_cases e <;> simp

private theorem select_one {m : Parameter} (c : Cell m) (i : Fin 2)
    (hdef : incomingDeficit m c.x c.y < 1)
    (hmem : regionI (incomingCell c i)) (hdir : c.e ≠ c.v ∨ i = 0) :
    ∃ S : Finset (Fin 2), incomingDeficit m c.x c.y < (S.card : ℤ) ∧
      ∀ j ∈ S, regionI (incomingCell c j) ∧ (c.e ≠ c.v ∨ j = 0) := by
  refine ⟨{i}, ?_, ?_⟩
  · simpa using hdef
  · intro j hj
    have hji : j = i := by simpa using hj
    subst j
    exact ⟨hmem, hdir⟩

private theorem select_both {m : Parameter} (c : Cell m)
    (hdef : incomingDeficit m c.x c.y < 2)
    (hzero : regionI (incomingCell c 0)) (hone : regionI (incomingCell c 1))
    (hdir : c.e ≠ c.v) :
    ∃ S : Finset (Fin 2), incomingDeficit m c.x c.y < (S.card : ℤ) ∧
      ∀ j ∈ S, regionI (incomingCell c j) ∧ (c.e ≠ c.v ∨ j = 0) := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · simpa using hdef
  · intro j _
    fin_cases j
    · exact ⟨hzero, Or.inl hdir⟩
    · exact ⟨hone, Or.inl hdir⟩

private theorem select_00 {m : Parameter} (c : Cell m)
    (hc : regionI c) (he : c.e = 0) (hv : c.v = 0) :
    ∃ S : Finset (Fin 2), incomingDeficit m c.x c.y < (S.card : ℤ) ∧
      ∀ i ∈ S, regionI (incomingCell c i) ∧ (c.e ≠ c.v ∨ i = 0) := by
  have hm := m.property
  have hr0 := c.hr0
  have hs0 := c.hs0
  have hsm := c.hsm
  have hI : c.r = 0 ∨ (1 ≤ c.r ∧ c.r ≤ c.s) := by
    simpa [regionI, he, hv] using hc
  have htable := incomingDeficit_00_at_cell m c.r c.s c.hr0 c.hrm c.hs0 c.hsm c.hMissing
  have hdef : incomingDeficit m c.x c.y < 1 := by
    simp only [Cell.x, Cell.y, he, hv, Fin.val_zero, Int.natCast_zero, add_zero]
    rw [htable]
    split_ifs <;> omega
  apply select_one c 0 hdef ?_ (Or.inr rfl)
  by_cases hs : c.s = 0
  · have hr : c.r = 0 := by omega
    obtain ⟨hr', hs', he', hv'⟩ := incomingCell_00_left_origin c he hv hr hs
    norm_num [regionI, hr', hs', he', hv']
  · obtain ⟨hr', hs', he', hv'⟩ := incomingCell_00_left_of_pos c he hv (by omega)
    norm_num [regionI, hr', hs', he', hv']
    omega

private theorem select_11 {m : Parameter} (c : Cell m)
    (hc : regionI c) (he : c.e = 1) (hv : c.v = 1) :
    ∃ S : Finset (Fin 2), incomingDeficit m c.x c.y < (S.card : ℤ) ∧
      ∀ i ∈ S, regionI (incomingCell c i) ∧ (c.e ≠ c.v ∨ i = 0) := by
  have hm := m.property
  have hr0 := c.hr0
  have hs0 := c.hs0
  have hsm := c.hsm
  have hI : (c.r = 0 ∧ 1 ≤ c.s) ∨
      (1 ≤ c.r ∧ c.r - 1 ≤ c.s ∧ c.s ≤ m.val - 2) ∨
      (c.r = 1 ∧ c.s = m.val - 1) := by
    simpa [regionI, he, hv] using hc
  have htable := incomingDeficit_11_at_cell m c.r c.s c.hr0 c.hrm c.hs0 c.hsm c.hMissing
  have hdef : incomingDeficit m c.x c.y < 1 := by
    simp only [Cell.x, Cell.y, he, hv, Fin.val_one, Int.natCast_one]
    rw [htable]
    split_ifs <;> omega
  apply select_one c 0 hdef ?_ (Or.inr rfl)
  obtain ⟨hr', hs', he', hv'⟩ := incomingCell_11_left c he hv
  norm_num [regionI, hr', hs', he', hv']
  omega

private theorem select_10 {m : Parameter} (c : Cell m)
    (hc : regionI c) (he : c.e = 1) (hv : c.v = 0) :
    ∃ S : Finset (Fin 2), incomingDeficit m c.x c.y < (S.card : ℤ) ∧
      ∀ i ∈ S, regionI (incomingCell c i) ∧ (c.e ≠ c.v ∨ i = 0) := by
  have hm := m.property
  have hr0 := c.hr0
  have hs0 := c.hs0
  have hsm := c.hsm
  have hI : (c.r = 0 ∧ 1 ≤ c.s) ∨ (1 ≤ c.r ∧ c.r - 1 ≤ c.s) := by
    simpa [regionI, he, hv] using hc
  have hdir : c.e ≠ c.v := by simp [he, hv]
  have htable := incomingDeficit_10_at_cell m c.r c.s c.hr0 c.hrm c.hs0 c.hsm c.hMissing
  have hdef : incomingDeficit m c.x c.y =
      if c.r = 0 then (if c.s = 0 then 4 else 0)
      else if c.r = 1 then (if 1 ≤ c.s then 1 else 0)
      else if c.r - c.s = 1 ∨ c.r - c.s = 3 then 0 else 1 := by
    simpa [Cell.x, Cell.y, he, hv] using htable
  by_cases hr : c.r = 0
  · apply select_one c 0 (by rw [hdef]; split_ifs <;> omega) ?_ (Or.inl hdir)
    obtain ⟨hr', hs', he', hv'⟩ := incomingCell_10_down c he hv
    norm_num [regionI, hr', hs', he', hv']
    omega
  by_cases ha : c.r - c.s = 1
  · apply select_one c 1 (by rw [hdef]; split_ifs <;> omega) ?_ (Or.inl hdir)
    obtain ⟨hr', hs', he', hv'⟩ := incomingCell_10_up_of_pos c he hv (by omega)
    norm_num [regionI, hr', hs', he', hv']
    omega
  apply select_both c (by rw [hdef]; split_ifs <;> omega) ?_ ?_ hdir
  · obtain ⟨hr', hs', he', hv'⟩ := incomingCell_10_down c he hv
    norm_num [regionI, hr', hs', he', hv']
    omega
  · obtain ⟨hr', hs', he', hv'⟩ := incomingCell_10_up_of_pos c he hv (by omega)
    norm_num [regionI, hr', hs', he', hv']
    omega

private theorem select_01 {m : Parameter} (c : Cell m)
    (hc : regionI c) (he : c.e = 0) (hv : c.v = 1) :
    ∃ S : Finset (Fin 2), incomingDeficit m c.x c.y < (S.card : ℤ) ∧
      ∀ i ∈ S, regionI (incomingCell c i) ∧ (c.e ≠ c.v ∨ i = 0) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have hI : c.r = 0 ∨ (1 ≤ c.r ∧ c.r - 1 ≤ c.s ∧ c.s ≤ m.val - 2) ∨
      (c.r = m.val + 1 ∧ c.s = m.val - 2) := by
    simpa [regionI, he, hv] using hc
  have hdir : c.e ≠ c.v := by simp [he, hv]
  have htable := incomingDeficit_01_at_cell m c.r c.s c.hr0 c.hrm c.hs0 c.hsm c.hMissing
  have hdef : incomingDeficit m c.x c.y =
      if c.r ≤ 1 then (if 1 ≤ c.s then 1 else 0)
      else if c.r - c.s = 1 ∨ c.r - c.s = 3 then 0 else 1 := by
    simpa [Cell.x, Cell.y, he, hv] using htable
  by_cases htop : c.r = m.val + 1
  · apply select_one c 0 (by rw [hdef]; split_ifs <;> omega) ?_ (Or.inl hdir)
    obtain ⟨hr', hs', he', hv'⟩ := incomingCell_01_down_top c he hv htop
    norm_num [regionI, hr', hs', he', hv']
    omega
  by_cases horigin : c.r = 0 ∧ c.s = 0
  · apply select_one c 0 (by rw [hdef]; split_ifs <;> omega) ?_ (Or.inl hdir)
    obtain ⟨hr', hs', he', hv'⟩ := incomingCell_01_down_inner c he hv (by omega) (by omega)
    norm_num [regionI, hr', hs', he', hv']
    omega
  by_cases ha : c.r - c.s = 1
  · apply select_one c 1 (by rw [hdef]; split_ifs <;> omega) ?_ (Or.inl hdir)
    obtain ⟨hr', hs', he', hv'⟩ := incomingCell_01_up c he hv
    norm_num [regionI, hr', hs', he', hv']
    omega
  apply select_both c (by rw [hdef]; split_ifs <;> omega) ?_ ?_ hdir
  · obtain ⟨hr', hs', he', hv'⟩ := incomingCell_01_down_inner c he hv (by omega) (by omega)
    norm_num [regionI, hr', hs', he', hv']
    omega
  · obtain ⟨hr', hs', he', hv'⟩ := incomingCell_01_up c he hv
    norm_num [regionI, hr', hs', he', hv']
    omega

/-- Region I has more internally selected incoming indices than its deficit.
Horizontal selections are leftward; both vertical directions are permitted. -/
theorem regionI_selected {m : Parameter} (c : Cell m) (hc : regionI c) :
    ∃ S : Finset (Fin 2), incomingDeficit m c.x c.y < (S.card : ℤ) ∧
      ∀ i ∈ S, regionI (incomingCell c i) ∧ (c.e ≠ c.v ∨ i = 0) := by
  rcases fin_two_cases c.e with he | he <;> rcases fin_two_cases c.v with hv | hv
  · exact select_00 c hc he hv
  · exact select_01 c hc he hv
  · exact select_10 c hc he hv
  · exact select_11 c hc he hv

end FLattice.Auxiliary.PlusEvenProfile
