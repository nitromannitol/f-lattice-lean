import FLattice.Auxiliary.PlusEvenRegionI
import FLattice.Auxiliary.PlusEvenLaterRegions

/-!
# Total stages for the even-plus cell partition

The four geometric regions have stages zero through three; the prescribed
class is exactly stage four. The characterization theorems exclude any
unclassified fallback. All stages concern valid literal representatives.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- The four source regions in order, with the prescribed class at stage four. -/
noncomputable def cellStage {m : Parameter} (c : Cell m) : ℕ := by
  classical
  exact if regionI c then 0 else if regionII c then 1 else
    if regionIII c then 2 else if regionIV c then 3 else 4

private theorem stage_of_I {m : Parameter} (c : Cell m) (hc : regionI c) :
    cellStage c = 0 := by
  simp only [cellStage, if_pos hc]

private theorem stage_of_II {m : Parameter} (c : Cell m) (hc : regionII c) :
    cellStage c = 1 := by
  have hI := ((regionII_iff_complement c).mp hc).2.1
  simp only [cellStage, if_neg hI, if_pos hc]

private theorem stage_of_III {m : Parameter} (c : Cell m) (hc : regionIII c) :
    cellStage c = 2 := by
  have hI : ¬regionI c := fun h => (cell_region_disjoint c).2.1 h |>.1 hc
  have hII : ¬regionII c := fun h => ((regionII_iff_complement c).mp h).2.2.1 hc
  simp only [cellStage, if_neg hI, if_neg hII, if_pos hc]

private theorem stage_of_IV {m : Parameter} (c : Cell m) (hc : regionIV c) :
    cellStage c = 3 := by
  have hI : ¬regionI c := fun h => (cell_region_disjoint c).2.1 h |>.2 hc
  have hII : ¬regionII c := fun h => ((regionII_iff_complement c).mp h).2.2.2 hc
  have hIII : ¬regionIII c := fun h => (cell_region_disjoint c).2.2 h hc
  simp only [cellStage, if_neg hI, if_neg hII, if_neg hIII, if_pos hc]

private theorem stage_of_prescribed {m : Parameter} (c : Cell m)
    (hc : cellPrescribed c) : cellStage c = 4 := by
  obtain ⟨hI, hIII, hIV⟩ := (cell_region_disjoint c).1 hc
  have hII : ¬regionII c := fun h => ((regionII_iff_complement c).mp h).1 hc
  simp only [cellStage, if_neg hI, if_neg hII, if_neg hIII, if_neg hIV]

private theorem stage_cases {m : Parameter} (c : Cell m) :
    (cellStage c = 0 ∧ regionI c) ∨ (cellStage c = 1 ∧ regionII c) ∨
      (cellStage c = 2 ∧ regionIII c) ∨ (cellStage c = 3 ∧ regionIV c) ∨
      (cellStage c = 4 ∧ cellPrescribed c) := by
  rcases cell_region_cover c with hP | hI | hII | hIII | hIV
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨stage_of_prescribed c hP, hP⟩)))
  · exact Or.inl ⟨stage_of_I c hI, hI⟩
  · exact Or.inr (Or.inl ⟨stage_of_II c hII, hII⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨stage_of_III c hIII, hIII⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨stage_of_IV c hIV, hIV⟩)))

/-- Stage zero is exactly Region I. -/
theorem cellStage_eq_zero_iff {m : Parameter} (c : Cell m) :
    cellStage c = 0 ↔ regionI c := by
  constructor
  · intro h
    rcases stage_cases c with hI | hII | hIII | hIV | hP
    · exact hI.2
    all_goals omega
  · exact stage_of_I c

/-- Stage one is exactly Region II. -/
theorem cellStage_eq_one_iff {m : Parameter} (c : Cell m) :
    cellStage c = 1 ↔ regionII c := by
  constructor
  · intro h
    rcases stage_cases c with hI | hII | hIII | hIV | hP
    · omega
    · exact hII.2
    all_goals omega
  · exact stage_of_II c

/-- Stage two is exactly Region III. -/
theorem cellStage_eq_two_iff {m : Parameter} (c : Cell m) :
    cellStage c = 2 ↔ regionIII c := by
  constructor
  · intro h
    rcases stage_cases c with hI | hII | hIII | hIV | hP
    · omega
    · omega
    · exact hIII.2
    all_goals omega
  · exact stage_of_III c

/-- Stage three is exactly Region IV. -/
theorem cellStage_eq_three_iff {m : Parameter} (c : Cell m) :
    cellStage c = 3 ↔ regionIV c := by
  constructor
  · intro h
    rcases stage_cases c with hI | hII | hIII | hIV | hP
    · omega
    · omega
    · omega
    · exact hIV.2
    · omega
  · exact stage_of_IV c

/-- The last stage consists exactly of the prescribed class, with no fallback cases. -/
theorem cellStage_eq_four_iff {m : Parameter} (c : Cell m) :
    cellStage c = 4 ↔ cellPrescribed c := by
  constructor
  · intro h
    rcases stage_cases c with hI | hII | hIII | hIV | hP
    · omega
    · omega
    · omega
    · omega
    · exact hP.2
  · exact stage_of_prescribed c

/-- Every valid representative is assigned one of the five stages. -/
theorem cellStage_le_four {m : Parameter} (c : Cell m) : cellStage c ≤ 4 := by
  rcases stage_cases c with hI | hII | hIII | hIV | hP <;> omega

/-- The four comparison stages are precisely the nonprescribed representatives. -/
theorem cellStage_lt_four_iff {m : Parameter} (c : Cell m) :
    cellStage c < 4 ↔ ¬cellPrescribed c := by
  have hbound := cellStage_le_four c
  rw [← cellStage_eq_four_iff c]
  omega

private theorem with_nonprescribed {m : Parameter} (c : Cell m) (i : Fin 2)
    (hc : cellStage c < 4)
    (horder : cellStage (incomingCell c i) < cellStage c ∨
      cellStage (incomingCell c i) = cellStage c ∧
        (c.e ≠ c.v ∨ i = (if cellStage c = 0 ∨ cellStage c = 2 then 0 else 1))) :
    ¬cellPrescribed (incomingCell c i) ∧
      (cellStage (incomingCell c i) < cellStage c ∨
        cellStage (incomingCell c i) = cellStage c ∧
          (c.e ≠ c.v ∨ i = (if cellStage c = 0 ∨ cellStage c = 2 then 0 else 1))) := by
  refine ⟨(cellStage_lt_four_iff (incomingCell c i)).mp ?_, horder⟩
  rcases horder with hlt | ⟨heq, _⟩ <;> omega

/-- Every nonprescribed cell has enough selected incoming indices in earlier
stages or in its own stage with the source's physical direction. The selected
indices are edges and are not assumed to decode to distinct cells. -/
theorem cell_selected {m : Parameter} (c : Cell m) (hc : ¬cellPrescribed c) :
    ∃ S : Finset (Fin 2), incomingDeficit m c.x c.y < (S.card : ℤ) ∧
      ∀ i ∈ S, ¬cellPrescribed (incomingCell c i) ∧
        (cellStage (incomingCell c i) < cellStage c ∨
          cellStage (incomingCell c i) = cellStage c ∧
            (c.e ≠ c.v ∨ i = (if cellStage c = 0 ∨ cellStage c = 2 then 0 else 1))) := by
  have hbound := (cellStage_lt_four_iff c).mpr hc
  rcases cell_region_cover c with hP | hI | hII | hIII | hIV
  · exact (hc hP).elim
  · obtain ⟨S, hcard, hsel⟩ := regionI_selected c hI
    have hs := stage_of_I c hI
    refine ⟨S, hcard, ?_⟩
    intro i hi
    apply with_nonprescribed c i hbound
    obtain ⟨hd, hdir⟩ := hsel i hi
    have hds := stage_of_I (incomingCell c i) hd
    exact Or.inr ⟨by omega, by simpa [hs] using hdir⟩
  · obtain ⟨S, hcard, hsel⟩ := regionII_selected c hII
    have hs := stage_of_II c hII
    refine ⟨S, hcard, ?_⟩
    intro i hi
    apply with_nonprescribed c i hbound
    rcases hsel i hi with hd | ⟨hd, hdir⟩
    · have hds := stage_of_I (incomingCell c i) hd
      exact Or.inl (by omega)
    · have hds := stage_of_II (incomingCell c i) hd
      exact Or.inr ⟨by omega, by simpa [hs] using hdir⟩
  · obtain ⟨S, hcard, hsel⟩ := regionIII_selected c hIII
    have hs := stage_of_III c hIII
    refine ⟨S, hcard, ?_⟩
    intro i hi
    apply with_nonprescribed c i hbound
    rcases hsel i hi with hd | hd | ⟨hd, hdir⟩
    · have hds := stage_of_I (incomingCell c i) hd
      exact Or.inl (by omega)
    · have hds := stage_of_II (incomingCell c i) hd
      exact Or.inl (by omega)
    · have hds := stage_of_III (incomingCell c i) hd
      exact Or.inr ⟨by omega, by simpa [hs] using hdir⟩
  · obtain ⟨S, hcard, hsel⟩ := regionIV_selected c hIV
    have hs := stage_of_IV c hIV
    refine ⟨S, hcard, ?_⟩
    intro i hi
    apply with_nonprescribed c i hbound
    rcases hsel i hi with hd | hd | hd | ⟨hd, hdir⟩
    · have hds := stage_of_I (incomingCell c i) hd
      exact Or.inl (by omega)
    · have hds := stage_of_II (incomingCell c i) hd
      exact Or.inl (by omega)
    · have hds := stage_of_III (incomingCell c i) hd
      exact Or.inl (by omega)
    · have hds := stage_of_IV (incomingCell c i) hd
      exact Or.inr ⟨by omega, by simpa [hs] using hdir⟩

end FLattice.Auxiliary.PlusEvenProfile
