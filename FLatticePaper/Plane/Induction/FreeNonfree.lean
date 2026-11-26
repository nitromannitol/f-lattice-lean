import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.FreeCutSucc

/-! # Three fixed sites are nonfree

`Nonfree z` says that no deck translate `z + v`, `v ∈ span`, lies in `freeH ∪ freeV`. A free point lies in the closed polygon and has
its `H` or `V` spectrum; a free `V` point has its west neighbour outside the polygon. For the fixed sites `(−1,−2)`, `(2,1)`, `(2,−2)`
the grades of `z + (i U + j V)` are `t(z) − jT` and `s(z) + iT`, and the closed polygon bounds leave at most one `(i, j)`; the
resulting point fails the spectra (or, for `(2,−2)`, its west neighbour lies in the polygon). Standing facts: `n, d` odd,
`d ≥ n + 2`, and `T = d² + 2dn − n² > 4d − 2`. -/

namespace FLatticePaper.FreeNonfree

open FLatticePaper FLatticePaper.Induction

/-- A free point lies in the closed polygon and has its `H` or `V` spectrum. -/
theorem union_bounds {frame : ChildFrame} {x : Site} (hx : x ∈ frame.freeH ∪ frame.freeV) :
    x ∈ frame.closedPolygon ∧ (frame.hSpectrum (frame.tGrade x) ∨ frame.vSpectrum (frame.sGrade x)) := by
  rcases hx with h | h
  · have h' := h
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at h'
    exact ⟨h'.1, Or.inl h'.2.2⟩
  · have h' := h
    simp only [ChildFrame.freeV, Set.mem_setOf_eq] at h'
    exact ⟨h'.1, Or.inr h'.2.2⟩

theorem big_T {frame : ChildFrame} : 4 * frame.child.den - 2 < frame.child.periodDenominator := by
  obtain ⟨hn0, hnd, hd2, -, -⟩ := frame.child_facts
  have hTd : frame.child.periodDenominator
      = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
  rw [hTd]
  nlinarith

/-- `(−1,−2)` is nonfree. -/
theorem nonfree_m12 {frame : ChildFrame} : Nonfree frame (-1, -2) := by
  obtain ⟨hn0, hnd, hd2, -, -⟩ := frame.child_facts
  obtain ⟨-, hdO⟩ := frame.child_odd
  have hTb := big_T (frame := frame)
  have hTpos : 0 < frame.child.periodDenominator := by omega
  have ht0 : frame.tGrade (-1, -2) = 2 * frame.child.den - frame.child.num := by
    unfold ChildFrame.tGrade; ring
  have hs0 : frame.sGrade (-1, -2) = -3 * frame.child.den + frame.child.num := by
    unfold ChildFrame.sGrade; ring
  intro v hv hm
  obtain ⟨i, j, rfl⟩ := hv
  have hc : ¬ EvenSite ((-1 : ℤ), (-2 : ℤ)) := by unfold EvenSite; norm_num
  have hodd : ¬ EvenSite ((-1, -2) + frame.child.modifiedDeck.combine i j) :=
    fun h => hc ((frame.evenSite_add_combine (-1, -2) i j).mp h)
  have hb := union_bounds hm
  have hcl := hb.1
  simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq, if_neg hodd] at hcl
  rw [ChildFrame.tGrade_add_combine, ChildFrame.sGrade_add_combine, ht0, hs0] at hcl
  have hj : j = 1 := by
    rcases (show j ≤ 0 ∨ j = 1 ∨ 2 ≤ j by omega) with h | h | h
    · nlinarith [hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2]
    · exact h
    · nlinarith [hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2]
  have hi : i = 1 := by
    rcases (show i ≤ 0 ∨ i = 1 ∨ 2 ≤ i by omega) with h | h | h
    · nlinarith [hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2]
    · exact h
    · nlinarith [hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2]
  subst hj hi
  rw [ChildFrame.tGrade_add_combine, ChildFrame.sGrade_add_combine, ht0, hs0] at hb
  rcases hb.2 with h | h
  · unfold ChildFrame.hSpectrum at h
    omega
  · unfold ChildFrame.vSpectrum at h
    omega

/-- `(2,1)` is nonfree. -/
theorem nonfree_21 {frame : ChildFrame} : Nonfree frame (2, 1) := by
  obtain ⟨hn0, hnd, hd2, -, -⟩ := frame.child_facts
  obtain ⟨-, hdO⟩ := frame.child_odd
  have hTb := big_T (frame := frame)
  have hTpos : 0 < frame.child.periodDenominator := by omega
  have ht0 : frame.tGrade (2, 1) = 2 * frame.child.num - frame.child.den := by
    unfold ChildFrame.tGrade; ring
  have hs0 : frame.sGrade (2, 1) = 3 * frame.child.den + frame.child.num := by
    unfold ChildFrame.sGrade; ring
  intro v hv hm
  obtain ⟨i, j, rfl⟩ := hv
  have hc : ¬ EvenSite ((2 : ℤ), (1 : ℤ)) := by unfold EvenSite; norm_num
  have hodd : ¬ EvenSite ((2, 1) + frame.child.modifiedDeck.combine i j) :=
    fun h => hc ((frame.evenSite_add_combine (2, 1) i j).mp h)
  have hb := union_bounds hm
  have hcl := hb.1
  simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq, if_neg hodd] at hcl
  rw [ChildFrame.tGrade_add_combine, ChildFrame.sGrade_add_combine, ht0, hs0] at hcl
  have hj : j = 0 := by
    rcases (show j ≤ -1 ∨ j = 0 ∨ 1 ≤ j by omega) with h | h | h
    · nlinarith [hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2]
    · exact h
    · nlinarith [hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2]
  have hi : i = 0 := by
    rcases (show i ≤ -1 ∨ i = 0 ∨ 1 ≤ i by omega) with h | h | h
    · nlinarith [hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2]
    · exact h
    · nlinarith [hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2]
  subst hj hi
  rw [ChildFrame.tGrade_add_combine, ChildFrame.sGrade_add_combine, ht0, hs0] at hb
  rcases hb.2 with h | h
  · unfold ChildFrame.hSpectrum at h
    omega
  · unfold ChildFrame.vSpectrum at h
    omega

/-- `(2,−2)` is nonfree: its only candidate translate is `(2,−2) + V`, whose spectrum fails, and whose west neighbour lies in the
closed polygon, so it is not in `freeV` either. -/
theorem nonfree_2m2 {frame : ChildFrame} : Nonfree frame (2, -2) := by
  obtain ⟨hn0, hnd, hd2, -, -⟩ := frame.child_facts
  obtain ⟨-, hdO⟩ := frame.child_odd
  have hTb := big_T (frame := frame)
  have hTpos : 0 < frame.child.periodDenominator := by omega
  have ht0 : frame.tGrade (2, -2) = 2 * frame.child.num + 2 * frame.child.den := by
    unfold ChildFrame.tGrade; ring
  have hs0 : frame.sGrade (2, -2) = 4 * frame.child.num := by
    unfold ChildFrame.sGrade; ring
  intro v hv hm
  obtain ⟨i, j, rfl⟩ := hv
  have hev : EvenSite ((2 : ℤ), (-2 : ℤ)) := by unfold EvenSite; norm_num
  have hevx : EvenSite ((2, -2) + frame.child.modifiedDeck.combine i j) :=
    (frame.evenSite_add_combine (2, -2) i j).mpr hev
  have hxcl := (union_bounds hm).1
  simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq, if_pos hevx] at hxcl
  rw [ChildFrame.tGrade_add_combine, ChildFrame.sGrade_add_combine, ht0, hs0] at hxcl
  have hj : j = 1 := by
    rcases (show j ≤ 0 ∨ j = 1 ∨ 2 ≤ j by omega) with h | h | h
    · nlinarith [hxcl.1, hxcl.2.1, hxcl.2.2.1, hxcl.2.2.2]
    · exact h
    · nlinarith [hxcl.1, hxcl.2.1, hxcl.2.2.1, hxcl.2.2.2]
  have hi : i = 0 := by
    rcases (show i ≤ -1 ∨ i = 0 ∨ 1 ≤ i by omega) with h | h | h
    · nlinarith [hxcl.1, hxcl.2.1, hxcl.2.2.1, hxcl.2.2.2]
    · exact h
    · nlinarith [hxcl.1, hxcl.2.1, hxcl.2.2.1, hxcl.2.2.2]
  subst hj hi
  rcases hm with hH | hV
  · have h' := hH
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at h'
    rw [ChildFrame.tGrade_add_combine, ht0] at h'
    unfold ChildFrame.hSpectrum at h'
    omega
  · have h' := hV
    simp only [ChildFrame.freeV, Set.mem_setOf_eq] at h'
    apply h'.2.1
    -- the west neighbour of the candidate lies in the closed polygon (odd site)
    have htn : frame.tGrade (((2, -2) + frame.child.modifiedDeck.combine 0 1).1 - 1,
        ((2, -2) + frame.child.modifiedDeck.combine 0 1).2) =
        frame.tGrade ((2, -2) + frame.child.modifiedDeck.combine 0 1) - frame.child.num := by
      unfold ChildFrame.tGrade; ring
    have hsn : frame.sGrade (((2, -2) + frame.child.modifiedDeck.combine 0 1).1 - 1,
        ((2, -2) + frame.child.modifiedDeck.combine 0 1).2) =
        frame.sGrade ((2, -2) + frame.child.modifiedDeck.combine 0 1) - (frame.child.den + frame.child.num) := by
      unfold ChildFrame.sGrade; ring
    have hxev : EvenSite ((2, -2) + frame.child.modifiedDeck.combine 0 1) := hevx
    have hodd_nb : ¬ EvenSite (((2, -2) + frame.child.modifiedDeck.combine 0 1).1 - 1,
        ((2, -2) + frame.child.modifiedDeck.combine 0 1).2) := by
      unfold EvenSite at hxev ⊢
      simp only [Prod.fst_add, Prod.snd_add] at hxev ⊢
      omega
    simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq, if_neg hodd_nb]
    rw [htn, hsn, ChildFrame.tGrade_add_combine, ChildFrame.sGrade_add_combine, ht0, hs0]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end FLatticePaper.FreeNonfree
