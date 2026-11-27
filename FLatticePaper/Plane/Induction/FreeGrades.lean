import FLatticePaper.Plane.Induction.RootFree
import FLatticePaper.Plane.Induction.RootWindow
import FLatticePaper.Plane.Induction.NonfreeBridge

/-! # The free sets of a conjugate child, in grades

For a child frame `F` with `num = D − N` and `den = D + N` (both odd) and `periodDenominator = 2T`, the closed polygon, the H and V
free sets, and their spectra are grade conditions (`RootFree.polyG`, `hSpecG`, `vSpecG`). A shift of a site by a span element `combine i j`
changes its grades by `t ↦ t − 2Tj`, `s ↦ s + 2Ti`. `nonfree_to_grades` turns `¬ Nonfree F z` into the free-closure hypothesis of
`RootFree.free_closure_B`. -/

namespace FLatticePaper.FreeGrades

open FLatticePaper FLatticePaper.Induction FLatticePaper.RootFree

theorem tGrade_add (F : ChildFrame) (p q : Site) : F.tGrade (p + q) = F.tGrade p + F.tGrade q := by
  unfold ChildFrame.tGrade; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem sGrade_add (F : ChildFrame) (p q : Site) : F.sGrade (p + q) = F.sGrade p + F.sGrade q := by
  unfold ChildFrame.sGrade; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem tGrade_down (F : ChildFrame) (p : Site) : F.tGrade (p.1, p.2 - 1) = F.tGrade p + F.child.den := by
  unfold ChildFrame.tGrade; ring

theorem sGrade_down (F : ChildFrame) (p : Site) :
    F.sGrade (p.1, p.2 - 1) = F.sGrade p - (F.child.den - F.child.num) := by
  unfold ChildFrame.sGrade; ring

theorem tGrade_left (F : ChildFrame) (p : Site) : F.tGrade (p.1 - 1, p.2) = F.tGrade p - F.child.num := by
  unfold ChildFrame.tGrade; ring

theorem sGrade_left (F : ChildFrame) (p : Site) :
    F.sGrade (p.1 - 1, p.2) = F.sGrade p - (F.child.den + F.child.num) := by
  unfold ChildFrame.sGrade; ring

/-- The parity of a site is the parity of its `t`-grade, for odd `num` and `den`. -/
theorem evenSite_iff_tGrade (F : ChildFrame) (hn : F.child.num % 2 = 1) (hd : F.child.den % 2 = 1) (p : Site) :
    EvenSite p ↔ F.tGrade p % 2 = 0 := by
  have h := FLatticePaper.RootWindow.par_t F.child.num F.child.den hn hd p
  have e : F.tGrade p = FLatticePaper.W1.w1t F.child.num F.child.den p := rfl
  unfold EvenSite
  rw [e, h]

/-- The closed polygon of the conjugate child, in grades. -/
theorem mem_closedPolygon_polyG (F : ChildFrame) (N D T : ℤ) (hnum : F.child.num = D - N)
    (hden : F.child.den = D + N) (hper : F.child.periodDenominator = 2 * T)
    (hn : F.child.num % 2 = 1) (hd : F.child.den % 2 = 1) (p : Site) :
    p ∈ F.closedPolygon ↔ polyG N D T (F.tGrade p) (F.sGrade p) := by
  rw [FLatticePaper.Induction.ChildFrame.mem_closedPolygon_iff F p, evenSite_iff_tGrade F hn hd p]
  unfold polyG
  unfold ChildFrame.tGrade ChildFrame.sGrade
  generalize ht : F.child.num * p.1 - F.child.den * p.2 = t
  generalize hs : (F.child.den + F.child.num) * p.1 + (F.child.den - F.child.num) * p.2 = s
  rw [hper, hnum, hden]
  constructor
  · rintro (⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩)
    · exact ⟨fun _ => ⟨by omega, by omega, by omega, by omega⟩, fun h => absurd h (by omega)⟩
    · exact ⟨fun h => absurd h (by omega), fun _ => ⟨by omega, by omega, by omega, by omega⟩⟩
  · rintro ⟨h1, h2⟩
    by_cases ht2 : t % 2 = 0
    · obtain ⟨a1, a2, a3, a4⟩ := h1 ht2
      exact Or.inl ⟨ht2, by omega, by omega, by omega, by omega⟩
    · have ht3 : t % 2 = 1 := by omega
      obtain ⟨a1, a2, a3, a4⟩ := h2 ht3
      exact Or.inr ⟨ht2, by omega, by omega, by omega, by omega⟩

/-- The grades of a span shift `z + combine i j`: `t ↦ t − 2Tj`, `s ↦ s + 2Ti`. -/
theorem shift_grades (F : ChildFrame) (N D T : ℤ) (hnum : F.child.num = D - N) (hden : F.child.den = D + N)
    (hT : T = D * D + 2 * D * N - N * N) (z : Site) (i j : ℤ) :
    F.tGrade (z + F.child.modifiedDeck.combine i j) = F.tGrade z - 2 * T * j ∧
      F.sGrade (z + F.child.modifiedDeck.combine i j) = F.sGrade z + 2 * T * i := by
  have hk := F.child_modifiedDeck_kernel
  have ht := F.child_modifiedDeck_transverse
  have h1 : F.tGrade (F.child.modifiedDeck.combine i j) = -(2 * T * j) := by
    unfold ChildFrame.tGrade FLatticePaper.Farey.PeriodDeck.combine
    rw [hk, ht]
    simp only
    rw [hnum, hden, hT]
    ring
  have h2 : F.sGrade (F.child.modifiedDeck.combine i j) = 2 * T * i := by
    unfold ChildFrame.sGrade FLatticePaper.Farey.PeriodDeck.combine
    rw [hk, ht]
    simp only
    rw [hnum, hden, hT]
    ring
  constructor
  · have := tGrade_add F z (F.child.modifiedDeck.combine i j)
    linarith
  · have := sGrade_add F z (F.child.modifiedDeck.combine i j)
    linarith

/-- **The free closure in grades.** If the conjugate child (with `num = D − N`, `den = D + N`) does not make `z` nonfree, then some
span shift of `z` is a free H or V point, in the grade form of `RootFree.FreeGradeH` / `FreeGradeV`. -/
theorem nonfree_to_grades (F : ChildFrame) (N D T : ℤ) (hnum : F.child.num = D - N)
    (hden : F.child.den = D + N) (hper : F.child.periodDenominator = 2 * T)
    (hT : T = D * D + 2 * D * N - N * N)
    (hn : F.child.num % 2 = 1) (hd : F.child.den % 2 = 1) (z : Site)
    (hz : ¬ FLatticePaper.Induction.Nonfree F z) :
    ∃ i j : ℤ,
      FreeGradeH N D T (F.tGrade z - 2 * T * j) (F.sGrade z + 2 * T * i) ∨
        FreeGradeV N D T (F.tGrade z - 2 * T * j) (F.sGrade z + 2 * T * i) := by
  unfold FLatticePaper.Induction.Nonfree at hz
  push Not at hz
  obtain ⟨w, hw, hwf⟩ := hz
  obtain ⟨i, j, rfl⟩ := hw
  obtain ⟨hgt, hgs⟩ := shift_grades F N D T hnum hden hT z i j
  refine ⟨i, j, ?_⟩
  rw [← hgt, ← hgs]
  rcases hwf with hH | hV
  · left
    have hpoly := (mem_closedPolygon_polyG F N D T hnum hden hper hn hd _).1 hH.1
    refine ⟨hpoly, ?_, ?_⟩
    · intro h
      apply hH.2.1
      rw [mem_closedPolygon_polyG F N D T hnum hden hper hn hd]
      rw [tGrade_down, sGrade_down, hden, hnum]
      have e : D + N - (D - N) = 2 * N := by ring
      rw [e]
      exact h
    · have hsp := hH.2.2
      unfold ChildFrame.hSpectrum at hsp
      rw [hnum, hden] at hsp
      unfold hSpecG
      rcases hsp with h | h
      · exact Or.inl ⟨h.1, by omega, by omega⟩
      · exact Or.inr ⟨h.1, by omega, by omega⟩
  · right
    have hpoly := (mem_closedPolygon_polyG F N D T hnum hden hper hn hd _).1 hV.1
    refine ⟨hpoly, ?_, ?_⟩
    · intro h
      apply hV.2.1
      rw [mem_closedPolygon_polyG F N D T hnum hden hper hn hd]
      rw [tGrade_left, sGrade_left, hden, hnum]
      have e : D + N + (D - N) = 2 * D := by ring
      rw [e]
      exact h
    · have hsp := hV.2.2
      unfold ChildFrame.vSpectrum at hsp
      rw [hnum, hden] at hsp
      unfold vSpecG
      refine ⟨hsp.1, ?_⟩
      rcases hsp.2 with h | h
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩

end FLatticePaper.FreeGrades
