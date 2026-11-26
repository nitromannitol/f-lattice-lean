import FLatticePaper.Plane.Induction.FreeCutPred
import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.FreeClosure

/-! # The reflections of the free cuts (easy and hard frames alike)

`σ z = (d+1−z₁, n−1−z₂)` maps the free H cut to itself, and `z ↦ vLast − z` maps the free V cut to itself
(`FreeCutPred.freeV_reflect`). The H symmetry comes from the window description `freeH z ↔ z ∈ closedPolygon ∧ hSpectrum (tGrade z)`
and the symmetry of `hSpectrum` under `t ↦ L − t` and of the polygon's `s`-window under `s ↦ T + 2n − s`. -/

namespace FLatticePaper.RouteReflect

open Farey FLatticePaper FLatticePaper.Induction

/-- The H-cut reflection `σ z = (d + 1 − z₁, n − 1 − z₂)`. -/
def sigmaH (frame : ChildFrame) (z : Site) : Site :=
  (frame.child.den + 1 - z.1, frame.child.num - 1 - z.2)

theorem tGrade_sigmaH (frame : ChildFrame) (z : Site) :
    frame.tGrade (sigmaH frame z) = (frame.child.den + frame.child.num) - frame.tGrade z := by
  unfold ChildFrame.tGrade sigmaH
  ring

theorem sGrade_sigmaH (frame : ChildFrame) (z : Site) :
    frame.sGrade (sigmaH frame z) = frame.child.periodDenominator + 2 * frame.child.num - frame.sGrade z := by
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  unfold ChildFrame.sGrade sigmaH
  rw [hT]
  ring

theorem tGrade_sub_y (frame : ChildFrame) (z : Site) :
    frame.tGrade (z.1, z.2 - 1) = frame.tGrade z + frame.child.den := by
  unfold ChildFrame.tGrade
  ring

/-- The parity of a site is that of its `t`-grade (`n`, `d` odd). -/
theorem tGrade_even_iff (frame : ChildFrame) (z : Site) :
    EvenSite z ↔ frame.tGrade z % 2 = 0 := by
  obtain ⟨hn2, hd2⟩ := frame.child_odd
  obtain ⟨a, ha⟩ : ∃ a, frame.child.num = 2 * a + 1 := ⟨frame.child.num / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den = 2 * b + 1 := ⟨frame.child.den / 2, by omega⟩
  have ht : frame.tGrade z = (z.1 - z.2) + 2 * (a * z.1 - b * z.2) := by
    unfold ChildFrame.tGrade
    rw [ha, hb]
    ring
  unfold EvenSite
  constructor
  · intro he
    rw [ht]
    generalize a * z.1 - b * z.2 = q
    omega
  · intro h
    rw [ht] at h
    generalize a * z.1 - b * z.2 = q at h
    omega

/-- **The window description of the free H cut.** The bottom condition `z − (0,1) ∉ closedPolygon` is automatic on the
`hSpectrum` window: `t(z − (0,1)) = t + d` leaves the polygon's `t`-range in both parities. -/
theorem freeH_iff_window (frame : ChildFrame) (z : Site) :
    z ∈ frame.freeH ↔ z ∈ frame.closedPolygon ∧ frame.hSpectrum (frame.tGrade z) := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨h1, ?_, h3⟩
    intro hb
    have hp := (tGrade_even_iff frame z)
    by_cases he : EvenSite z
    · have ho : ¬ EvenSite (z.1, z.2 - 1) := by
        unfold EvenSite at he ⊢
        simp only at he ⊢
        omega
      rw [FreeVWindow.mem_closedPolygon_odd frame ho, tGrade_sub_y] at hb
      have h3' := h3
      unfold ChildFrame.hSpectrum at h3'
      have ht0 := hp.mp he
      omega
    · have ho : EvenSite (z.1, z.2 - 1) := by
        unfold EvenSite at he ⊢
        simp only at he ⊢
        omega
      rw [FreeVWindow.mem_closedPolygon_even frame ho, tGrade_sub_y] at hb
      have h3' := h3
      unfold ChildFrame.hSpectrum at h3'
      have ht1 : frame.tGrade z % 2 = 1 := by
        have : ¬ (frame.tGrade z % 2 = 0) := fun h => he (hp.mpr h)
        omega
      omega

/-- **The free H cut is symmetric under `σ`.** -/
theorem freeH_sigmaH_iff (frame : ChildFrame) (z : Site) :
    z ∈ frame.freeH ↔ sigmaH frame z ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hn2, hd2'⟩ := frame.child_odd
  have hTpos : 0 ≤ frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  rw [freeH_iff_window, freeH_iff_window, tGrade_sigmaH]
  have hpar : EvenSite (sigmaH frame z) ↔ EvenSite z := by
    unfold EvenSite sigmaH
    simp only
    omega
  have hp := tGrade_even_iff frame z
  by_cases he : EvenSite z
  · have hep : EvenSite (sigmaH frame z) := hpar.mpr he
    rw [FreeVWindow.mem_closedPolygon_even frame he, FreeVWindow.mem_closedPolygon_even frame hep,
      sGrade_sigmaH frame z, tGrade_sigmaH frame z]
    unfold ChildFrame.hSpectrum
    have ht := hp.mp he
    constructor
    · rintro ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, h3⟩
      refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> omega
    · rintro ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, h3⟩
      refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> omega
  · have ho : ¬ EvenSite (sigmaH frame z) := fun h => he (hpar.mp h)
    rw [FreeVWindow.mem_closedPolygon_odd frame he, FreeVWindow.mem_closedPolygon_odd frame ho,
      sGrade_sigmaH frame z, tGrade_sigmaH frame z]
    unfold ChildFrame.hSpectrum
    have ht : ¬ frame.tGrade z % 2 = 0 := fun h => he (hp.mpr h)
    constructor
    · rintro ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, h3⟩
      refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> omega
    · rintro ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, h3⟩
      refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> omega

theorem kernel_eq (frame : ChildFrame) :
    frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) := by
  rw [ChildFrame.child_modifiedDeck_kernel]

theorem transverse_eq (frame : ChildFrame) :
    frame.child.modifiedDeck.transverse = (frame.child.num - frame.child.den, frame.child.num + frame.child.den) := by
  rw [ChildFrame.child_modifiedDeck_transverse]

/-- The free V cut is invariant under `z ↦ vLast − z` (`FreeCutPred.freeV_reflect`, in site form). -/
theorem freeV_vLast_sub (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) :
    frame.vLast - z ∈ frame.freeV := by
  have h := FreeCutPred.freeV_reflect frame hz
  have e : frame.vLast - z = (frame.child.num - frame.child.den + 1 - z.1, frame.child.num + frame.child.den - 1 - z.2) := by
    unfold ChildFrame.vLast
    ext <;> simp
  rw [e]
  exact h

/-- **The free-closure predicate is invariant under `z ↦ vLast − z`** (one direction; the other is the same map). -/
theorem freeClosure_of_vLast (frame : ChildFrame) {c : Site}
    (h : FreeClosure.freeClosure frame (frame.vLast - c)) : FreeClosure.freeClosure frame c := by
  obtain ⟨s, ⟨i, j, rfl⟩, hf⟩ := h
  have hK := kernel_eq frame
  have hV := transverse_eq frame
  rcases hf with hf | hf
  · have hσ := (freeH_sigmaH_iff frame _).mp hf
    refine ⟨frame.child.modifiedDeck.combine (-i + 1) (-j - 1), ⟨-i + 1, -j - 1, rfl⟩, Or.inl ?_⟩
    convert hσ using 1
    unfold sigmaH PeriodDeck.combine ChildFrame.vLast
    rw [hK, hV]
    ext <;> simp <;> ring
  · have hr := freeV_vLast_sub frame hf
    refine ⟨frame.child.modifiedDeck.combine (-i) (-j), ⟨-i, -j, rfl⟩, Or.inr ?_⟩
    convert hr using 1
    unfold PeriodDeck.combine ChildFrame.vLast
    rw [hK, hV]
    ext <;> simp <;> ring

theorem freeClosure_vLast_iff (frame : ChildFrame) (c : Site) :
    FreeClosure.freeClosure frame (frame.vLast - c) ↔ FreeClosure.freeClosure frame c :=
  ⟨freeClosure_of_vLast frame, fun h => freeClosure_of_vLast frame (c := frame.vLast - c) (by rw [sub_sub_cancel]; exact h)⟩

theorem nonfree_iff_not_closure (frame : ChildFrame) (c : Site) :
    Induction.Nonfree frame c ↔ ¬ FreeClosure.freeClosure frame c := by
  constructor
  · rintro hn ⟨s, hs, h⟩
    refine hn s hs ?_
    rcases h with h | h
    · exact Set.mem_union_left _ h
    · exact Set.mem_union_right _ h
  · intro hn v hv hm
    exact hn ⟨v, hv, (Set.mem_union _ _ _).mp hm⟩

/-- **`Nonfree` is invariant under `z ↦ vLast − z`.** -/
theorem nonfree_vLast_iff (frame : ChildFrame) (c : Site) :
    Induction.Nonfree frame (frame.vLast - c) ↔ Induction.Nonfree frame c := by
  rw [nonfree_iff_not_closure frame (frame.vLast - c), nonfree_iff_not_closure frame c, freeClosure_vLast_iff]

end FLatticePaper.RouteReflect
