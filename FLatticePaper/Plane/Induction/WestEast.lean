import FLatticePaper.Plane.Induction.HderivEasy
import FLatticePaper.Plane.Induction.CentralForced
import FLatticePaper.Plane.Induction.DeckSelection
import FLatticePaper.Plane.Induction.ReflectionI
import FLatticePaper.Plane.Induction.Potentials

/-! # The west case of hderiv (eta = +1) from the east case

For an even free V root `z` (not the origin, not `vLast`) the west middle is `M1 = (z.1 - 1, z.2)` and the diagonal is
`M2 = (z.1 - 1, z.2 + 1)`. Let `A = I + tr` (with `I = (1, -1)` and `tr` the transverse period, `A = (1 + (n-d), -1 + (n+d))`), an even centre,
and `w = A - z`. Then `w` is an even free V root (its `t`-grade is `L - P - t(z)` and its `s`-grade is `2n - s(z)`), the east middles of `w`
are `A - M1` and `A - M2`, and the Laplacian is `A`-equivariant (`I`-invariance of the Laplacian, plus the transverse period of the
Laplacian). So `hderiv_easy` at `w` gives the forced edge `A - M1 → A - M2`, and `CentralForced.forcedEdge_cref` carries it back. -/

namespace FLatticePaper.Induction

open FLatticePaper.CentralForced

theorem transverse_eq (frame : ChildFrame) :
    frame.child.modifiedDeck.transverse = (frame.child.num - frame.child.den, frame.child.num + frame.child.den) :=
  frame.child_modifiedDeck_transverse

/-- The centre `A = I + tr` of the west reflection, in coordinates. -/
theorem centre_eq (frame : ChildFrame) :
    reflectionI + frame.child.modifiedDeck.transverse =
      (1 + (frame.child.num - frame.child.den), -1 + (frame.child.num + frame.child.den)) := by
  rw [transverse_eq]
  unfold reflectionI
  rfl

theorem centre_even (frame : ChildFrame) : EvenSite (reflectionI + frame.child.modifiedDeck.transverse) := by
  rw [centre_eq]
  unfold EvenSite
  dsimp only
  omega

/-- The Laplacian is equivariant under `y ↦ A − y`, from the `I`-invariance and the transverse period of the Laplacian. -/
theorem lap_cref_centre (frame : ChildFrame) {G : Field} {cU cV : ℤ}
    (hI : ∀ z, G (reflectionI - z) = G z)
    (hF : HasGeneratorPeriods frame.child G cU cV) (y : Site) :
    laplacian G (cref (reflectionI + frame.child.modifiedDeck.transverse) y) = laplacian G y := by
  have e : cref (reflectionI + frame.child.modifiedDeck.transverse) y
      = (reflectionI - y) + frame.child.modifiedDeck.transverse := by
    unfold cref
    rw [centre_eq, transverse_eq]
    unfold reflectionI
    ext <;> simp <;> ring
  rw [e]
  have hp := FLatticePaper.DeckSelection.laplacian_add_span frame hF 0 1 (reflectionI - y)
  simp only [zero_smul, one_smul, zero_add] at hp
  rw [hp, laplacian_reflectI hI]

/-- The grades of the reflected point: `t(A - z) = L - P - t(z)`, `s(A - z) = 2n - s(z)`. -/
theorem tGrade_cref (frame : ChildFrame) (z : Site) :
    frame.tGrade (cref (reflectionI + frame.child.modifiedDeck.transverse) z)
      = frame.child.num + frame.child.den - frame.child.periodDenominator - frame.tGrade z := by
  have hP := (frame.child_facts).2.2.2.2
  rw [centre_eq]
  unfold cref ChildFrame.tGrade
  dsimp only
  rw [hP]
  ring

theorem sGrade_cref (frame : ChildFrame) (z : Site) :
    frame.sGrade (cref (reflectionI + frame.child.modifiedDeck.transverse) z) = 2 * frame.child.num - frame.sGrade z := by
  rw [centre_eq]
  unfold cref ChildFrame.sGrade
  dsimp only
  ring

/-- The reflected root `A - z` is an even free V root (not the origin). -/
theorem cref_freeV (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z)
    (hzF : z ≠ FLatticePaper.Induction.vFirst) (hzL : z ≠ frame.vLast) :
    cref (reflectionI + frame.child.modifiedDeck.transverse) z ∈ frame.freeV ∧
      EvenSite (cref (reflectionI + frame.child.modifiedDeck.transverse) z) ∧
      cref (reflectionI + frame.child.modifiedDeck.transverse) z ≠ FLatticePaper.Induction.vFirst := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  obtain ⟨hs1, hs2, ht1, ht2⟩ := frame.root_bounds hz hev
  have htlo := frame.t_le_neg_L hz hev hzF
  have hvs : frame.vSpectrum (frame.sGrade z) := hz.2.2
  have hsE : frame.sGrade z % 2 = 0 := by
    unfold ChildFrame.vSpectrum at hvs
    exact hvs.1
  have hs2ne := frame.s_ne_two_n hz hev hzL
  have hPgt := P_gt_L _ _ _ hn0 hdn hP
  have hw_even : EvenSite (cref (reflectionI + frame.child.modifiedDeck.transverse) z) :=
    (evenSite_cref (centre_even frame) z).mpr hev
  have hwpar : ((cref (reflectionI + frame.child.modifiedDeck.transverse) z).1
      + (cref (reflectionI + frame.child.modifiedDeck.transverse) z).2) % 2 = 0 := hw_even
  have hcp : cref (reflectionI + frame.child.modifiedDeck.transverse) z ∈ frame.closedPolygon := by
    refine (frame.mem_closedPolygon_iff _).mpr (Or.inl ⟨hw_even, ?_, ?_, ?_, ?_⟩)
    · rw [tGrade_cref]; omega
    · rw [tGrade_cref]; omega
    · rw [sGrade_cref]; omega
    · rw [sGrade_cref]; omega
  have hnot : ((cref (reflectionI + frame.child.modifiedDeck.transverse) z).1 - 1,
      (cref (reflectionI + frame.child.modifiedDeck.transverse) z).2) ∉ frame.closedPolygon := by
    intro hc
    rcases (frame.mem_closedPolygon_iff _).mp hc with h | h
    · exfalso
      have hev2 := h.1
      unfold EvenSite at hev2
      dsimp only at hev2
      omega
    · have h' := h.2.2.2.1
      rw [frame.sGrade_sub_x, sGrade_cref] at h'
      omega
  refine ⟨⟨hcp, hnot, ?_⟩, hw_even, ?_⟩
  · unfold ChildFrame.vSpectrum
    rw [sGrade_cref]
    exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
  · intro h0
    have hs0 : frame.sGrade (cref (reflectionI + frame.child.modifiedDeck.transverse) z) = 0 := by
      rw [h0]
      unfold FLatticePaper.Induction.vFirst ChildFrame.sGrade
      simp
    rw [sGrade_cref] at hs0
    exact hs2ne (by omega)

/-- **hderiv at eta = +1 (the west middle), from the east case.** -/
theorem hderiv_west {G : Field} (frame : ChildFrame)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) {cU cV : ℤ}
    (hI : ∀ z, G (reflectionI - z) = G z) (hF : HasGeneratorPeriods frame.child G cU cV)
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hzF : z ≠ FLatticePaper.Induction.vFirst)
    (hzL : z ≠ frame.vLast)
    (hlapM1 : laplacian G (z.1 - 1, z.2) = 0) (hlapM2 : laplacian G (z.1 - 1, z.2 + 1) = 0) :
    FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2) (z.1 - 1, z.2 + 1) := by
  obtain ⟨hw, hwev, hwF⟩ := cref_freeV frame hz hev hzF hzL
  have hE := hderiv_easy frame hW1 hw hwev hwF
    (by
      have e : ((cref (reflectionI + frame.child.modifiedDeck.transverse) z).1 + 1,
          (cref (reflectionI + frame.child.modifiedDeck.transverse) z).2)
          = cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1 - 1, z.2) := by
        exact Prod.ext (by simp only [cref]; try ring) (by simp only [cref]; try ring)
      rw [e, lap_cref_centre frame hI hF]
      exact hlapM1)
    (by
      have e : ((cref (reflectionI + frame.child.modifiedDeck.transverse) z).1 + 1,
          (cref (reflectionI + frame.child.modifiedDeck.transverse) z).2 - 1)
          = cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1 - 1, z.2 + 1) := by
        exact Prod.ext (by simp only [cref]; try ring) (by simp only [cref]; try ring)
      rw [e, lap_cref_centre frame hI hF]
      exact hlapM2)
  have hT := forcedEdge_cref (centre_even frame) (lap_cref_centre frame hI hF) hE
  have e2 : cref (reflectionI + frame.child.modifiedDeck.transverse)
      ((cref (reflectionI + frame.child.modifiedDeck.transverse) z).1 + 1,
        (cref (reflectionI + frame.child.modifiedDeck.transverse) z).2) = (z.1 - 1, z.2) := by
    exact Prod.ext (by simp only [cref]; try ring) (by simp only [cref]; try ring)
  have e3 : cref (reflectionI + frame.child.modifiedDeck.transverse)
      ((cref (reflectionI + frame.child.modifiedDeck.transverse) z).1 + 1,
        (cref (reflectionI + frame.child.modifiedDeck.transverse) z).2 - 1) = (z.1 - 1, z.2 + 1) := by
    exact Prod.ext (by simp only [cref]; try ring) (by simp only [cref]; try ring)
  rw [e2, e3] at hT
  exact hT

end FLatticePaper.Induction
