import FLatticePaper.Plane.Induction.OddVNWFan
import FLatticePaper.Plane.Induction.WestEast
import FLatticePaper.Plane.Induction.LowerMem
import FLatticePaper.Plane.Induction.CentralForced

/-! # The hard east case of hderiv, in the regime `d < 2n`, from the odd V north-west arrow

For an even free V root `z` (not the origin, not `vLast`), with `Y = (z.1, z.2 - 1)` its lower input, the reflected point
`z' = A - Y` (`A = I + tr`) is an odd free V root whose south point is `A - z` (free, by `WestEast.cref_freeV`). The rotated fan
arrow of the odd V north-west square (`oddV_NW_arrow`, the prefix of `OddVNWFan.parentSquareOut_oddV_NW_fan_rot`) at `z'` is the
arrow `A - M1 → A - M2`, and `CentralForced.forcedEdge_cref` carries it to `M1 → M2`. The regime `d < 2n` is the hypothesis of the
rotated fan (`K_bounds_rot` needs `3N - 1 ≤ D`). -/

namespace FLatticePaper.HardEast

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut
open FLatticePaper.RotatedForced FLatticePaper.RotatedCap FLatticePaper.CapConeGrades FLatticePaper.CentralForced

/-- The arrow `z - (1,1) → z - (1,0)` of the odd V north-west square, from the rotated fan (the prefix of
`OddVNWFan.parentSquareOut_oddV_NW_fan_rot`). -/
theorem oddV_NW_arrow {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (hW1 : FLatticePaper.W1.W1Forced fr.child.num fr.child.den G)
    (hper : ∀ z : Site, G (z + (fr.child.den, fr.child.num)) = G z)
    (N D : ℤ) (hN2 : 2 * N = fr.child.den - fr.child.num) (hD2 : 2 * D = fr.child.den + fr.child.num)
    (hN0 : 0 < N) (hNDlt : N < D) (hreg : fr.child.den < 2 * fr.child.num)
    {z : Site} (hz : z ∈ fr.freeV) (hodd : ¬ EvenSite z) (hPfree : (z.1, z.2 - 1) ∈ fr.freeV)
    (hPs : fr.sGrade (z.1, z.2 - 1) ≠ 0) :
    FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2 - 1) (z.1 - 1, z.2) := by
  obtain ⟨hn1, hnd, hdn, hd3, hPT⟩ := fr.child_facts
  have hev : (fr.child.num + fr.child.den) % 2 = 0 := fr.child_even
  have hnum := FLatticePaper.FanInputs.num_odd fr
  have hodd' : (D + N) % 2 = 1 := by omega
  have hPeven : EvenSite (z.1, z.2 - 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  simp only [FLatticePaper.Induction.ChildFrame.freeV, Set.mem_setOf_eq] at hPfree hz
  obtain ⟨hPE, -, -⟩ := hPfree
  obtain ⟨hzE, -, hVz⟩ := hz
  rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_pos hPeven] at hPE
  rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_neg hodd] at hzE
  have hsz' : fr.sGrade z = fr.sGrade (z.1, z.2 - 1) + 2 * N := by
    have e1 : fr.sGrade z = (fr.child.den + fr.child.num) * z.1 + (fr.child.den - fr.child.num) * z.2 := rfl
    have e2 : fr.sGrade (z.1, z.2 - 1)
        = (fr.child.den + fr.child.num) * z.1 + (fr.child.den - fr.child.num) * (z.2 - 1) := rfl
    have h2 : fr.child.den - fr.child.num = 2 * N := by omega
    rw [e1, e2, h2]
    ring
  have hsid : fr.sGrade z = 2 * (N * z.2 + D * z.1) := by
    have e : fr.sGrade z = (fr.child.den + fr.child.num) * z.1 + (fr.child.den - fr.child.num) * z.2 := rfl
    have h1 : fr.child.den + fr.child.num = 2 * D := by omega
    have h2 : fr.child.den - fr.child.num = 2 * N := by omega
    rw [e, h1, h2]
    ring
  have hsPeven : fr.sGrade (z.1, z.2 - 1) % 2 = 0 := by
    have e : fr.sGrade (z.1, z.2 - 1) = 2 * (N * z.2 + D * z.1) - 2 * N := by
      have h := hsz'
      omega
    rw [e]
    omega
  have hs0 : 0 ≤ fr.sGrade (z.1, z.2 - 1) := hPE.2.2.1
  have hsP2 : 2 ≤ fr.sGrade (z.1, z.2 - 1) := by omega
  have hs2 : 2 ≤ fr.sGrade z := by omega
  have hsL : fr.sGrade z ≤ fr.child.den + fr.child.num - 2 := by
    unfold FLatticePaper.Induction.ChildFrame.vSpectrum at hVz
    rcases hVz.2 with h | h <;> omega
  have hR : resRegion fr.child.num fr.child.den (z.2, 1 - z.1) :=
    resRegion_start_of_box fr hodd hzE hVz
  obtain ⟨K, hK2, hKs, hKr⟩ := K_bounds_rot (N := N) (D := D) (by omega) (by omega)
  have hstart := nw_start_mem hP hprice hdrU hdrV N D hN2 hD2 hN0 hNDlt hodd hs2 hsL hR K hK2
  have hb : N + 1 ≤ N * (z.2, -z.1).1 - D * (z.2, -z.1).2 := by
    dsimp only
    linarith [hsid, hsz', hsP2]
  have heven : EvenSite (z.2, 1 - z.1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  obtain ⟨arrow, -⟩ := rotated_fan_arrow_G hP hprice hdrU hdrV hW1 hper N D hN2 hD2 hN0 hNDlt hodd' K hK2 hKs hKr
    (z.2, -z.1) (z.2, 1 - z.1) hb hstart heven hR
  have eR : Zs (z.2, 1 - z.1) = (z.1 - 1, z.2 - 1) := by
    unfold Zs
    refine Prod.ext ?_ ?_
    all_goals simp only
    all_goals omega
  have eQ : Zs (incomingPos (z.2, 1 - z.1)) = (z.1 - 1, z.2) := by
    unfold incomingPos
    rw [if_pos heven]
    unfold Zs
    refine Prod.ext ?_ ?_
    all_goals simp only
    all_goals omega
  rw [eR, eQ] at arrow
  exact arrow

/-- The reflected lower input is an odd free V root: its `t`-grade is `L - P - t(Y)`, its `s`-grade `2n - s(Y)`. -/
theorem cref_lower_freeV (frame : ChildFrame) {Y : Site} (hYfree : Y ∈ frame.freeV) (hYodd : ¬ EvenSite Y)
    (hYv : Y ∈ frame.vBand) :
    cref (reflectionI + frame.child.modifiedDeck.transverse) Y ∈ frame.freeV ∧
      ¬ EvenSite (cref (reflectionI + frame.child.modifiedDeck.transverse) Y) := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hevY : (Y.1 + Y.2) % 2 ≠ 0 := by
    unfold EvenSite at hYodd
    exact hYodd
  obtain ⟨hcpY, hrangeY⟩ := (frame.mem_vBand_iff Y).mp hYv
  rw [if_neg hYodd] at hrangeY
  obtain ⟨hr1, hr2⟩ := hrangeY
  have hsY : frame.sGrade Y % 2 = 0 := by
    have hvs : frame.vSpectrum (frame.sGrade Y) := hYfree.2.2
    unfold ChildFrame.vSpectrum at hvs
    exact hvs.1
  have hYb : frame.child.num - frame.child.periodDenominator ≤ frame.tGrade Y ∧
      frame.tGrade Y ≤ frame.child.den ∧ 2 - frame.child.den + frame.child.num ≤ frame.sGrade Y ∧
      frame.sGrade Y ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2 := by
    rcases (frame.mem_closedPolygon_iff Y).mp hcpY with h | h
    · exact absurd h.1 hYodd
    · exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  obtain ⟨hYb1, hYb2, hYb3, hYb4⟩ := hYb
  have hz'par : ¬ EvenSite (cref (reflectionI + frame.child.modifiedDeck.transverse) Y) := by
    rw [evenSite_cref (centre_even frame) Y]
    exact hYodd
  have hPgt := P_gt_L _ _ _ hn0 hdn hP
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine (frame.mem_closedPolygon_iff _).mpr (Or.inr ⟨hz'par, ?_, ?_, ?_, ?_⟩)
      · rw [tGrade_cref]
        omega
      · rw [tGrade_cref]
        omega
      · rw [sGrade_cref]
        omega
      · rw [sGrade_cref]
        omega
    · intro hc
      rcases (frame.mem_closedPolygon_iff _).mp hc with h | h
      · have h' := h.2.2.2.1
        rw [frame.sGrade_sub_x, sGrade_cref] at h'
        omega
      · exfalso
        apply h.1
        unfold EvenSite at hz'par ⊢
        dsimp only at hz'par ⊢
        omega
    · unfold ChildFrame.vSpectrum
      rw [sGrade_cref]
      exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
  · exact hz'par

/-- **hderiv in the regime `d < 2n`**: the east middle `M1 = (z.1 + 1, z.2)` forces its lower neighbour `M2 = (z.1 + 1, z.2 - 1)`,
for an even free V root `z` (not the origin, not `vLast`). Its colour is not needed. -/
theorem hderiv_regime {G : Field} (frame : ChildFrame) (hP : frame.Packet G)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price G z ∧ frame.price G z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1)
    (hdrV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hper : ∀ z : Site, G (z + (frame.child.den, frame.child.num)) = G z)
    (hreg : frame.child.den < 2 * frame.child.num)
    (hI : ∀ z, G (reflectionI - z) = G z)
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hzF : z ≠ FLatticePaper.Induction.vFirst)
    (hzL : z ≠ frame.vLast) :
    FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (z.1 + 1, z.2) (z.1 + 1, z.2 - 1) := by
  have hodd := frame.child_num_odd
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  obtain ⟨N, hN2⟩ : ∃ N : ℤ, 2 * N = frame.child.den - frame.child.num := ⟨(frame.child.den - frame.child.num) / 2, by omega⟩
  obtain ⟨D, hD2⟩ : ∃ D : ℤ, 2 * D = frame.child.den + frame.child.num := ⟨(frame.child.den + frame.child.num) / 2, by omega⟩
  obtain ⟨hn0, hnd, hdn, hd3, hPT⟩ := frame.child_facts
  have hN0 : 0 < N := by omega
  have hNDlt : N < D := by omega
  have hY := frame.lower_mem_freeV hz hev hzF (δ := 1) (Or.inl rfl) (Or.inl rfl)
  have hYv := frame.lower_in_vBand hz hev hzF (δ := 1) (Or.inl rfl) (Or.inl rfl)
  have hYodd : ¬ EvenSite (z.1, z.2 - 1) := by
    show ¬ ((z.1 + (z.2 - 1)) % 2 = 0)
    omega
  obtain ⟨hz'free, hz'odd⟩ := cref_lower_freeV frame hY hYodd hYv
  have hPeq : ((cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1, z.2 - 1)).1,
      (cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1, z.2 - 1)).2 - 1)
      = cref (reflectionI + frame.child.modifiedDeck.transverse) z := by
    exact Prod.ext (by simp only [cref]; try ring) (by simp only [cref]; try ring)
  have hPfree : ((cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1, z.2 - 1)).1,
      (cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1, z.2 - 1)).2 - 1) ∈ frame.freeV := by
    rw [hPeq]
    exact (cref_freeV frame hz hev hzF hzL).1
  have hPs : frame.sGrade ((cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1, z.2 - 1)).1,
      (cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1, z.2 - 1)).2 - 1) ≠ 0 := by
    rw [hPeq, sGrade_cref]
    intro h0
    apply frame.s_ne_two_n hz hev hzL
    omega
  have arrow := oddV_NW_arrow hP hprice hdrU hdrV hW1 hper N D hN2 hD2 hN0 hNDlt hreg hz'free hz'odd hPfree hPs
  have e1 : ((cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1, z.2 - 1)).1 - 1,
      (cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1, z.2 - 1)).2 - 1)
      = cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1 + 1, z.2) := by
    exact Prod.ext (by simp only [cref]; try ring) (by simp only [cref]; try ring)
  have e2 : ((cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1, z.2 - 1)).1 - 1,
      (cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1, z.2 - 1)).2)
      = cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1 + 1, z.2 - 1) := by
    exact Prod.ext (by simp only [cref]; try ring) (by simp only [cref]; try ring)
  rw [e1, e2] at arrow
  have hT := forcedEdge_cref (centre_even frame)
    (fun y => lap_cref_centre frame hI hP.periods y) arrow
  rw [cref_cref, cref_cref] at hT
  exact hT

/-- `A - vLast = vFirst` for the centre `A = I + tr`: the reflection exchanges the two ends of the V arc. -/
theorem cref_vLast_eq_vFirst (frame : ChildFrame) :
    cref (reflectionI + frame.child.modifiedDeck.transverse) frame.vLast = FLatticePaper.Induction.vFirst := by
  rw [centre_eq]
  unfold cref ChildFrame.vLast FLatticePaper.Induction.vFirst
  refine Prod.ext ?_ ?_
  all_goals (simp only; ring)

/-- **hderiv in the regime `d < 2n`, the west middle `M1 = (z.1 - 1, z.2)`**, from the east case at the reflected root `A - z`. -/
theorem hderiv_west_regime {G : Field} (frame : ChildFrame) (hP : frame.Packet G)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price G z ∧ frame.price G z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1)
    (hdrV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hper : ∀ z : Site, G (z + (frame.child.den, frame.child.num)) = G z)
    (hreg : frame.child.den < 2 * frame.child.num)
    (hI : ∀ z, G (reflectionI - z) = G z)
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hzF : z ≠ FLatticePaper.Induction.vFirst)
    (hzL : z ≠ frame.vLast) :
    FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2) (z.1 - 1, z.2 + 1) := by
  obtain ⟨hw, hwev, hwF⟩ := cref_freeV frame hz hev hzF hzL
  have hwL : cref (reflectionI + frame.child.modifiedDeck.transverse) z ≠ frame.vLast := by
    intro h
    apply hzF
    have h2 := cref_cref (reflectionI + frame.child.modifiedDeck.transverse) z
    rw [h, cref_vLast_eq_vFirst] at h2
    exact h2.symm
  have hE := hderiv_regime frame hP hprice hdrU hdrV hW1 hper hreg hI hw hwev hwF hwL
  have hT := forcedEdge_cref (centre_even frame)
    (fun y => lap_cref_centre frame hI hP.periods y) hE
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

end FLatticePaper.HardEast
