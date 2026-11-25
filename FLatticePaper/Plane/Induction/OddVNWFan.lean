import FLatticePaper.Plane.Induction.OddVSquare
import FLatticePaper.Plane.Induction.RotatedForced

/-! # The odd V root with the NW-fan square, for the sign `η = −1` (`δ = +1`)

The NW square of `OddVSquare.parentSquareOut_oddV_NW_eta_minus` assumes the west point `Q = z − (1,0)` nonfree with `lap Q = 0`. For the
NW-fan roots `Q` is black (`lap Q = −1`): its two inputs are retained (quota), and the arrow `R → Q` out of the white corner `R = z − (1,1)`
is the forced east arrow of the rotated fan (the hypothesis `hfan`). Everything else is the minus square verbatim. -/

namespace FLatticePaper.OddVNWFan

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut
open FLatticePaper.RotatedForced FLatticePaper.RotatedCap FLatticePaper.CapConeGrades

theorem parentSquareOut_oddV_NW_fan {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed (-1))
    (hpres : PrescribedAt frame G (-1) W.retained)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z)
    (hPfree : (z.1, z.2 - 1) ∈ frame.freeV) (hPlap : laplacian G (z.1, z.2 - 1) = 0)
    (hPne : (z.1, z.2 - 1) ≠ FLatticePaper.Induction.vFirst)
    (hzw : laplacian G z = 0)
    (hQb : laplacian G (z.1 - 1, z.2) = -1) (hRlap : laplacian G (z.1 - 1, z.2 - 1) = 0)
    (hfan : ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2 - 1) (z.1 - 1, z.2)) :
    ParentSquareOut G W.retained z := by
  have hzF : z ≠ FLatticePaper.Induction.vFirst := by
    intro h
    apply hodd
    rw [h]
    simp [EvenSite, FLatticePaper.Induction.vFirst]
  have hzL : z ≠ frame.vLast := by
    intro h
    apply hodd
    rw [h]
    unfold EvenSite ChildFrame.vLast
    dsimp only
    omega
  have hprz : frame.prescribedV (-1) z = (0, -(-1)) :=
    FLatticePaper.Induction.CanonicalDirections.prescribedV_internal_odd frame (-1) hzF hzL hodd
  have hPeven : EvenSite (z.1, z.2 - 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hprP : frame.prescribedV (-1) (z.1, z.2 - 1) = (-1, 0) := by
    unfold ChildFrame.prescribedV
    rw [if_neg hPne]
    by_cases hL : (z.1, z.2 - 1) = frame.vLast
    · rw [if_pos hL]
    · rw [if_neg hL, if_pos hPeven]
  have hQeven : EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hRodd : ¬ EvenSite (z.1 - 1, z.2 - 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hzero : (0 : Site) ∈ frame.child.modifiedDeck.span :=
    ⟨0, 0, by ext <;> simp [FLatticePaper.Farey.PeriodDeck.combine]⟩
  have hzfree : ¬ Nonfree frame z := by
    intro h
    exact h 0 hzero (Set.mem_union_right _ (by simpa using hz))
  -- the incidence facts of the square `z − Q − R − P − z`
  have Ep : (z.1 - 1, z.2 - 1) = incomingNeg (z.1, z.2 - 1) := by
    simp only [incomingNeg, if_pos hPeven]
  have Eq : (z.1 - 1, z.2) = incomingPos (z.1 - 1, z.2 - 1) := by
    rw [FLatticePaper.EvenHSquare.pos_of_odd _ hRodd]
    exact Prod.ext rfl (by simp)
  have Ez : z = incomingPos (z.1 - 1, z.2) := by
    rw [FLatticePaper.EvenHSquare.pos_of_even _ hQeven]
    exact Prod.ext (by simp) rfl
  have Eo : (z.1, z.2 + 1) = incomingPos z := by
    rw [FLatticePaper.EvenHSquare.pos_of_odd _ hodd]
  -- the forced and prescribed arrows
  have hR12 : W.retained (z.1 - 1, z.2 - 1) (z.1 - 1, z.2) := by
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hfan)
  have hR23 : W.retained (z.1 - 1, z.2) z := by
    have hb := W.quota.1 (z.1 - 1, z.2) hQb
    rw [← Ez] at hb
    exact hb.2
  have hR01 : W.retained (z.1, z.2 - 1) (z.1 - 1, z.2 - 1) := by
    refine (hpres.2 _ hPfree hPlap _).mpr ?_
    rw [hprP]
    exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  have hRz : W.retained z (z.1, z.2 + 1) := by
    refine (hpres.2 z hz hzw _).mpr ?_
    rw [hprz]
    exact Prod.ext (by simp) (by simp)
  refine ⟨(z.1, z.2 - 1), (z.1 - 1, z.2 - 1), (z.1 - 1, z.2), (z.1, z.2 + 1), z.1 - 1, z.2 - 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FLatticePaper.FanCompat.mem_squareCorners_iff]
    try dsimp only
    omega
  · rw [FLatticePaper.FanCompat.mem_squareCorners_iff]
    try dsimp only
    omega
  · rw [FLatticePaper.FanCompat.mem_squareCorners_iff]
    try dsimp only
    omega
  · rw [FLatticePaper.FanCompat.mem_squareCorners_iff]
    try dsimp only
    omega
  · intro c' hc' hne
    obtain ⟨p1, p2⟩ := c'
    rw [FLatticePaper.FanCompat.mem_squareCorners_iff] at hc'
    try dsimp only at hc'
    have hne' : ¬ (p1 = z.1 ∧ p2 = z.2) := fun h => hne (by rw [h.1, h.2])
    simp only [Prod.mk.injEq]
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · left
    unfold incomingNeg
    rw [if_neg hodd]
  · intro h
    have := (hpres.2 z hz hzw _).mp h
    rw [hprz] at this
    have h1 := congrArg Prod.fst this
    have h2 := congrArg Prod.snd this
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    omega
  · exact Or.inl Ep
  · exact Or.inr Eq
  · exact Or.inr Ez
  · exact hR01
  · exact hR12
  · exact hR23
  · right
    exact Eo
  · intro h
    rw [FLatticePaper.FanCompat.mem_squareCorners_iff] at h
    dsimp only at h
    omega
  · exact hRz
  · intro j hj
    have := (hpres.2 z hz hzw j).mp hj
    rw [hprz] at this
    rw [this]
    exact Prod.ext (by simp) (by simp)
  · right
    exact ⟨hPlap, fun j hj => hwu _ j _ hPlap hj hR01⟩
  · right
    exact ⟨hRlap, fun j hj => hwu _ j _ hRlap hj hR12⟩
  · left
    exact hQb

/-- **The odd V NW-fan square, in the fan regime `d < 2n`.** For an odd free white V root `z` whose south point `P = z − (0,1)` is free,
white, not `vFirst` and off the `s = 0` line (`s(P) ≠ 0`), and whose west point `Q = z − (1,0)` is black, the square of `z` is the
parent square. The apex bound, the depth and the start are derived from the box of `P` (`s(P) ≥ 2`), and the forced arrow `R → Q` is
the rotated fan (`RotatedForced.rotated_fan_arrow_G`). -/
theorem parentSquareOut_oddV_NW_fan_rot {fr : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (hW1 : FLatticePaper.W1.W1Forced fr.child.num fr.child.den G)
    (hper : ∀ z : Site, G (z + (fr.child.den, fr.child.num)) = G z)
    (N D : ℤ) (hN2 : 2 * N = fr.child.den - fr.child.num) (hD2 : 2 * D = fr.child.den + fr.child.num)
    (hN0 : 0 < N) (hNDlt : N < D) (hreg : fr.child.den < 2 * fr.child.num)
    (W : FLatticePaper.W1Witness.OldPolicyWitness fr G seed (-1))
    (hpres : PrescribedAt fr G (-1) W.retained)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    {z : Site} (hz : z ∈ fr.freeV) (hodd : ¬ EvenSite z)
    (hPfree : (z.1, z.2 - 1) ∈ fr.freeV) (hPlap : laplacian G (z.1, z.2 - 1) = 0)
    (hPne : (z.1, z.2 - 1) ≠ FLatticePaper.Induction.vFirst)
    (hPs : fr.sGrade (z.1, z.2 - 1) ≠ 0)
    (hzw : laplacian G z = 0) (hQb : laplacian G (z.1 - 1, z.2) = -1) :
    ParentSquareOut G W.retained z := by
  obtain ⟨hn1, hnd, hdn, hd3, hPT⟩ := fr.child_facts
  have hz0 := hz
  have hPfree0 := hPfree
  have hev : (fr.child.num + fr.child.den) % 2 = 0 := fr.child_even
  have hnum := FLatticePaper.FanInputs.num_odd fr
  have hodd' : (D + N) % 2 = 1 := by omega
  have hPeven : EvenSite (z.1, z.2 - 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  -- the closed polygon at `P` (even) and at `z` (odd)
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
  obtain ⟨arrow, hlap⟩ := rotated_fan_arrow_G hP hprice hdrU hdrV hW1 hper N D hN2 hD2 hN0 hNDlt hodd' K hK2 hKs hKr
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
  rw [eR] at hlap
  rw [eR, eQ] at arrow
  exact parentSquareOut_oddV_NW_fan W hpres hwu hz0 hodd hPfree0 hPlap hPne hzw hQb hlap arrow

end FLatticePaper.OddVNWFan
