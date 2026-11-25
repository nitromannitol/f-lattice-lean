import FLatticePaper.Plane.Induction.EvenHSquare
import FLatticePaper.Plane.Induction.CanonicalDirections

/-! # The odd V root with the NW square, for the sign `η = −1` (`δ = +1`)

The V analogue of `EvenHSquare.parentSquareOut_evenH_NW`. The root `z` is an odd free V site with inputs `±(0,1)`. Its corners are
`P = z − (0,1)` (even, free), `Q = z + (−1,0)` (even, nonfree) and `R = z + (−1,−1)` (odd, nonfree); the square is `z, P, R, Q`,
the output is `z + (0,1)`, and the prescriptions are `P ↦ R` (`η` east at even `P`), `z ↦ z + (0,1)` (`−η` north at odd `z`). -/

namespace FLatticePaper.OddVSquare

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut

theorem parentSquareOut_oddV_NW_eta_minus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed (-1))
    (hpres : PrescribedAt frame G (-1) W.retained)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z)
    (hPfree : (z.1, z.2 - 1) ∈ frame.freeV) (hPlap : laplacian G (z.1, z.2 - 1) = 0)
    (hPne : (z.1, z.2 - 1) ≠ FLatticePaper.Induction.vFirst)
    (hzw : laplacian G z = 0)
    (hQnf : Nonfree frame (z.1 - 1, z.2)) (hQlap : laplacian G (z.1 - 1, z.2) = 0)
    (hRnf : Nonfree frame (z.1 - 1, z.2 - 1)) (hRlap : laplacian G (z.1 - 1, z.2 - 1) = 0) :
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
    have hF : ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2 - 1) (z.1 - 1, z.2) :=
      FLatticePaper.ForcedArrows.forced_two_chain hP hW1 hRnf hRlap hQlap (Or.inr Eq) (Or.inr Ez) hzfree
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hR23 : W.retained (z.1 - 1, z.2) z := by
    have hF : ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2) z :=
      FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hQnf hQlap (Or.inr Ez) hzfree
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
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
  · right
    exact ⟨hQlap, fun j hj => hwu _ j _ hQlap hj hR23⟩

/-- The odd V root with the SW square, for the sign `η = −1` (`δ = +1`): the corners `P = z−(0,1)` (even, nonfree),
`SE = z+(1,−1)` (odd, free) and `E = z+(1,0)` (even, nonfree); the square is `z, P, SE, E`, the output `z+(0,1)`. -/
theorem parentSquareOut_oddV_SW_eta_minus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed (-1))
    (hpres : PrescribedAt frame G (-1) W.retained)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z)
    (hPnf : Nonfree frame (z.1, z.2 - 1)) (hPlap : laplacian G (z.1, z.2 - 1) = 0)
    (hSEfree : (z.1 + 1, z.2 - 1) ∈ frame.freeV) (hSElap : laplacian G (z.1 + 1, z.2 - 1) = 0)
    (hEnf : Nonfree frame (z.1 + 1, z.2)) (hElap : laplacian G (z.1 + 1, z.2) = 0)
    (hzw : laplacian G z = 0) :
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
  have hSEodd : ¬ EvenSite (z.1 + 1, z.2 - 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hSEF : (z.1 + 1, z.2 - 1) ≠ FLatticePaper.Induction.vFirst := by
    intro h
    apply hSEodd
    rw [h]
    simp [EvenSite, FLatticePaper.Induction.vFirst]
  have hSEL : (z.1 + 1, z.2 - 1) ≠ frame.vLast := by
    intro h
    apply hSEodd
    rw [h]
    unfold EvenSite ChildFrame.vLast
    dsimp only
    omega
  have hprSE : frame.prescribedV (-1) (z.1 + 1, z.2 - 1) = (0, -(-1)) :=
    FLatticePaper.Induction.CanonicalDirections.prescribedV_internal_odd frame (-1) hSEF hSEL hSEodd
  have hPeven : EvenSite (z.1, z.2 - 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hEeven : EvenSite (z.1 + 1, z.2) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hzero : (0 : Site) ∈ frame.child.modifiedDeck.span :=
    ⟨0, 0, by ext <;> simp [FLatticePaper.Farey.PeriodDeck.combine]⟩
  have hzfree : ¬ Nonfree frame z := by
    intro h
    exact h 0 hzero (Set.mem_union_right _ (by simpa using hz))
  have hSEfr : ¬ Nonfree frame (z.1 + 1, z.2 - 1) := by
    intro h
    exact h 0 hzero (Set.mem_union_right _ (by simpa using hSEfree))
  -- the incidence facts of the square `z − P − SE − E − z`
  have E1 : (z.1 + 1, z.2 - 1) = incomingPos (z.1, z.2 - 1) := by
    rw [FLatticePaper.EvenHSquare.pos_of_even _ hPeven]
  have E2 : (z.1 + 1, z.2) = incomingPos (z.1 + 1, z.2 - 1) := by
    rw [FLatticePaper.EvenHSquare.pos_of_odd _ hSEodd]
    exact Prod.ext rfl (by simp)
  have E3 : z = incomingNeg (z.1 + 1, z.2) := by
    simp only [incomingNeg, if_pos hEeven]
    try exact Prod.ext (by simp) rfl
  have Eo : (z.1, z.2 + 1) = incomingPos z := by
    rw [FLatticePaper.EvenHSquare.pos_of_odd _ hodd]
  -- the forced and prescribed arrows
  have hR01 : W.retained (z.1, z.2 - 1) (z.1 + 1, z.2 - 1) := by
    have hF : ForcedEdge G (fun _ _ => False) (z.1, z.2 - 1) (z.1 + 1, z.2 - 1) :=
      FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hPnf hPlap (Or.inr E1) hSEfr
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hR12 : W.retained (z.1 + 1, z.2 - 1) (z.1 + 1, z.2) := by
    refine (hpres.2 _ hSEfree hSElap _).mpr ?_
    rw [hprSE]
    exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  have hR23 : W.retained (z.1 + 1, z.2) z := by
    have hF : ForcedEdge G (fun _ _ => False) (z.1 + 1, z.2) z :=
      FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hEnf hElap (Or.inl E3) hzfree
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hRz : W.retained z (z.1, z.2 + 1) := by
    refine (hpres.2 z hz hzw _).mpr ?_
    rw [hprz]
    exact Prod.ext (by simp) (by simp)
  refine ⟨(z.1, z.2 - 1), (z.1 + 1, z.2 - 1), (z.1 + 1, z.2), (z.1, z.2 + 1), z.1, z.2 - 1,
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
  · exact Or.inr E1
  · exact Or.inr E2
  · exact Or.inl E3
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
    exact ⟨hSElap, fun j hj => hwu _ j _ hSElap hj hR12⟩
  · right
    exact ⟨hElap, fun j hj => hwu _ j _ hElap hj hR23⟩

/-- The odd V root with the NW square, for the sign `η = +1` (`δ = −1`): the corners `N = z+(0,1)` (even, free),
`E = z+(1,0)` (even, nonfree) and `NE = z+(1,1)` (odd, nonfree); the square is `z, N, NE, E`, the output `z+(0,−1)`. -/
theorem parentSquareOut_oddV_NW_eta_plus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed 1)
    (hpres : PrescribedAt frame G 1 W.retained)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z)
    (hNfree : (z.1, z.2 + 1) ∈ frame.freeV) (hNlap : laplacian G (z.1, z.2 + 1) = 0)
    (hNEnf : Nonfree frame (z.1 + 1, z.2 + 1)) (hNElap : laplacian G (z.1 + 1, z.2 + 1) = 0)
    (hEnf : Nonfree frame (z.1 + 1, z.2)) (hElap : laplacian G (z.1 + 1, z.2) = 0)
    (hzw : laplacian G z = 0) :
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
  have hprz : frame.prescribedV 1 z = (0, -1) :=
    FLatticePaper.Induction.CanonicalDirections.prescribedV_internal_odd frame 1 hzF hzL hodd
  have hNeven : EvenSite (z.1, z.2 + 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hEeven : EvenSite (z.1 + 1, z.2) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hNEodd : ¬ EvenSite (z.1 + 1, z.2 + 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  -- the prescription of the even corner `N` is `η` east, for every even `N` (the endpoints `vFirst`, `vLast` also give `(1,0)`)
  have hprN : frame.prescribedV 1 (z.1, z.2 + 1) = (1, 0) := by
    unfold ChildFrame.prescribedV
    by_cases h1 : (z.1, z.2 + 1) = FLatticePaper.Induction.vFirst
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : (z.1, z.2 + 1) = frame.vLast
      · rw [if_pos h2]
      · rw [if_neg h2, if_pos hNeven]
  have hzero : (0 : Site) ∈ frame.child.modifiedDeck.span :=
    ⟨0, 0, by ext <;> simp [FLatticePaper.Farey.PeriodDeck.combine]⟩
  have hzfree : ¬ Nonfree frame z := by
    intro h
    exact h 0 hzero (Set.mem_union_right _ (by simpa using hz))
  have hNfr : ¬ Nonfree frame (z.1, z.2 + 1) := by
    intro h
    exact h 0 hzero (Set.mem_union_right _ (by simpa using hNfree))
  -- the incidence facts of the square `z − N − NE − E − z`
  have EqN : (z.1, z.2 + 1) = incomingPos z := by
    rw [FLatticePaper.EvenHSquare.pos_of_odd _ hodd]
  have E1 : (z.1 + 1, z.2 + 1) = incomingPos (z.1, z.2 + 1) := by
    rw [FLatticePaper.EvenHSquare.pos_of_even _ hNeven]
  have E2 : (z.1 + 1, z.2) = incomingNeg (z.1 + 1, z.2 + 1) := by
    rw [FLatticePaper.EvenHSquare.neg_of_odd _ hNEodd]
    exact Prod.ext rfl (by simp)
  have E3 : z = incomingNeg (z.1 + 1, z.2) := by
    simp only [incomingNeg, if_pos hEeven]
    try exact Prod.ext (by simp) rfl
  have Eo : (z.1, z.2 - 1) = incomingNeg z := by
    rw [FLatticePaper.EvenHSquare.neg_of_odd _ hodd]
  -- the forced and prescribed arrows
  have hR01 : W.retained (z.1, z.2 + 1) (z.1 + 1, z.2 + 1) := by
    refine (hpres.2 _ hNfree hNlap _).mpr ?_
    rw [hprN]
    exact Prod.ext (by simp) (by simp)
  have hR12 : W.retained (z.1 + 1, z.2 + 1) (z.1 + 1, z.2) := by
    have hF : ForcedEdge G (fun _ _ => False) (z.1 + 1, z.2 + 1) (z.1 + 1, z.2) :=
      FLatticePaper.ForcedArrows.forced_two_chain hP hW1 hNEnf hNElap hElap (Or.inl E2) (Or.inl E3) hzfree
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hR23 : W.retained (z.1 + 1, z.2) z := by
    have hF : ForcedEdge G (fun _ _ => False) (z.1 + 1, z.2) z :=
      FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hEnf hElap (Or.inl E3) hzfree
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hRz : W.retained z (z.1, z.2 - 1) := by
    refine (hpres.2 z hz hzw _).mpr ?_
    rw [hprz]
    exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  refine ⟨(z.1, z.2 + 1), (z.1 + 1, z.2 + 1), (z.1 + 1, z.2), (z.1, z.2 - 1), z.1, z.2,
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
  · right
    exact EqN
  · intro h
    have := (hpres.2 z hz hzw _).mp h
    rw [hprz] at this
    have h1 := congrArg Prod.fst this
    have h2 := congrArg Prod.snd this
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    omega
  · exact Or.inr E1
  · exact Or.inl E2
  · exact Or.inl E3
  · exact hR01
  · exact hR12
  · exact hR23
  · left
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
    exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  · right
    exact ⟨hNlap, fun j hj => hwu _ j _ hNlap hj hR01⟩
  · right
    exact ⟨hNElap, fun j hj => hwu _ j _ hNElap hj hR12⟩
  · right
    exact ⟨hElap, fun j hj => hwu _ j _ hElap hj hR23⟩

/-- The odd V root with the SW square, for the sign `η = +1` (`δ = −1`): the corners `N = z+(0,1)` (even, nonfree),
`NW = z+(−1,1)` (odd, free) and `W = z+(−1,0)` (even, nonfree); the square is `z, N, NW, W`, the output `z+(0,−1)`. -/
theorem parentSquareOut_oddV_SW_eta_plus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed 1)
    (hpres : PrescribedAt frame G 1 W.retained)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z)
    (hNnf : Nonfree frame (z.1, z.2 + 1)) (hNlap : laplacian G (z.1, z.2 + 1) = 0)
    (hNWfree : (z.1 - 1, z.2 + 1) ∈ frame.freeV) (hNWlap : laplacian G (z.1 - 1, z.2 + 1) = 0)
    (hWnf : Nonfree frame (z.1 - 1, z.2)) (hWlap : laplacian G (z.1 - 1, z.2) = 0)
    (hzw : laplacian G z = 0) :
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
  have hprz : frame.prescribedV 1 z = (0, -1) :=
    FLatticePaper.Induction.CanonicalDirections.prescribedV_internal_odd frame 1 hzF hzL hodd
  have hNWodd : ¬ EvenSite (z.1 - 1, z.2 + 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hNWF : (z.1 - 1, z.2 + 1) ≠ FLatticePaper.Induction.vFirst := by
    intro h
    apply hNWodd
    rw [h]
    simp [EvenSite, FLatticePaper.Induction.vFirst]
  have hNWL : (z.1 - 1, z.2 + 1) ≠ frame.vLast := by
    intro h
    apply hNWodd
    rw [h]
    unfold EvenSite ChildFrame.vLast
    dsimp only
    omega
  have hprNW : frame.prescribedV 1 (z.1 - 1, z.2 + 1) = (0, -1) :=
    FLatticePaper.Induction.CanonicalDirections.prescribedV_internal_odd frame 1 hNWF hNWL hNWodd
  have hNeven : EvenSite (z.1, z.2 + 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hWeven : EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hzero : (0 : Site) ∈ frame.child.modifiedDeck.span :=
    ⟨0, 0, by ext <;> simp [FLatticePaper.Farey.PeriodDeck.combine]⟩
  have hzfree : ¬ Nonfree frame z := by
    intro h
    exact h 0 hzero (Set.mem_union_right _ (by simpa using hz))
  have hNWfr : ¬ Nonfree frame (z.1 - 1, z.2 + 1) := by
    intro h
    exact h 0 hzero (Set.mem_union_right _ (by simpa using hNWfree))
  -- the incidence facts of the square `z − N − NW − W − z`
  have EqN : (z.1, z.2 + 1) = incomingPos z := by
    rw [FLatticePaper.EvenHSquare.pos_of_odd _ hodd]
  have E1 : (z.1 - 1, z.2 + 1) = incomingNeg (z.1, z.2 + 1) := by
    simp only [incomingNeg, if_pos hNeven]
  have E2 : (z.1 - 1, z.2) = incomingNeg (z.1 - 1, z.2 + 1) := by
    rw [FLatticePaper.EvenHSquare.neg_of_odd _ hNWodd]
    exact Prod.ext rfl (by simp)
  have E3 : z = incomingPos (z.1 - 1, z.2) := by
    rw [FLatticePaper.EvenHSquare.pos_of_even _ hWeven]
    exact Prod.ext (by simp) rfl
  have Eo : (z.1, z.2 - 1) = incomingNeg z := by
    rw [FLatticePaper.EvenHSquare.neg_of_odd _ hodd]
  -- the forced and prescribed arrows
  have hR01 : W.retained (z.1, z.2 + 1) (z.1 - 1, z.2 + 1) := by
    have hF : ForcedEdge G (fun _ _ => False) (z.1, z.2 + 1) (z.1 - 1, z.2 + 1) :=
      FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hNnf hNlap (Or.inl E1) hNWfr
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hR12 : W.retained (z.1 - 1, z.2 + 1) (z.1 - 1, z.2) := by
    refine (hpres.2 _ hNWfree hNWlap _).mpr ?_
    rw [hprNW]
    exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  have hR23 : W.retained (z.1 - 1, z.2) z := by
    have hF : ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2) z :=
      FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hWnf hWlap (Or.inr E3) hzfree
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hRz : W.retained z (z.1, z.2 - 1) := by
    refine (hpres.2 z hz hzw _).mpr ?_
    rw [hprz]
    exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  refine ⟨(z.1, z.2 + 1), (z.1 - 1, z.2 + 1), (z.1 - 1, z.2), (z.1, z.2 - 1), z.1 - 1, z.2,
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
  · right
    exact EqN
  · intro h
    have := (hpres.2 z hz hzw _).mp h
    rw [hprz] at this
    have h1 := congrArg Prod.fst this
    have h2 := congrArg Prod.snd this
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    omega
  · exact Or.inl E1
  · exact Or.inl E2
  · exact Or.inr E3
  · exact hR01
  · exact hR12
  · exact hR23
  · left
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
    exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  · right
    exact ⟨hNlap, fun j hj => hwu _ j _ hNlap hj hR01⟩
  · right
    exact ⟨hNWlap, fun j hj => hwu _ j _ hNWlap hj hR12⟩
  · right
    exact ⟨hWlap, fun j hj => hwu _ j _ hWlap hj hR23⟩

end FLatticePaper.OddVSquare
