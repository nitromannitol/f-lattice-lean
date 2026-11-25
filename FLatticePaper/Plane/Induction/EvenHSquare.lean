import FLatticePaper.Plane.Induction.ForcedArrows
import FLatticePaper.Plane.Induction.ReturnPrescribed
import FLatticePaper.Plane.Induction.NativeCases
import FLatticePaper.Plane.Induction.W1Witness
import FLatticePaper.Plane.Induction.W1NonfreeOut
import FLatticePaper.Plane.Induction.WestSelect
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.FanCompat
import FLatticePaper.Plane.Induction.ReflectedFan
import FLatticePaper.Plane.Induction.CoveredSW

/-! # The even H interior root: the NW square (Q32 even H, the C.2 diagonal)

For an even free H root `z` whose west input `z+W` is a free H point (prescription `N`, and `z+W ≠ hFirst`), with the north
corners `z+N`, `z+NW` white and nonfree, the NW square is a parent square:
`z+W → z+NW` (prescription of `z+W`), `z+NW → z+N` (`ForcedArrows.forced_two_chain`, the exit `z`), `z+N → z`
(`ForcedArrows.forced_to_free_input`), and `z` keeps its prescription `z+E` and rejects `z+W`. -/

namespace FLatticePaper.EvenHSquare

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut
  FLatticePaper.ForcedArrows FLatticePaper.W1Witness FLatticePaper.ReturnPrescribed FLatticePaper.FanCompat
  FLatticePaper.CapRay FLatticePaper.AllBranchFan FLatticePaper.ContactCone Farey

theorem pos_of_even (x : Site) (hx : EvenSite x) : incomingPos x = (x.1 + 1, x.2) := by
  unfold incomingPos
  rw [if_pos hx]

theorem pos_of_odd (x : Site) (hx : ¬ EvenSite x) : incomingPos x = (x.1, x.2 + 1) := by
  unfold incomingPos
  rw [if_neg hx]

theorem neg_of_odd (x : Site) (hx : ¬ EvenSite x) : incomingNeg x = (x.1, x.2 - 1) := by
  unfold incomingNeg
  rw [if_neg hx]

theorem parentSquareOut_evenH_NW {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : OldPolicyWitness frame G seed η)
    (hpres : PrescribedAt frame G η W.retained)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z)
    (hWfree : (z.1 - 1, z.2) ∈ frame.freeH) (hWlap : laplacian G (z.1 - 1, z.2) = 0)
    (hWne : (z.1 - 1, z.2) ≠ FLatticePaper.Induction.hFirst)
    (hzw : laplacian G z = 0)
    (hN : laplacian G (z.1, z.2 + 1) = 0) (hNnf : Nonfree frame (z.1, z.2 + 1))
    (hNW : laplacian G (z.1 - 1, z.2 + 1) = 0) (hNWnf : Nonfree frame (z.1 - 1, z.2 + 1)) :
    ParentSquareOut G W.retained z := by
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hzF : z ≠ FLatticePaper.Induction.hFirst := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    unfold FLatticePaper.Induction.hFirst at h1 h2
    unfold EvenSite at hev
    simp only at h1 h2 hev
    omega
  have hzL : z ≠ frame.hLast := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    unfold ChildFrame.hLast at h1 h2
    unfold EvenSite at hev
    simp only at h1 h2 hev
    omega
  have hprz : frame.prescribedH η z = (1, 0) := prescribedH_even η hev hzF hzL
  have hodd1 : ¬ EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hWprz : frame.prescribedH η (z.1 - 1, z.2) = (0, 1) := by
    rw [FLatticePaper.NativeCases.prescribedH_odd_eq frame η hodd1, if_neg hWne]
  have hq1e : EvenSite (z.1 - 1, z.2 + 1) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hq2o : ¬ EvenSite (z.1, z.2 + 1) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hzero : (0 : Site) ∈ frame.child.modifiedDeck.span :=
    ⟨0, 0, by ext <;> simp [FLatticePaper.Farey.PeriodDeck.combine]⟩
  have hzfree : ¬ Nonfree frame z := by
    intro h
    exact h 0 hzero (Set.mem_union_left _ (by simpa using hz))
  -- the incidence facts of the square
  have E1 : (z.1 - 1, z.2 + 1) = incomingPos (z.1 - 1, z.2) := by
    rw [pos_of_odd _ hodd1]
  have E2 : (z.1, z.2 + 1) = incomingPos (z.1 - 1, z.2 + 1) := by
    rw [pos_of_even _ hq1e]
    exact Prod.ext (by simp) (by simp)
  have E3 : z = incomingNeg (z.1, z.2 + 1) := by
    rw [neg_of_odd _ hq2o]
    exact Prod.ext rfl (by simp)
  have hR12 : W.retained (z.1 - 1, z.2 + 1) (z.1, z.2 + 1) := by
    have hF : ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2 + 1) (z.1, z.2 + 1) :=
      forced_two_chain hP hW1 hNWnf hNW hN (Or.inr E2) (Or.inl E3) hzfree
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hR23 : W.retained (z.1, z.2 + 1) z := by
    have hF : ForcedEdge G (fun _ _ => False) (z.1, z.2 + 1) z :=
      forced_to_free_input hP hW1 hNnf hN (Or.inl E3) hzfree
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hR01 : W.retained (z.1 - 1, z.2) (z.1 - 1, z.2 + 1) := by
    refine (hpres.1 _ hWfree hWlap _).mpr ?_
    rw [hWprz]
    exact Prod.ext (by simp) (by simp)
  have hRz : W.retained z (z.1 + 1, z.2) := by
    refine (hpres.1 z hz hzw _).mpr ?_
    rw [hprz]
    exact Prod.ext (by simp) (by simp)
  have hoin : (z.1 + 1, z.2) = incomingPos z := by
    rw [pos_of_even _ hev]
  refine ⟨(z.1 - 1, z.2), (z.1 - 1, z.2 + 1), (z.1, z.2 + 1), (z.1 + 1, z.2), z.1 - 1, z.2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_squareCorners_iff]
    try dsimp only
    omega
  · rw [mem_squareCorners_iff]
    try dsimp only
    omega
  · rw [mem_squareCorners_iff]
    try dsimp only
    omega
  · rw [mem_squareCorners_iff]
    try dsimp only
    omega
  · intro c' hc' hne
    obtain ⟨p1, p2⟩ := c'
    rw [mem_squareCorners_iff] at hc'
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
    rw [if_pos hev]
  · intro h
    have := (hpres.1 z hz hzw _).mp h
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
    exact hoin
  · intro h
    rw [mem_squareCorners_iff] at h
    dsimp only at h
    omega
  · exact hRz
  · intro j hj
    have := (hpres.1 z hz hzw j).mp hj
    rw [hprz] at this
    rw [this]
    exact Prod.ext (by simp) (by simp)
  · right
    exact ⟨hWlap, fun j hj => hwu _ j _ hWlap hj hR01⟩
  · right
    exact ⟨hNW, fun j hj => hwu _ j _ hNW hj hR12⟩
  · right
    exact ⟨hN, fun j hj => hwu _ j _ hN hj hR23⟩

/-- A free H point is not nonfree. -/
theorem not_nonfree_of_freeH {frame : ChildFrame} {p : Site} (hp : p ∈ frame.freeH) : ¬ Nonfree frame p := by
  intro h
  have hzero : (0 : Site) ∈ frame.child.modifiedDeck.span :=
    ⟨0, 0, by ext <;> simp [FLatticePaper.Farey.PeriodDeck.combine]⟩
  exact h 0 hzero (Set.mem_union_left _ (by simpa using hp))

/-- **The even H interior root: the SW square.** For an even free H root `z` whose west input `z+W` and south input `z+S` are
nonfree whites and whose south-west corner `z+SW` is a free H point (prescription `E`), the SW square is a parent square:
`z+W → z+SW` (`forced_to_free_input`), `z+SW → z+S` (prescription of `z+SW`), `z+S → z` (`forced_to_free_input`). -/
theorem parentSquareOut_evenH_SW {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : OldPolicyWitness frame G seed η)
    (hpres : PrescribedAt frame G η W.retained)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z)
    (hWnf : Nonfree frame (z.1 - 1, z.2)) (hWlap : laplacian G (z.1 - 1, z.2) = 0)
    (hSWfree : (z.1 - 1, z.2 - 1) ∈ frame.freeH) (hSWlap : laplacian G (z.1 - 1, z.2 - 1) = 0)
    (hSnf : Nonfree frame (z.1, z.2 - 1)) (hSlap : laplacian G (z.1, z.2 - 1) = 0)
    (hzw : laplacian G z = 0) :
    ParentSquareOut G W.retained z := by
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hzF : z ≠ FLatticePaper.Induction.hFirst := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    unfold FLatticePaper.Induction.hFirst at h1 h2
    unfold EvenSite at hev
    simp only at h1 h2 hev
    omega
  have hzL : z ≠ frame.hLast := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    unfold ChildFrame.hLast at h1 h2
    unfold EvenSite at hev
    simp only at h1 h2 hev
    omega
  have hprz : frame.prescribedH η z = (1, 0) := prescribedH_even η hev hzF hzL
  have hodd1 : ¬ EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hq1e : EvenSite (z.1 - 1, z.2 - 1) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hq2o : ¬ EvenSite (z.1, z.2 - 1) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hq1F : (z.1 - 1, z.2 - 1) ≠ FLatticePaper.Induction.hFirst := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    unfold FLatticePaper.Induction.hFirst at h1 h2
    unfold EvenSite at hq1e
    simp only at h1 h2 hq1e
    omega
  have hq1L : (z.1 - 1, z.2 - 1) ≠ frame.hLast := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    unfold ChildFrame.hLast at h1 h2
    unfold EvenSite at hq1e
    simp only at h1 h2 hq1e
    omega
  have hprq1 : frame.prescribedH η (z.1 - 1, z.2 - 1) = (1, 0) :=
    prescribedH_even η hq1e hq1F hq1L
  have hzfree : ¬ Nonfree frame z := not_nonfree_of_freeH hz
  have hq1free : ¬ Nonfree frame (z.1 - 1, z.2 - 1) := not_nonfree_of_freeH hSWfree
  -- the incidence facts
  have E1 : (z.1 - 1, z.2 - 1) = incomingNeg (z.1 - 1, z.2) := by
    rw [neg_of_odd _ hodd1]
  have E2 : (z.1, z.2 - 1) = incomingPos (z.1 - 1, z.2 - 1) := by
    rw [pos_of_even _ hq1e]
    exact Prod.ext (by simp) (by simp)
  have E3 : z = incomingPos (z.1, z.2 - 1) := by
    rw [pos_of_odd _ hq2o]
    exact Prod.ext rfl (by simp)
  have hR01 : W.retained (z.1 - 1, z.2) (z.1 - 1, z.2 - 1) := by
    have hF : ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2) (z.1 - 1, z.2 - 1) :=
      forced_to_free_input hP hW1 hWnf hWlap (Or.inl E1) hq1free
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hR12 : W.retained (z.1 - 1, z.2 - 1) (z.1, z.2 - 1) := by
    refine (hpres.1 _ hSWfree hSWlap _).mpr ?_
    rw [hprq1]
    exact Prod.ext (by simp) (by simp)
  have hR23 : W.retained (z.1, z.2 - 1) z := by
    have hF : ForcedEdge G (fun _ _ => False) (z.1, z.2 - 1) z :=
      forced_to_free_input hP hW1 hSnf hSlap (Or.inr E3) hzfree
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hNot : ¬ W.retained z (z.1 - 1, z.2) := by
    intro h
    have := (hpres.1 z hz hzw _).mp h
    rw [hprz] at this
    have h1 := congrArg Prod.fst this
    have h2 := congrArg Prod.snd this
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    omega
  have hRz : W.retained z (z.1 + 1, z.2) := by
    refine (hpres.1 z hz hzw _).mpr ?_
    rw [hprz]
    exact Prod.ext (by simp) (by simp)
  have hoin : (z.1 + 1, z.2) = incomingPos z := by
    rw [pos_of_even _ hev]
  refine ⟨(z.1 - 1, z.2), (z.1 - 1, z.2 - 1), (z.1, z.2 - 1), (z.1 + 1, z.2), z.1 - 1, z.2 - 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_squareCorners_iff]
    try dsimp only
    omega
  · rw [mem_squareCorners_iff]
    try dsimp only
    omega
  · rw [mem_squareCorners_iff]
    try dsimp only
    omega
  · rw [mem_squareCorners_iff]
    try dsimp only
    omega
  · intro c' hc' hne
    obtain ⟨p1, p2⟩ := c'
    rw [mem_squareCorners_iff] at hc'
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
    rw [if_pos hev]
  · exact hNot
  · exact Or.inl E1
  · exact Or.inr E2
  · exact Or.inr E3
  · exact hR01
  · exact hR12
  · exact hR23
  · right
    exact hoin
  · intro h
    rw [mem_squareCorners_iff] at h
    try dsimp only at h
    omega
  · exact hRz
  · intro j hj
    have := (hpres.1 z hz hzw j).mp hj
    rw [hprz] at this
    rw [this]
    exact Prod.ext (by simp) (by simp)
  · right
    exact ⟨hWlap, fun j hj => hwu _ j _ hWlap hj hR01⟩
  · right
    exact ⟨hSWlap, fun j hj => hwu _ j _ hSWlap hj hR12⟩
  · right
    exact ⟨hSlap, fun j hj => hwu _ j _ hSlap hj hR23⟩

/-- **The even H interior root with black `z+N`: the NW square with the fan start.** The arrow `z+NW → z+N` is the forced east edge
of the contact fan of the apex `z+W` (`ReflectedFan.fan_start_forced`, the start `z+NW = (z+W)+N`), and `z+N → z` is the black rule.
The named inputs are the all-slope cap ray `hAS`, the depth `d ≥ 3n − 2`, the apex height `t(z+W) ≥ n + 2`, the start's strict
interior membership and contact value; all four are verified at every such root over words of length at most 6. -/
theorem parentSquareOut_evenH_NW_fan {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    (hAS : ∀ K : ℕ, 2 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 3 * frame.child.num - 1 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)))
    (hdn : 3 * frame.child.num - 2 ≤ frame.child.den)
    (W : OldPolicyWitness frame G seed η)
    (hpres : PrescribedAt frame G η W.retained)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z)
    (hWfree : (z.1 - 1, z.2) ∈ frame.freeH) (hWlap : laplacian G (z.1 - 1, z.2) = 0)
    (hWne : (z.1 - 1, z.2) ≠ FLatticePaper.Induction.hFirst)
    (hapex : frame.child.num + 2 ≤ frame.tGrade (z.1 - 1, z.2))
    (hzw : laplacian G z = 0)
    (hNB : laplacian G (z.1, z.2 + 1) = -1)
    (hNW : laplacian G (z.1 - 1, z.2 + 1) = 0)
    (hSIstart : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (z.1 - 1, z.2 + 1))
    (hcontact : G (z.1 - 1, z.2 + 1) = 0) :
    ParentSquareOut G W.retained z := by
  have hn : 1 ≤ frame.child.num := by
    obtain ⟨hn1, -, -, -, -⟩ := frame.child_facts
    omega
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hzF : z ≠ FLatticePaper.Induction.hFirst := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    unfold FLatticePaper.Induction.hFirst at h1 h2
    unfold EvenSite at hev
    simp only at h1 h2 hev
    omega
  have hzL : z ≠ frame.hLast := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    unfold ChildFrame.hLast at h1 h2
    unfold EvenSite at hev
    simp only at h1 h2 hev
    omega
  have hprz : frame.prescribedH η z = (1, 0) := prescribedH_even η hev hzF hzL
  have hodd1 : ¬ EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hWprz : frame.prescribedH η (z.1 - 1, z.2) = (0, 1) := by
    rw [FLatticePaper.NativeCases.prescribedH_odd_eq frame η hodd1, if_neg hWne]
  have hq1e : EvenSite (z.1 - 1, z.2 + 1) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hq2o : ¬ EvenSite (z.1, z.2 + 1) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hzfree : ¬ Nonfree frame z := not_nonfree_of_freeH hz
  -- the fan start: the forced east edge of `z+NW`, apex `z+W`
  obtain ⟨K, hK2, hKs, hKr⟩ := CoveredSW.K_bounds_of_three_n hn hdn
  obtain ⟨p, q, hs, hcap⟩ := hAS K hK2 hKs hKr
  have hbstart : ConeRoot (z.1 - 1, z.2) K (z.1 - 1, z.2 + 1) := by
    unfold ConeRoot
    refine ⟨?_, ?_, fun _ => ?_, fun h => absurd hq1e h⟩
    · simp only
      omega
    · simp only
      omega
    · simp only
      omega
  have hstart : (z.1 - 1, z.2 + 1) ∈ contactFan frame G (z.1 - 1, z.2) K := by
    refine mem_contactFan.mpr ⟨⟨(FLatticePaper.W1Exit.openRect_iff frame _).mpr hSIstart, hbstart⟩, ?_⟩
    unfold parabolaField
    rw [hcontact]
    have e : (z.1 - 1, z.2 + 1).2 - (z.1 - 1, z.2).2 = 1 := by simp
    rw [e]
    norm_num [FLatticePaper.QuadraticCap.capMin]
  obtain ⟨o, ho⟩ := hW1 (z.1 - 1, z.2 + 1) hSIstart hNW
  have hO := ReflectedFan.fan_start_forced hP hsig hs hK2 hKs (by linarith) hcap hapex hstart hq1e ho
  rw [hO] at ho
  have hF : ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2 + 1) (incomingPos (z.1 - 1, z.2 + 1)) :=
    FLatticePaper.W1.forcedEdgeIn_forced ho
  have hR12 : W.retained (z.1 - 1, z.2 + 1) (z.1, z.2 + 1) := by
    have e : incomingPos (z.1 - 1, z.2 + 1) = (z.1, z.2 + 1) := by
      rw [pos_of_even _ hq1e]
      exact Prod.ext (by simp) (by simp)
    rw [e] at hF
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hq2inc : incomingNeg (z.1, z.2 + 1) = z := by
    rw [neg_of_odd _ hq2o]
    exact Prod.ext rfl (by simp)
  have hR23 : W.retained (z.1, z.2 + 1) z := by
    have hb := W.quota.1 (z.1, z.2 + 1) hNB
    rw [hq2inc] at hb
    exact hb.1
  have hR01 : W.retained (z.1 - 1, z.2) (z.1 - 1, z.2 + 1) := by
    refine (hpres.1 _ hWfree hWlap _).mpr ?_
    rw [hWprz]
    exact Prod.ext (by simp) (by simp)
  have hRz : W.retained z (z.1 + 1, z.2) := by
    refine (hpres.1 z hz hzw _).mpr ?_
    rw [hprz]
    exact Prod.ext (by simp) (by simp)
  have E1 : (z.1 - 1, z.2 + 1) = incomingPos (z.1 - 1, z.2) := by
    rw [pos_of_odd _ hodd1]
  have E2 : (z.1, z.2 + 1) = incomingPos (z.1 - 1, z.2 + 1) := by
    rw [pos_of_even _ hq1e]
    exact Prod.ext (by simp) (by simp)
  have E3 : z = incomingNeg (z.1, z.2 + 1) := hq2inc.symm
  have hoin : (z.1 + 1, z.2) = incomingPos z := by
    rw [pos_of_even _ hev]
  refine ⟨(z.1 - 1, z.2), (z.1 - 1, z.2 + 1), (z.1, z.2 + 1), (z.1 + 1, z.2), z.1 - 1, z.2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_squareCorners_iff]
    try dsimp only
    omega
  · rw [mem_squareCorners_iff]
    try dsimp only
    omega
  · rw [mem_squareCorners_iff]
    try dsimp only
    omega
  · rw [mem_squareCorners_iff]
    try dsimp only
    omega
  · intro c' hc' hne
    obtain ⟨p1, p2⟩ := c'
    rw [mem_squareCorners_iff] at hc'
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
    rw [if_pos hev]
  · intro h
    have := (hpres.1 z hz hzw _).mp h
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
    exact hoin
  · intro h
    rw [mem_squareCorners_iff] at h
    try dsimp only at h
    omega
  · exact hRz
  · intro j hj
    have := (hpres.1 z hz hzw j).mp hj
    rw [hprz] at this
    rw [this]
    exact Prod.ext (by simp) (by simp)
  · right
    exact ⟨hWlap, fun j hj => hwu _ j _ hWlap hj hR01⟩
  · right
    exact ⟨hNW, fun j hj => hwu _ j _ hNW hj hR12⟩
  · left
    exact hNB

end FLatticePaper.EvenHSquare
