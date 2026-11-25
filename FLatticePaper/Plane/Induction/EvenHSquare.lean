import FLatticePaper.Plane.Induction.ForcedArrows
import FLatticePaper.Plane.Induction.ReturnPrescribed
import FLatticePaper.Plane.Induction.NativeCases
import FLatticePaper.Plane.Induction.W1Witness
import FLatticePaper.Plane.Induction.W1NonfreeOut
import FLatticePaper.Plane.Induction.WestSelect
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.FanCompat

/-! # The even H interior root: the NW square (Q32 even H, the C.2 diagonal)

For an even free H root `z` whose west input `z+W` is a free H point (prescription `N`, and `z+W ≠ hFirst`), with the north
corners `z+N`, `z+NW` white and nonfree, the NW square is a parent square:
`z+W → z+NW` (prescription of `z+W`), `z+NW → z+N` (`ForcedArrows.forced_two_chain`, the exit `z`), `z+N → z`
(`ForcedArrows.forced_to_free_input`), and `z` keeps its prescription `z+E` and rejects `z+W`. -/

namespace FLatticePaper.EvenHSquare

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut
  FLatticePaper.ForcedArrows FLatticePaper.W1Witness FLatticePaper.ReturnPrescribed FLatticePaper.FanCompat
  Farey

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

end FLatticePaper.EvenHSquare
