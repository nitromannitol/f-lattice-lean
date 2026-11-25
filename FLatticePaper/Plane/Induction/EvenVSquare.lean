import FLatticePaper.Plane.Induction.OddVSquare

/-! # The even V root squares (type B of §C.1), one sign `δ` with `η = −δ`

For an even free white V root `z` and `δ = ±1` the square has corners `z`, `X1 = z + δ(1,0)` (the rejected horizontal input),
`X2 = X1 − δ(0,1)`, `X3 = z − δ(0,1)` (free, white, with prescription `(0, −η) = (0, δ)`), and output `o = z + η(1,0) = z − δ(1,0)`.
The arrows are `X1 → X2`, `X2 → X3`, `X3 → z` and `z → o`. `X3 → z` and `z → o` are prescriptions. `X2 → X3` is the black rule at a black
`X2` and `forced_to_free_input` at a nonfree white `X2`. `X1 → X2` is the black rule at a black `X1` and `forced_two_chain` at a nonfree
white `X1` with white `X2`. The one remaining case (nonfree white `X1`, black `X2`) is the named input `hcanon`. -/

namespace FLatticePaper.EvenVSquare

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut
  FLatticePaper.AndOrRank

theorem prescV_even {frame : ChildFrame} (η : ℤ) {z : Site} (h1 : z ≠ FLatticePaper.Induction.vFirst)
    (he : EvenSite z) : frame.prescribedV η z = (η, 0) := by
  unfold ChildFrame.prescribedV
  rw [if_neg h1]
  by_cases hL : z = frame.vLast
  · rw [if_pos hL]
  · rw [if_neg hL, if_pos he]

theorem inNeg_even (x : Site) (h : EvenSite x) : incomingNeg x = (x.1 - 1, x.2) := by
  unfold incomingNeg
  rw [if_pos h]

theorem inPos_even (x : Site) (h : EvenSite x) : incomingPos x = (x.1 + 1, x.2) := by
  unfold incomingPos
  rw [if_pos h]

theorem inNeg_odd (x : Site) (h : ¬ EvenSite x) : incomingNeg x = (x.1, x.2 - 1) := by
  unfold incomingNeg
  rw [if_neg h]

theorem inPos_odd (x : Site) (h : ¬ EvenSite x) : incomingPos x = (x.1, x.2 + 1) := by
  unfold incomingPos
  rw [if_neg h]

/-- The square from its four arrows (the core: the colour cases are already decided by `hR12`, `hR23`). -/
theorem evenV_square_core {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η δ : ℤ}
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η)
    (hpres : PrescribedAt frame G η W.retained)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hzF : z ≠ FLatticePaper.Induction.vFirst)
    (hzw : laplacian G z = 0) (hη : η = -δ) (hδ : δ = 1 ∨ δ = -1)
    (hX3 : (z.1, z.2 - δ) ∈ frame.freeV) (hX3w : laplacian G (z.1, z.2 - δ) = 0)
    (hR12 : W.retained (z.1 + δ, z.2) (z.1 + δ, z.2 - δ))
    (hR23 : W.retained (z.1 + δ, z.2 - δ) (z.1, z.2 - δ)) :
    ParentSquareOut G W.retained z := by
  have hX1odd : ¬ EvenSite (z.1 + δ, z.2) := by
    unfold EvenSite at hev ⊢
    dsimp only at hev ⊢
    omega
  have hX2ev : EvenSite (z.1 + δ, z.2 - δ) := by
    unfold EvenSite at hev ⊢
    dsimp only at hev ⊢
    omega
  have hX3odd : ¬ EvenSite (z.1, z.2 - δ) := by
    unfold EvenSite at hev ⊢
    dsimp only at hev ⊢
    omega
  have hX3F : (z.1, z.2 - δ) ≠ FLatticePaper.Induction.vFirst := by
    intro h
    apply hX3odd
    rw [h]
    simp [EvenSite, FLatticePaper.Induction.vFirst]
  have hX3L : (z.1, z.2 - δ) ≠ frame.vLast := by
    intro h
    apply hX3odd
    rw [h]
    unfold EvenSite ChildFrame.vLast
    dsimp only
    omega
  have hprX3 : frame.prescribedV η (z.1, z.2 - δ) = (0, -η) :=
    FLatticePaper.Induction.CanonicalDirections.prescribedV_internal_odd frame η hX3F hX3L hX3odd
  have hR3z : W.retained (z.1, z.2 - δ) z := by
    refine (hpres.2 _ hX3 hX3w z).mpr ?_
    rw [hprX3]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add]
      omega
  have hprz : frame.prescribedV η z = (η, 0) := prescV_even η hzF hev
  have hRz : ∀ j, W.retained z j ↔ j = (z.1 + η, z.2) := by
    intro j
    rw [hpres.2 z hz hzw j, hprz]
    constructor
    · intro h
      rw [h]
      exact Prod.ext (by simp) (by simp)
    · intro h
      rw [h]
      exact Prod.ext (by simp) (by simp)
  have hRzo : W.retained z (z.1 + η, z.2) := (hRz _).mpr rfl
  have hRzU : ∀ j, W.retained z j → j = (z.1 + η, z.2) := fun j hj => (hRz j).mp hj
  have hmem : ∀ p : Site, p ∈ squareCorners ((z.1 + (δ - 1) / 2)) ((z.2 + (-δ - 1) / 2)) ↔
      ((p.1 = (z.1 + (δ - 1) / 2) ∨ p.1 = (z.1 + (δ - 1) / 2) + 1) ∧
        (p.2 = (z.2 + (-δ - 1) / 2) ∨ p.2 = (z.2 + (-δ - 1) / 2) + 1)) := fun p =>
    FLatticePaper.FanCompat.mem_squareCorners_iff _ _ p
  have hzinX1 : (z.1 + δ, z.2) = incomingNeg z ∨ (z.1 + δ, z.2) = incomingPos z := by
    rcases hδ with rfl | rfl
    · right
      rw [inPos_even z hev]
    · left
      rw [inNeg_even z hev]
      all_goals (try (refine Prod.ext ?_ ?_ <;> rfl))
  have hX2inX1 : (z.1 + δ, z.2 - δ) = incomingNeg (z.1 + δ, z.2) ∨
      (z.1 + δ, z.2 - δ) = incomingPos (z.1 + δ, z.2) := by
    rcases hδ with rfl | rfl
    · left
      rw [inNeg_odd (z.1 + 1, z.2) hX1odd]
    · right
      rw [inPos_odd (z.1 + -1, z.2) hX1odd]
      all_goals (try (refine Prod.ext ?_ ?_ <;> rfl))
  have hX3inX2 : (z.1, z.2 - δ) = incomingNeg (z.1 + δ, z.2 - δ) ∨
      (z.1, z.2 - δ) = incomingPos (z.1 + δ, z.2 - δ) := by
    rcases hδ with rfl | rfl
    · left
      rw [inNeg_even (z.1 + 1, z.2 - 1) hX2ev]
      all_goals (try (refine Prod.ext ?_ ?_ <;> (first | rfl | ring)))
    · right
      rw [inPos_even (z.1 + -1, z.2 - -1) hX2ev]
      all_goals (try (refine Prod.ext ?_ ?_ <;> (first | rfl | ring)))
  have hzinX3 : z = incomingNeg (z.1, z.2 - δ) ∨ z = incomingPos (z.1, z.2 - δ) := by
    rcases hδ with rfl | rfl
    · right
      rw [inPos_odd (z.1, z.2 - 1) hX3odd]
      all_goals (try (refine Prod.ext ?_ ?_ <;> (first | rfl | ring)))
    · left
      rw [inNeg_odd (z.1, z.2 - -1) hX3odd]
      all_goals (try (refine Prod.ext ?_ ?_ <;> (first | rfl | ring)))
  have ho : (z.1 + η, z.2) = incomingNeg z ∨ (z.1 + η, z.2) = incomingPos z := by
    rcases hδ with rfl | rfl
    · have hη' : η = -1 := by omega
      subst hη'
      simp [incomingNeg, incomingPos, hev]
      try ring
    · have hη' : η = 1 := by omega
      subst hη'
      simp [incomingNeg, incomingPos, hev]
      try ring
  refine ⟨(z.1 + δ, z.2), (z.1 + δ, z.2 - δ), (z.1, z.2 - δ), (z.1 + η, z.2),
    (z.1 + (δ - 1) / 2), (z.2 + (-δ - 1) / 2),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hmem _).mpr ⟨by omega, by omega⟩
  · exact (hmem _).mpr ⟨by omega, by omega⟩
  · exact (hmem _).mpr ⟨by omega, by omega⟩
  · exact (hmem _).mpr ⟨by omega, by omega⟩
  · intro c' hc' hne
    obtain ⟨p1, p2⟩ := c'
    rw [hmem] at hc'
    try dsimp only at hc'
    simp only [ne_eq, Prod.ext_iff] at hne ⊢
    omega
  · intro h
    simp only [Prod.ext_iff] at h
    omega
  · intro h
    simp only [Prod.ext_iff] at h
    omega
  · intro h
    simp only [Prod.ext_iff] at h
    omega
  · exact hzinX1
  · intro h
    have := hRzU _ h
    simp only [Prod.ext_iff] at this
    omega
  · exact hX2inX1
  · exact hX3inX2
  · exact hzinX3
  · exact hR12
  · exact hR23
  · exact hR3z
  · exact ho
  · intro h
    rw [hmem] at h
    try dsimp only at h
    omega
  · exact hRzo
  · exact hRzU
  · rcases hbin (z.1 + δ, z.2) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun j hj => hwu _ j _ h hj hR12⟩
  · rcases hbin (z.1 + δ, z.2 - δ) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun j hj => hwu _ j _ h hj hR23⟩
  · exact Or.inr ⟨hX3w, fun j hj => hwu _ j _ hX3w hj hR3z⟩

/-- The two adjacencies of the even V square: `X2` is a vertical neighbour of `X1` (its input), and `X3` a horizontal neighbour of `X2`. -/
theorem evenV_adj {z : Site} {δ : ℤ} (hev : EvenSite z) (hδ : δ = 1 ∨ δ = -1) :
    ((z.1 + δ, z.2 - δ) = incomingNeg (z.1 + δ, z.2) ∨ (z.1 + δ, z.2 - δ) = incomingPos (z.1 + δ, z.2)) ∧
      ((z.1, z.2 - δ) = incomingNeg (z.1 + δ, z.2 - δ) ∨ (z.1, z.2 - δ) = incomingPos (z.1 + δ, z.2 - δ)) := by
  have hX1odd : ¬ EvenSite (z.1 + δ, z.2) := by
    unfold EvenSite at hev ⊢
    dsimp only at hev ⊢
    omega
  have hX2ev : EvenSite (z.1 + δ, z.2 - δ) := by
    unfold EvenSite at hev ⊢
    dsimp only at hev ⊢
    omega
  refine ⟨?_, ?_⟩
  · rcases hδ with rfl | rfl
    · left
      rw [inNeg_odd (z.1 + 1, z.2) hX1odd]
    · right
      rw [inPos_odd (z.1 + -1, z.2) hX1odd]
      all_goals (try (refine Prod.ext ?_ ?_ <;> rfl))
  · rcases hδ with rfl | rfl
    · left
      rw [inNeg_even (z.1 + 1, z.2 - 1) hX2ev]
      all_goals (try (refine Prod.ext ?_ ?_ <;> (first | rfl | ring)))
    · right
      rw [inPos_even (z.1 + -1, z.2 - -1) hX2ev]
      all_goals (try (refine Prod.ext ?_ ?_ <;> (first | rfl | ring)))

/-- **The even V parent square, for every colour case of its middles** (the one unforced case, a nonfree white `X1` with black `X2`,
is the named canonical choice `hcanon`). -/
theorem evenV_square {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η δ : ℤ}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η)
    (hpres : PrescribedAt frame G η W.retained)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hzF : z ≠ FLatticePaper.Induction.vFirst)
    (hzw : laplacian G z = 0) (hη : η = -δ) (hδ : δ = 1 ∨ δ = -1)
    (hX3 : (z.1, z.2 - δ) ∈ frame.freeV) (hX3w : laplacian G (z.1, z.2 - δ) = 0)
    (hX1 : laplacian G (z.1 + δ, z.2) = -1 ∨
      (laplacian G (z.1 + δ, z.2) = 0 ∧ Nonfree frame (z.1 + δ, z.2)))
    (hX2 : laplacian G (z.1 + δ, z.2 - δ) = -1 ∨
      (laplacian G (z.1 + δ, z.2 - δ) = 0 ∧ Nonfree frame (z.1 + δ, z.2 - δ)))
    (hcanon : laplacian G (z.1 + δ, z.2) = 0 → laplacian G (z.1 + δ, z.2 - δ) = -1 →
      W.retained (z.1 + δ, z.2) (z.1 + δ, z.2 - δ)) :
    ParentSquareOut G W.retained z := by
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hzero : (0 : Site) ∈ frame.child.modifiedDeck.span :=
    ⟨0, 0, by ext <;> simp [FLatticePaper.Farey.PeriodDeck.combine]⟩
  have hzfree3 : ¬ Nonfree frame (z.1, z.2 - δ) :=
    fun h => h 0 hzero (Set.mem_union_right _ (by simpa using hX3))
  obtain ⟨hX2inX1, hX3inX2⟩ := evenV_adj hev hδ
  have hR23 : W.retained (z.1 + δ, z.2 - δ) (z.1, z.2 - δ) := by
    rcases hX2 with h2 | ⟨h2, hn2⟩
    · rcases hX3inX2 with e | e
      · rw [e]
        exact (W.quota.1 _ h2).1
      · rw [e]
        exact (W.quota.1 _ h2).2
    · have hF : ForcedEdge G (fun _ _ => False) (z.1 + δ, z.2 - δ) (z.1, z.2 - δ) :=
        FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hn2 h2 hX3inX2 hzfree3
      exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hR12 : W.retained (z.1 + δ, z.2) (z.1 + δ, z.2 - δ) := by
    rcases hX1 with h1 | ⟨h1, hn1⟩
    · rcases hX2inX1 with e | e
      · rw [e]
        exact (W.quota.1 _ h1).1
      · rw [e]
        exact (W.quota.1 _ h1).2
    · rcases hX2 with h2 | ⟨h2, hn2⟩
      · exact hcanon h1 h2
      · have hF : ForcedEdge G (fun _ _ => False) (z.1 + δ, z.2) (z.1 + δ, z.2 - δ) :=
          FLatticePaper.ForcedArrows.forced_two_chain hP hW1 hn1 h1 h2 hX2inX1 hX3inX2 hzfree3
        exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  exact evenV_square_core hbin W hpres hwu hz hev hzF hzw hη hδ hX3 hX3w hR12 hR23

end FLatticePaper.EvenVSquare
