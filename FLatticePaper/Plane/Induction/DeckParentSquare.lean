import FLatticePaper.Plane.Induction.W1NonfreeOut
import FLatticePaper.Plane.Induction.FanCompat
import FLatticePaper.Plane.Induction.RowCovariance
import FLatticePaper.Plane.Induction.RepInputs
import FLatticePaper.Plane.Induction.NonfreeBridge

/-! # Deck covariance of `ParentSquareOut` (Q32 part (c))

For an even vector `τ` (a deck lattice vector), if the policy `R` is deck-equivariant (`R x u ↔ R (x − τ) (u − τ)`) and the laplacian is
deck-invariant (`laplacian G (w − τ) = laplacian G w`), then `ParentSquareOut G R z` implies `ParentSquareOut G R (z − τ)`: the witness is
translated by `−τ`. -/

namespace FLatticePaper.DeckParentSquare

open FLatticePaper FLatticePaper.W1NonfreeOut FLatticePaper.FanCompat FLatticePaper.RowCovariance FLatticePaper.AndOrRank FLatticePaper.Induction

theorem mem_squareCorners_sub (a b : ℤ) (t p : Site) :
    p ∈ squareCorners (a - t.1) (b - t.2) ↔ p + t ∈ squareCorners a b := by
  rw [mem_squareCorners_iff, mem_squareCorners_iff]
  simp only [Prod.fst_add, Prod.snd_add]
  constructor
  · intro h
    omega
  · intro h
    omega

theorem even_sub_iff {x τ : Site} (hτ : EvenSite τ) : EvenSite (x - τ) ↔ EvenSite x := by
  unfold EvenSite at hτ ⊢
  simp only [Prod.fst_sub, Prod.snd_sub] at hτ ⊢
  omega

theorem incomingNeg_sub_even {x τ : Site} (hτ : EvenSite τ) :
    incomingNeg (x - τ) = incomingNeg x - τ := by
  have h := incomingNeg_add_U (U := -τ) (z := x) (by
    rw [← sub_eq_add_neg]
    exact even_sub_iff (x := x) hτ)
  rw [← sub_eq_add_neg, ← sub_eq_add_neg] at h
  exact h

theorem incomingPos_sub_even {x τ : Site} (hτ : EvenSite τ) :
    incomingPos (x - τ) = incomingPos x - τ := by
  have h := incomingPos_add_U (U := -τ) (z := x) (by
    rw [← sub_eq_add_neg]
    exact even_sub_iff (x := x) hτ)
  rw [← sub_eq_add_neg, ← sub_eq_add_neg] at h
  exact h

theorem edge_sub_even {y x τ : Site} (hτ : EvenSite τ) : Edge (y - τ) (x - τ) ↔ Edge y x := by
  unfold Edge
  simp only [incomingNeg_sub_even hτ, incomingPos_sub_even hτ, sub_left_inj]

/-- The colour clause of a corner translates: a black corner stays black, a white corner keeps its unique retained input. -/
theorem colour_sub {G : Field} {R : Site → Site → Prop} {τ q t : Site}
    (hR : ∀ x u, R x u ↔ R (x - τ) (u - τ)) (hL : ∀ w, laplacian G (w - τ) = laplacian G w)
    (h : laplacian G q = -1 ∨ (laplacian G q = 0 ∧ ∀ j, R q j → j = t)) :
    laplacian G (q - τ) = -1 ∨ (laplacian G (q - τ) = 0 ∧ ∀ j, R (q - τ) j → j = t - τ) := by
  rcases h with h | ⟨h, hu⟩
  · exact Or.inl ((hL q).trans h)
  · refine Or.inr ⟨(hL q).trans h, fun j hj => ?_⟩
    have hj' : R q (j + τ) := (hR q (j + τ)).mpr (by rw [add_sub_cancel_right]; exact hj)
    exact eq_sub_of_add_eq (hu _ hj')

/-- **Deck covariance of `ParentSquareOut`**: the parent square of `z` translates to the parent square of `z − τ`. -/
theorem parentSquareOut_sub {G : Field} {R : Site → Site → Prop} {z τ : Site} (hτ : EvenSite τ)
    (hR : ∀ x u, R x u ↔ R (x - τ) (u - τ)) (hL : ∀ w, laplacian G (w - τ) = laplacian G w)
    (h : ParentSquareOut G R z) : ParentSquareOut G R (z - τ) := by
  obtain ⟨q0, q1, q2, o, a, b, hz, hq0, hq1, hq2, hcov, h01, h12, h02, hq0n, hRz0, hE1, hE2, hE3,
    hR0, hR1, hR2, hon, hoout, hRo, hRu, hc0, hc1, hc2⟩ := h
  refine ⟨q0 - τ, q1 - τ, q2 - τ, o - τ, a - τ.1, b - τ.2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mem_squareCorners_sub a b τ (z - τ)).mpr (by rw [sub_add_cancel]; exact hz)
  · exact (mem_squareCorners_sub a b τ (q0 - τ)).mpr (by rw [sub_add_cancel]; exact hq0)
  · exact (mem_squareCorners_sub a b τ (q1 - τ)).mpr (by rw [sub_add_cancel]; exact hq1)
  · exact (mem_squareCorners_sub a b τ (q2 - τ)).mpr (by rw [sub_add_cancel]; exact hq2)
  · intro c' hc' hne
    have hc'' : c' + τ ∈ squareCorners a b := (mem_squareCorners_sub a b τ c').mp hc'
    have hne' : c' + τ ≠ z := fun h' => hne (eq_sub_of_add_eq h')
    rcases hcov (c' + τ) hc'' hne' with h1 | h1 | h1
    · exact Or.inl (eq_sub_of_add_eq h1)
    · exact Or.inr (Or.inl (eq_sub_of_add_eq h1))
    · exact Or.inr (Or.inr (eq_sub_of_add_eq h1))
  · exact fun h' => h01 (sub_left_inj.mp h')
  · exact fun h' => h12 (sub_left_inj.mp h')
  · exact fun h' => h02 (sub_left_inj.mp h')
  · rcases hq0n with h1 | h1
    · exact Or.inl (by rw [incomingNeg_sub_even hτ, h1])
    · exact Or.inr (by rw [incomingPos_sub_even hτ, h1])
  · exact fun h' => hRz0 ((hR z q0).mpr h')
  · exact (edge_sub_even hτ).mpr hE1
  · exact (edge_sub_even hτ).mpr hE2
  · exact (edge_sub_even hτ).mpr hE3
  · exact (hR q0 q1).mp hR0
  · exact (hR q1 q2).mp hR1
  · exact (hR q2 z).mp hR2
  · rcases hon with h1 | h1
    · exact Or.inl (by rw [incomingNeg_sub_even hτ, h1])
    · exact Or.inr (by rw [incomingPos_sub_even hτ, h1])
  · intro h'
    have := (mem_squareCorners_sub a b τ (o - τ)).mp h'
    rw [sub_add_cancel] at this
    exact hoout this
  · exact (hR z o).mp hRo
  · intro j hj
    have hj' : R z (j + τ) := (hR z (j + τ)).mpr (by rw [add_sub_cancel_right]; exact hj)
    exact eq_sub_of_add_eq (hRu _ hj')
  · exact colour_sub hR hL hc0
  · exact colour_sub hR hL hc1
  · exact colour_sub hR hL hc2


/-- The lattice vectors negate: `combine (−i) (−j) = −combine i j`. -/
theorem combine_neg (deck : Farey.PeriodDeck) (i j : ℤ) : deck.combine (-i) (-j) = -deck.combine i j := by
  unfold Farey.PeriodDeck.combine
  exact Prod.ext (by simp only [Prod.fst_neg]; ring) (by simp only [Prod.snd_neg]; ring)

/-- **Two-sided deck equivariance** from the one-sided one for all lattice vectors. -/
theorem equivariant_two_sided {R : Site → Site → Prop} (frame : ChildFrame)
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u → R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    (i j : ℤ) (z u : Site) :
    R z u ↔ R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j) := by
  refine ⟨hdeck i j z u, fun h => ?_⟩
  have h' := hdeck (-i) (-j) _ _ h
  simp only [combine_neg, sub_neg_eq_add, sub_add_cancel] at h'
  exact h'

/-- The laplacian is invariant under a lattice translation (the field's deck law). -/
theorem laplacian_sub_lattice {G : Field} (frame : ChildFrame) (hP : frame.Packet G) (i j : ℤ) (w : Site) :
    laplacian G (w - frame.child.modifiedDeck.combine i j) = laplacian G w := by
  have h := frame.laplacian_add_lattice hP i j (w - frame.child.modifiedDeck.combine i j)
  rw [sub_add_cancel] at h
  exact h.symm

/-- **Native-to-translate transport of `ParentSquareOut`**: the parent square of a native free root translates to any deck translate. -/
theorem parentSquareOut_translate {G : Field} {R : Site → Site → Prop} (frame : ChildFrame) (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u → R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    (i j : ℤ) {z : Site} (h : ParentSquareOut G R z) :
    ParentSquareOut G R (z - frame.child.modifiedDeck.combine i j) :=
  parentSquareOut_sub (frame.evenSite_combine i j)
    (equivariant_two_sided frame hdeck i j) (laplacian_sub_lattice frame hP i j) h

/-- **`ParentSquareOut` at every non-free root from the native free roots.** A root `z` that is not `Nonfree` has a deck translate
`z + combine i j` in the free H or V set; if white there and `ParentSquareOut` holds at that native free site, it holds at `z`. -/
theorem parentSquareOut_of_native {G : Field} {R : Site → Site → Prop} (frame : ChildFrame) (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u → R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    (hnative : ∀ z' : Site, z' ∈ frame.freeH ∪ frame.freeV → laplacian G z' = 0 → ParentSquareOut G R z')
    {z : Site} (hnf : ¬ Nonfree frame z) (hw : laplacian G z = 0) :
    ParentSquareOut G R z := by
  unfold Nonfree at hnf
  have hex : ∃ v ∈ frame.child.modifiedDeck.span, z + v ∈ frame.freeH ∪ frame.freeV := by
    by_contra hc
    exact hnf (fun v hv hmem => hc ⟨v, hv, hmem⟩)
  obtain ⟨v, hv, hmem⟩ := hex
  obtain ⟨i, j, rfl⟩ := hv
  have hz : z = (z + frame.child.modifiedDeck.combine i j) - frame.child.modifiedDeck.combine i j := by abel
  rw [hz]
  apply parentSquareOut_translate frame hP hdeck i j
  apply hnative _ hmem
  rw [frame.laplacian_add_lattice hP i j z]
  exact hw

end FLatticePaper.DeckParentSquare
