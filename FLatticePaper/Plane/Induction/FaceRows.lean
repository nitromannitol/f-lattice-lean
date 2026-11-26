import FLatticePaper.Plane.Induction.EndpointRows
import FLatticePaper.Plane.Induction.GenericSquare

/-! # The face rows of the collar, in the conjugate frame (Q33 (1))

The physical face table of Q33 is mapped by `zTurn` into the conjugate frame; the four conjugate root classes are `(1,0)`, `(0,0)`,
`(0,−1)`, `(1,−1)`. Each row is a unit square at its root, with corners `q0 → q1 → q2 → root` (`ParentSquareOut`). The rows whose
corners are black, free or a deck translate of a free site are instances of the generic square `GenericSquare.psq_of_arrows`:

* `row_H10_left` (`η = 1`, the left face): the corners `(1,1)` (black), `(0,1)`, `(0,0)` (free), root `(1,0)` (free);
* `row_Vm1_right` (`η = −1`, the right face): the corners `(0,−2)` (black), `(1,−2)`, `(1,−1)` (translates of the free
  `V_prev`, `V_last`), root `(0,−1)` (a translate of the free `H_last`).

The remaining faces have a corner that is black or nonfree depending on the word; they need the forced arrow of that corner. -/

namespace FLatticePaper.FaceRows

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1NonfreeOut
  FLatticePaper.EndpointRows FLatticePaper.GenericSquare

/-- The prescribed input of `V_prev = (n−d+1, n+d−2)` (an odd internal free V site) is `(0, −η)`. -/
theorem prescV_vPrev {frame : ChildFrame} (η : ℤ) :
    frame.prescribedV η (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) = (0, -η) := by
  obtain ⟨hn1, hnd, hdn, hd3, -⟩ := frame.child_facts
  apply FLatticePaper.Induction.CanonicalDirections.prescribedV_internal_odd frame η
  · intro h
    simp only [FLatticePaper.Induction.vFirst, Prod.mk.injEq] at h
    omega
  · intro h
    simp only [ChildFrame.vLast, Prod.mk.injEq] at h
    omega
  · unfold EvenSite
    dsimp only
    omega

/-- The prescribed input of `V_last` is `(η, 0)`. -/
theorem prescV_vLast {frame : ChildFrame} (η : ℤ) : frame.prescribedV η frame.vLast = (η, 0) := by
  obtain ⟨hn1, hnd, hdn, hd3, -⟩ := frame.child_facts
  unfold ChildFrame.prescribedV
  have h1 : frame.vLast ≠ FLatticePaper.Induction.vFirst := by
    intro h
    simp only [ChildFrame.vLast, FLatticePaper.Induction.vFirst, Prod.mk.injEq] at h
    omega
  rw [if_neg h1, if_pos rfl]

/-- The prescribed input of `H_last` is `(0, 1)`. -/
theorem prescH_hLast {frame : ChildFrame} (η : ℤ) : frame.prescribedH η frame.hLast = (0, 1) := by
  obtain ⟨hn1, hnd, hdn, hd3, -⟩ := frame.child_facts
  unfold ChildFrame.prescribedH
  have h1 : frame.hLast ≠ FLatticePaper.Induction.hFirst := by
    intro h
    simp only [ChildFrame.hLast, FLatticePaper.Induction.hFirst, Prod.mk.injEq] at h
    omega
  rw [if_neg h1, if_pos rfl]

/-- **The left row at the root `(1,0)`** (`η = 1`): the square `(1,1) → (0,1) → (0,0) → (1,0)`. The corner `(1,1)` is black
(`b11`), the others are free with their prescriptions. -/
theorem row_H10_left {frame : ChildFrame} {G : Field} {R : Site → Site → Prop} (hP : frame.Packet G)
    (hpres : PrescribedAt frame G 1 R)
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hq : RetainQuota G R) (F : EndpointFacts frame G) :
    ParentSquareAt G R (1, 0) (1, 1) (0, 1) (0, 0) (1, -1) 0 0 := by
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hz : ((1 : ℤ), (0 : ℤ)) ∈ squareCorners 0 0 := by simp [squareCorners]
  have h0 : ((1 : ℤ), (1 : ℤ)) ∈ squareCorners 0 0 := by simp [squareCorners]
  have h1 : ((0 : ℤ), (1 : ℤ)) ∈ squareCorners 0 0 := by simp [squareCorners]
  have h2 : ((0 : ℤ), (0 : ℤ)) ∈ squareCorners 0 0 := by simp [squareCorners]
  have hcov : ∀ c' ∈ squareCorners 0 0, c' ≠ ((1 : ℤ), (0 : ℤ)) →
      c' = ((1 : ℤ), (1 : ℤ)) ∨ c' = ((0 : ℤ), (1 : ℤ)) ∨ c' = ((0 : ℤ), (0 : ℤ)) := by
    intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  have d01 : ((1 : ℤ), (1 : ℤ)) ≠ ((0 : ℤ), (1 : ℤ)) := by decide
  have d12 : ((0 : ℤ), (1 : ℤ)) ≠ ((0 : ℤ), (0 : ℤ)) := by decide
  have d02 : ((1 : ℤ), (1 : ℤ)) ≠ ((0 : ℤ), (0 : ℤ)) := by decide
  have hin0 : ((1 : ℤ), (1 : ℤ)) = incomingNeg ((1 : ℤ), (0 : ℤ)) ∨
      ((1 : ℤ), (1 : ℤ)) = incomingPos ((1 : ℤ), (0 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have e1 : Edge ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (1 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  have e2 : Edge ((0 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  have e3 : Edge ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (0 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  -- the black corner (1,1): its arrow is the quota
  have A0 : laplacian G ((1 : ℤ), (1 : ℤ)) = 0 → R ((1 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ)) := fun h => by
    rw [F.b11] at h
    norm_num at h
  -- the free corner (0,1): prescription (0,−1)
  have A1 : laplacian G ((0 : ℤ), (1 : ℤ)) = 0 → R ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (0 : ℤ)) := fun h => by
    have hA := arrow_of_free_V hpres F.fV01 h
    rw [prescV01] at hA
    have e : ((0 : ℤ), (1 : ℤ)) + ((0 : ℤ), -(1 : ℤ)) = ((0 : ℤ), (0 : ℤ)) := by
      ext <;> simp
    rwa [e] at hA
  -- the free corner (0,0): prescription (1,0)
  have A2 : laplacian G ((0 : ℤ), (0 : ℤ)) = 0 → R ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) := fun h => by
    have hA := arrow_of_free_V hpres F.fV00 h
    rw [prescV00] at hA
    have e : ((0 : ℤ), (0 : ℤ)) + ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (0 : ℤ)) := by ext <;> simp
    rwa [e] at hA
  -- the root (1,0): retains (1,−1), its prescription (0,−1)
  have ro : R ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (-1 : ℤ)) := by
    have hA := arrow_of_free_H hpres F.fH10 F.w10
    have hpr : frame.prescribedH 1 ((1 : ℤ), (0 : ℤ)) = ((0 : ℤ), (-1 : ℤ)) := by
      unfold ChildFrame.prescribedH
      simp [FLatticePaper.Induction.hFirst]
    rw [hpr] at hA
    have e : ((1 : ℤ), (0 : ℤ)) + ((0 : ℤ), (-1 : ℤ)) = ((1 : ℤ), (-1 : ℤ)) := by ext <;> simp
    rwa [e] at hA
  have hout : ((1 : ℤ), (-1 : ℤ)) = incomingNeg ((1 : ℤ), (0 : ℤ)) ∨
      ((1 : ℤ), (-1 : ℤ)) = incomingPos ((1 : ℤ), (0 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  have hosq : ((1 : ℤ), (-1 : ℤ)) ∉ squareCorners 0 0 := by
    simp [squareCorners]
  exact psq_of_arrows_at hbin hq hwu F.w10 hz h0 h1 h2 hcov d01 d12 d02 hin0 e1 e2 e3 A0 A1 A2 hout hosq ro

/-- The deck vector `combine 0 1` is the transverse `Vdeck`. -/
theorem combine_zero_one_eq_Vdeck' (frame : ChildFrame) :
    frame.child.modifiedDeck.combine 0 1 = Vdeck frame := by
  unfold PeriodDeck.combine Vdeck
  rw [frame.child_modifiedDeck_transverse]
  simp

/-- The deck vector `combine 1 0` is the kernel `Kdeck`. -/
theorem combine_one_zero_eq_Kdeck' (frame : ChildFrame) :
    frame.child.modifiedDeck.combine 1 0 = Kdeck frame := by
  unfold PeriodDeck.combine Kdeck
  rw [frame.kernel_coords]
  simp

/-- **The right row at the root `(0,−1)`** (`η = −1`): the square `(0,−2) → (1,−2) → (1,−1) → (0,−1)`. The corner `(0,−2)` is black
(`b0m2`); the corners `(1,−2)`, `(1,−1)` and the root are translates of the free `V_prev`, `V_last`, `H_last` by the deck, so their arrows
are the transported prescriptions (`arrow_of_transport`, with the equivariance `hdeck` of the policy). -/
theorem row_Vm1_right {frame : ChildFrame} {G : Field} {R : Site → Site → Prop} (hP : frame.Packet G)
    (hpres : PrescribedAt frame G (-1) R)
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u →
      R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    (hq : RetainQuota G R) (F : EndpointFacts frame G) :
    ParentSquareAt G R (0, -1) (0, -2) (1, -2) (1, -1) (0, 0) 0 (-2) := by
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hcV := combine_zero_one_eq_Vdeck' frame
  have hcK := combine_one_zero_eq_Kdeck' frame
  -- the translates of the free points are white
  have hvP : laplacian G (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) = 0 := by
    have e : ((frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) : Site) =
        ((1 : ℤ), (-2 : ℤ)) + frame.child.modifiedDeck.combine 0 1 := by
      rw [hcV]
      unfold Vdeck
      ext <;> simp <;> ring
    rw [e, frame.laplacian_add_lattice hP 0 1 ((1 : ℤ), (-2 : ℤ))]
    exact F.w1m2
  have hvL : laplacian G frame.vLast = 0 := by
    have e : frame.vLast = ((1 : ℤ), (-1 : ℤ)) + frame.child.modifiedDeck.combine 0 1 := by
      rw [hcV]
      unfold Vdeck ChildFrame.vLast
      ext <;> simp <;> ring
    rw [e, frame.laplacian_add_lattice hP 0 1 ((1 : ℤ), (-1 : ℤ))]
    exact F.w1m1
  have hhL : laplacian G frame.hLast = 0 := by
    have e : frame.hLast = ((0 : ℤ), (-1 : ℤ)) + frame.child.modifiedDeck.combine 1 0 := by
      rw [hcK]
      unfold Kdeck ChildFrame.hLast
      exact Prod.ext (by simp) (by simp; omega)
    rw [e, frame.laplacian_add_lattice hP 1 0 ((0 : ℤ), (-1 : ℤ))]
    exact F.w0m1
  have hz : ((0 : ℤ), (-1 : ℤ)) ∈ squareCorners 0 (-2) := by simp [squareCorners]
  have h0 : ((0 : ℤ), (-2 : ℤ)) ∈ squareCorners 0 (-2) := by simp [squareCorners]
  have h1 : ((1 : ℤ), (-2 : ℤ)) ∈ squareCorners 0 (-2) := by simp [squareCorners]
  have h2 : ((1 : ℤ), (-1 : ℤ)) ∈ squareCorners 0 (-2) := by simp [squareCorners]
  have hcov : ∀ c' ∈ squareCorners 0 (-2), c' ≠ ((0 : ℤ), (-1 : ℤ)) →
      c' = ((0 : ℤ), (-2 : ℤ)) ∨ c' = ((1 : ℤ), (-2 : ℤ)) ∨ c' = ((1 : ℤ), (-1 : ℤ)) := by
    intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  have d01 : ((0 : ℤ), (-2 : ℤ)) ≠ ((1 : ℤ), (-2 : ℤ)) := by decide
  have d12 : ((1 : ℤ), (-2 : ℤ)) ≠ ((1 : ℤ), (-1 : ℤ)) := by decide
  have d02 : ((0 : ℤ), (-2 : ℤ)) ≠ ((1 : ℤ), (-1 : ℤ)) := by decide
  have hin0 : ((0 : ℤ), (-2 : ℤ)) = incomingNeg ((0 : ℤ), (-1 : ℤ)) ∨
      ((0 : ℤ), (-2 : ℤ)) = incomingPos ((0 : ℤ), (-1 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  have e1 : Edge ((1 : ℤ), (-2 : ℤ)) ((0 : ℤ), (-2 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have e2 : Edge ((1 : ℤ), (-1 : ℤ)) ((1 : ℤ), (-2 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have e3 : Edge ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (-1 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  -- the black corner (0,−2)
  have A0 : laplacian G ((0 : ℤ), (-2 : ℤ)) = 0 → R ((0 : ℤ), (-2 : ℤ)) ((1 : ℤ), (-2 : ℤ)) := fun h => by
    rw [F.b0m2] at h
    norm_num at h
  -- the translate of V_prev: the arrow (1,−2) → (1,−1)
  have A1 : laplacian G ((1 : ℤ), (-2 : ℤ)) = 0 → R ((1 : ℤ), (-2 : ℤ)) ((1 : ℤ), (-1 : ℤ)) := fun _ => by
    have hA := arrow_of_free_V hpres F.fVP hvP
    rw [prescV_vPrev] at hA
    have hT := arrow_of_transport (i := 0) (j := 1) hdeck hA
    rw [hcV] at hT
    have e3' : (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) - Vdeck frame =
        ((1 : ℤ), (-2 : ℤ)) := by
      unfold Vdeck
      ext <;> simp
    rw [e3'] at hT
    have e4 : ((1 : ℤ), (-2 : ℤ)) + ((0 : ℤ), -(-1 : ℤ)) = ((1 : ℤ), (-1 : ℤ)) := by ext <;> simp
    rwa [e4] at hT
  -- the translate of V_last: the arrow (1,−1) → (0,−1)
  have A2 : laplacian G ((1 : ℤ), (-1 : ℤ)) = 0 → R ((1 : ℤ), (-1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) := fun _ => by
    have hA := arrow_of_free_V hpres F.fVL hvL
    rw [prescV_vLast] at hA
    have hT := arrow_of_transport (i := 0) (j := 1) hdeck hA
    rw [hcV] at hT
    have e5 : frame.vLast - Vdeck frame = ((1 : ℤ), (-1 : ℤ)) := by
      unfold Vdeck ChildFrame.vLast
      ext <;> simp
    rw [e5] at hT
    have e6 : ((1 : ℤ), (-1 : ℤ)) + ((-1 : ℤ), (0 : ℤ)) = ((0 : ℤ), (-1 : ℤ)) := by ext <;> simp
    rwa [e6] at hT
  -- the translate of H_last: the root retains (0,0)
  have ro : R ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (0 : ℤ)) := by
    have hA := arrow_of_free_H hpres F.fHL hhL
    rw [prescH_hLast] at hA
    have hT := arrow_of_transport (i := 1) (j := 0) hdeck hA
    rw [hcK] at hT
    have e7 : frame.hLast - Kdeck frame = ((0 : ℤ), (-1 : ℤ)) := by
      unfold Kdeck ChildFrame.hLast
      ext <;> simp
    rw [e7] at hT
    have e8 : ((0 : ℤ), (-1 : ℤ)) + ((0 : ℤ), (1 : ℤ)) = ((0 : ℤ), (0 : ℤ)) := by ext <;> simp
    rwa [e8] at hT
  have hout : ((0 : ℤ), (0 : ℤ)) = incomingNeg ((0 : ℤ), (-1 : ℤ)) ∨
      ((0 : ℤ), (0 : ℤ)) = incomingPos ((0 : ℤ), (-1 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have hosq : ((0 : ℤ), (0 : ℤ)) ∉ squareCorners 0 (-2) := by simp [squareCorners]
  exact psq_of_arrows_at hbin hq hwu F.w0m1 hz h0 h1 h2 hcov d01 d12 d02 hin0 e1 e2 e3 A0 A1 A2 hout hosq ro

end FLatticePaper.FaceRows
