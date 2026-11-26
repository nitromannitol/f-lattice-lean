import FLatticePaper.Plane.Induction.FaceRows
import FLatticePaper.Plane.Induction.NonfreeHelpers
import FLatticePaper.Plane.Induction.ForcedArrows

/-! # The three face rows with a forced corner (Q33 (1), the rows with a helper corner)

The rows `(0,0)` left, `(0,−1)` bottom and `(1,−1)` right contain one corner that is black or white and nonfree (a helper of
`NonfreeHelpers`). Its arrow is the forced input (`ForcedArrows.forced_to_free_input`: a nonfree white whose input is not nonfree is
forced to that input; the forced edge is retained by `hret`). The other corners are black (quota), free (prescription) or translates of
free sites (`arrow_of_transport`). -/

namespace FLatticePaper.FaceRowsForced

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1NonfreeOut
  FLatticePaper.EndpointRows FLatticePaper.GenericSquare FLatticePaper.FaceRows FLatticePaper.NonfreeHelpers

/-- **The left row at `(0,0)`** (`η = 1`): the square `(−1,0) → (−1,1) → (0,1) → (0,0)`. The corner `(−1,0)` is black; `(−1,1)` is
nonfree (`nonfree_m11_one`), its input `(0,1)` is free and forces it; `(0,1)` has the prescription `(0,−1)`; the root retains `(1,0)`. -/
theorem row_V00_left {frame : ChildFrame} {G : Field} {R : Site → Site → Prop} (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hpres : PrescribedAt frame G 1 R)
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hq : RetainQuota G R)
    (hret : ∀ c i, ForcedEdge G (fun _ _ => False) c i → R c i)
    (F : EndpointFacts frame G) :
    ParentSquareAt G R (0, 0) (-1, 0) (-1, 1) (0, 1) (1, 0) (-1) 0 := by
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hfreeV01 : ¬ Nonfree frame ((0 : ℤ), (1 : ℤ)) :=
    translate_free (zero_mem_span frame) (by rw [add_zero]; exact Set.mem_union_right _ F.fV01)
  have hz : ((0 : ℤ), (0 : ℤ)) ∈ squareCorners (-1) 0 := by simp [squareCorners]
  have h0 : ((-1 : ℤ), (0 : ℤ)) ∈ squareCorners (-1) 0 := by simp [squareCorners]
  have h1 : ((-1 : ℤ), (1 : ℤ)) ∈ squareCorners (-1) 0 := by simp [squareCorners]
  have h2 : ((0 : ℤ), (1 : ℤ)) ∈ squareCorners (-1) 0 := by simp [squareCorners]
  have hcov : ∀ c' ∈ squareCorners (-1) 0, c' ≠ ((0 : ℤ), (0 : ℤ)) →
      c' = ((-1 : ℤ), (0 : ℤ)) ∨ c' = ((-1 : ℤ), (1 : ℤ)) ∨ c' = ((0 : ℤ), (1 : ℤ)) := by
    intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  have d01 : ((-1 : ℤ), (0 : ℤ)) ≠ ((-1 : ℤ), (1 : ℤ)) := by decide
  have d12 : ((-1 : ℤ), (1 : ℤ)) ≠ ((0 : ℤ), (1 : ℤ)) := by decide
  have d02 : ((-1 : ℤ), (0 : ℤ)) ≠ ((0 : ℤ), (1 : ℤ)) := by decide
  have hin0 : ((-1 : ℤ), (0 : ℤ)) = incomingNeg ((0 : ℤ), (0 : ℤ)) ∨
      ((-1 : ℤ), (0 : ℤ)) = incomingPos ((0 : ℤ), (0 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  have e1 : Edge ((-1 : ℤ), (1 : ℤ)) ((-1 : ℤ), (0 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have e2 : Edge ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (1 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have e3 : Edge ((0 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  -- the black corner (−1,0)
  have A0 : laplacian G ((-1 : ℤ), (0 : ℤ)) = 0 → R ((-1 : ℤ), (0 : ℤ)) ((-1 : ℤ), (1 : ℤ)) := fun h => by
    rw [F.bm10] at h
    norm_num at h
  -- the nonfree corner (−1,1): forced to its free input (0,1)
  have A1 : laplacian G ((-1 : ℤ), (1 : ℤ)) = 0 → R ((-1 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ)) := fun h =>
    hret _ _ (FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 (nonfree_m11_one frame) h
      (Or.inr (by simp [incomingPos, EvenSite])) hfreeV01)
  -- the free corner (0,1): prescription (0,−1)
  have A2 : laplacian G ((0 : ℤ), (1 : ℤ)) = 0 → R ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (0 : ℤ)) := fun h => by
    have hA := arrow_of_free_V hpres F.fV01 h
    rw [prescV01] at hA
    have e : ((0 : ℤ), (1 : ℤ)) + ((0 : ℤ), -(1 : ℤ)) = ((0 : ℤ), (0 : ℤ)) := by ext <;> simp
    rwa [e] at hA
  -- the root (0,0): retains (1,0), its prescription
  have ro : R ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) := by
    have hA := arrow_of_free_V hpres F.fV00 F.w00
    rw [prescV00] at hA
    have e : ((0 : ℤ), (0 : ℤ)) + ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (0 : ℤ)) := by ext <;> simp
    rwa [e] at hA
  have hout : ((1 : ℤ), (0 : ℤ)) = incomingNeg ((0 : ℤ), (0 : ℤ)) ∨
      ((1 : ℤ), (0 : ℤ)) = incomingPos ((0 : ℤ), (0 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have hosq : ((1 : ℤ), (0 : ℤ)) ∉ squareCorners (-1) 0 := by simp [squareCorners]
  exact psq_of_arrows_at hbin hq hwu F.w00 hz h0 h1 h2 hcov d01 d12 d02 hin0 e1 e2 e3 A0 A1 A2 hout hosq ro

/-- The prescribed input of the free H site `(dc−1, nc−1)` (the translate of `(−1,−1)` by the kernel) is `(1,0)`. -/
theorem prescH_hPrev {frame : ChildFrame} (η : ℤ) :
    frame.prescribedH η (frame.child.den - 1, frame.child.num - 1) = (1, 0) := by
  obtain ⟨hn1, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  unfold ChildFrame.prescribedH
  have h1 : ((frame.child.den - 1, frame.child.num - 1) : Site) ≠ FLatticePaper.Induction.hFirst := by
    intro h
    simp only [FLatticePaper.Induction.hFirst, Prod.mk.injEq] at h
    omega
  have h2 : ((frame.child.den - 1, frame.child.num - 1) : Site) ≠ frame.hLast := by
    intro h
    simp only [ChildFrame.hLast, Prod.mk.injEq] at h
    omega
  have hev : EvenSite ((frame.child.den - 1, frame.child.num - 1) : Site) := by
    unfold EvenSite
    dsimp only
    omega
  rw [if_neg h1, if_neg h2, if_pos hev]

/-- **The bottom row at `(0,−1)`** (both signs): the square `(0,−2) → (−1,−2) → (−1,−1) → (0,−1)`. The corner `(0,−2)` is black; the
corner `(−1,−2)` is nonfree (`nonfree_m1m2`) and is forced to its free input `(−1,−1)` (a translate of the free `H_prev`); the corner
`(−1,−1)` is the deck translate of `H_prev` (prescription `(1,0)`); the root is the translate of `H_last` (prescription `(0,1)`). -/
theorem row_Vm01_bottom {frame : ChildFrame} {G : Field} {R : Site → Site → Prop} {η : ℤ} (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hpres : PrescribedAt frame G η R)
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u →
      R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    (hq : RetainQuota G R)
    (hret : ∀ c i, ForcedEdge G (fun _ _ => False) c i → R c i)
    (F : EndpointFacts frame G) :
    ParentSquareAt G R (0, -1) (0, -2) (-1, -2) (-1, -1) (0, 0) (-1) (-2) := by
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hcK := combine_one_zero_eq_Kdeck' frame
  have hPrevE : ((-1 : ℤ), (-1 : ℤ)) + Kdeck frame = (frame.child.den - 1, frame.child.num - 1) := by
    unfold Kdeck
    refine Prod.ext ?_ ?_
    · simp
      omega
    · simp
      omega
  have hLastE : ((0 : ℤ), (-1 : ℤ)) + Kdeck frame = frame.hLast := by
    unfold Kdeck ChildFrame.hLast
    refine Prod.ext ?_ ?_
    · simp
    · simp
      ring
  have hLapPrev : laplacian G (frame.child.den - 1, frame.child.num - 1) = 0 := by
    rw [← hPrevE, ← hcK, frame.laplacian_add_lattice hP 1 0]
    exact F.wm11
  have hLapLast : laplacian G frame.hLast = 0 := by
    rw [← hLastE, ← hcK, frame.laplacian_add_lattice hP 1 0]
    exact F.w0m1
  -- the corner (−1,−1): transported prescription (1,0) of H_prev
  have hA1 : R (frame.child.den - 1, frame.child.num - 1) ((frame.child.den - 1, frame.child.num - 1) + (1, 0)) := by
    have hA := arrow_of_free_H hpres F.fHP hLapPrev
    rwa [prescH_hPrev] at hA
  have hT1 := arrow_of_transport (i := 1) (j := 0) hdeck hA1
  have eP : (frame.child.den - 1, frame.child.num - 1) - frame.child.modifiedDeck.combine 1 0 = ((-1 : ℤ), (-1 : ℤ)) := by
    rw [hcK, ← hPrevE]
    ext <;> simp
  rw [eP] at hT1
  have eP2 : ((-1 : ℤ), (-1 : ℤ)) + ((1 : ℤ), (0 : ℤ)) = ((0 : ℤ), (-1 : ℤ)) := by ext <;> simp
  rw [eP2] at hT1
  -- the root (0,−1): transported prescription (0,1) of H_last
  have hA2 : R frame.hLast (frame.hLast + (0, 1)) := by
    have hA := arrow_of_free_H hpres F.fHL hLapLast
    rwa [prescH_hLast] at hA
  have hT2 := arrow_of_transport (i := 1) (j := 0) hdeck hA2
  have eL : frame.hLast - frame.child.modifiedDeck.combine 1 0 = ((0 : ℤ), (-1 : ℤ)) := by
    rw [hcK, ← hLastE]
    ext <;> simp
  rw [eL] at hT2
  have eL2 : ((0 : ℤ), (-1 : ℤ)) + ((0 : ℤ), (1 : ℤ)) = ((0 : ℤ), (0 : ℤ)) := by ext <;> simp
  rw [eL2] at hT2
  -- the forced corner (−1,−2): forced to its free input (−1,−1)
  have hfreePrev : ¬ Nonfree frame ((-1 : ℤ), (-1 : ℤ)) :=
    translate_free (Kdeck_mem_span frame) (by rw [hPrevE]; exact Set.mem_union_left _ F.fHP)
  have A1 : laplacian G ((-1 : ℤ), (-2 : ℤ)) = 0 → R ((-1 : ℤ), (-2 : ℤ)) ((-1 : ℤ), (-1 : ℤ)) := fun h =>
    hret _ _ (FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 (nonfree_m1m2 frame) h
      (Or.inr (by simp [incomingPos, EvenSite])) hfreePrev)
  have A0 : laplacian G ((0 : ℤ), (-2 : ℤ)) = 0 → R ((0 : ℤ), (-2 : ℤ)) ((-1 : ℤ), (-2 : ℤ)) := fun h => by
    rw [F.b0m2] at h
    norm_num at h
  have A2 : laplacian G ((-1 : ℤ), (-1 : ℤ)) = 0 → R ((-1 : ℤ), (-1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) := fun _ => hT1
  have hz : ((0 : ℤ), (-1 : ℤ)) ∈ squareCorners (-1) (-2) := by simp [squareCorners]
  have h0 : ((0 : ℤ), (-2 : ℤ)) ∈ squareCorners (-1) (-2) := by simp [squareCorners]
  have h1 : ((-1 : ℤ), (-2 : ℤ)) ∈ squareCorners (-1) (-2) := by simp [squareCorners]
  have h2 : ((-1 : ℤ), (-1 : ℤ)) ∈ squareCorners (-1) (-2) := by simp [squareCorners]
  have hcov : ∀ c' ∈ squareCorners (-1) (-2), c' ≠ ((0 : ℤ), (-1 : ℤ)) →
      c' = ((0 : ℤ), (-2 : ℤ)) ∨ c' = ((-1 : ℤ), (-2 : ℤ)) ∨ c' = ((-1 : ℤ), (-1 : ℤ)) := by
    intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  have d01 : ((0 : ℤ), (-2 : ℤ)) ≠ ((-1 : ℤ), (-2 : ℤ)) := by decide
  have d12 : ((-1 : ℤ), (-2 : ℤ)) ≠ ((-1 : ℤ), (-1 : ℤ)) := by decide
  have d02 : ((0 : ℤ), (-2 : ℤ)) ≠ ((-1 : ℤ), (-1 : ℤ)) := by decide
  have hin0 : ((0 : ℤ), (-2 : ℤ)) = incomingNeg ((0 : ℤ), (-1 : ℤ)) ∨
      ((0 : ℤ), (-2 : ℤ)) = incomingPos ((0 : ℤ), (-1 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  have e1 : Edge ((-1 : ℤ), (-2 : ℤ)) ((0 : ℤ), (-2 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  have e2 : Edge ((-1 : ℤ), (-1 : ℤ)) ((-1 : ℤ), (-2 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have e3 : Edge ((0 : ℤ), (-1 : ℤ)) ((-1 : ℤ), (-1 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have hout : ((0 : ℤ), (0 : ℤ)) = incomingNeg ((0 : ℤ), (-1 : ℤ)) ∨
      ((0 : ℤ), (0 : ℤ)) = incomingPos ((0 : ℤ), (-1 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have hosq : ((0 : ℤ), (0 : ℤ)) ∉ squareCorners (-1) (-2) := by simp [squareCorners]
  have ro : R ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (0 : ℤ)) := hT2
  exact psq_of_arrows_at hbin hq hwu F.w0m1 hz h0 h1 h2 hcov d01 d12 d02 hin0 e1 e2 e3 A0 A1 A2 hout hosq ro

/-- **The right row at `(1,−1)`** (`η = −1`): the square `(2,−1) → (2,−2) → (1,−2) → (1,−1)`. The corner `(2,−1)` is black; `(2,−2)`
is nonfree (`nonfree_2m2`) and is forced to its free input `(1,−2)` (a translate of the free `V_prev`, with prescription `(0,1)`); the root is
the translate of `V_last` (prescription `(−1,0)`). -/
theorem row_1m1_right {frame : ChildFrame} {G : Field} {R : Site → Site → Prop} (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hpres : PrescribedAt frame G (-1) R)
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u →
      R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    (hq : RetainQuota G R)
    (hret : ∀ c i, ForcedEdge G (fun _ _ => False) c i → R c i)
    (F : EndpointFacts frame G) :
    ParentSquareAt G R (1, -1) (2, -1) (2, -2) (1, -2) (0, -1) 1 (-2) := by
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hcV := combine_zero_one_eq_Vdeck' frame
  -- the corner (1,−2): transported prescription (0,1) of V_prev
  have hvP : laplacian G (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) = 0 := by
    have e : ((frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) : Site) =
        ((1 : ℤ), (-2 : ℤ)) + frame.child.modifiedDeck.combine 0 1 := by
      rw [hcV]
      unfold Vdeck
      ext <;> simp <;> ring
    rw [e, frame.laplacian_add_lattice hP 0 1 ((1 : ℤ), (-2 : ℤ))]
    exact F.w1m2
  have hA1 := arrow_of_free_V hpres F.fVP hvP
  rw [prescV_vPrev] at hA1
  have hT1 := arrow_of_transport (i := 0) (j := 1) hdeck hA1
  have eV : (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) -
      frame.child.modifiedDeck.combine 0 1 = ((1 : ℤ), (-2 : ℤ)) := by
    rw [hcV]
    unfold Vdeck
    ext <;> simp
  rw [eV] at hT1
  have eV2 : ((1 : ℤ), (-2 : ℤ)) + ((0 : ℤ), -(-1 : ℤ)) = ((1 : ℤ), (-1 : ℤ)) := by ext <;> simp
  rw [eV2] at hT1
  -- the root (1,−1): transported prescription (−1,0) of V_last
  have hvL : laplacian G frame.vLast = 0 := by
    have e : frame.vLast = ((1 : ℤ), (-1 : ℤ)) + frame.child.modifiedDeck.combine 0 1 := by
      rw [hcV]
      unfold Vdeck ChildFrame.vLast
      ext <;> simp <;> ring
    rw [e, frame.laplacian_add_lattice hP 0 1 ((1 : ℤ), (-1 : ℤ))]
    exact F.w1m1
  have hA2 := arrow_of_free_V hpres F.fVL hvL
  rw [prescV_vLast] at hA2
  have hT2 := arrow_of_transport (i := 0) (j := 1) hdeck hA2
  have eW : frame.vLast - frame.child.modifiedDeck.combine 0 1 = ((1 : ℤ), (-1 : ℤ)) := by
    rw [hcV]
    unfold Vdeck ChildFrame.vLast
    ext <;> simp
  rw [eW] at hT2
  have eW2 : ((1 : ℤ), (-1 : ℤ)) + ((-1 : ℤ), (0 : ℤ)) = ((0 : ℤ), (-1 : ℤ)) := by ext <;> simp
  rw [eW2] at hT2
  -- the forced corner (2,−2): forced to its free input (1,−2)
  have hfreeVP : ¬ Nonfree frame ((1 : ℤ), (-2 : ℤ)) :=
    translate_free (Vdeck_mem_span frame) (by
      have e : ((1 : ℤ), (-2 : ℤ)) + Vdeck frame =
          (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) := by
        unfold Vdeck
        ext <;> simp <;> ring
      rw [e]
      exact Set.mem_union_right _ F.fVP)
  have A1 : laplacian G ((2 : ℤ), (-2 : ℤ)) = 0 → R ((2 : ℤ), (-2 : ℤ)) ((1 : ℤ), (-2 : ℤ)) := fun h =>
    hret _ _ (FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 (nonfree_2m2 frame) h
      (Or.inl (by simp [incomingNeg, EvenSite])) hfreeVP)
  have A0 : laplacian G ((2 : ℤ), (-1 : ℤ)) = 0 → R ((2 : ℤ), (-1 : ℤ)) ((2 : ℤ), (-2 : ℤ)) := fun h => by
    rw [F.b2m1] at h
    norm_num at h
  have A2 : laplacian G ((1 : ℤ), (-2 : ℤ)) = 0 → R ((1 : ℤ), (-2 : ℤ)) ((1 : ℤ), (-1 : ℤ)) := fun _ => hT1
  have hz : ((1 : ℤ), (-1 : ℤ)) ∈ squareCorners 1 (-2) := by simp [squareCorners]
  have h0 : ((2 : ℤ), (-1 : ℤ)) ∈ squareCorners 1 (-2) := by simp [squareCorners]
  have h1 : ((2 : ℤ), (-2 : ℤ)) ∈ squareCorners 1 (-2) := by simp [squareCorners]
  have h2 : ((1 : ℤ), (-2 : ℤ)) ∈ squareCorners 1 (-2) := by simp [squareCorners]
  have hcov : ∀ c' ∈ squareCorners 1 (-2), c' ≠ ((1 : ℤ), (-1 : ℤ)) →
      c' = ((2 : ℤ), (-1 : ℤ)) ∨ c' = ((2 : ℤ), (-2 : ℤ)) ∨ c' = ((1 : ℤ), (-2 : ℤ)) := by
    intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  have d01 : ((2 : ℤ), (-1 : ℤ)) ≠ ((2 : ℤ), (-2 : ℤ)) := by decide
  have d12 : ((2 : ℤ), (-2 : ℤ)) ≠ ((1 : ℤ), (-2 : ℤ)) := by decide
  have d02 : ((2 : ℤ), (-1 : ℤ)) ≠ ((1 : ℤ), (-2 : ℤ)) := by decide
  have hin0 : ((2 : ℤ), (-1 : ℤ)) = incomingNeg ((1 : ℤ), (-1 : ℤ)) ∨
      ((2 : ℤ), (-1 : ℤ)) = incomingPos ((1 : ℤ), (-1 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have e1 : Edge ((2 : ℤ), (-2 : ℤ)) ((2 : ℤ), (-1 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  have e2 : Edge ((1 : ℤ), (-2 : ℤ)) ((2 : ℤ), (-2 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  have e3 : Edge ((1 : ℤ), (-1 : ℤ)) ((1 : ℤ), (-2 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have hout : ((0 : ℤ), (-1 : ℤ)) = incomingNeg ((1 : ℤ), (-1 : ℤ)) ∨
      ((0 : ℤ), (-1 : ℤ)) = incomingPos ((1 : ℤ), (-1 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  have hosq : ((0 : ℤ), (-1 : ℤ)) ∉ squareCorners 1 (-2) := by simp [squareCorners]
  have ro : R ((1 : ℤ), (-1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) := hT2
  exact psq_of_arrows_at hbin hq hwu F.w1m1 hz h0 h1 h2 hcov d01 d12 d02 hin0 e1 e2 e3 A0 A1 A2 hout hosq ro

end FLatticePaper.FaceRowsForced
