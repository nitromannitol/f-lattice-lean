import FLatticePaper.Plane.Induction.FaceRowsForced
import FLatticePaper.Plane.Induction.FreeCutSucc
import FLatticePaper.Plane.Induction.FreeHWhite
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.BothFreeGrades

/-! # The bottom row at `V_0` (the UR square at `(0,0)`)

The square `squareCorners (-1) (-1)` at the root `V_0 = (0,0)`: the corner `(-1,0)` is black (`EndpointFacts.bm10`), `(-1,-1)` is a translate
of the free H point `f = (d-1, n-1)` by `-K` (its prescription east lands on `(0,-1)`), and `(0,-1)` is a translate of `H_last` by `-K`
(its prescription north lands on `V_0`). The root keeps its prescription east, `(1,0)`, which leaves the square. -/

namespace FLatticePaper.BottomV0Row

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1NonfreeOut
  FLatticePaper.EndpointRows FLatticePaper.GenericSquare FLatticePaper.FaceRows FLatticePaper.FaceRowsForced

/-- The corner `(d-1, n-1)` of the child rectangle is a free H point: its grade `t = d - n` is an even H value, and the point below it,
`(d-1, n-2)`, is odd with `t = 2d - n > d`, outside the closed polygon. -/
theorem mem_freeH_diag (frame : ChildFrame) :
    (frame.child.den - 1, frame.child.num - 1) ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hev : frame.child.Even := frame.child_even
  unfold Fraction.Even at hev
  rw [FreeCutSucc.mem_freeH_iff]
  have hE : EvenSite (frame.child.den - 1, frame.child.num - 1) := by
    unfold EvenSite; dsimp only; omega
  have hO : ¬ EvenSite (frame.child.den - 1, frame.child.num - 1 - 1) := by
    unfold EvenSite; dsimp only; omega
  have ht : frame.tGrade (frame.child.den - 1, frame.child.num - 1) = frame.child.den - frame.child.num := by
    unfold ChildFrame.tGrade; dsimp only; ring
  refine ⟨?_, ?_, ?_⟩
  · unfold FLatticePaper.W1.closedRect
    rw [if_pos hE]
    unfold FLatticePaper.W1.w1t FLatticePaper.W1.w1s FLatticePaper.W1.w1T
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · unfold FLatticePaper.W1.closedRect
    rw [if_neg hO]
    unfold FLatticePaper.W1.w1t
    dsimp only
    intro h
    nlinarith [h.2.1]
  · rw [ht]
    unfold ChildFrame.hSpectrum
    left
    refine ⟨?_, ?_, ?_⟩ <;> omega

/-- **The bottom row at `V_0`**: the UR square `squareCorners (-1) (-1)` at the root `(0,0)`, with the outward input `(1,0)`, the black
corner `(-1,0)`, and the free corners `(-1,-1)` and `(0,-1)` (their arrows are the deck translates by `-K` of the free H point
`(d-1, n-1)` and of `H_last`). -/
theorem row_V00_bottom {frame : ChildFrame} {G : Field} {R : Site → Site → Prop} {η : ℤ} (hP : frame.Packet G)
    (hpres : PrescribedAt frame G η R)
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u →
      R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    (hq : RetainQuota G R) (F : EndpointFacts frame G) :
    ParentSquareAt G R (0, 0) (-1, 0) (-1, -1) (0, -1) (1, 0) (-1) (-1) := by
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hK : frame.child.modifiedDeck.combine 1 0 = Kdeck frame := FLatticePaper.FaceRows.combine_one_zero_eq_Kdeck' frame
  -- the free H corner f = (d-1, n-1), white, with prescription east
  have hfree : (frame.child.den - 1, frame.child.num - 1) ∈ frame.freeH := mem_freeH_diag frame
  have hlapf : laplacian G (frame.child.den - 1, frame.child.num - 1) = 0 :=
    FLatticePaper.Induction.laplacian_eq_zero_of_freeH frame hP.strips hfree
  have hEf : EvenSite (frame.child.den - 1, frame.child.num - 1) := by
    have hev : frame.child.Even := frame.child_even
    unfold Fraction.Even at hev
    unfold EvenSite; dsimp only; omega
  have hpf : frame.prescribedH η (frame.child.den - 1, frame.child.num - 1) = (1, 0) :=
    FLatticePaper.BothFreeGrades.prescribedH_even_east frame η _ hEf
  have arrowf : R (frame.child.den - 1, frame.child.num - 1) ((frame.child.den - 1, frame.child.num - 1) + (1, 0)) := by
    have h := arrow_of_free_H hpres hfree hlapf
    rw [hpf] at h
    exact h
  have hT1 : R ((frame.child.den - 1, frame.child.num - 1) - Kdeck frame)
      ((frame.child.den - 1, frame.child.num - 1) + (1, 0) - Kdeck frame) := by
    have h := hdeck 1 0 _ _ arrowf
    rw [hK] at h
    exact h
  -- the H_last arrow (north), transported by -K
  have hLastArrow : R frame.hLast (frame.hLast + (0, 1)) := by
    have h := arrow_of_free_H hpres F.fHL F.wHL
    rw [prescH_hLast η] at h
    exact h
  have hT2 : R (frame.hLast - Kdeck frame) (frame.hLast + (0, 1) - Kdeck frame) := by
    have h := hdeck 1 0 _ _ hLastArrow
    rw [hK] at h
    exact h
  have e1 : (frame.child.den - 1, frame.child.num - 1) - Kdeck frame = (-1, -1) := by
    unfold Kdeck; ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
  have e2 : (frame.child.den - 1, frame.child.num - 1) + (1, 0) - Kdeck frame = (0, -1) := by
    unfold Kdeck; ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
  have e3 : frame.hLast - Kdeck frame = (0, -1) := by
    unfold ChildFrame.hLast Kdeck; ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
  have e4 : frame.hLast + (0, 1) - Kdeck frame = (0, 0) := by
    unfold ChildFrame.hLast Kdeck; ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
  rw [e1, e2] at hT1
  rw [e3, e4] at hT2
  have hz : ((0 : ℤ), (0 : ℤ)) ∈ squareCorners (-1) (-1) := by simp [squareCorners]
  have h0 : ((-1 : ℤ), (0 : ℤ)) ∈ squareCorners (-1) (-1) := by simp [squareCorners]
  have h1 : ((-1 : ℤ), (-1 : ℤ)) ∈ squareCorners (-1) (-1) := by simp [squareCorners]
  have h2 : ((0 : ℤ), (-1 : ℤ)) ∈ squareCorners (-1) (-1) := by simp [squareCorners]
  have hcov : ∀ c' ∈ squareCorners (-1) (-1), c' ≠ ((0 : ℤ), (0 : ℤ)) →
      c' = ((-1 : ℤ), (0 : ℤ)) ∨ c' = ((-1 : ℤ), (-1 : ℤ)) ∨ c' = ((0 : ℤ), (-1 : ℤ)) := by
    intro c' hc' hne
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · exact absurd rfl hne
  have d01 : ((-1 : ℤ), (0 : ℤ)) ≠ ((-1 : ℤ), (-1 : ℤ)) := by decide
  have d12 : ((-1 : ℤ), (-1 : ℤ)) ≠ ((0 : ℤ), (-1 : ℤ)) := by decide
  have d02 : ((-1 : ℤ), (0 : ℤ)) ≠ ((0 : ℤ), (-1 : ℤ)) := by decide
  have hin0 : ((-1 : ℤ), (0 : ℤ)) = incomingNeg ((0 : ℤ), (0 : ℤ)) ∨
      ((-1 : ℤ), (0 : ℤ)) = incomingPos ((0 : ℤ), (0 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  have ee1 : Edge ((-1 : ℤ), (-1 : ℤ)) ((-1 : ℤ), (0 : ℤ)) := Or.inl (by simp [incomingNeg, EvenSite])
  have ee2 : Edge ((0 : ℤ), (-1 : ℤ)) ((-1 : ℤ), (-1 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have ee3 : Edge ((0 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have A0 : laplacian G ((-1 : ℤ), (0 : ℤ)) = 0 → R ((-1 : ℤ), (0 : ℤ)) ((-1 : ℤ), (-1 : ℤ)) := fun h => by
    rw [F.bm10] at h; norm_num at h
  have A1 : laplacian G ((-1 : ℤ), (-1 : ℤ)) = 0 → R ((-1 : ℤ), (-1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) := fun _ => hT1
  have A2 : laplacian G ((0 : ℤ), (-1 : ℤ)) = 0 → R ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (0 : ℤ)) := fun _ => hT2
  have hout : ((1 : ℤ), (0 : ℤ)) = incomingNeg ((0 : ℤ), (0 : ℤ)) ∨
      ((1 : ℤ), (0 : ℤ)) = incomingPos ((0 : ℤ), (0 : ℤ)) := Or.inr (by simp [incomingPos, EvenSite])
  have hosq : ((1 : ℤ), (0 : ℤ)) ∉ squareCorners (-1) (-1) := by simp [squareCorners]
  have ro : R ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) := by
    have h := arrow_of_free_V hpres F.fV00 F.w00
    have hv : frame.prescribedV η ((0 : ℤ), (0 : ℤ)) = (1, 0) := frame.prescribedV_vFirst η
    rw [hv] at h
    simpa using h
  exact psq_of_arrows_at hbin hq hwu F.w00 hz h0 h1 h2 hcov d01 d12 d02 hin0 ee1 ee2 ee3 A0 A1 A2 hout hosq ro

end FLatticePaper.BottomV0Row
