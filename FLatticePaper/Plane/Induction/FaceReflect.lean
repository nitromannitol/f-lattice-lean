import FLatticePaper.Plane.Induction.FaceWitness
import FLatticePaper.Plane.Induction.CollarTop
import FLatticePaper.Plane.Induction.FreeCutPred

/-! # The reflection of the witnesses through the centre, and the four-way witness split of a collar centre

The centre `R = (n+1, 2n+d-1)` satisfies `R = vLast + K` (`vLast = (n-d+1, n+d-1)`, `K = (d,n)`). Reflecting through the centre
swaps the top face with the bottom face (`CollarTop.top_bottom_witness`) and the two vertical faces with each other
(`FreeCutPred.freeV_reflect`: the free V cut is invariant under `z ↦ vLast - z`). The reflection preserves `ε`, so the aligned face
goes to the aligned face of the reflected centre only through the opposite face, as used by the callers. -/

namespace FLatticePaper.FaceReflect

open FLatticePaper FLatticePaper.Induction FLatticePaper.FaceWitness

/-- `R - x - K = vLast - x`: the centre reflection of a site, shifted by the kernel. -/
theorem centre_sub_kernel (frame : ChildFrame) (x : Site) :
    frame.centre - x - frame.child.modifiedDeck.kernel
      = (frame.child.num - frame.child.den + 1 - x.1, frame.child.num + frame.child.den - 1 - x.2) := by
  rw [ChildFrame.centre_eq, ChildFrame.child_modifiedDeck_kernel]
  ext <;> simp <;> ring

/-- The free V cut is invariant under `x ↦ R - x - K`. -/
theorem reflect_freeV_of_freeV (frame : ChildFrame) {x : Site} (hx : x ∈ frame.freeV) :
    frame.centre - x - frame.child.modifiedDeck.kernel ∈ frame.freeV := by
  rw [centre_sub_kernel frame x]
  exact FreeCutPred.freeV_reflect frame (x := x.1) (y := x.2) hx

/-- A free V cut translated by the kernel reflects to a free V point through the centre. -/
theorem reflect_freeV_of_shift (frame : ChildFrame) {x : Site} (hx : x - frame.child.modifiedDeck.kernel ∈ frame.freeV) :
    frame.centre - x ∈ frame.freeV := by
  have h := reflect_freeV_of_freeV frame hx
  have e : frame.centre - (x - frame.child.modifiedDeck.kernel) - frame.child.modifiedDeck.kernel
      = frame.centre - x := by
    ext <;> simp <;> ring
  rw [e] at h
  exact h

/-- The top face reflects to the bottom face of the reflected centre. -/
theorem topWit_bottom (frame : ChildFrame) {c : Site} (h : TopWit frame c) :
    BottomWit frame (frame.centre - c) :=
  CollarTop.top_bottom_witness frame h

/-- The left face reflects to the right face of the reflected centre. -/
theorem leftWit_rightWit (frame : ChildFrame) {c : Site} (h : LeftWit frame c) :
    RightWit frame (frame.centre - c) := by
  obtain ⟨v, hv1, hv2, hv⟩ := h
  refine ⟨frame.centre - v, ?_, ?_, ?_⟩
  · have e : (frame.centre - v).1 - (frame.centre - c).1 = c.1 - v.1 := by
      simp only [Prod.fst_sub]; ring
    rw [e, abs_sub_comm]; exact hv1
  · have e : (frame.centre - v).2 - (frame.centre - c).2 = c.2 - v.2 := by
      simp only [Prod.snd_sub]; ring
    rw [e, abs_sub_comm]; exact hv2
  · exact reflect_freeV_of_freeV frame hv

/-- The right face reflects to the left face of the reflected centre. -/
theorem rightWit_leftWit (frame : ChildFrame) {c : Site} (h : RightWit frame c) :
    LeftWit frame (frame.centre - c) := by
  obtain ⟨v, hv1, hv2, hv⟩ := h
  refine ⟨frame.centre - v, ?_, ?_, ?_⟩
  · have e : (frame.centre - v).1 - (frame.centre - c).1 = c.1 - v.1 := by
      simp only [Prod.fst_sub]; ring
    rw [e, abs_sub_comm]; exact hv1
  · have e : (frame.centre - v).2 - (frame.centre - c).2 = c.2 - v.2 := by
      simp only [Prod.snd_sub]; ring
    rw [e, abs_sub_comm]; exact hv2
  · exact reflect_freeV_of_shift frame hv

/-- The opposite face reflects to the aligned face of the reflected centre (the sign `ε` is unchanged). -/
theorem oppositeWit_alignedWit (frame : ChildFrame) {c : Site} (h : OppositeWit frame c) :
    AlignedWit frame (frame.centre - c) := by
  rcases h with ⟨he, hR⟩ | ⟨he, hL⟩
  · exact Or.inl ⟨he, rightWit_leftWit frame hR⟩
  · exact Or.inr ⟨he, leftWit_rightWit frame hL⟩

/-- A collar centre has one of the four witnesses: bottom, aligned, top or opposite. -/
theorem collar_witness_cases (frame : ChildFrame) {c : Site} (h : FLatticePaper.W1CollarFrame.CollarFrame frame c) :
    BottomWit frame c ∨ AlignedWit frame c ∨ TopWit frame c ∨ OppositeWit frame c := by
  obtain ⟨v, hv1, hv2, hv⟩ := h
  rcases hv with h1 | h2 | h3 | h4
  · exact Or.inl ⟨v, hv1, hv2, h1⟩
  · rcases frame.eps_unit with he | he
    · exact Or.inr (Or.inl (Or.inl ⟨he, v, hv1, hv2, h2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨he, v, hv1, hv2, h2⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨v, hv1, hv2, h3⟩))
  · rcases frame.eps_unit with he | he
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨he, v, hv1, hv2, h4⟩)))
    · exact Or.inr (Or.inl (Or.inr ⟨he, v, hv1, hv2, h4⟩))

end FLatticePaper.FaceReflect
