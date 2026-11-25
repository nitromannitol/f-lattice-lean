import FLatticePaper.Plane.Induction.LowerBand

/-! # The lower input of an even free V root is a free V root

`y = (z.1, z.2 - δ)` lies in the V band (`ChildFrame.lower_in_vBand`). That band is exactly the odd branch of the V spectrum,
`2 - d + n ≤ s ≤ d + n - 2`, and `s(y) < L`, so the left neighbour `y - (1, 0)` has negative `s`-grade and is outside the closed
polygon. Hence `y ∈ freeV`, which is the membership half of `hX3`. -/

namespace FLatticePaper.Induction

namespace ChildFrame
variable (frame : ChildFrame)

theorem lower_mem_freeV {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z)
    (hzF : z ≠ FLatticePaper.Induction.vFirst) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    (hδz : δ = 1 ∨ z ≠ frame.vLast) :
    (z.1, z.2 - δ) ∈ frame.freeV := by
  have hlow := frame.lower_in_vBand hz hev hzF hδ hδz
  obtain ⟨hcp, hrange⟩ := (frame.mem_vBand_iff _).mp hlow
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  have hodd : ¬ EvenSite (z.1, z.2 - δ) := by
    show ¬ ((z.1 + (z.2 - δ)) % 2 = 0)
    rcases hδ with rfl | rfl <;> omega
  rw [if_neg hodd] at hrange
  obtain ⟨hr1, hr2⟩ := hrange
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hodd' := frame.child_num_odd
  have hsE : frame.sGrade z % 2 = 0 := by
    have hvs : frame.vSpectrum (frame.sGrade z) := hz.2.2
    unfold ChildFrame.vSpectrum at hvs
    exact hvs.1
  refine ⟨hcp, ?_, ?_⟩
  · intro hc
    rcases (frame.mem_closedPolygon_iff _).mp hc with h | h
    · have h' := h.2.2.2.1
      rw [frame.sGrade_sub_x] at h'
      omega
    · have hev2 : EvenSite ((z.1, z.2 - δ).1 - 1, (z.1, z.2 - δ).2) := by
        show (z.1 - 1 + (z.2 - δ)) % 2 = 0
        rcases hδ with rfl | rfl <;> omega
      exact h.1 hev2
  · show frame.vSpectrum (frame.sGrade (z.1, z.2 - δ))
    unfold ChildFrame.vSpectrum
    refine ⟨?_, Or.inr ⟨hr1, hr2⟩⟩
    rcases hδ with rfl | rfl
    · rw [frame.sGrade_sub_y]
      omega
    · rw [show z.2 - -1 = z.2 + 1 by ring, frame.sGrade_add_y]
      omega

end ChildFrame

end FLatticePaper.Induction
