import FLatticePaper.Plane.Induction.MinusRowEndpoint

/-! # The plus row endpoints `H_0` and `V_0`: white refutations from the earlier entries (eta = 1)

In the plus row `V_{-r-1}..V_{-1}, H_0, V_0, V_1.., H_{-1}..`, the entry `V_{-1}` precedes `H_0`. Under `eta = 1` the free
prescription of `H_0 = (1, 0)` is its incoming site `(1, -1) = V_{-1}`, a single free input, so `H_0` is a free white refuted by
the earlier entry `V_{-1}` through the white rule. Likewise the prescription of `V_0 = (0, 0)` (even, `(eta, 0)`) is `(1, 0) = H_0`,
so `V_0` is a free white refuted by the earlier entry `H_0`. No restricted core is needed. -/

namespace FLatticePaper.PlusRowEndpoint

open FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeRows

/-- A free prescription witness makes its site free-closed (the witness is the free closure's witness). -/
theorem freeClosure_of_freePresc (frame : ChildFrame) {η : ℤ} {c i : Site}
    (h : FreePolicy.FreePresc frame η c i) : FreeClosure.freeClosure frame c := by
  obtain ⟨t, ht, h⟩ := h
  refine ⟨t, ht, ?_⟩
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- **The plus `H_0` is refuted by `V_{-1}`.** Its laplacian is zero, and its only free prescription under `eta = 1` is
`(1, -1)`, the earlier entry `V_{-1}`. -/
theorem refuted_H0_plus (frame : ChildFrame) (F : Field) {E C : Site → Prop}
    (hw : laplacian F ((1 : ℤ), (0 : ℤ)) = 0)
    (hpos : FreePolicy.FreePresc frame 1 ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (-1 : ℤ)))
    (hE : E ((1 : ℤ), (-1 : ℤ))) :
    RefuteTree.Refuted frame F 1 E C ((1 : ℤ), (0 : ℤ)) := by
  have hperm : permitsQ1 frame F 1 ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (-1 : ℤ)) :=
    Or.inr ⟨hw, Or.inl ⟨freeClosure_of_freePresc frame hpos, hpos⟩⟩
  exact RefuteTree.Refuted.white hw hperm (RefuteTree.Refuted.earlier hE)

/-- **The plus `V_0` is refuted by `H_0`.** Its laplacian is zero, and its only free prescription under `eta = 1` is
`(1, 0) = H_0`, the earlier entry. -/
theorem refuted_V0_plus (frame : ChildFrame) (F : Field) {E C : Site → Prop}
    (hw : laplacian F ((0 : ℤ), (0 : ℤ)) = 0)
    (hpos : FreePolicy.FreePresc frame 1 ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)))
    (hE : E ((1 : ℤ), (0 : ℤ))) :
    RefuteTree.Refuted frame F 1 E C ((0 : ℤ), (0 : ℤ)) := by
  have hperm : permitsQ1 frame F 1 ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) :=
    Or.inr ⟨hw, Or.inl ⟨freeClosure_of_freePresc frame hpos, hpos⟩⟩
  exact RefuteTree.Refuted.white hw hperm (RefuteTree.Refuted.earlier hE)

end FLatticePaper.PlusRowEndpoint
