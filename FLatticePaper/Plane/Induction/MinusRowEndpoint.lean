import FLatticePaper.Plane.Induction.MinusRowWiring
import FLatticePaper.Plane.Induction.EndpointStrips
import FLatticePaper.Plane.Induction.FaceRows
import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.FreeClosure
import FLatticePaper.Plane.Induction.Rank4Fort
import FLatticePaper.Plane.Induction.RefuteTree

/-! # The last H entry of the minus row: `H_{−1} = hLast − U` is refuted by the earlier entry `V_0`

`H_{-1} = hAt(−1) = hpath(d−1) − U = hLast − U = (0, −1)` is a free white site: its translate `hLast` is free with prescribed
input `(0,1)` (north), and `hLast + (0,1) − U`-shift lands on `V_0 = vFirst = (0,0)`. The white rule of `Refuted` then refutes
`H_{-1}` from the earlier entry `V_0`, which is in the row before `H_{-1}` (position `r + 1`). -/

namespace FLatticePaper.MinusRowEndpoint

open FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeRows

theorem hAt_neg_one_add_U (frame : ChildFrame) :
    RowAt.hAt frame (-1) + RowAt.Uvec frame = frame.hLast := by
  have h := RowAt.hAt_add_den frame (-1)
  have hd1 : (0 : ℤ) < frame.child.den := RowAt.den_pos frame
  have hnat : (-1 + frame.child.den) = (((frame.child.den - 1).toNat : ℕ) : ℤ) := by omega
  rw [hnat, RowAt.hAt_nat frame _ (by omega)] at h
  have hm := HChain.freeH_eq_hpath frame ((frame.child.den - 1).toNat) frame.hLast
    (EndpointStrips.fHL frame) (by simp only [ChildFrame.hLast]; omega)
  exact (hm.trans h).symm

theorem hAt_neg_one_eq (frame : ChildFrame) : RowAt.hAt frame (-1) = (0, -1) := by
  have hsum := hAt_neg_one_add_U frame
  have h1 := congrArg Prod.fst hsum
  have h2 := congrArg Prod.snd hsum
  simp only [Prod.fst_add, Prod.snd_add, RowAt.Uvec, ChildFrame.hLast] at h1 h2
  exact Prod.ext (by simp only; omega) (by simp only; omega)

/-- **The endpoint refutation.** `H_{−1} = hAt(−1)` is refuted by the white rule from the earlier entry `V_0 = vFirst`. -/
theorem refuted_hAt_neg_one (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {E C : Site → Prop}
    (hE : E FLatticePaper.Induction.vFirst) :
    RefuteTree.Refuted frame F (-1) E C (RowAt.hAt frame (-1)) := by
  have hsum := hAt_neg_one_add_U frame
  have hlapL : laplacian F frame.hLast = 0 := EndpointStrips.lap_hL hP.strips
  have hlap : laplacian F (RowAt.hAt frame (-1)) = 0 := by
    have h := laplacian_add_combine hP.periods (RowAt.hAt frame (-1)) 1 0
    rw [EasyHRank.combine_one_zero_eq_Uvec frame, hsum, hlapL] at h
    exact h.symm
  have he := hAt_neg_one_eq frame
  have hfree : FreeClosure.freeClosure frame (RowAt.hAt frame (-1)) :=
    ⟨RowAt.Uvec frame, Rank4Fort.uvec_mem_span frame, Or.inl (by rw [hsum]; exact EndpointStrips.fHL frame)⟩
  have hpres : FreePolicy.FreePresc frame (-1) (RowAt.hAt frame (-1)) FLatticePaper.Induction.vFirst :=
    ⟨RowAt.Uvec frame, Rank4Fort.uvec_mem_span frame,
      Or.inl ⟨by rw [hsum]; exact EndpointStrips.fHL frame, by rw [hsum, FaceRows.prescH_hLast, he]; rfl⟩⟩
  have hperm : permitsQ1 frame F (-1) (RowAt.hAt frame (-1)) FLatticePaper.Induction.vFirst :=
    Or.inr ⟨hlap, Or.inl ⟨hfree, hpres⟩⟩
  exact RefuteTree.Refuted.white hlap hperm (RefuteTree.Refuted.earlier hE)

/-- The row entry `V_0` sits at position `r + 1` of the minus row, before `H_{−1}`. -/
theorem minusRow_get_V0 (r L d : ℤ) :
    (minusRow r L d)[r.toNat + 1]? = some (FreeLabel.V 0) := by
  unfold minusRow
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_right (by simp only [List.length_map, List.length_range]; omega)]
  have hsub : r.toNat + 1 - ((List.range r.toNat).map fun i : ℕ => FreeLabel.V (r - (i : ℤ))).length = 1 := by
    simp only [List.length_map, List.length_range]
    omega
  rw [hsub]
  simp

end FLatticePaper.MinusRowEndpoint
