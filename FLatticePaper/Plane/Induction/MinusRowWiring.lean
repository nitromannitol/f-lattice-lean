import FLatticePaper.Plane.Induction.FreeRows
import FLatticePaper.Plane.Induction.EasyHRank
import FLatticePaper.Plane.Induction.ConeBoundary
import FLatticePaper.Plane.Induction.RefuteTree
import FLatticePaper.Plane.Induction.OddAxialRank

/-! # The minus row: list positions of the H and V labels, and the earlier sets of `hG`

The minus row `V_r, …, V_1, H_0, V_0, H_{-1}, …, H_{1-d}, V_{-1}, …` (`FreeRows.minusRow`) places the label `H_j` (for
`1 − d ≤ j ≤ −1`) at position `r + 2 + (−1 − j)` and the label `V_k` (for `1 ≤ k ≤ r`) at position `r − k`. The earlier entries of the
entry `H_{m−d}` are the row entries before its position; with `z = hpath m` (so `z.1 = m + 1`), they contain `hpath k − U` for
`m + 1 ≤ k < d` (the H labels `H_{k−d}`) and `vpath k` for `1 ≤ k ≤ r` (the V labels), which are exactly the inputs `hEH`, `hEV` of
`ConeBoundary.hG_of_faces`. -/

namespace FLatticePaper.MinusRowWiring

open FLatticePaper FLatticePaper.Induction FLatticePaper.FreeRows

/-- The V label `V (r − i)` sits at position `i` of the minus row, for `i < r`. -/
theorem minusRow_get_V (r L d : ℤ) (i : ℕ) (hi : (i : ℤ) < r) :
    (minusRow r L d)[i]? = some (FreeLabel.V (r - (i : ℤ))) := by
  unfold minusRow
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_left (by simp only [List.length_map, List.length_range]; omega)]
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  simp

/-- The H label `H j` (for `1 − d ≤ j ≤ −1`) sits at position `r + 2 + (−1 − j)` of the minus row. -/
theorem minusRow_get_H (r L d : ℤ) (j : ℤ) (hj1 : 1 - d ≤ j) (hj2 : j ≤ -1) :
    (minusRow r L d)[r.toNat + 2 + (-1 - j).toNat]? = some (FreeLabel.H j) := by
  unfold minusRow
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_right (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  have hsub : r.toNat + 2 + (-1 - j).toNat -
      (((List.range r.toNat).map fun i : ℕ => FreeLabel.V (r - (i : ℤ))) ++ [FreeLabel.H 0, FreeLabel.V 0]).length
      = (-1 - j).toNat := by
    simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
    omega
  rw [hsub, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some]
  congr 2
  omega

/-- The rowSites of the minus row for the frame, with the break `r`. -/
noncomputable def minusSites (frame : ChildFrame) (r : ℤ) : List Site :=
  rowSites (RowAt.vAt frame) (RowAt.hAt frame)
    (minusRow r (frame.child.den + frame.child.num) frame.child.den)

/-- The earlier entries of the row position `kz`: the sites of the entries before it. -/
def earlierAt (frame : ChildFrame) (r : ℤ) (kz : ℕ) : Set Site :=
  {x | ∃ j : ℕ, j < kz ∧ (minusSites frame r)[j]? = some x}

/-- **The H labels of `hEH`.** For the entry `H_{m−d}` (position `kz`, the `z = hpath m` entry), the sites `hpath k − U`,
`m + 1 ≤ k < d`, are earlier entries of the minus row. -/
theorem hEH_row (frame : ChildFrame) (r : ℤ) (m : ℕ) :
    ∀ k : ℕ, (m : ℤ) + 1 ≤ (k : ℤ) → (k : ℤ) < frame.child.den →
      HChain.hpath frame k - RowAt.Uvec frame ∈
        earlierAt frame r (r.toNat + 2 + (-1 - ((m : ℤ) - frame.child.den)).toNat) := by
  intro k hk1 hk2
  rw [← EasyHRank.hAt_sub_den frame hk2]
  refine ⟨r.toNat + 2 + (-1 - ((k : ℤ) - frame.child.den)).toNat, by omega, ?_⟩
  unfold minusSites rowSites
  rw [List.getElem?_map, minusRow_get_H _ _ _ _ (by omega) (by omega)]
  simp [labelSite]

/-- **The V labels of `hEV`.** The labels `V_k` for `1 ≤ k ≤ r` are earlier entries of every H entry of the minus row. -/
theorem hEV_row (frame : ChildFrame) (r : ℤ) (hr0 : 0 ≤ r) (m : ℕ) :
    ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num → 1 ≤ (k : ℤ) → (k : ℤ) ≤ r →
      VChain.vpath frame k ∈
        earlierAt frame r (r.toNat + 2 + (-1 - ((m : ℤ) - frame.child.den)).toNat) := by
  intro k hkL hk1 hkr
  rw [← RowAt.vAt_nat frame k hkL]
  refine ⟨(r - (k : ℤ)).toNat, by omega, ?_⟩
  unfold minusSites rowSites
  rw [List.getElem?_map, minusRow_get_V r _ _ (r - (k : ℤ)).toNat (by omega)]
  have hv : r - (((r - (k : ℤ)).toNat : ℕ) : ℤ) = (k : ℤ) := by omega
  simp only [Option.map_some, hv]
  rfl

/-- The position of the H entry `H_{m−d}` (the entry of `z = hpath m`) in the minus row. -/
def entryPos (frame : ChildFrame) (r : ℤ) (m : ℕ) : ℕ :=
  r.toNat + 2 + (-1 - ((m : ℤ) - frame.child.den)).toNat

/-- The next H label `H_{m+1−d}` (the east neighbour's entry) is an earlier entry of `H_{m−d}`. -/
theorem hAt_mem_earlier (frame : ChildFrame) (r : ℤ) (m : ℕ) (hm : (m : ℤ) + 1 < frame.child.den) :
    RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den) ∈ earlierAt frame r (entryPos frame r m) := by
  have h := hEH_row frame r m (m + 1) (by push_cast; omega) (by push_cast; omega)
  have e : (m : ℤ) + 1 - frame.child.den = ((m + 1 : ℕ) : ℤ) - frame.child.den := by push_cast; ring
  rw [e, EasyHRank.hAt_sub_den frame (by push_cast; omega)]
  exact h

/-- **Rank 1 at the minus row.** The even H entry with a free east step is refuted by the earlier entries of its position. -/
theorem minus_refuted_even_east (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV) (r : ℤ) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den) (hev : EvenSite (HChain.hpath frame m))
    (hfree : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∈ frame.freeH) :
    RefuteTree.Refuted frame F (-1) (fun x => x ∈ earlierAt frame r (entryPos frame r m)) (fun _ => False)
      (RowAt.hAt frame ((m : ℤ) - frame.child.den)) :=
  EasyHRank.refuted_even_H_east_free frame F hP hper hm1 hm2 hev hfree (hAt_mem_earlier frame r m hm2)

/-- **Rank 2 at the minus row.** The even H entry with a diagonal step is refuted by the earlier entries of its position. -/
theorem minus_refuted_even_diag (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV) (r : ℤ)
    (hd2 : 2 * frame.child.num ≤ frame.child.den)
    (hZ : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den) (hev : EvenSite (HChain.hpath frame m))
    (hdiag : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∉ frame.freeH) :
    RefuteTree.Refuted frame F (-1) (fun x => x ∈ earlierAt frame r (entryPos frame r m)) (fun _ => False)
      (RowAt.hAt frame ((m : ℤ) - frame.child.den)) :=
  EasyHRankDiag.refuted_even_H_diag frame F hP hper hd2 hZ hm1 hm2 hev hdiag (hAt_mem_earlier frame r m hm2)

/-- **Rank 3 at the minus row.** The odd H entry with `t ≥ d + 2 − 2n` is refuted by the earlier entries of its position. -/
theorem minus_refuted_odd_late (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV) (r : ℤ)
    (hd2 : 2 * frame.child.num ≤ frame.child.den)
    (hZ : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den) (hodd : ¬ EvenSite (HChain.hpath frame m))
    (hlate : frame.child.den + 2 - 2 * frame.child.num ≤ frame.tGrade (HChain.hpath frame m)) :
    RefuteTree.Refuted frame F (-1) (fun x => x ∈ earlierAt frame r (entryPos frame r m)) (fun _ => False)
      (RowAt.hAt frame ((m : ℤ) - frame.child.den)) :=
  OddAxialRank.refuted_odd_H_axial frame F hP hper hd2 hZ hm1 hm2 hodd hlate (hAt_mem_earlier frame r m hm2)

end FLatticePaper.MinusRowWiring
