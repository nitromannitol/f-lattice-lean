import FLatticePaper.Plane.Induction.RowVTail

/-! # The V tail of the minus row, at its positions in the row (`2n ≤ d`)

The minus row is `FreeRows.minusRow r L d`. Its V tail `V_{-1}, …, V_{r+1-L}` sits after the H block: `V_{-1-i}` is at position
`r.toNat + 2 + (d-1).toNat + i`, and `H_{-1-i}` is at `r.toNat + 2 + i`. The row of sites is `FreeRows.rowSites`. This module gives the
index facts, the value `vAt(-1) = (1,-1)` and `hAt(-1) = (0,-1)`, and the `href` of the V tail positions with the empty core `C = False`. -/

namespace FLatticePaper.RowVTailRow

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeRows FLatticePaper.RefuteTree
open FLatticePaper.RowVTail

/-- The H block: `H_{-1-i}` sits at position `r + 2 + i`. -/
theorem getH_minusRow (r L d : ℤ) {i : ℕ} (hi : (i : ℤ) < d - 1) :
    (minusRow r L d)[r.toNat + 2 + i]? = some (FreeLabel.H (-1 - (i : ℤ))) := by
  unfold minusRow
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp)]
  simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
  rw [show r.toNat + 2 + i - (r.toNat + 1 + 1) = i by omega, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-- The V tail: `V_{-1-i}` sits at position `r + 2 + (d-1) + i`. -/
theorem getV_minusRow (r L d : ℤ) {i : ℕ} (hi : (i : ℤ) < L - r - 1) :
    (minusRow r L d)[r.toNat + 2 + (d - 1).toNat + i]? = some (FreeLabel.V (-1 - (i : ℤ))) := by
  unfold minusRow
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
  rw [show r.toNat + 2 + (d - 1).toNat + i - (r.toNat + 2 + (d - 1).toNat) = i by omega, List.getElem?_map,
    List.getElem?_range (by omega)]
  rfl

/-- `hAt(-1) + U = hLast`: the H chain closes up at its last site. -/
theorem hAt_neg_one_add_U (frame : ChildFrame) :
    RowAt.hAt frame (-1) + RowAt.Uvec frame = frame.hLast := by
  have h := RowAt.hAt_add_den frame (-1)
  have hd1 : (0 : ℤ) < frame.child.den := RowAt.den_pos frame
  have hnat : (-1 + frame.child.den) = (((frame.child.den - 1).toNat : ℕ) : ℤ) := by omega
  rw [hnat, RowAt.hAt_nat frame _ (by omega)] at h
  have hm := HChain.freeH_eq_hpath frame ((frame.child.den - 1).toNat) frame.hLast
    (EndpointStrips.fHL frame) (by simp only [ChildFrame.hLast]; omega)
  exact (hm.trans h).symm

/-- `hAt(-1) = (0,-1)`. -/
theorem hAt_neg_one_eq (frame : ChildFrame) : RowAt.hAt frame (-1) = (0, -1) := by
  have hsum := hAt_neg_one_add_U frame
  have h1 := congrArg Prod.fst hsum
  have h2 := congrArg Prod.snd hsum
  simp only [Prod.fst_add, Prod.snd_add, RowAt.Uvec, ChildFrame.hLast] at h1 h2
  exact Prod.ext (by simp only; omega) (by simp only; omega)

/-- `vAt(-1) = vLast - Vt = (1,-1)`. -/
theorem vAt_neg_one_eq (frame : ChildFrame) : RowAt.vAt frame (-1) = (1, -1) := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  rw [RoutePlus.vAt_neg_eq frame (-1) (by omega) (by omega)]
  have hk : ((-1 + (frame.child.den + frame.child.num)).toNat) = (frame.child.num + frame.child.den - 1).toNat := by
    congr 1
    ring
  rw [hk, ← VChain.vLast_eq_vpath]
  ext <;> simp [ChildFrame.vLast, RoutePlus.Vt]

/-- The row of sites of the minus row of the frame (`L = den + num`, `d = den`). -/
noncomputable def tailRow (frame : ChildFrame) (r : ℤ) : List Site :=
  rowSites (RowAt.vAt frame) (RowAt.hAt frame) (minusRow r (frame.child.den + frame.child.num) frame.child.den)

theorem tailRow_getElem? (frame : ChildFrame) (r : ℤ) {k : ℕ} {ℓ : FreeLabel}
    (h : (minusRow r (frame.child.den + frame.child.num) frame.child.den)[k]? = some ℓ) :
    (tailRow frame r)[k]? = some (labelSite (RowAt.vAt frame) (RowAt.hAt frame) ℓ) := by
  unfold tailRow rowSites
  rw [List.getElem?_map, h]
  rfl

/-- **The V tail, at its position.** The entry `vAt j` (`j ≤ -1` in the tail) is refuted by the certificates of `RowVTail`, from
the earlier entries of the row before its position. -/
theorem tail_refuted_at {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {r : ℤ} (hr : 0 ≤ r) (hd : 2 ≤ frame.child.den)
    {j : ℤ} (hj1 : r + 1 - (frame.child.den + frame.child.num) ≤ j) (hj2 : j ≤ -1) :
    Refuted frame F (-1) (fun x => ∃ k : ℕ, k < r.toNat + 2 + (frame.child.den - 1).toNat + (-1 - j).toNat ∧
      (tailRow frame r)[k]? = some x) (fun _ => False) (RowAt.vAt frame j) := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  rcases eq_or_lt_of_le hj2 with rfl | hlt
  · apply refuted_tail_last hP
    refine ⟨r.toNat + 2 + 0, by omega, ?_⟩
    rw [tailRow_getElem? frame r (getH_minusRow r _ _ (i := 0) (by simp; omega))]
    congr 1
    simp only [labelSite, Nat.cast_zero, sub_zero]
    rw [vAt_neg_one_eq frame, hAt_neg_one_eq frame]
    ext <;> simp
  · have hj2' : j ≤ -2 := by omega
    have hj1' : -(frame.child.den + frame.child.num) + 1 ≤ j := by omega
    refine refuted_tail hP hS hO hd2 hj1' hj2' ⟨r.toNat + 2 + (frame.child.den - 1).toNat + (-2 - j).toNat, by omega, ?_⟩
    have hrow := getV_minusRow r (frame.child.den + frame.child.num) frame.child.den (i := (-2 - j).toNat)
      (by rw [Int.toNat_of_nonneg (by omega)]; omega)
    have e : (-1 - (((-2 - j).toNat : ℕ) : ℤ)) = j + 1 := by omega
    rw [tailRow_getElem? frame r hrow, e]
    rfl

/-- **The `href` of the V tail positions.** The entry at a tail position `k` (`k` in the V block of the minus row) is refuted from
the earlier entries of the row, with the empty core `C = False`. -/
theorem tail_href_row {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {r : ℤ} (hr : 0 ≤ r) (hd : 2 ≤ frame.child.den)
    (k : ℕ) (e : Site) (hk : (tailRow frame r)[k]? = some e)
    (hlo : r.toNat + 2 + (frame.child.den - 1).toNat ≤ k)
    (hhi : k < r.toNat + 2 + (frame.child.den - 1).toNat + (frame.child.den + frame.child.num - r - 1).toNat) :
    Refuted frame F (-1) (fun x => ∃ k' : ℕ, k' < k ∧ (tailRow frame r)[k']? = some x) (fun _ => False) e := by
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, k = r.toNat + 2 + (frame.child.den - 1).toNat + i :=
    ⟨k - (r.toNat + 2 + (frame.child.den - 1).toNat), by omega⟩
  have hi : (i : ℤ) < frame.child.den + frame.child.num - r - 1 := by omega
  have hrow := getV_minusRow r (frame.child.den + frame.child.num) frame.child.den (i := i) hi
  rw [tailRow_getElem? frame r hrow] at hk
  have he : e = RowAt.vAt frame (-1 - (i : ℤ)) := (Option.some.inj hk).symm
  subst he
  have H := tail_refuted_at hP hS hO hd2 hr hd (j := -1 - (i : ℤ)) (by omega) (by omega)
  have hidx : (-1 - (-1 - (i : ℤ))).toNat = i := by omega
  rw [hidx] at H
  exact H

end FLatticePaper.RowVTailRow

