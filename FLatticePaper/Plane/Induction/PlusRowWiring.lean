import FLatticePaper.Plane.Induction.MinusRowWiring

/-! # The plus row: list positions of the labels, and the earlier sets of the plus H entries

The plus row `V_{-r-1}, …, V_{-1}, H_0, V_0, V_1, …, V_{L-r-2}, H_{-1}, …, H_{1-d}` (`FreeRows.plusRow`) places `V_{-r-1+i}` at
position `i` (`i ≤ r`), `H_0` at `r + 1`, `V_0` at `r + 2`, `V_{1+i}` at `(r+1) + 2 + i` (`i < L - r - 2`), and `H_j` (`1 - d ≤ j ≤ -1`)
at `(r+1) + 2 + (L - r - 2) + (-1 - j)`. With `L = d + n`, the H entry `H_{m-d}` sits at `L + 1 + (d - 1 - m)`. The earlier sets are the
row entries before the position, as for the minus row. -/

namespace FLatticePaper.PlusRowWiring

open FLatticePaper FLatticePaper.Induction FLatticePaper.FreeRows

/-- The V label `V (-r-1+i)` sits at position `i` of the plus row, for `i ≤ r`. -/
theorem plusRow_get_Vneg (r L d : ℤ) (i : ℕ) (hi : (i : ℤ) ≤ r) :
    (plusRow r L d)[i]? = some (FreeLabel.V (-r - 1 + (i : ℤ))) := by
  unfold plusRow
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_left (by simp only [List.length_map, List.length_range]; omega)]
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  simp

/-- The label `V_0` sits at position `r + 2` of the plus row. -/
theorem plusRow_get_V0 (r L d : ℤ) :
    (plusRow r L d)[(r + 1).toNat + 1]? = some (FreeLabel.V 0) := by
  unfold plusRow
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_right (by simp only [List.length_map, List.length_range]; omega)]
  have hsub : (r + 1).toNat + 1 - ((List.range (r + 1).toNat).map fun i : ℕ => FreeLabel.V (-r - 1 + (i : ℤ))).length = 1 := by
    simp only [List.length_map, List.length_range]
    omega
  rw [hsub]
  simp

/-- The V tail: `V (1+i)` sits at position `(r+1) + 2 + i`, for `i < L - r - 2`. -/
theorem plusRow_get_Vtail (r L d : ℤ) (i : ℕ) (hi : (i : ℤ) < L - r - 2) :
    (plusRow r L d)[(r + 1).toNat + 2 + i]? = some (FreeLabel.V (1 + (i : ℤ))) := by
  unfold plusRow
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_right (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  have hsub : (r + 1).toNat + 2 + i - (((List.range (r + 1).toNat).map fun i : ℕ => FreeLabel.V (-r - 1 + (i : ℤ)))
      ++ [FreeLabel.H 0, FreeLabel.V 0]).length = i := by
    simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
    omega
  rw [hsub, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some]

/-- The H label `H j` (for `1 - d ≤ j ≤ -1`) sits at position `(r+1) + 2 + (L - r - 2) + (-1 - j)` of the plus row. -/
theorem plusRow_get_H (r L d : ℤ) (j : ℤ) (hj1 : 1 - d ≤ j) (hj2 : j ≤ -1) :
    (plusRow r L d)[(r + 1).toNat + 2 + (L - r - 2).toNat + (-1 - j).toNat]? = some (FreeLabel.H j) := by
  unfold plusRow
  rw [List.getElem?_append_right (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  have hsub : (r + 1).toNat + 2 + (L - r - 2).toNat + (-1 - j).toNat
      - (((List.range (r + 1).toNat).map fun i : ℕ => FreeLabel.V (-r - 1 + (i : ℤ))) ++ [FreeLabel.H 0, FreeLabel.V 0]
        ++ ((List.range (L - r - 2).toNat).map fun i : ℕ => FreeLabel.V (1 + (i : ℤ)))).length = (-1 - j).toNat := by
    simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
    omega
  rw [hsub, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some]
  congr 2
  omega

/-- The plus site list: the row sites of the plus row. -/
noncomputable def plusSites (frame : ChildFrame) (r : ℤ) : List Site :=
  rowSites (RowAt.vAt frame) (RowAt.hAt frame) (plusRow r (frame.child.den + frame.child.num) frame.child.den)

/-- The earlier entries of the plus row at position `kz`. -/
def earlierPlus (frame : ChildFrame) (r : ℤ) (kz : ℕ) : Set Site :=
  {x | ∃ j : ℕ, j < kz ∧ (plusSites frame r)[j]? = some x}

/-- The position of the H entry `H_{m-d}` (the entry of `z = hpath m`) in the plus row: `L + 1 + (d - 1 - m)`. -/
def entryPosPlus (frame : ChildFrame) (r : ℤ) (m : ℕ) : ℕ :=
  (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat + (-1 - ((m : ℤ) - frame.child.den)).toNat

/-- The H labels of `hEH` for the plus row: `hpath k - U`, `m + 1 ≤ k < d`, are earlier entries of `H_{m-d}`. -/
theorem hEH_plus (frame : ChildFrame) (r : ℤ) (m : ℕ) :
    ∀ k : ℕ, (m : ℤ) + 1 ≤ (k : ℤ) → (k : ℤ) < frame.child.den →
      HChain.hpath frame k - RowAt.Uvec frame ∈ earlierPlus frame r (entryPosPlus frame r m) := by
  intro k hk1 hk2
  rw [← EasyHRank.hAt_sub_den frame hk2]
  refine ⟨(r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat + (-1 - ((k : ℤ) - frame.child.den)).toNat,
    by unfold entryPosPlus; omega, ?_⟩
  unfold plusSites rowSites
  rw [List.getElem?_map, plusRow_get_H r _ _ _ (by omega) (by omega)]
  simp [labelSite]

/-- The V labels of `hEV` for the plus row: `vpath k`, `1 ≤ k ≤ L - r - 2`, are earlier entries of every H entry. -/
theorem hEV_plus (frame : ChildFrame) (r : ℤ) (m : ℕ) :
    ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num → 1 ≤ (k : ℤ) →
      (k : ℤ) ≤ frame.child.den + frame.child.num - r - 2 →
      VChain.vpath frame k ∈ earlierPlus frame r (entryPosPlus frame r m) := by
  intro k hkL hk1 hkr
  rw [← RowAt.vAt_nat frame k hkL]
  refine ⟨(r + 1).toNat + 2 + ((k : ℤ) - 1).toNat, by unfold entryPosPlus; omega, ?_⟩
  unfold plusSites rowSites
  rw [List.getElem?_map, plusRow_get_Vtail r _ _ _ (by omega)]
  have hv : (1 : ℤ) + (((k : ℤ) - 1).toNat : ℕ) = (k : ℤ) := by omega
  simp only [Option.map_some, labelSite, hv]

/-- The position of `V_0` in the plus site list: it is an earlier entry of every plus H entry. -/
theorem vFirst_mem_earlierPlus (frame : ChildFrame) (r : ℤ) (hL : 0 < frame.child.den + frame.child.num)
    (m : ℕ) : FLatticePaper.Induction.vFirst ∈ earlierPlus frame r (entryPosPlus frame r m) := by
  refine ⟨(r + 1).toNat + 1, by unfold entryPosPlus; omega, ?_⟩
  unfold plusSites rowSites
  rw [List.getElem?_map, plusRow_get_V0 r _ _]
  have hv : RowAt.vAt frame 0 = FLatticePaper.Induction.vFirst := by
    have h := RowAt.vAt_nat frame 0 (by omega)
    simp only [Nat.cast_zero] at h
    rw [h, VChain.vpath_zero]
  simp only [Option.map_some, labelSite, hv]

/-- The next H label `H_{m+1-d}` is an earlier entry of `H_{m-d}`. -/
theorem hAt_mem_earlierPlus (frame : ChildFrame) (r : ℤ)
    (m : ℕ) (hm : (m : ℤ) + 1 < frame.child.den) :
    RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den) ∈ earlierPlus frame r (entryPosPlus frame r m) := by
  have h := hEH_plus frame r m (m + 1) (by push_cast; omega) (by push_cast; omega)
  have e : (m : ℤ) + 1 - frame.child.den = ((m + 1 : ℕ) : ℤ) - frame.child.den := by push_cast; ring
  rw [e, EasyHRank.hAt_sub_den frame (by push_cast; omega)]
  exact h

/-- The V_0 label is an earlier entry of any entry at a position beyond `r + 2` of the plus row. -/
theorem vFirst_mem_earlierPlus_of_lt (frame : ChildFrame) (r : ℤ) (hL : 0 < frame.child.den + frame.child.num)
    (kz : ℕ) (hkz : (r + 1).toNat + 1 < kz) : FLatticePaper.Induction.vFirst ∈ earlierPlus frame r kz := by
  refine ⟨(r + 1).toNat + 1, hkz, ?_⟩
  unfold plusSites rowSites
  rw [List.getElem?_map, plusRow_get_V0 r _ _]
  have hv : RowAt.vAt frame 0 = FLatticePaper.Induction.vFirst := by
    have h := RowAt.vAt_nat frame 0 (by omega)
    simp only [Nat.cast_zero] at h
    rw [h, VChain.vpath_zero]
  simp only [Option.map_some, labelSite, hv]

end FLatticePaper.PlusRowWiring
