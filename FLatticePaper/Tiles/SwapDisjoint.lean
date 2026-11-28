import FLatticePaper.Tiles.SameParentStd

/-! The pairs of copies of one parent tile exchanged by the half-turn, in the standard decomposition of a child that is not
corrected, that do not meet: the odd child `0, 1` after a `1`, `2, 5` after a `2` (and after a `1` with `W_1` even), `3, 4` after a
`2` (and after a `1` with `W_1` odd); the even child `4, 5` after a `1`, `0, 3` always, `1, 2` after a `3`. (The other swapped pairs
meet, in a copy of a grandparent tile.) The separation is that of `SameParentCopies`. -/

namespace FLatticePaper.Tiles.SwapDisjoint

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.H3Bounds FLatticePaper.Tiles.H3Pairs
  FLatticePaper.Tiles.SameParentCopies FLatticePaper.Tiles.SameParentAlt
open FLatticePaper.Tiles.ChildGlue (oddP oddQ evenP evenQ)
open FLatticePaper.Tiles.ClosedPathAssembly (dOdd dEven)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)

/-- Copies `0` and `1` of the odd standard child after a `1`, `W_1` odd. -/
theorem so01_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (oddP w).getD 0 0 ∈ oddTile U)
    (hb : z - (oddP w).getD 1 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [oddP, MixedPieces.pOffsetsOdd, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `1` of the odd standard child after a `1`, `W_1` even. -/
theorem so01_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (oddP w).getD 0 0 ∈ oddTile U)
    (hb : z - (oddP w).getD 1 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [oddP, MixedPieces.pOffsetsOdd, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `4` and `5` of the even standard child after a `1`, `W_1` odd. -/
theorem se45_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (evenQ w).getD 0 0 ∈ evenTile U)
    (hb : z - (evenQ w).getD 1 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [evenQ, MixedPieces.qOffsetsEven, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `4` and `5` of the even standard child after a `1`, `W_1` even. -/
theorem se45_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (evenQ w).getD 0 0 ∈ evenTile U)
    (hb : z - (evenQ w).getD 1 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [evenQ, MixedPieces.qOffsetsEven, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `2` and `5` of the odd standard child after a `2`, `W_1` odd. -/
theorem so25_two_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 0 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 3 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `2` and `5` of the odd standard child after a `2`, `W_1` even. -/
theorem so25_two_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 0 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 3 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `2` and `5` of the odd standard child after a `1`, `W_1` even. -/
theorem so25_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 0 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 3 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `3` and `4` of the odd standard child after a `2`, `W_1` odd. -/
theorem so34_two_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 1 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 2 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `3` and `4` of the odd standard child after a `2`, `W_1` even. -/
theorem so34_two_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 1 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 2 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `3` and `4` of the odd standard child after a `1`, `W_1` odd. -/
theorem so34_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 1 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 2 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `3` of the even standard child after a `1`, `W_1` odd. -/
theorem se03_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 0 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 3 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `3` of the even standard child after a `1`, `W_1` even. -/
theorem se03_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 0 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 3 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `3` of the even standard child after a `3`, `W_1` odd. -/
theorem se03_three_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 0 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 3 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `3` of the even standard child after a `3`, `W_1` even. -/
theorem se03_three_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 0 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 3 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `2` of the even standard child after a `3`, `W_1` odd. -/
theorem se12_three_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 1 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 2 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `2` of the even standard child after a `3`, `W_1` even. -/
theorem se12_three_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 1 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 2 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

theorem dOdd_sub' (w u1 u2 : Word) {z : ℤ × ℤ} {k : ℕ} (h : z ∈ dOdd w u1 u2 k) :
    (k < 2 → z - (oddP w).getD k 0 ∈ oddTile u1) ∧ (∀ m, k = m + 2 → z - (oddQ w).getD m 0 ∈ evenTile u2) := by
  have hl : (oddP w).length = 2 := by unfold oddP MixedPieces.pOffsetsOdd; split_ifs <;> rfl
  refine ⟨fun hk => ?_, fun m hm => ?_⟩
  · simp only [dOdd, ChildGlue.pieceSet, hl, if_pos hk] at h
    exact Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ h)
  · subst hm
    simp only [dOdd, ChildGlue.pieceSet, hl, if_neg (show ¬ m + 2 < 2 by omega), Nat.add_sub_cancel] at h
    exact Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ h)

theorem dEven_sub' (w u1 u2 : Word) {z : ℤ × ℤ} {k : ℕ} (h : z ∈ dEven w u1 u2 k) :
    (k < 4 → z - (evenP w).getD k 0 ∈ oddTile u1) ∧ (∀ m, k = m + 4 → z - (evenQ w).getD m 0 ∈ evenTile u2) := by
  have hl : (evenP w).length = 4 := by unfold evenP MixedPieces.pOffsetsEven; split_ifs <;> rfl
  refine ⟨fun hk => ?_, fun m hm => ?_⟩
  · simp only [dEven, ChildGlue.pieceSet, hl, if_pos hk] at h
    exact Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ h)
  · subst hm
    simp only [dEven, ChildGlue.pieceSet, hl, if_neg (show ¬ m + 4 < 4 by omega), Nat.add_sub_cancel] at h
    exact Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ h)

/-- **Copies `0` and `1` of the odd standard child do not meet** after a `1`. -/
theorem swapOdd01_one (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? = some Digit.one) (z : ℤ × ℤ)
    (h1 : z ∈ dOdd w u1 u2 0) (h2 : z ∈ dOdd w u1 u2 1) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  by_cases hph : phase w = 1
  · exact so01_one_of w hw hd hph u1 hU1 ((dOdd_sub' w u1 u2 h1).1 (by omega)) ((dOdd_sub' w u1 u2 h2).1 (by omega))
  · exact so01_one_ef w hw hd hph u1 hU1 ((dOdd_sub' w u1 u2 h1).1 (by omega)) ((dOdd_sub' w u1 u2 h2).1 (by omega))

/-- **Copies `4` and `5` of the even standard child do not meet** after a `1`. -/
theorem swapEven45_one (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? = some Digit.one) (z : ℤ × ℤ)
    (h1 : z ∈ dEven w u1 u2 4) (h2 : z ∈ dEven w u1 u2 5) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  by_cases hph : phase w = 1
  · exact se45_one_of w hw hd hph u2 hU2 ((dEven_sub' w u1 u2 h1).2 0 rfl) ((dEven_sub' w u1 u2 h2).2 1 rfl)
  · exact se45_one_ef w hw hd hph u2 hU2 ((dEven_sub' w u1 u2 h1).2 0 rfl) ((dEven_sub' w u1 u2 h2).2 1 rfl)

/-- **Copies `2` and `5` of the odd standard child do not meet** after a `2`. -/
theorem swapOdd25_two (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? = some Digit.two) (z : ℤ × ℤ)
    (h1 : z ∈ dOdd w u1 u2 2) (h2 : z ∈ dOdd w u1 u2 5) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  by_cases hph : phase w = 1
  · exact so25_two_of w hw hd hph u2 hU2 ((dOdd_sub' w u1 u2 h1).2 0 rfl) ((dOdd_sub' w u1 u2 h2).2 3 rfl)
  · exact so25_two_ef w hw hd hph u2 hU2 ((dOdd_sub' w u1 u2 h1).2 0 rfl) ((dOdd_sub' w u1 u2 h2).2 3 rfl)

/-- **Copies `2` and `5` of the odd standard child do not meet** after a `1`, `W_1` even. -/
theorem swapOdd25_one (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (z : ℤ × ℤ)
    (h1 : z ∈ dOdd w u1 u2 2) (h2 : z ∈ dOdd w u1 u2 5) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  exact so25_one_ef w hw hd hph u2 hU2 ((dOdd_sub' w u1 u2 h1).2 0 rfl) ((dOdd_sub' w u1 u2 h2).2 3 rfl)

/-- **Copies `3` and `4` of the odd standard child do not meet** after a `2`. -/
theorem swapOdd34_two (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? = some Digit.two) (z : ℤ × ℤ)
    (h1 : z ∈ dOdd w u1 u2 3) (h2 : z ∈ dOdd w u1 u2 4) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  by_cases hph : phase w = 1
  · exact so34_two_of w hw hd hph u2 hU2 ((dOdd_sub' w u1 u2 h1).2 1 rfl) ((dOdd_sub' w u1 u2 h2).2 2 rfl)
  · exact so34_two_ef w hw hd hph u2 hU2 ((dOdd_sub' w u1 u2 h1).2 1 rfl) ((dOdd_sub' w u1 u2 h2).2 2 rfl)

/-- **Copies `3` and `4` of the odd standard child do not meet** after a `1`, `W_1` odd. -/
theorem swapOdd34_one (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (z : ℤ × ℤ)
    (h1 : z ∈ dOdd w u1 u2 3) (h2 : z ∈ dOdd w u1 u2 4) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  exact so34_one_of w hw hd hph u2 hU2 ((dOdd_sub' w u1 u2 h1).2 1 rfl) ((dOdd_sub' w u1 u2 h2).2 2 rfl)

/-- **Copies `0` and `3` of the even standard child do not meet** after a `1`. -/
theorem swapEven03_one (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? = some Digit.one) (z : ℤ × ℤ)
    (h1 : z ∈ dEven w u1 u2 0) (h2 : z ∈ dEven w u1 u2 3) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  by_cases hph : phase w = 1
  · exact se03_one_of w hw hd hph u1 hU1 ((dEven_sub' w u1 u2 h1).1 (by omega)) ((dEven_sub' w u1 u2 h2).1 (by omega))
  · exact se03_one_ef w hw hd hph u1 hU1 ((dEven_sub' w u1 u2 h1).1 (by omega)) ((dEven_sub' w u1 u2 h2).1 (by omega))

/-- **Copies `0` and `3` of the even standard child do not meet** after a `3`. -/
theorem swapEven03_three (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? = some Digit.three) (z : ℤ × ℤ)
    (h1 : z ∈ dEven w u1 u2 0) (h2 : z ∈ dEven w u1 u2 3) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  by_cases hph : phase w = 1
  · exact se03_three_of w hw hd hph u1 hU1 ((dEven_sub' w u1 u2 h1).1 (by omega)) ((dEven_sub' w u1 u2 h2).1 (by omega))
  · exact se03_three_ef w hw hd hph u1 hU1 ((dEven_sub' w u1 u2 h1).1 (by omega)) ((dEven_sub' w u1 u2 h2).1 (by omega))

/-- **Copies `1` and `2` of the even standard child do not meet** after a `3`. -/
theorem swapEven12_three (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? = some Digit.three) (z : ℤ × ℤ)
    (h1 : z ∈ dEven w u1 u2 1) (h2 : z ∈ dEven w u1 u2 2) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  by_cases hph : phase w = 1
  · exact se12_three_of w hw hd hph u1 hU1 ((dEven_sub' w u1 u2 h1).1 (by omega)) ((dEven_sub' w u1 u2 h2).1 (by omega))
  · exact se12_three_ef w hw hd hph u1 hU1 ((dEven_sub' w u1 u2 h1).1 (by omega)) ((dEven_sub' w u1 u2 h2).1 (by omega))

end FLatticePaper.Tiles.SwapDisjoint
