import FLatticePaper.Tiles.SameParentAlt

/-! Copies of one parent tile that are not a doubled pair and are not exchanged by the half-turn, among the six copies of the
standard decomposition of a child that is not corrected (the odd child after a `1` or a `2`: copies `2, 4` and `3, 5` of the even
parent; the even child after a `1` or a `3`: copies `0, 2` and `1, 3` of the odd parent), do not meet. The separation is that
of `SameParentCopies` and `SameParentAlt`. The statements on the copies of `ClosedPathAssembly` are `stdOdd_same_disjoint` and
`stdEven_same_disjoint`. -/

namespace FLatticePaper.Tiles.SameParentStd

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.H3Bounds FLatticePaper.Tiles.H3Pairs
  FLatticePaper.Tiles.SameParentCopies FLatticePaper.Tiles.SameParentAlt
open FLatticePaper.Tiles.ChildGlue (oddP oddQ evenP evenQ)
open FLatticePaper.Tiles.ClosedPathAssembly (dOdd dEven)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)

/-- Copies `2` and `4` of the odd standard child after a `1`, `W_1` odd. -/
theorem so24_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 0 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 2 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  have r3 := rel_one_qnum w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `2` and `4` of the odd standard child after a `1`, `W_1` even. -/
theorem so24_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 0 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 2 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  have r3 := rel_one_qint w hw hd hph
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `2` and `4` of the odd standard child after a `2`, `W_1` odd. -/
theorem so24_two_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 0 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 2 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `2` and `4` of the odd standard child after a `2`, `W_1` even. -/
theorem so24_two_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 0 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 2 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `3` and `5` of the odd standard child after a `1`, `W_1` odd. -/
theorem so35_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 1 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 3 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  have r3 := rel_one_qnum w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `3` and `5` of the odd standard child after a `1`, `W_1` even. -/
theorem so35_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 1 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 3 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  have r3 := rel_one_qint w hw hd hph
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `3` and `5` of the odd standard child after a `2`, `W_1` odd. -/
theorem so35_two_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 1 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 3 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `3` and `5` of the odd standard child after a `2`, `W_1` even. -/
theorem so35_two_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (oddQ w).getD 1 0 ∈ evenTile U)
    (hb : z - (oddQ w).getD 3 0 ∈ evenTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [oddQ, MixedPieces.qOffsetsOdd, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `2` of the even standard child after a `1`, `W_1` odd. -/
theorem se02_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 0 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 2 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `2` of the even standard child after a `1`, `W_1` even. -/
theorem se02_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 0 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 2 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `2` of the even standard child after a `3`, `W_1` odd. -/
theorem se02_three_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 0 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 2 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `2` of the even standard child after a `3`, `W_1` even. -/
theorem se02_three_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 0 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 2 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `3` of the even standard child after a `1`, `W_1` odd. -/
theorem se13_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 1 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 3 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `3` of the even standard child after a `1`, `W_1` even. -/
theorem se13_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 1 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 3 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `3` of the even standard child after a `3`, `W_1` odd. -/
theorem se13_three_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 1 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 3 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_eq w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `3` of the even standard child after a `3`, `W_1` even. -/
theorem se13_three_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (evenP w).getD 1 0 ∈ oddTile U)
    (hb : z - (evenP w).getD 3 0 ∈ oddTile U) : False := by
  have hfl := ClosedPathAlt.beq_of_ne w hph
  simp only [evenP, MixedPieces.pOffsetsEven, hfl, ↓reduceIte, Bool.false_eq_true, List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

theorem dOdd_sub (w u1 u2 : Word) {z : ℤ × ℤ} {k : ℕ} (h : z ∈ dOdd w u1 u2 k) (m : ℕ) (hm : k = m + 2) :
    z - (oddQ w).getD m 0 ∈ evenTile u2 := by
  subst hm
  have hl : (oddP w).length = 2 := by unfold oddP MixedPieces.pOffsetsOdd; split_ifs <;> rfl
  simp only [dOdd, ChildGlue.pieceSet, hl, if_neg (show ¬ m + 2 < 2 by omega), Nat.add_sub_cancel] at h
  exact Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ h)

/-- **The copies of one parent of the odd standard child that are not a doubled pair and are not exchanged by the half-turn do
not meet**, at every non-base word whose odd child is not corrected. -/
theorem stdOdd_same_disjoint (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? ≠ some Digit.three) (i j : ℕ)
    (hij : (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2) ∨ (i = 3 ∧ j = 5) ∨ (i = 5 ∧ j = 3)) (z : ℤ × ℤ) (h1 : z ∈ dOdd w u1 u2 i) (h2 : z ∈ dOdd w u1 u2 j) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  have hne : w.getLast? ≠ none := by
    intro h
    exact hw (Or.inl (List.getLast?_eq_none_iff.1 h))
  obtain ⟨dg, hdg⟩ := Option.ne_none_iff_exists'.mp hne
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases dg
    · by_cases hph : phase w = 1
      · exact so24_one_of w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h1 _ rfl) (dOdd_sub w u1 u2 h2 _ rfl)
      · exact so24_one_ef w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h1 _ rfl) (dOdd_sub w u1 u2 h2 _ rfl)
    · by_cases hph : phase w = 1
      · exact so24_two_of w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h1 _ rfl) (dOdd_sub w u1 u2 h2 _ rfl)
      · exact so24_two_ef w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h1 _ rfl) (dOdd_sub w u1 u2 h2 _ rfl)
    · exact absurd hdg hd
  · cases dg
    · by_cases hph : phase w = 1
      · exact so24_one_of w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h2 _ rfl) (dOdd_sub w u1 u2 h1 _ rfl)
      · exact so24_one_ef w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h2 _ rfl) (dOdd_sub w u1 u2 h1 _ rfl)
    · by_cases hph : phase w = 1
      · exact so24_two_of w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h2 _ rfl) (dOdd_sub w u1 u2 h1 _ rfl)
      · exact so24_two_ef w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h2 _ rfl) (dOdd_sub w u1 u2 h1 _ rfl)
    · exact absurd hdg hd
  · cases dg
    · by_cases hph : phase w = 1
      · exact so35_one_of w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h1 _ rfl) (dOdd_sub w u1 u2 h2 _ rfl)
      · exact so35_one_ef w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h1 _ rfl) (dOdd_sub w u1 u2 h2 _ rfl)
    · by_cases hph : phase w = 1
      · exact so35_two_of w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h1 _ rfl) (dOdd_sub w u1 u2 h2 _ rfl)
      · exact so35_two_ef w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h1 _ rfl) (dOdd_sub w u1 u2 h2 _ rfl)
    · exact absurd hdg hd
  · cases dg
    · by_cases hph : phase w = 1
      · exact so35_one_of w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h2 _ rfl) (dOdd_sub w u1 u2 h1 _ rfl)
      · exact so35_one_ef w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h2 _ rfl) (dOdd_sub w u1 u2 h1 _ rfl)
    · by_cases hph : phase w = 1
      · exact so35_two_of w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h2 _ rfl) (dOdd_sub w u1 u2 h1 _ rfl)
      · exact so35_two_ef w hw hdg hph u2 hU2 (dOdd_sub w u1 u2 h2 _ rfl) (dOdd_sub w u1 u2 h1 _ rfl)
    · exact absurd hdg hd

theorem dEven_sub (w u1 u2 : Word) {z : ℤ × ℤ} {k : ℕ} (h : z ∈ dEven w u1 u2 k) (hk : k < 4) :
    z - (evenP w).getD k 0 ∈ oddTile u1 := by
  have hl : (evenP w).length = 4 := by unfold evenP MixedPieces.pOffsetsEven; split_ifs <;> rfl
  simp only [dEven, ChildGlue.pieceSet, hl, if_pos hk] at h
  exact Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ h)

/-- **The copies of one parent of the even standard child that are not a doubled pair and are not exchanged by the half-turn do
not meet**, at every non-base word whose even child is not corrected. -/
theorem stdEven_same_disjoint (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? ≠ some Digit.two) (i j : ℕ)
    (hij : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)) (z : ℤ × ℤ) (h1 : z ∈ dEven w u1 u2 i) (h2 : z ∈ dEven w u1 u2 j) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  have hne : w.getLast? ≠ none := by
    intro h
    exact hw (Or.inl (List.getLast?_eq_none_iff.1 h))
  obtain ⟨dg, hdg⟩ := Option.ne_none_iff_exists'.mp hne
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases dg
    · by_cases hph : phase w = 1
      · exact se02_one_of w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h1 (by omega)) (dEven_sub w u1 u2 h2 (by omega))
      · exact se02_one_ef w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h1 (by omega)) (dEven_sub w u1 u2 h2 (by omega))
    · exact absurd hdg hd
    · by_cases hph : phase w = 1
      · exact se02_three_of w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h1 (by omega)) (dEven_sub w u1 u2 h2 (by omega))
      · exact se02_three_ef w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h1 (by omega)) (dEven_sub w u1 u2 h2 (by omega))
  · cases dg
    · by_cases hph : phase w = 1
      · exact se02_one_of w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h2 (by omega)) (dEven_sub w u1 u2 h1 (by omega))
      · exact se02_one_ef w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h2 (by omega)) (dEven_sub w u1 u2 h1 (by omega))
    · exact absurd hdg hd
    · by_cases hph : phase w = 1
      · exact se02_three_of w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h2 (by omega)) (dEven_sub w u1 u2 h1 (by omega))
      · exact se02_three_ef w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h2 (by omega)) (dEven_sub w u1 u2 h1 (by omega))
  · cases dg
    · by_cases hph : phase w = 1
      · exact se13_one_of w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h1 (by omega)) (dEven_sub w u1 u2 h2 (by omega))
      · exact se13_one_ef w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h1 (by omega)) (dEven_sub w u1 u2 h2 (by omega))
    · exact absurd hdg hd
    · by_cases hph : phase w = 1
      · exact se13_three_of w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h1 (by omega)) (dEven_sub w u1 u2 h2 (by omega))
      · exact se13_three_ef w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h1 (by omega)) (dEven_sub w u1 u2 h2 (by omega))
  · cases dg
    · by_cases hph : phase w = 1
      · exact se13_one_of w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h2 (by omega)) (dEven_sub w u1 u2 h1 (by omega))
      · exact se13_one_ef w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h2 (by omega)) (dEven_sub w u1 u2 h1 (by omega))
    · exact absurd hdg hd
    · by_cases hph : phase w = 1
      · exact se13_three_of w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h2 (by omega)) (dEven_sub w u1 u2 h1 (by omega))
      · exact se13_three_ef w hw hdg hph u1 hU1 (dEven_sub w u1 u2 h2 (by omega)) (dEven_sub w u1 u2 h1 (by omega))

end FLatticePaper.Tiles.SameParentStd
