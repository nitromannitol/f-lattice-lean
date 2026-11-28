import FLatticePaper.Tiles.SwapContainPairs

/-! # The overlap of a meeting swapped pair: the pairs of copies separated by the boxes of the parent tiles

The pairs of copies of the two frames (as in `SwapContainPairs`) that the strips do not separate are separated by a coordinate,
through the boxes of the parent tiles (`SwapContainCore.sep_x`, `sep_y`). Generated. -/

namespace FLatticePaper.Tiles.SwapContainBox

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SameParentCopies FLatticePaper.Tiles.SwapContainCore
open FLatticePaper.Tiles.ChildGlue (oddP oddQ evenP evenQ)

set_option hygiene false in
/-- Unfolds the offsets of the two frames and of the copies into the vectors of the parents of `u`. -/
macro "swap_unfold'" : tactic => `(tactic| (simp only [oddP, oddQ, evenP, evenQ, MixedPieces.pOffsetsOdd,
  MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, hfw, hfu, ↓reduceIte, Bool.false_eq_true,
  List.getD_cons_succ, List.getD_cons_zero, CeilWords.parentsAt_snoc_one, CeilWords.parentsAt_snoc_two,
  CeilWords.parentsAt_snoc_three, tv1o_cur, tv2_curO, tv1e_cur, tv2_curE] at ha hb))

set_option hygiene false in
/-- Closes the box inequality in the entries of the parents of `u`. -/
macro "box_close" : tactic => `(tactic| (simp only [loX, hiX, hiY, e1, e2, if_true, if_false, Bool.false_eq_true, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero]; linarith))

theorem e12_one_of_02 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_x U1 U2 false true ?_ hb ha
  box_close

theorem e12_one_of_51 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_x U1 U2 true false ?_ hb ha
  box_close

theorem e12_one_ef_03 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_y U1 U2 true false ?_ ha hb
  box_close

theorem e12_one_ef_41 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_y U1 U2 false true ?_ ha hb
  box_close

theorem e45_three_ef_10 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_y U1 U2 true true ?_ ha hb
  box_close

theorem e45_three_ef_32 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_y U1 U2 true true ?_ ha hb
  box_close

theorem e45_three_of_10 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_x U1 U2 true true ?_ hb ha
  box_close

theorem e45_three_of_32 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_x U1 U2 true true ?_ hb ha
  box_close

theorem o01_two_ef_23 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_x U1 U2 false false ?_ hb ha
  box_close

theorem o01_two_ef_45 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_x U1 U2 false false ?_ hb ha
  box_close

theorem o01_two_of_32 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_y U1 U2 false false ?_ ha hb
  box_close

theorem o01_two_of_54 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_y U1 U2 false false ?_ ha hb
  box_close

theorem o25_one_ef_24 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_x U1 U2 false true ?_ hb ha
  box_close

theorem o25_one_ef_51 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_x U1 U2 true false ?_ hb ha
  box_close

theorem o34_one_of_24 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_y U1 U2 true false ?_ ha hb
  box_close

theorem o34_one_of_51 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold'
  have e1 : StandardClause.fracOdd U1 = (parentsAt u).odd := hU1
  have e2 : StandardClause.fracEven U2 = (parentsAt u).even := hU2
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior u (H3Data.nonbase_one_two hu)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior u (H3Data.nonbase_one_three hu)
  refine sep_y U1 U2 false true ?_ ha hb
  box_close

end FLatticePaper.Tiles.SwapContainBox
