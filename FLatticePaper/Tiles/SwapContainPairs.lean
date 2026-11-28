import FLatticePaper.Tiles.SwapContainCore
import FLatticePaper.Tiles.JointRot
import FLatticePaper.Tiles.CeilWords

/-! # The overlap of a meeting swapped pair: the separated pairs of copies of the two frames

For each meeting swapped pair of a word `w = u d` (the odd child `0, 1` after a `2`, `2, 5` after a `1` with `W_1` odd, `3, 4`
after a `1` with `W_1` even; the even child `1, 2` after a `1`, `4, 5` after a `3`), the copies `A`, `B` of the decomposition of
the register `u` in the two frames, other than the copy `G` and its partner, do not meet (`SwapContainCore.sep_lam`,
`sep_sig` at the mediant of the parents of `u`). Generated; the strip and the side of each pair are those of the numerics
(words up to length 7). -/

namespace FLatticePaper.Tiles.SwapContainPairs

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.H3Bounds FLatticePaper.Tiles.H3Pairs
  FLatticePaper.Tiles.SameParentCopies FLatticePaper.Tiles.SameParentAlt FLatticePaper.Tiles.SwapContainCore
open FLatticePaper.Tiles.ChildGlue (oddP oddQ evenP evenQ)

set_option hygiene false in
/-- Unfolds the offsets of the two frames and of the copies into the vectors of the parents of `u`. -/
macro "swap_unfold" : tactic => `(tactic| (simp only [oddP, oddQ, evenP, evenQ, MixedPieces.pOffsetsOdd,
  MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, hfw, hfu, ↓reduceIte, Bool.false_eq_true,
  List.getD_cons_succ, List.getD_cons_zero, CeilWords.parentsAt_snoc_one, CeilWords.parentsAt_snoc_two,
  CeilWords.parentsAt_snoc_three, tv1o_cur, tv2_curO, tv1e_cur, tv2_curE] at ha hb))

set_option hygiene false in
/-- Closes the separation inequality of a pair of copies. -/
macro "swap_close" : tactic => `(tactic| (simp only [loL, hiL, loS, hiS, hE, mLP, mLQ, mSP, mSQ, lam_add, lam_sub, lam_neg', lam_zero, sig_add, sig_sub, sig_neg', sig_zero, Bool.false_eq_true, if_true, if_false, one_eq_neg_one_false, neg_one_eq_one_false]; linarith))

theorem e12_one_of_00 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_01 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_of_04 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_of_05 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_of_10 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_11 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_12 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_14 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_15 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_20 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_21 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_of_22 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_24 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_25 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (hnc : u.getLast? ≠ some Digit.three) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · exact absurd hdu hnc

theorem e12_one_of_30 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_31 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_of_32 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_34 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_35 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_50 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_52 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_54 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_of_55 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_ef_00 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_01 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_04 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_05 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_10 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e12_one_ef_11 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_13 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_14 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_15 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_20 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_21 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_23 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_24 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_25 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_30 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_31 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_33 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_34 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (hnc : u.getLast? ≠ some Digit.three) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · exact absurd hdu hnc

theorem e12_one_ef_35 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_40 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_43 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_44 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e12_one_ef_45 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_00 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_01 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_02 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_03 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_05 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_11 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_12 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_13 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_15 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_20 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_21 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_22 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_23 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_25 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_30 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e45_three_ef_31 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_33 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_35 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_40 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_41 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_42 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_ef_43 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_00 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_01 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_02 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_03 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_05 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_11 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_12 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_13 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_15 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_20 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e45_three_of_21 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e45_three_of_22 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_23 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_25 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e45_three_of_30 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e45_three_of_31 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e45_three_of_33 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_35 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e45_three_of_40 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e45_three_of_41 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem e45_three_of_42 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem e45_three_of_43 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_ef_02 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_ef_03 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_ef_04 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_ef_05 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_ef_21 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_ef_22 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_ef_24 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_ef_25 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_ef_31 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_ef_32 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_ef_33 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_ef_34 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_ef_35 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_ef_41 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_ef_42 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_ef_43 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_ef_44 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_ef_51 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_ef_52 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_ef_53 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_ef_54 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_ef_55 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o01_two_of_02 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_03 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_04 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_05 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_21 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_22 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_23 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_24 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_25 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_31 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_33 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_34 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_35 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_41 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_42 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_43 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_44 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_45 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 2 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_51 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_52 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_53 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o01_two_of_55 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddQ u).getD 3 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_01 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_02 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_03 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_04 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_05 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_11 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_12 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (hnc : u.getLast? ≠ some Digit.two) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · exact absurd hdu hnc
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_13 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_14 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_15 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_21 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_22 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_23 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_25 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_41 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_42 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_43 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_44 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_45 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_52 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_53 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o25_one_ef_54 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) hb ha
    cases A <;> swap_close

theorem o25_one_ef_55 (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = -1 := if_neg hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    have r3 := rel_one_qint u hu hdu hph
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_01 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_02 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_03 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_04 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_05 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 0 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_11 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_12 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (hnc : u.getLast? ≠ some Digit.two) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · exact absurd hdu hnc
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_13 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_14 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_15 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_21 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_22 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_23 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_25 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 true false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_41 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 1 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_42 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_43 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_44 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_45 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_52 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 2 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_53 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 3 0) ∈ tileK U1 U2 true) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false true (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_54 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenQ u).getD 0 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_sig u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

theorem o34_one_of_55 (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site}
    (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenQ u).getD 1 0) ∈ tileK U1 U2 false) : False := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  swap_unfold
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals u
  obtain ⟨c1, c2⟩ := mediant_bounds u hu
  have hE : eW u = 1 := if_pos hph
  obtain ⟨du, hdu⟩ : ∃ du, u.getLast? = some du :=
    Option.ne_none_iff_exists'.mp (fun h => hu (Or.inl (List.getLast?_eq_none_iff.1 h)))
  cases du
  · have r1 := rel_one u hu hdu
    have r2 := rel_one_qnum u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_two u hu hdu
    have r2 := rel_two_qnum u hu hdu
    have r3 := rel_two_qint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close
  · have r1 := rel_three u hu hdu
    have r2 := rel_three_qnum u hu hdu
    have r3 := rel_three_pint u hu hdu
    refine sep_lam u hu U1 U2 hU1 hU2 false false (fun A => ?_) ha hb
    cases A <;> swap_close

end FLatticePaper.Tiles.SwapContainPairs
