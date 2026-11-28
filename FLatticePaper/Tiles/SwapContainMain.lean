import FLatticePaper.Tiles.SwapContainNested
import FLatticePaper.Tiles.GlueFull

/-! # The overlap of a meeting swapped pair lies in the grandparent copy (text, lines 4545-4561)

For each meeting swapped pair of a word `u d`, a point of both copies of the register tile `T` lies in the copy `X` of the
decomposition of `T` in the first frame: `T` is the union of its six standard copies in each frame (`GlueFull.oddTile_union`,
`evenTile_union`), a point in the copy `A` of the first frame and `B` of the second lies in `X` when `A = X`, or `B = Y` (the same
copy in the second frame), and otherwise the pair `A`, `B` is separated (`SwapContainPairs`, `SwapContainBox`) or nested
(`SwapContainNested`). Generated. -/

namespace FLatticePaper.Tiles.SwapContainMain

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SwapContainCore
open FLatticePaper.Tiles.ChildGlue (oddP oddQ evenP evenQ)

set_option hygiene false in
/-- Unfolds the offsets of the frames and of the register's copies into the vectors of the parents of `u`. -/
macro "rel_unfold" : tactic => `(tactic| (simp only [oddP, oddQ, evenP, evenQ, MixedPieces.pOffsetsOdd,
  MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, hfw, hfu, ↓reduceIte, Bool.false_eq_true,
  List.getD_cons_succ, List.getD_cons_zero, CeilWords.parentsAt_snoc_one, CeilWords.parentsAt_snoc_two,
  CeilWords.parentsAt_snoc_three, tv1o_cur, tv2_curO, tv1e_cur, tv2_curE]))

/-- **The overlap of the copies `0`, `1` of the frame list** of `u 2` (class O01, `W_1` of `u` odd) lies in the copy `1` of the
first frame. -/
theorem contain_o01_of (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word)
    (hT1 : (stateAt u).tOdd = oddTile U1) (hT2 : (stateAt u).tEven = evenTile U2) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site} (h1 : z - (oddP (u ++ [Digit.two])).getD 0 0 ∈ oddTile u) (h2 : z - (oddP (u ++ [Digit.two])).getD 1 0 ∈ oddTile u) :
    z - (oddP (u ++ [Digit.two])).getD 0 0 - (oddP u).getD 1 0 ∈ oddTile U1 := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = true := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  have rel : (oddP (u ++ [Digit.two])).getD 0 0 + (oddP u).getD 1 0 = (oddP (u ++ [Digit.two])).getD 1 0 + (oddP u).getD 0 0 := by rel_unfold; abel
  obtain ⟨A, hA6, hA⟩ := (GlueFull.oddTile_union u U1 U2 hu hT1 hT2 _).1 h1
  obtain ⟨B, hB6, hB⟩ := (GlueFull.oddTile_union u U1 U2 hu hT1 hT2 _).1 h2
  interval_cases A <;> interval_cases B
  · simp only [GlueFull.offO] at hB
    rw [show z - (oddP (u ++ [Digit.two])).getD 0 0 - (oddP u).getD 1 0 = z - (oddP (u ++ [Digit.two])).getD 1 0 - (oddP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB ⊢
    simpa using SwapContainNested.o01_nested u hu U1 hT1 (by simpa using hA) (by simpa using hB)
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_02 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_03 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_04 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_05 u hu hph U1 U2 hU1 hU2 hA hB
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simp only [GlueFull.offO] at hB
    rw [show z - (oddP (u ++ [Digit.two])).getD 0 0 - (oddP u).getD 1 0 = z - (oddP (u ++ [Digit.two])).getD 1 0 - (oddP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_21 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_22 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_23 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_24 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_25 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (oddP (u ++ [Digit.two])).getD 0 0 - (oddP u).getD 1 0 = z - (oddP (u ++ [Digit.two])).getD 1 0 - (oddP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_31 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.o01_two_of_32 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_33 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_34 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_35 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (oddP (u ++ [Digit.two])).getD 0 0 - (oddP u).getD 1 0 = z - (oddP (u ++ [Digit.two])).getD 1 0 - (oddP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_41 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_42 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_43 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_44 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_45 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (oddP (u ++ [Digit.two])).getD 0 0 - (oddP u).getD 1 0 = z - (oddP (u ++ [Digit.two])).getD 1 0 - (oddP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_51 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_52 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_53 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.o01_two_of_54 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_of_55 u hu hph U1 U2 hU1 hU2 hA hB

/-- **The overlap of the copies `0`, `1` of the frame list** of `u 2` (class O01, `W_1` of `u` even) lies in the copy `1` of the
first frame. -/
theorem contain_o01_ef (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word)
    (hT1 : (stateAt u).tOdd = oddTile U1) (hT2 : (stateAt u).tEven = evenTile U2) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site} (h1 : z - (oddP (u ++ [Digit.two])).getD 0 0 ∈ oddTile u) (h2 : z - (oddP (u ++ [Digit.two])).getD 1 0 ∈ oddTile u) :
    z - (oddP (u ++ [Digit.two])).getD 0 0 - (oddP u).getD 1 0 ∈ oddTile U1 := by
  have hfw : (phase (u ++ [Digit.two]) == 1) = false := by
    rw [JointRot.phase_snoc_two]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  have rel : (oddP (u ++ [Digit.two])).getD 0 0 + (oddP u).getD 1 0 = (oddP (u ++ [Digit.two])).getD 1 0 + (oddP u).getD 0 0 := by rel_unfold; abel
  obtain ⟨A, hA6, hA⟩ := (GlueFull.oddTile_union u U1 U2 hu hT1 hT2 _).1 h1
  obtain ⟨B, hB6, hB⟩ := (GlueFull.oddTile_union u U1 U2 hu hT1 hT2 _).1 h2
  interval_cases A <;> interval_cases B
  · simp only [GlueFull.offO] at hB
    rw [show z - (oddP (u ++ [Digit.two])).getD 0 0 - (oddP u).getD 1 0 = z - (oddP (u ++ [Digit.two])).getD 1 0 - (oddP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB ⊢
    simpa using SwapContainNested.o01_nested u hu U1 hT1 (by simpa using hA) (by simpa using hB)
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_02 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_03 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_04 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_05 u hu hph U1 U2 hU1 hU2 hA hB
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simp only [GlueFull.offO] at hB
    rw [show z - (oddP (u ++ [Digit.two])).getD 0 0 - (oddP u).getD 1 0 = z - (oddP (u ++ [Digit.two])).getD 1 0 - (oddP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_21 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_22 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.o01_two_ef_23 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_24 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_25 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (oddP (u ++ [Digit.two])).getD 0 0 - (oddP u).getD 1 0 = z - (oddP (u ++ [Digit.two])).getD 1 0 - (oddP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_31 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_32 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_33 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_34 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_35 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (oddP (u ++ [Digit.two])).getD 0 0 - (oddP u).getD 1 0 = z - (oddP (u ++ [Digit.two])).getD 1 0 - (oddP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_41 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_42 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_43 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_44 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.o01_two_ef_45 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (oddP (u ++ [Digit.two])).getD 0 0 - (oddP u).getD 1 0 = z - (oddP (u ++ [Digit.two])).getD 1 0 - (oddP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_51 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_52 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_53 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_54 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o01_two_ef_55 u hu hph U1 U2 hU1 hU2 hA hB

/-- **The overlap of the copies `0`, `3` of the frame list** of `u 1` (class O25, `W_1` of `u` even) lies in the copy `3` of the
first frame. -/
theorem contain_o25_ef (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word)
    (hT1 : (stateAt u).tOdd = oddTile U1) (hT2 : (stateAt u).tEven = evenTile U2) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site} (h1 : z - (oddQ (u ++ [Digit.one])).getD 0 0 ∈ evenTile u) (h2 : z - (oddQ (u ++ [Digit.one])).getD 3 0 ∈ evenTile u) :
    z - (oddQ (u ++ [Digit.one])).getD 0 0 - (evenP u).getD 3 0 ∈ oddTile U1 := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  have rel : (oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 3 0 = (oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 0 0 := by rel_unfold; abel
  obtain ⟨A, hA6, hA⟩ := (GlueFull.evenTile_union u U1 U2 hu hT1 hT2 _).1 h1
  obtain ⟨B, hB6, hB⟩ := (GlueFull.evenTile_union u U1 U2 hu hT1 hT2 _).1 h2
  interval_cases A <;> interval_cases B
  · simp only [GlueFull.offE] at hB
    rw [show z - (oddQ (u ++ [Digit.one])).getD 0 0 - (evenP u).getD 3 0 = z - (oddQ (u ++ [Digit.one])).getD 3 0 - (evenP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_01 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_02 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_03 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_04 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_05 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (oddQ (u ++ [Digit.one])).getD 0 0 - (evenP u).getD 3 0 = z - (oddQ (u ++ [Digit.one])).getD 3 0 - (evenP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_11 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB ⊢
    simpa using SwapContainNested.o25_mid u hu hph U1 hT1 (by simpa using hA) (by simpa using hB)
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_13 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_14 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_15 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (oddQ (u ++ [Digit.one])).getD 0 0 - (evenP u).getD 3 0 = z - (oddQ (u ++ [Digit.one])).getD 3 0 - (evenP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_21 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_22 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_23 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.o25_one_ef_24 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_25 u hu hph U1 U2 hU1 hU2 hA hB
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simp only [GlueFull.offE] at hB
    rw [show z - (oddQ (u ++ [Digit.one])).getD 0 0 - (evenP u).getD 3 0 = z - (oddQ (u ++ [Digit.one])).getD 3 0 - (evenP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_41 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_42 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_43 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_44 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_45 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (oddQ (u ++ [Digit.one])).getD 0 0 - (evenP u).getD 3 0 = z - (oddQ (u ++ [Digit.one])).getD 3 0 - (evenP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.o25_one_ef_51 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_52 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_53 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_54 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o25_one_ef_55 u hu hph U1 U2 hU1 hU2 hA hB

/-- **The overlap of the copies `1`, `2` of the frame list** of `u 1` (class O34, `W_1` of `u` odd) lies in the copy `3` of the
first frame. -/
theorem contain_o34_of (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word)
    (hT1 : (stateAt u).tOdd = oddTile U1) (hT2 : (stateAt u).tEven = evenTile U2) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site} (h1 : z - (oddQ (u ++ [Digit.one])).getD 1 0 ∈ evenTile u) (h2 : z - (oddQ (u ++ [Digit.one])).getD 2 0 ∈ evenTile u) :
    z - (oddQ (u ++ [Digit.one])).getD 1 0 - (evenP u).getD 3 0 ∈ oddTile U1 := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  have rel : (oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 3 0 = (oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 0 0 := by rel_unfold; abel
  obtain ⟨A, hA6, hA⟩ := (GlueFull.evenTile_union u U1 U2 hu hT1 hT2 _).1 h1
  obtain ⟨B, hB6, hB⟩ := (GlueFull.evenTile_union u U1 U2 hu hT1 hT2 _).1 h2
  interval_cases A <;> interval_cases B
  · simp only [GlueFull.offE] at hB
    rw [show z - (oddQ (u ++ [Digit.one])).getD 1 0 - (evenP u).getD 3 0 = z - (oddQ (u ++ [Digit.one])).getD 2 0 - (evenP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_01 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_02 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_03 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_04 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_05 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (oddQ (u ++ [Digit.one])).getD 1 0 - (evenP u).getD 3 0 = z - (oddQ (u ++ [Digit.one])).getD 2 0 - (evenP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_11 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB ⊢
    simpa using SwapContainNested.o34_mid u hu hph U1 hT1 (by simpa using hA) (by simpa using hB)
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_13 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_14 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_15 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (oddQ (u ++ [Digit.one])).getD 1 0 - (evenP u).getD 3 0 = z - (oddQ (u ++ [Digit.one])).getD 2 0 - (evenP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_21 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_22 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_23 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.o34_one_of_24 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_25 u hu hph U1 U2 hU1 hU2 hA hB
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simp only [GlueFull.offE] at hB
    rw [show z - (oddQ (u ++ [Digit.one])).getD 1 0 - (evenP u).getD 3 0 = z - (oddQ (u ++ [Digit.one])).getD 2 0 - (evenP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_41 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_42 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_43 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_44 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_45 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (oddQ (u ++ [Digit.one])).getD 1 0 - (evenP u).getD 3 0 = z - (oddQ (u ++ [Digit.one])).getD 2 0 - (evenP u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.o34_one_of_51 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_52 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_53 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_54 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.o34_one_of_55 u hu hph U1 U2 hU1 hU2 hA hB

/-- **The overlap of the copies `1`, `2` of the frame list** of `u 1` (class E12, `W_1` of `u` odd) lies in the copy `4` of the
first frame. -/
theorem contain_e12_of (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word)
    (hT1 : (stateAt u).tOdd = oddTile U1) (hT2 : (stateAt u).tEven = evenTile U2) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site} (h1 : z - (evenP (u ++ [Digit.one])).getD 1 0 ∈ oddTile u) (h2 : z - (evenP (u ++ [Digit.one])).getD 2 0 ∈ oddTile u) :
    z - (evenP (u ++ [Digit.one])).getD 1 0 - (oddQ u).getD 2 0 ∈ evenTile U2 := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  have rel : (evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 2 0 = (evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 1 0 := by rel_unfold; abel
  obtain ⟨A, hA6, hA⟩ := (GlueFull.oddTile_union u U1 U2 hu hT1 hT2 _).1 h1
  obtain ⟨B, hB6, hB⟩ := (GlueFull.oddTile_union u U1 U2 hu hT1 hT2 _).1 h2
  interval_cases A <;> interval_cases B
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_00 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_01 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.e12_one_of_02 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (evenP (u ++ [Digit.one])).getD 1 0 - (oddQ u).getD 2 0 = z - (evenP (u ++ [Digit.one])).getD 2 0 - (oddQ u).getD 1 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_04 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_05 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_10 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_11 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_12 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (evenP (u ++ [Digit.one])).getD 1 0 - (oddQ u).getD 2 0 = z - (evenP (u ++ [Digit.one])).getD 2 0 - (oddQ u).getD 1 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_14 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_15 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_20 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_21 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_22 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (evenP (u ++ [Digit.one])).getD 1 0 - (oddQ u).getD 2 0 = z - (evenP (u ++ [Digit.one])).getD 2 0 - (oddQ u).getD 1 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_24 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB ⊢
    simpa using SwapContainNested.e12_mid_of u hu hph U2 hT2 (by simpa using hA) (by simpa using hB)
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_30 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_31 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_32 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (evenP (u ++ [Digit.one])).getD 1 0 - (oddQ u).getD 2 0 = z - (evenP (u ++ [Digit.one])).getD 2 0 - (oddQ u).getD 1 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_34 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_35 u hu hph U1 U2 hU1 hU2 hA hB
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_50 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.e12_one_of_51 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_52 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (evenP (u ++ [Digit.one])).getD 1 0 - (oddQ u).getD 2 0 = z - (evenP (u ++ [Digit.one])).getD 2 0 - (oddQ u).getD 1 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_54 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_of_55 u hu hph U1 U2 hU1 hU2 hA hB

/-- **The overlap of the copies `1`, `2` of the frame list** of `u 1` (class E12, `W_1` of `u` even) lies in the copy `5` of the
first frame. -/
theorem contain_e12_ef (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word)
    (hT1 : (stateAt u).tOdd = oddTile U1) (hT2 : (stateAt u).tEven = evenTile U2) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site} (h1 : z - (evenP (u ++ [Digit.one])).getD 1 0 ∈ oddTile u) (h2 : z - (evenP (u ++ [Digit.one])).getD 2 0 ∈ oddTile u) :
    z - (evenP (u ++ [Digit.one])).getD 1 0 - (oddQ u).getD 3 0 ∈ evenTile U2 := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by
    rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  have rel : (evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 3 0 = (evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 0 0 := by rel_unfold; abel
  obtain ⟨A, hA6, hA⟩ := (GlueFull.oddTile_union u U1 U2 hu hT1 hT2 _).1 h1
  obtain ⟨B, hB6, hB⟩ := (GlueFull.oddTile_union u U1 U2 hu hT1 hT2 _).1 h2
  interval_cases A <;> interval_cases B
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_00 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_01 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (evenP (u ++ [Digit.one])).getD 1 0 - (oddQ u).getD 3 0 = z - (evenP (u ++ [Digit.one])).getD 2 0 - (oddQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.e12_one_ef_03 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_04 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_05 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_10 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_11 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (evenP (u ++ [Digit.one])).getD 1 0 - (oddQ u).getD 3 0 = z - (evenP (u ++ [Digit.one])).getD 2 0 - (oddQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_13 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_14 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_15 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_20 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_21 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (evenP (u ++ [Digit.one])).getD 1 0 - (oddQ u).getD 3 0 = z - (evenP (u ++ [Digit.one])).getD 2 0 - (oddQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_23 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_24 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_25 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_30 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_31 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (evenP (u ++ [Digit.one])).getD 1 0 - (oddQ u).getD 3 0 = z - (evenP (u ++ [Digit.one])).getD 2 0 - (oddQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_33 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB ⊢
    simpa using SwapContainNested.e12_mid_ef u hu hph U2 hT2 (by simpa using hA) (by simpa using hB)
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_35 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_40 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.e12_one_ef_41 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offO] at hB
    rw [show z - (evenP (u ++ [Digit.one])).getD 1 0 - (oddQ u).getD 3 0 = z - (evenP (u ++ [Digit.one])).getD 2 0 - (oddQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_43 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_44 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offO] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e12_one_ef_45 u hu hph U1 U2 hU1 hU2 hA hB
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA
  · simpa [GlueFull.offO] using hA

/-- **The overlap of the copies `0`, `1` of the frame list** of `u 3` (class E45, `W_1` of `u` odd) lies in the copy `5` of the
first frame. -/
theorem contain_e45_of (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 U2 : Word)
    (hT1 : (stateAt u).tOdd = oddTile U1) (hT2 : (stateAt u).tEven = evenTile U2) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site} (h1 : z - (evenQ (u ++ [Digit.three])).getD 0 0 ∈ evenTile u) (h2 : z - (evenQ (u ++ [Digit.three])).getD 1 0 ∈ evenTile u) :
    z - (evenQ (u ++ [Digit.three])).getD 0 0 - (evenQ u).getD 1 0 ∈ evenTile U2 := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = true := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  have rel : (evenQ (u ++ [Digit.three])).getD 0 0 + (evenQ u).getD 1 0 = (evenQ (u ++ [Digit.three])).getD 1 0 + (evenQ u).getD 0 0 := by rel_unfold; abel
  obtain ⟨A, hA6, hA⟩ := (GlueFull.evenTile_union u U1 U2 hu hT1 hT2 _).1 h1
  obtain ⟨B, hB6, hB⟩ := (GlueFull.evenTile_union u U1 U2 hu hT1 hT2 _).1 h2
  interval_cases A <;> interval_cases B
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_00 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_01 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_02 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_03 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (evenQ (u ++ [Digit.three])).getD 0 0 - (evenQ u).getD 1 0 = z - (evenQ (u ++ [Digit.three])).getD 1 0 - (evenQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_05 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.e45_three_of_10 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_11 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_12 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_13 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (evenQ (u ++ [Digit.three])).getD 0 0 - (evenQ u).getD 1 0 = z - (evenQ (u ++ [Digit.three])).getD 1 0 - (evenQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_15 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_20 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_21 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_22 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_23 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (evenQ (u ++ [Digit.three])).getD 0 0 - (evenQ u).getD 1 0 = z - (evenQ (u ++ [Digit.three])).getD 1 0 - (evenQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_25 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_30 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_31 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.e45_three_of_32 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_33 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (evenQ (u ++ [Digit.three])).getD 0 0 - (evenQ u).getD 1 0 = z - (evenQ (u ++ [Digit.three])).getD 1 0 - (evenQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_35 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_40 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_41 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_42 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_of_43 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (evenQ (u ++ [Digit.three])).getD 0 0 - (evenQ u).getD 1 0 = z - (evenQ (u ++ [Digit.three])).getD 1 0 - (evenQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB ⊢
    simpa using SwapContainNested.e45_nested u hu U2 hT2 (by simpa using hA) (by simpa using hB)
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA

/-- **The overlap of the copies `0`, `1` of the frame list** of `u 3` (class E45, `W_1` of `u` even) lies in the copy `5` of the
first frame. -/
theorem contain_e45_ef (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 U2 : Word)
    (hT1 : (stateAt u).tOdd = oddTile U1) (hT2 : (stateAt u).tEven = evenTile U2) (hU1 : curO U1 = (parentsAt u).odd)
    (hU2 : curE U2 = (parentsAt u).even) {z : Site} (h1 : z - (evenQ (u ++ [Digit.three])).getD 0 0 ∈ evenTile u) (h2 : z - (evenQ (u ++ [Digit.three])).getD 1 0 ∈ evenTile u) :
    z - (evenQ (u ++ [Digit.three])).getD 0 0 - (evenQ u).getD 1 0 ∈ evenTile U2 := by
  have hfw : (phase (u ++ [Digit.three]) == 1) = false := by
    rw [JointRot.phase_snoc_three]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  have rel : (evenQ (u ++ [Digit.three])).getD 0 0 + (evenQ u).getD 1 0 = (evenQ (u ++ [Digit.three])).getD 1 0 + (evenQ u).getD 0 0 := by rel_unfold; abel
  obtain ⟨A, hA6, hA⟩ := (GlueFull.evenTile_union u U1 U2 hu hT1 hT2 _).1 h1
  obtain ⟨B, hB6, hB⟩ := (GlueFull.evenTile_union u U1 U2 hu hT1 hT2 _).1 h2
  interval_cases A <;> interval_cases B
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_00 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_01 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_02 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_03 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (evenQ (u ++ [Digit.three])).getD 0 0 - (evenQ u).getD 1 0 = z - (evenQ (u ++ [Digit.three])).getD 1 0 - (evenQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_05 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.e45_three_ef_10 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_11 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_12 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_13 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (evenQ (u ++ [Digit.three])).getD 0 0 - (evenQ u).getD 1 0 = z - (evenQ (u ++ [Digit.three])).getD 1 0 - (evenQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_15 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_20 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_21 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_22 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_23 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (evenQ (u ++ [Digit.three])).getD 0 0 - (evenQ u).getD 1 0 = z - (evenQ (u ++ [Digit.three])).getD 1 0 - (evenQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_25 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_30 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_31 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainBox.e45_three_ef_32 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_33 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (evenQ (u ++ [Digit.three])).getD 0 0 - (evenQ u).getD 1 0 = z - (evenQ (u ++ [Digit.three])).getD 1 0 - (evenQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_35 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_40 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_41 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_42 u hu hph U1 U2 hU1 hU2 hA hB
  · exfalso
    simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB
    exact SwapContainPairs.e45_three_ef_43 u hu hph U1 U2 hU1 hU2 hA hB
  · simp only [GlueFull.offE] at hB
    rw [show z - (evenQ (u ++ [Digit.three])).getD 0 0 - (evenQ u).getD 1 0 = z - (evenQ (u ++ [Digit.three])).getD 1 0 - (evenQ u).getD 0 0 by rw [sub_sub, sub_sub, rel]]
    simpa using hB
  · simp only [GlueFull.offE] at hA hB
    rw [sub_sub] at hA hB ⊢
    simpa using SwapContainNested.e45_nested u hu U2 hT2 (by simpa using hA) (by simpa using hB)
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA
  · simpa [GlueFull.offE] using hA

end FLatticePaper.Tiles.SwapContainMain
