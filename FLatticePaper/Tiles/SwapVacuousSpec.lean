import FLatticePaper.Tiles.GlueFull

/-! # The vacuous families of `SwapBaseInput`: the statements the assembly consumes

The one-base-register clauses of `SwapBaseInput` whose overlaps are empty (`SwapBaseClauses.pairCompat_of_disjoint`). Each field
is a statement about the pieces `oddFull f w` and `evenFull f w` of the word `w` of the family, with `GoodBelow D f w.length` and
`D.S = paperS`. The assembly (`SwapBaseInputAssembly`) dispatches every clause of `SwapBaseInput` to one of these fields or to
the nonvacuous clauses `SwapNonvac`, `SwapRegionClauses`. -/

namespace FLatticePaper.Tiles.SwapVacuousSpec

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.JointInduction
open FLatticePaper.Tiles.GlueFull FLatticePaper.Tiles.TileCompatInputs FLatticePaper.Tiles.WeakStepPaper

/-- The vacuous families. -/
structure SwapVacuous : Prop where
  /-- `w = [1]`: the odd pairs (0,1), (3,4) and the even pairs (0,3), (4,5). -/
  V5 : ∀ (D : JointData) (f : Word → JSlice) (w : Word), D.S = paperS → w = [Digit.one] →
    GoodBelow D f w.length →
      PairCompat (oddFull f w) 0 1 ∧ PairCompat (oddFull f w) 3 4 ∧
        PairCompat (evenFull f w) 0 3 ∧ PairCompat (evenFull f w) 4 5
  /-- `w = 3^k 1`, `k ≥ 1`: the odd pair (0,1), (3,4) and the even pairs (0,3), (4,5). -/
  V3 : ∀ (D : JointData) (f : Word → JSlice) (k : ℕ) (w : Word), D.S = paperS → 1 ≤ k →
    w = List.replicate k Digit.three ++ [Digit.one] → GoodBelow D f w.length →
      PairCompat (oddFull f w) 0 1 ∧ PairCompat (oddFull f w) 3 4 ∧
        PairCompat (evenFull f w) 0 3 ∧ PairCompat (evenFull f w) 4 5
  /-- `w = 2^k 1`, `k ≥ 1`: the odd pair (0,1), (3,4) and the even pairs (0,3), (4,5). -/
  V4 : ∀ (D : JointData) (f : Word → JSlice) (k : ℕ) (w : Word), D.S = paperS → 1 ≤ k →
    w = List.replicate k Digit.two ++ [Digit.one] → GoodBelow D f w.length →
      PairCompat (oddFull f w) 0 1 ∧ PairCompat (oddFull f w) 3 4 ∧
        PairCompat (evenFull f w) 0 3 ∧ PairCompat (evenFull f w) 4 5
  /-- `w = 3^(m+1) 2`: the odd pairs (3,4) and (2,5) (the odd pair (0,1) is the block `N1`). -/
  V1 : ∀ (D : JointData) (f : Word → JSlice) (m : ℕ) (w : Word), D.S = paperS →
    w = List.replicate (m + 1) Digit.three ++ [Digit.two] → GoodBelow D f w.length →
      PairCompat (oddFull f w) 3 4 ∧ PairCompat (oddFull f w) 2 5
  /-- `w = u d 2^m` with `u` a base word, `d ∈ {1,3}`, `m ≥ 1`, excluding `u` all-three with `d = 3`, `m = 1` (that is `V1`). -/
  V2 : ∀ (D : JointData) (f : Word → JSlice) (u : Word) (d : Digit) (m : ℕ) (w : Word), D.S = paperS →
    FLatticePaper.Tiles.Standard.IsBase u → (d = Digit.one ∨ d = Digit.three) → 1 ≤ m →
    ¬ (d = Digit.three ∧ m = 1 ∧ ∀ x ∈ u, x = Digit.three) →
    w = u ++ [d] ++ List.replicate m Digit.two → GoodBelow D f w.length →
      PairCompat (oddFull f w) 3 4 ∧ PairCompat (oddFull f w) 2 5
  /-- `w = 2^(m+1) 3`: the even pairs (0,3) and (1,2) (the even pair (4,5) is the block `N3`). -/
  V6 : ∀ (D : JointData) (f : Word → JSlice) (m : ℕ) (w : Word), D.S = paperS →
    w = List.replicate (m + 1) Digit.two ++ [Digit.three] → GoodBelow D f w.length →
      PairCompat (evenFull f w) 0 3 ∧ PairCompat (evenFull f w) 1 2
  /-- `w = u d 3^m` with `u` a base word, `d ∈ {1,2}`, `m ≥ 1`, excluding `u` all-two with `d = 2`, `m = 1` (that is `V6`). -/
  V7 : ∀ (D : JointData) (f : Word → JSlice) (u : Word) (d : Digit) (m : ℕ) (w : Word), D.S = paperS →
    FLatticePaper.Tiles.Standard.IsBase u → (d = Digit.one ∨ d = Digit.two) → 1 ≤ m →
    ¬ (d = Digit.two ∧ m = 1 ∧ ∀ x ∈ u, x = Digit.two) →
    w = u ++ [d] ++ List.replicate m Digit.three → GoodBelow D f w.length →
      PairCompat (evenFull f w) 0 3 ∧ PairCompat (evenFull f w) 1 2

end FLatticePaper.Tiles.SwapVacuousSpec
