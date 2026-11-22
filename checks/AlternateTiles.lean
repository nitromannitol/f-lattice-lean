import FLatticePaper.Tiles.AlternateTiles

/-! Task 33 checks: the PROVISIONAL alternate tiles of `FLatticePaper/Tiles/AlternateTiles.lean` fail the finite
properties of `lemma:alternate_tile_properties` at the words below (the numerics of `scripts/alt_report.txt`, up to length 4,
give the same counts). Each failure is a decided statement about explicit cells. -/

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles.Standard FLatticePaper.Tiles.Alternate

/-- The alternate odd child of the word `1` is not row-convex: the cells `(-2, 2)` and `(0, 2)` lie in the row `2`,
the cell `(-1, 2)` does not. -/
theorem altOdd_one_not_rowConvex :
    ((-2 : ℤ), (2 : ℤ)) ∈ altOddTile [Digit.one] ∧ ((0 : ℤ), (2 : ℤ)) ∈ altOddTile [Digit.one] ∧
      ((-1 : ℤ), (2 : ℤ)) ∉ altOddTile [Digit.one] := by
  decide +kernel

/-- The alternate odd child of the word `13` has the lowest cell `(-8, 0)`, not at the origin: the tile is not normalised
at its origin (the origin is the piece of the offset `0`). -/
theorem altOdd_13_not_normalised : ¬ IsNormalised (altOddTile [Digit.one, Digit.three]) := by
  intro h
  have hmem : ((-8 : ℤ), (0 : ℤ)) ∈ altOddTile [Digit.one, Digit.three] := by decide +kernel
  have hle := h.2 _ hmem
  simp [lexLE] at hle

/-- The rotation identity `R(T̂(p_0)) = T̂(q_0 of the swapped word) + t(p_0)` fails for the word `1`: the cell `(-11, -1)`
lies in the rotated odd child but not in the translated even child (`t = tF`, the parent `(1/2, 1/3)` and the child `2/5`). -/
theorem altOdd_one_rotation_fails :
    ¬ (rot (altOddTile [Digit.one]) =
        shift (altEvenTile [Digit.one]) (tF ((parentsAt [Digit.one]).current .odd))) := by
  intro h
  have h1 : ((-11 : ℤ), (-1 : ℤ)) ∈ rot (altOddTile [Digit.one]) := by decide +kernel
  have h2 : ((-11 : ℤ), (-1 : ℤ)) ∉ shift (altEvenTile [Digit.one])
      (tF ((parentsAt [Digit.one]).current .odd)) := by decide +kernel
  rw [h] at h1
  exact h2 h1

/-- For every word the standard part of the alternate state is the Farey standard state of the word. -/
theorem altState_std_all (w : Word) : (altState w).std = stateAt w := altState_std w

/-- For every word the parent pair of the alternate state is `parentsAt w`. -/
theorem altState_par_all (w : Word) : (altState w).std.par = parentsAt w := altState_par w

#print axioms altOdd_one_not_rowConvex
#print axioms altOdd_13_not_normalised
#print axioms altOdd_one_rotation_fails
#print axioms altState_std_all
#print axioms altState_par_all
