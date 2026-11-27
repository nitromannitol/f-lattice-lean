import FLatticePaper.Tiles.BaseCasePseudoSquares

/-! # The alternate staircase as a partial `w_h`-pseudo-square (surgical `lemma:basecase_3k_even_alt`, E15)

Surgical lines 2262 (Moreover) and 2268-2269 (the strings): for `d = 2k + 3`, `T̂_{1/d}` has a `w_h = q p^{k+1}` horizontal
boundary string starting at `c(T̂_{1/d}) = (0,0)` (the exception to the lower-left vertex, `c` at line 3566) and a `rev(w_h)`
reversed horizontal string starting at `(4 − 2d, d − 2)`. Only the horizontal pair is claimed (the vertical entry of the table
is `-`).

This file proves the containment clause for these two strings, for every `k`: every placed tile site lies in
`paperStairAltTile (2k+3)`, and the exceptional corner `(0,0)` lies in the tile. The respect clause (the odometer on each
subtile) is not part of this file. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Construction (paperStairAltTile paperStairAltA paperStairAltB paperStairAltC paperStairAltD)

/-- The placed sites of the two horizontal strings of the alternate staircase, with the forward string at `(0,0)` and the
reversed string at `(4 - 2d, d - 2)`, `d = 2k + 3`. -/
theorem mem_altStair_horizontal (k : ℕ) (x : GInt) :
    x ∈ placedSites (hStringAt (stairH k) (0, 0) ++
        hRevStringAt (stairH k).reverse (4 - 2 * (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 - 2)) ↔
      (oneAt (0, 0) x ∨ ∃ j : ℕ, j ≤ k ∧ zeroAt (2 + (j : ℤ) * 2, 0) x) ∨
        ((∃ j : ℕ, j ≤ k ∧
            zeroAt ((4 - 2 * (2 * (k : ℤ) + 3)) + (j : ℤ) * 2, 2 * (k : ℤ) + 3 - 2) x) ∨
          oneAt ((4 - 2 * (2 * (k : ℤ) + 3)) + (k : ℤ) * 2 + 2, 2 * (k : ℤ) + 3 - 2 + 1) x) := by
  simp only [placedSites_append, List.mem_append]
  rw [stairH_reverse, mem_hLower, mem_hRevRun]
  exact Iff.rfl

/-- **Containment of the alternate staircase strings.** Every placed site of the two horizontal strings lies in
`paperStairAltTile (2k+3)`. -/
theorem altStair_horizontal_contain (k : ℕ) (x : GInt)
    (hx : x ∈ placedSites (hStringAt (stairH k) (0, 0) ++
        hRevStringAt (stairH k).reverse (4 - 2 * (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 - 2))) :
    x ∈ paperStairAltTile (2 * (k : ℤ) + 3) := by
  rw [mem_altStair_horizontal] at hx
  unfold paperStairAltTile
  simp only [Set.mem_union, paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD, Set.mem_setOf_eq]
  rcases hx with (h | ⟨j, hj, h⟩) | ((⟨j, hj, h⟩ | h))
  all_goals (simp only [oneAt, zeroAt] at *; omega)

/-- The exceptional corner `c(T̂_{1/d}) = (0,0)` lies in the alternate staircase tile (`d = 2k + 3`). -/
theorem altStair_zero_mem (k : ℕ) : (0 : GInt) ∈ paperStairAltTile (2 * (k : ℤ) + 3) := by
  unfold paperStairAltTile
  simp only [Set.mem_union, paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD, Set.mem_setOf_eq,
    Prod.fst_zero, Prod.snd_zero]
  omega

end FLatticePaper.Tiles
