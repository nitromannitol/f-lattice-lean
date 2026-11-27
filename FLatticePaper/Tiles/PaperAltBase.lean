import FLatticePaper.Tiles.StandardTiles

/-! # The base alternate tiles of `prop:base_cases` as finite sets, with `c(T̂) = 0`

Surgical edition 274ad18. The base alternates of the base words (`lemma:basecase_3k_even_alt`, `lemma:basecase_3k_odd_alt`,
`lemma:basecase_2k_odd_alt`, `lemma:basecase_2k_even_alt`) as finite sets of points, placed with `c(T̂) = 0`: `c` of a base
alternate is its lower-left vertex (line 3694), except `c(T̂_{1/d}) = (0, 0)` for the even alternate of `3^k` (line 2262). So
the near-one alternates are translated by `(0, -1)` and the odd alternate of `3^k` by `(1, 1)` (its lower-left vertex is
`(-1, -1)` in the paper's chart). These are the frames of `SurgicalAlt.PaperAltBaseCond`. The boxes `boxF d` contain the paper's
sets for `d ≥ 3`. -/

namespace FLatticePaper.Tiles.PaperAltBase

open FLatticePaper.Farey
open FLatticePaper.Tiles.Standard (shift Tile)

/-- A box containing the base alternate tiles. -/
def boxF (d : ℤ) : Finset Site := Finset.Icc (-3 * d) (3 * d) ×ˢ Finset.Icc (-3 * d) (3 * d)

/-- `T̂_{1/d}` of `lemma:basecase_3k_even_alt` (`paperStairAltTile d`), with `c(T̂_{1/d}) = (0, 0)` by the exception of the text. -/
def stairAltF (d : ℤ) : Finset Site :=
  (boxF d).filter fun x =>
    (x.1 = 1 - d ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∨ (x.1 = 3 ∧ d ≤ x.2 ∧ x.2 ≤ d + 1) ∨
    (x.1 + x.2 = 2 ∧ 0 < x.2 ∧ x.2 < d) ∨
    (1 - d ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = -1) ∨ (4 - d ≤ x.1 ∧ x.1 ≤ 3 ∧ x.2 = d + 1) ∨
    (4 - 2 * d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d ∧ -d + 2 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d + 2)

/-- `T̂_{1/d}` of `lemma:basecase_3k_odd_alt` (`paperLadderAltTile d`), in the paper's chart (lower-left vertex `(-1, -1)`). -/
def ladderAltF (d : ℤ) : Finset Site :=
  (boxF d).filter fun x =>
    ((x = (-1, -1) ∨ x = (d, d + 2)) ∨ (x.1 + x.2 = d ∧ 0 < x.1 ∧ x.1 < d - 1) ∨
      (1 - d ≤ x.1 ∧ x.1 ≤ 2 * d - 2 ∧ -1 ≤ x.2 ∧ x.2 ≤ d + 2 ∧ -1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 2 * d + 1)) ∧
    ¬ ((d ≤ x.1 ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∨ (x.1 ≤ -1 ∧ d + 1 ≤ x.2 ∧ x.2 ≤ d + 2))

/-- `T̂_{p_1}` of `lemma:basecase_2k_odd_alt` (`paperNearStairAltTile d`), in the paper's chart. -/
def nearStairAltF (d : ℤ) : Finset Site :=
  (boxF d).filter fun x =>
    (-1 ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = 2 * d) ∨ (d ≤ x.1 ∧ x.1 ≤ d + 1 ∧ x.2 = d - 2) ∨
    (x.2 - x.1 = d - 1 ∧ 0 < x.1 ∧ x.1 < d) ∨
    (x.1 = -1 ∧ d + 1 ≤ x.2 ∧ x.2 ≤ 2 * d) ∨ (x.1 = d + 1 ∧ d - 2 ≤ x.2 ∧ x.2 ≤ 2 * d - 3) ∨
    (0 ≤ x.1 ∧ x.1 ≤ d ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 3 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d - 1)

/-- `T̂_{q_1}` of `lemma:basecase_2k_even_alt` (`paperNearLadderAltTile d`), in the paper's chart. -/
def nearLadderAltF (d : ℤ) : Finset Site :=
  (boxF d).filter fun x =>
    ((x = (-2, 2 * d) ∨ x = (d + 1, d - 1)) ∨ (x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d - 1) ∨
      (-2 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 2 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d + 1)) ∧
    ¬ ((x.1 ≤ -1 ∧ x.2 ≤ d - 1) ∨ (d ≤ x.1 ∧ 2 * d ≤ x.2))

/-- The base alternate tiles of the base words, in the frames of `PaperAltBaseCond`: the near-one alternates read at
`x + (0, 1)`, the odd alternate of `3^k` at `x - (1, 1)`, and `T̂_{1/d}` as it is (`c(T̂_{1/d}) = (0, 0)`). -/
def paperAltBaseTiles (w : Word) : Tile × Tile :=
  if w = [] then (shift (nearStairAltF 3) (0, -1), stairAltF 3)
  else if w = List.replicate w.length Digit.three then
    (shift (ladderAltF (2 * (w.length : ℤ) + 2)) (1, 1), stairAltF (2 * (w.length : ℤ) + 3))
  else (shift (nearStairAltF (2 * (w.length : ℤ) + 3)) (0, -1), shift (nearLadderAltF (2 * (w.length : ℤ) + 2)) (0, -1))

end FLatticePaper.Tiles.PaperAltBase
