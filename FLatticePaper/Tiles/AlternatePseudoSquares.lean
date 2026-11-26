import FLatticePaper.Tiles.AlternatePseudoSquares1

-- AlternatePseudoSquares: part 2 of 2; declarations from altStair3_no_bottom_string to altLadder6_short_words_no.
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
namespace FLatticePaper.Tiles
open FLatticePaper.Construction

/-- The horizontal one-sided reading fails for the alternate stair `d = 3` (word `q p`): no placement of the string
`q p` inside the tile covers its bottom row. -/
theorem altStair3_no_bottom_string : ∀ lo ∈ candStair3,
    (insideAll altStair3 (placedSites (hStringAt [Letter.q, Letter.p] lo)) &&
      coversAll (placedSites (hStringAt [Letter.q, Letter.p] lo)) [(-2, -1), (-1, -1), (0, -1)]) = false := by
  decide +kernel

/-- The same for `d = 5` (word `q p p`) and `d = 7` (word `q p p p`). -/
theorem altStair5_no_bottom_string : ∀ lo ∈ candStair5,
    (insideAll altStair5 (placedSites (hStringAt [Letter.q, Letter.p, Letter.p] lo)) &&
      coversAll (placedSites (hStringAt [Letter.q, Letter.p, Letter.p] lo))
        [(-4, -1), (-3, -1), (-2, -1), (-1, -1), (0, -1)]) = false := by
  decide +kernel

theorem altStair7_no_bottom_string : ∀ lo ∈ candStair7,
    (insideAll altStair7 (placedSites (hStringAt [Letter.q, Letter.p, Letter.p, Letter.p] lo)) &&
      coversAll (placedSites (hStringAt [Letter.q, Letter.p, Letter.p, Letter.p] lo))
        [(-6, -1), (-5, -1), (-4, -1), (-3, -1), (-2, -1), (-1, -1), (0, -1)]) = false := by
  decide +kernel

/-- The vertical one-sided reading fails for the alternate ladder `d = 4` (word `p p p q`): no placement of the forward
string covers the two right-side cells `(3,0)` and `(6,2)` inside the tile. -/
theorem altLadder4_no_right_string : ∀ s ∈ candLadder4,
    (insideAll altLadder4 (placedSites (vStringAt [Letter.p, Letter.p, Letter.p, Letter.q] s)) &&
      coversAll (placedSites (vStringAt [Letter.p, Letter.p, Letter.p, Letter.q] s)) [(3, 0), (6, 2)]) = false := by
  decide +kernel

theorem altLadder6_no_right_string : ∀ s ∈ candLadder6,
    (insideAll altLadder6 (placedSites (vStringAt [Letter.p, Letter.p, Letter.p, Letter.p, Letter.p, Letter.q] s)) &&
      coversAll (placedSites (vStringAt [Letter.p, Letter.p, Letter.p, Letter.p, Letter.p, Letter.q] s))
        [(5, 0), (10, 2)]) = false := by
  decide +kernel

/-! ### Shifted words (exploration, task 22 follow-up). No statement above is changed.

`binWords n` lists the binary words of length `n`; the decided statements below quantify over all words of length at
most `L` (`(List.range (L + 1)).flatMap binWords`). A word fits a bottom row (resp. a set of right-side cells) when some
placement of its string inside the tile covers it. -/

/-- The binary words of length `n`. -/
def binWords : ℕ → List BinaryWord
  | 0 => [[]]
  | n + 1 => (binWords n).flatMap fun w => [Letter.p :: w, Letter.q :: w]

/-- Whether some placement of the horizontal string `w` in `T` covers the cells `ys`. -/
def horizontalFits (T : List GInt) (w : BinaryWord) (cands : List GInt) (ys : List GInt) : Bool :=
  cands.any fun lo => coversAll (placedSites (hStringAt w lo)) ys && insideAll T (placedSites (hStringAt w lo))

/-- Whether some placement of the vertical string `w` in `T` covers the cells `ys`. -/
def verticalFits (T : List GInt) (w : BinaryWord) (cands : List GInt) (ys : List GInt) : Bool :=
  cands.any fun s => coversAll (placedSites (vStringAt w s)) ys && insideAll T (placedSites (vStringAt w s))

/-- For `d = 3` the word `q q` fits the bottom row: the doubled tile `T^d_{1/1}` of the second letter covers the cell
`(0,-1)`. This is not a word of the table. -/
theorem altStair3_qq_fits : horizontalFits altStair3 [.q, .q] candStair3 [(-2, -1), (-1, -1), (0, -1)] = true := by
  decide +kernel

/-- The shifted stair word `q p^k` (`d = 2k + 3`) does not fit `d = 3, 5, 7`, nor do the table's words `q p^{k+1}`
(checked above). Words of length at most `3` do not fit `d = 5` and `d = 7`. -/
theorem altStair3_shifted_no : horizontalFits altStair3 [.q] candStair3 [(-2, -1), (-1, -1), (0, -1)] = false := by
  decide +kernel

theorem altStair5_short_words_no : ∀ w ∈ (List.range 4).flatMap binWords,
    horizontalFits altStair5 w candStair5 [(-4, -1), (-3, -1), (-2, -1), (-1, -1), (0, -1)] = false := by
  decide +kernel

theorem altStair7_short_words_no : ∀ w ∈ (List.range 4).flatMap binWords,
    horizontalFits altStair7 w candStair7 [(-6, -1), (-5, -1), (-4, -1), (-3, -1), (-2, -1), (-1, -1), (0, -1)] = false := by
  decide +kernel

/-- The ladder cases: the shifted vertical words `p^{2k} q` and `p^{2k+2} q` do not fit, and words of length at most `3`
do not fit `d = 4` or `d = 6`. Every vertical word fails by the monotonicity of the vertical offsets (`p ↦ (-1,1)`,
`q ↦ (0,2)`): the corner `x`-coordinates along a vertical string never increase. -/
theorem altLadder4_shifted_no : verticalFits altLadder4 [.p, .p, .q] candLadder4 [(3, 0), (6, 2)] = false := by
  decide +kernel

theorem altLadder4_short_words_no : ∀ w ∈ (List.range 4).flatMap binWords,
    verticalFits altLadder4 w candLadder4 [(3, 0), (6, 2)] = false := by
  decide +kernel

theorem altLadder6_shifted_no : verticalFits altLadder6 [.p, .p, .p, .p, .q] candLadder6 [(5, 0), (10, 2)] = false := by
  decide +kernel

theorem altLadder6_short_words_no : ∀ w ∈ (List.range 4).flatMap binWords,
    verticalFits altLadder6 w candLadder6 [(5, 0), (10, 2)] = false := by
  decide +kernel

end FLatticePaper.Tiles

