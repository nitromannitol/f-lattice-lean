import FLatticePaper.Tiles.NearOneRotation

/-! The near-one tiles as quarter-turns of the reciprocal tiles, decided on the finite site lists for d = 3, 5, 7 (stair)
and d = 4, 6 (ladder). The chart is `x ↦ (x1, x2 - 1)` of the TeX tile (`chartDown`), and the quarter turn sends the
reciprocal site `y` to `(-y2 + d + 1, y1 + d - 2)` (`turnedTile (d+1, d-2)`). -/

open FLatticePaper.Tiles

set_option maxRecDepth 20000

def rectC (a b c e : ℤ) : List GInt :=
  ((List.range (b - a + 1).toNat).map fun i : ℕ =>
    (List.range (e - c + 1).toNat).map fun j : ℕ => ((a + (i : ℤ), c + (j : ℤ)) : GInt)).flatten

def nsPredC (d : ℤ) (x : GInt) : Bool :=
  decide ((0 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 2 * d - 1 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ d) ∨
    x = (0, d + 1) ∨ x = (d + 1, d - 1))
def nsListC (d : ℤ) : List GInt := (rectC 0 (d + 1) 1 (2 * d - 1)).filter (nsPredC d)

def nlPredC (d : ℤ) (x : GInt) : Bool :=
  decide (((x = (-1, 2 * d + 1)) ∨ x = (d + 1, d - 1) ∨ (x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d) ∨
      (-1 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 1 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d + 1)) ∧
    ¬((x.1 = -1 ∧ x.2 ≤ d + 1) ∨ (x.1 = d + 1 ∧ 2 * d - 1 ≤ x.2)))
def nlListC (d : ℤ) : List GInt := (rectC (-1) (d + 1) 1 (3 * d - 1)).filter (nlPredC d)

def spPredC (d : ℤ) (x : GInt) : Bool :=
  decide ((2 - d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 1 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d + 2) ∨
    x = (0, 0) ∨ x = (2, d + 1))
def spListC (d : ℤ) : List GInt := (rectC (2 - d) d 0 (d + 1)).filter (spPredC d)

def lpPredC (d : ℤ) (x : GInt) : Bool :=
  decide (((x = (0, 0)) ∨ x = (d + 2, d + 2) ∨ (x.1 + x.2 = d + 2 ∧ 1 < x.2 ∧ x.2 < d + 1) ∨
      (-d + 2 ≤ x.1 ∧ x.1 ≤ 2 * d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 2 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 2 * d + 3)) ∧
    ¬((d ≤ x.1 ∧ x.2 = 0) ∨ (x.1 ≤ 2 ∧ x.2 = d + 2)))
def lpListC (d : ℤ) : List GInt := (rectC (-d + 2) (2 * d) 0 (d + 2)).filter (lpPredC d)

/-- The quarter turn of `chartDown`: `y ↦ (-y2 + d + 1, y1 + d - 2)`, for the stair, and the same for the ladder. -/
def turnImgC (d : ℤ) (y : GInt) : GInt := (-y.2 + (d + 1), y.1 + (d - 2))

def chartC (L : List GInt) : List GInt := L.map fun x => (x.1, x.2 - 1)

def sameSetC (A B : List GInt) : Bool :=
  A.length == B.length && A.all (fun x => B.contains x) && B.all (fun x => A.contains x)

theorem near_stair_three_chart : sameSetC (chartC (nsListC 3)) ((spListC 3).map (turnImgC 3)) = true := by decide
theorem near_stair_five_chart : sameSetC (chartC (nsListC 5)) ((spListC 5).map (turnImgC 5)) = true := by decide
theorem near_stair_seven_chart : sameSetC (chartC (nsListC 7)) ((spListC 7).map (turnImgC 7)) = true := by decide
theorem near_ladder_four_chart : sameSetC (chartC (nlListC 4)) ((lpListC 4).map (turnImgC 4)) = true := by decide
theorem near_ladder_six_chart : sameSetC (chartC (nlListC 6)) ((lpListC 6).map (turnImgC 6)) = true := by decide

/-- The words are the rotated reciprocal words, for the first rows. -/
theorem near_words_zero : (nearStairH 0, nearStairV 0) = rotPseudo (stairH 0) (stairV 0) := by decide
theorem near_words_one : (nearLadderH 1, nearLadderV 1) = rotPseudo (ladderH 1) (ladderV 1) := by decide

#print axioms chartDown_nearStair
#print axioms chartDown_nearLadder
#print axioms nearStair_isRotPseudoSquareT
#print axioms nearLadder_isRotPseudoSquareT
#print axioms near_stair_three_chart
