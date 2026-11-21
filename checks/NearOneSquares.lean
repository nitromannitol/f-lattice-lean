import FLatticePaper.Tiles.PseudoSquareAlong

/-! The near-one base tiles of `prop:base_cases` (d) with the words of its table (lines 1912-1920), decided against the
walk placement of `Tiles/PseudoSquareAlong.lean`. The tiles are the TeX tiles `paperNearStairTile d` and
`paperNearLadderTile d` (`Construction/NearOneBaseCases.lean`) as finite site lists; the predicate is translation
invariant, so the TeX chart (an odd shift of the physical one) does not change the outcome.

The words depend on `k` and the tile on `d`. The containment clause holds exactly for the pairings `k = (d-3)/2` on the
stair family and `d = 2k+2` on the ladder family; the other pairings fail both clauses. For the paired instances the
covering clause fails, so the walk placement does not make these tiles pseudo-squares. -/

open FLatticePaper.Tiles

set_option maxRecDepth 20000

/-- The rectangle `[a, b] × [c, e]` of sites, as a list. -/
def rectN (a b c e : ℤ) : List GInt :=
  ((List.range (b - a + 1).toNat).map fun i : ℕ =>
    (List.range (e - c + 1).toNat).map fun j : ℕ => ((a + (i : ℤ), c + (j : ℤ)) : GInt)).flatten

/-- The site predicate of `paperNearStairTile d`. -/
def nsPred (d : ℤ) (x : GInt) : Bool :=
  decide ((0 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 2 * d - 1 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ d) ∨
    x = (0, d + 1) ∨ x = (d + 1, d - 1))

/-- The site list of `paperNearStairTile d`. -/
def nsList (d : ℤ) : List GInt := (rectN 0 (d + 1) 1 (2 * d - 1)).filter (nsPred d)

/-- The site predicate of `paperNearLadderTile d`. -/
def nlPred (d : ℤ) (x : GInt) : Bool :=
  decide (((x = (-1, 2 * d + 1)) ∨ x = (d + 1, d - 1) ∨ (x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d) ∨
      (-1 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 1 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d + 1)) ∧
    ¬((x.1 = -1 ∧ x.2 ≤ d + 1) ∨ (x.1 = d + 1 ∧ 2 * d - 1 ≤ x.2)))

/-- The site list of `paperNearLadderTile d`. -/
def nlList (d : ℤ) : List GInt := (rectN (-1) (d + 1) 1 (3 * d - 1)).filter (nlPred d)

/-- The words `q^{2(k+1)} p` and `p q^{k+1}` of the near-one stair (table, row `2^k` odd). -/
def nsH (k : ℕ) : BinaryWord := List.replicate (2 * k + 2) Letter.q ++ [Letter.p]
def nsV (k : ℕ) : BinaryWord := Letter.p :: List.replicate (k + 1) Letter.q

/-- The words `q^{2k+1} p` and `p q^k p q^{k+1}` of the near-one ladder (table, row `2^k` even). -/
def nlH (k : ℕ) : BinaryWord := List.replicate (2 * k + 1) Letter.q ++ [Letter.p]
def nlV (k : ℕ) : BinaryWord :=
  [Letter.p] ++ List.replicate k Letter.q ++ [Letter.p] ++ List.replicate (k + 1) Letter.q

/-- Clause 1 of the walk placement, on the list `T`: the placed strings lie in `T`. -/
def alongContain (T : List GInt) (wh wv : BinaryWord) : Bool :=
  match lowerLeftList T with
  | none => false
  | some c => (placedSites (alongStrings wh wv c)).all fun x => T.contains x

/-- Clause 2 of the walk placement, on the list `T`: the placed strings cover `∂⁻T`. -/
def alongCover (T : List GInt) (wh wv : BinaryWord) : Bool :=
  match lowerLeftList T with
  | none => false
  | some c => (innerBoundaryList T).all fun x => (placedSites (alongStrings wh wv c)).contains x

/-! The paired instances: the containment clause holds and the covering clause fails. -/

theorem near_stair_three_contain : alongContain (nsList 3) (nsH 0) (nsV 0) = true := by decide
theorem near_stair_three_cover_fails : ¬ alongCover (nsList 3) (nsH 0) (nsV 0) = true := by decide
theorem near_stair_three_not_pseudoSquare : ¬ IsPseudoSquareAlong (nsList 3) (nsH 0) (nsV 0) := by decide

theorem near_stair_five_contain : alongContain (nsList 5) (nsH 1) (nsV 1) = true := by decide
theorem near_stair_five_cover_fails : ¬ alongCover (nsList 5) (nsH 1) (nsV 1) = true := by decide
theorem near_stair_five_not_pseudoSquare : ¬ IsPseudoSquareAlong (nsList 5) (nsH 1) (nsV 1) := by decide

theorem near_stair_seven_contain : alongContain (nsList 7) (nsH 2) (nsV 2) = true := by decide
theorem near_stair_seven_cover_fails : ¬ alongCover (nsList 7) (nsH 2) (nsV 2) = true := by decide
theorem near_stair_seven_not_pseudoSquare : ¬ IsPseudoSquareAlong (nsList 7) (nsH 2) (nsV 2) := by decide

theorem near_ladder_four_contain : alongContain (nlList 4) (nlH 1) (nlV 1) = true := by decide
theorem near_ladder_four_cover_fails : ¬ alongCover (nlList 4) (nlH 1) (nlV 1) = true := by decide
theorem near_ladder_four_not_pseudoSquare : ¬ IsPseudoSquareAlong (nlList 4) (nlH 1) (nlV 1) := by decide

theorem near_ladder_six_contain : alongContain (nlList 6) (nlH 2) (nlV 2) = true := by decide
theorem near_ladder_six_cover_fails : ¬ alongCover (nlList 6) (nlH 2) (nlV 2) = true := by decide
theorem near_ladder_six_not_pseudoSquare : ¬ IsPseudoSquareAlong (nlList 6) (nlH 2) (nlV 2) := by decide

#print axioms near_stair_three_not_pseudoSquare
#print axioms near_stair_five_cover_fails
#print axioms near_ladder_four_cover_fails
#print axioms near_ladder_six_contain
