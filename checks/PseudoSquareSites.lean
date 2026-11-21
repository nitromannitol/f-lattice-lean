import FLatticePaper.Tiles.PseudoSquareSites
import FLatticePaper.Construction.BaseCaseRecurrence

open FLatticePaper.Tiles FLatticePaper.Construction

set_option maxRecDepth 20000

/-! The base tiles of `prop:base_cases` (d), as finite site lists with the membership of `paperStairTile d` and
`paperLadderTile d`, and the instances of the literal pseudo-square predicate. -/

/-- The rectangle `[a, b] × [c, e]` of sites, as a list. -/
def rect (a b c e : ℤ) : List GInt :=
  ((List.range (b - a + 1).toNat).map fun i : ℕ =>
    (List.range (e - c + 1).toNat).map fun j : ℕ => ((a + (i : ℤ), c + (j : ℤ)) : GInt)).flatten

theorem mem_rect_iff (a b c e : ℤ) (x : GInt) :
    x ∈ rect a b c e ↔ a ≤ x.1 ∧ x.1 ≤ b ∧ c ≤ x.2 ∧ x.2 ≤ e := by
  unfold rect
  rw [List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hx⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hi' := Int.lt_toNat.mp (List.mem_range.mp hi)
    have hj' := Int.lt_toNat.mp (List.mem_range.mp hj)
    simp only
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨_, List.mem_map.mpr ⟨(x.1 - a).toNat, List.mem_range.mpr (Int.lt_toNat.mpr (by omega)), rfl⟩, ?_⟩
    refine List.mem_map.mpr ⟨(x.2 - c).toNat, List.mem_range.mpr (Int.lt_toNat.mpr (by omega)), ?_⟩
    have e1 : ((x.1 - a).toNat : ℤ) = x.1 - a := Int.toNat_of_nonneg (by omega)
    have e2 : ((x.2 - c).toNat : ℤ) = x.2 - c := Int.toNat_of_nonneg (by omega)
    ext
    · simp only; omega
    · simp only; omega

/-- The set-builder of `paperStairTile d` as a disjunction (lines 21-23 of `Construction/BaseCaseRecurrence.lean`). -/
theorem mem_paperStairTile_disj (d : ℤ) (x : GInt) :
    x ∈ paperStairTile d ↔
      (2 - d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 1 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d + 2) ∨
        (x.1 = 0 ∧ x.2 = 0) ∨ (x.1 = 2 ∧ x.2 = d + 1) := by
  unfold paperStairTile
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]

/-- The Boolean predicate of `paperStairTile d`. -/
def stairPred (d : ℤ) (x : GInt) : Bool :=
  (2 - d ≤ x.1 && x.1 ≤ d && 0 ≤ x.2 && x.2 ≤ d + 1 && 1 ≤ x.1 + x.2 && x.1 + x.2 ≤ d + 2)
    || (x == (0, 0)) || (x == (2, d + 1))

theorem stairPred_iff (d : ℤ) (x : GInt) :
    stairPred d x = true ↔
      ((2 - d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 1 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d + 2) ∨
        (x.1 = 0 ∧ x.2 = 0) ∨ (x.1 = 2 ∧ x.2 = d + 1)) := by
  unfold stairPred
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Prod.ext_iff]
  omega

/-- The site list of `paperStairTile d`. -/
def stairList (d : ℤ) : List GInt := (rect (2 - d) d 0 (d + 1)).filter (stairPred d)

theorem mem_stairList_iff (d : ℤ) (hd : 3 ≤ d) (x : GInt) :
    x ∈ stairList d ↔ x ∈ paperStairTile d := by
  unfold stairList
  rw [List.mem_filter, mem_rect_iff, stairPred_iff, mem_paperStairTile_disj]
  omega

/-- The set-builder of `paperLadderTile d` as a disjunction (lines 59-75 of `Construction/BaseCaseRecurrence.lean`). -/
theorem mem_paperLadderTile_disj (d : ℤ) (x : GInt) :
    x ∈ paperLadderTile d ↔
      ((x.1 = 0 ∧ x.2 = 0) ∨ (x.1 = d + 2 ∧ x.2 = d + 2) ∨
        (x.1 + x.2 = d + 2 ∧ 1 < x.2 ∧ x.2 < d + 1) ∨
        (-d + 2 ≤ x.1 ∧ x.1 ≤ 2 * d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 2 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 2 * d + 3)) ∧
        ¬ ((d ≤ x.1 ∧ x.2 = 0) ∨ (x.1 ≤ 2 ∧ x.2 = d + 2)) := by
  unfold paperLadderTile paperLadderA paperLadderB paperLadderC paperLadderD
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.ext_iff]
  constructor <;> intro h <;> tauto

/-- The membership of `paperLadderTile d` as a Prop: `(A ∪ B ∪ C) \ D` written out (lines 59-75). -/
abbrev ladderProp (d : ℤ) (x : GInt) : Prop :=
  ((x.1 = 0 ∧ x.2 = 0) ∨ (x.1 = d + 2 ∧ x.2 = d + 2) ∨
      (x.1 + x.2 = d + 2 ∧ 1 < x.2 ∧ x.2 < d + 1) ∨
      (-d + 2 ≤ x.1 ∧ x.1 ≤ 2 * d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 2 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 2 * d + 3)) ∧
    ¬ ((d ≤ x.1 ∧ x.2 = 0) ∨ (x.1 ≤ 2 ∧ x.2 = d + 2))

/-- The Boolean predicate of `paperLadderTile d`: the decision of `ladderProp`. -/
def ladderPred (d : ℤ) (x : GInt) : Bool := decide (ladderProp d x)

theorem ladderPred_iff (d : ℤ) (x : GInt) : ladderPred d x = true ↔ ladderProp d x := by
  unfold ladderPred
  exact decide_eq_true_iff

/-- The site list of `paperLadderTile d`. -/
def ladderList (d : ℤ) : List GInt := (rect (-d + 2) (2 * d) 0 (d + 2)).filter (ladderPred d)

theorem mem_ladderList_iff (d : ℤ) (hd : 4 ≤ d) (x : GInt) :
    x ∈ ladderList d ↔ x ∈ paperLadderTile d := by
  unfold ladderList
  rw [List.mem_filter, mem_rect_iff, ladderPred_iff, mem_paperLadderTile_disj]
  unfold ladderProp
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨h1, _⟩ := h
    rcases h1 with h1 | h1 | h1 | h1 <;> omega

-- The base tiles of prop:base_cases (d) with the words of its table (lines 1912-1920).
def qpp : BinaryWord := [Letter.q, Letter.p, Letter.p]
def ppppq : BinaryWord := [Letter.p, Letter.p, Letter.p, Letter.p, Letter.q]
def qp : BinaryWord := [Letter.q, Letter.p]
def ppq : BinaryWord := [Letter.p, Letter.p, Letter.q]
def qpqpp : BinaryWord := [Letter.q, Letter.p, Letter.q, Letter.p, Letter.p]
def pppq : BinaryWord := [Letter.p, Letter.p, Letter.p, Letter.q]

/-! ### Instances that hold: the base tile for d = 3 -/

theorem base_stair_three_pseudoSquare : IsPseudoSquareSites (stairList 3) qp ppq := by decide

/-! ### Instances that fail: the base tiles for d = 5 and the ladder tile for d = 4. Each failing clause is recorded. -/

theorem base_stair_five_contain_fails : ¬ (stringsInside (stairList 5) qpp ppppq = true) := by decide
theorem base_stair_five_cover_fails : ¬ (coversBoundary (stairList 5) qpp ppppq = true) := by decide
theorem base_stair_five_not_pseudoSquare : ¬ IsPseudoSquareSites (stairList 5) qpp ppppq := by decide
theorem base_ladder_four_contain_fails : ¬ (stringsInside (ladderList 4) qpqpp pppq = true) := by decide
theorem base_ladder_four_cover_fails : ¬ (coversBoundary (ladderList 4) qpqpp pppq = true) := by decide
theorem base_ladder_four_not_pseudoSquare : ¬ IsPseudoSquareSites (ladderList 4) qpqpp pppq := by decide

/-! The witnesses of the failing clauses: the corner of the d = 5 and ladder d = 4 tiles, and the sites that leave the
tile or are left uncovered when the four strings are placed as above. -/

example : lowerLeftList (stairList 5) = some (0, 0) := by decide
example : ((4 : ℤ), (4 : ℤ)) ∈ placedSites (pseudoStrings qpp ppppq (0, 0)) ∧
    ((4 : ℤ), (4 : ℤ)) ∉ stairList 5 := by decide
example : ((1 : ℤ), (6 : ℤ)) ∈ innerBoundaryList (stairList 5) ∧
    ((1 : ℤ), (6 : ℤ)) ∉ placedSites (pseudoStrings qpp ppppq (0, 0)) := by decide
example : lowerLeftList (ladderList 4) = some (0, 0) := by decide
example : ((7 : ℤ), (5 : ℤ)) ∈ placedSites (pseudoStrings qpqpp pppq (0, 0)) ∧
    ((7 : ℤ), (5 : ℤ)) ∉ ladderList 4 := by decide
#print axioms FLatticePaper.Tiles.IsPseudoSquareSites
#print axioms mem_stairList_iff
#print axioms mem_ladderList_iff
#print axioms base_stair_three_pseudoSquare
#print axioms base_stair_five_not_pseudoSquare
#print axioms base_ladder_four_not_pseudoSquare
#print axioms base_stair_five_contain_fails
#print axioms base_stair_five_cover_fails
#print axioms base_ladder_four_contain_fails
#print axioms base_ladder_four_cover_fails
