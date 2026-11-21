import FLatticePaper.Tiles.PseudoSquareAlong
import FLatticePaper.Construction.BaseCaseRecurrence

open FLatticePaper.Tiles FLatticePaper.Construction

set_option maxRecDepth 20000

/-! The walk placement of the strings (`FLatticePaper/Tiles/PseudoSquareAlong.lean`) on the base tiles of
prop:base_cases (d): the stair tiles for odd d (words q p^{k+1}, p^{2(k+1)} q, d = 2k+3) and the ladder tiles for even d
(words q p^k q p^{k+1}, p^{2k+1} q). The site lists have the membership of the paper's set-builders (proved below). -/

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

-- The words of the table at lines 1912-1920.
def qp : BinaryWord := [Letter.q, Letter.p]
def ppq : BinaryWord := [Letter.p, Letter.p, Letter.q]
def qpp : BinaryWord := [Letter.q, Letter.p, Letter.p]
def ppppq : BinaryWord := [Letter.p, Letter.p, Letter.p, Letter.p, Letter.q]
def qppp : BinaryWord := [Letter.q, Letter.p, Letter.p, Letter.p]
def pppppppq : BinaryWord := [Letter.p, Letter.p, Letter.p, Letter.p, Letter.p, Letter.p, Letter.q]
def qpqpp : BinaryWord := [Letter.q, Letter.p, Letter.q, Letter.p, Letter.p]
def pppq : BinaryWord := [Letter.p, Letter.p, Letter.p, Letter.q]
def qppqppp : BinaryWord := [Letter.q, Letter.p, Letter.p, Letter.q, Letter.p, Letter.p, Letter.p]
def ppppp_q : BinaryWord := [Letter.p, Letter.p, Letter.p, Letter.p, Letter.p, Letter.q]

/-! ### Instances: the staircases for d = 3, 5, 7 and the ladders for d = 4, 6 -/

theorem along_stair_three : IsPseudoSquareAlong (stairList 3) qp ppq := by decide
theorem along_stair_five : IsPseudoSquareAlong (stairList 5) qpp ppppq := by decide
theorem along_stair_seven : IsPseudoSquareAlong (stairList 7) qppp pppppppq := by decide
theorem along_ladder_four : IsPseudoSquareAlong (ladderList 4) qpqpp pppq := by decide
theorem along_ladder_six : IsPseudoSquareAlong (ladderList 6) qppqppp ppppp_q := by decide

/-! The Lemma 4.2 sums of the words for d = 6 and d = 7: Σw_1 + i = v_{1/d,1} and Σw_2 - 1 = v_{1/d,2}, with
v_{1/6,1} = (12, 2) (odd child, doubled), v_{1/6,2} = (-5, 7), and v_{1/7,1} = (7, 1), v_{1/7,2} = (-6, 8). -/
theorem sums_ladder_six : F2Word.sum (gPseudo qppqppp ppppp_q).1 + gI = (12, 2) ∧
    F2Word.sum (gPseudo qppqppp ppppp_q).2 - gOne = (-5, 7) := by decide
theorem sums_stair_seven : F2Word.sum (gPseudo qppp pppppppq).1 + gI = (7, 1) ∧
    F2Word.sum (gPseudo qppp pppppppq).2 - gOne = (-6, 8) := by decide

#print axioms along_stair_three
#print axioms along_stair_five
#print axioms along_stair_seven
#print axioms along_ladder_four
#print axioms along_ladder_six
#print axioms sums_ladder_six
#print axioms sums_stair_seven
