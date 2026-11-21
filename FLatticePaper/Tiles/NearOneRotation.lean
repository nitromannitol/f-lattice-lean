import FLatticePaper.Tiles.BaseCasePseudoSquares
import FLatticePaper.Construction.NearOneBaseCases

/-! The near-one base tiles of `prop:base_cases` (d) as quarter-turns of the reciprocal tiles (eq:rotate_tile, line 1689).

The near-one tile of denominator `d`, read in the chart `chartDown` (the TeX tile shifted so that its lower-left vertex is
the origin, `c(T) = (0,0)` as for the reciprocal tile), is the image of the reciprocal tile under the quarter turn
`(x1, x2) ↦ (-x2, x1)` followed by the translation `(d+1, d-2)`, for every `d`. The rotated words are
`R(w_h, w_v) = (F w_v, F w_h)` (eq:rotate_boundary_string), which are the near-one words of the table. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Construction (paperNearStairTile paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC
  paperNearLadderD paperStairTile paperLadderTile)

/-- The near-one tile in the chart with lower-left vertex at the origin: `x ∈ chartDown T` iff `x + (0,1) ∈ T`. -/
def chartDown (T : Set GInt) : Set GInt := {x | (x.1, x.2 + 1) ∈ T}

/-- The image of `T0` under the quarter turn `(x1, x2) ↦ (-x2, x1)` followed by the translation `v`, written as a
preimage: `x` lies in it iff `(x2 - v2, v1 - x1)` lies in `T0`. -/
def turnedTile (v : GInt) (T0 : Set GInt) : Set GInt := {x | (x.2 - v.2, v.1 - x.1) ∈ T0}

/-- `T` is an `R(w_h, w_v)`-pseudo-square by transport (eq:rotate_tile): `T` is a quarter turn of a
`(w_h, w_v)`-pseudo-square `T0`, and `T` and `T0` have the same lower-left vertex `c`. -/
def IsRotPseudoSquareT (T : Set GInt) (wh' wv' : BinaryWord) : Prop :=
  ∃ (T0 : Set GInt) (wh wv : BinaryWord) (v c : GInt),
    (wh', wv') = rotPseudo wh wv ∧ IsPseudoSquareAlongT T0 wh wv ∧ IsLowerLeftVertex T0 c ∧
      IsLowerLeftVertex T c ∧ T = turnedTile v T0

/-- The words of the near-one stair (table, row `2^k` odd): `q^{2(k+1)} p` and `p q^{k+1}`. -/
def nearStairH (k : ℕ) : BinaryWord := List.replicate (2 * k + 2) Letter.q ++ [Letter.p]
def nearStairV (k : ℕ) : BinaryWord := Letter.p :: List.replicate (k + 1) Letter.q

/-- The words of the near-one ladder (table, row `2^k` even): `q^{2k+1} p` and `p q^k p q^{k+1}`. -/
def nearLadderH (k : ℕ) : BinaryWord := List.replicate (2 * k + 1) Letter.q ++ [Letter.p]
def nearLadderV (k : ℕ) : BinaryWord :=
  [Letter.p] ++ List.replicate k Letter.q ++ [Letter.p] ++ List.replicate (k + 1) Letter.q

theorem mem_chartDown (T : Set GInt) (x : GInt) : x ∈ chartDown T ↔ (x.1, x.2 + 1) ∈ T := Iff.rfl

theorem mem_turnedTile (v : GInt) (T0 : Set GInt) (x : GInt) :
    x ∈ turnedTile v T0 ↔ (x.2 - v.2, v.1 - x.1) ∈ T0 := Iff.rfl

/-- The near-one stair tile is the quarter turn of the reciprocal stair tile, for every `d`. -/
theorem chartDown_nearStair (d : ℤ) :
    chartDown (paperNearStairTile d) = turnedTile (d + 1, d - 2) (paperStairTile d) := by
  ext x
  rw [mem_chartDown, mem_turnedTile, mem_stairT_disj]
  unfold paperNearStairTile
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor <;> intro h <;> omega

/-- The near-one ladder tile is the quarter turn of the reciprocal ladder tile, for every `d`. -/
theorem chartDown_nearLadder (d : ℤ) :
    chartDown (paperNearLadderTile d) = turnedTile (d + 1, d - 2) (paperLadderTile d) := by
  ext x
  rw [mem_chartDown, mem_turnedTile, mem_ladderT_disj]
  unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor <;> intro h <;> omega

/-- The near-one words are the rotated reciprocal words, `R(w_h, w_v) = (F w_v, F w_h)`. -/
theorem nearStair_words (k : ℕ) :
    (nearStairH k, nearStairV k) = rotPseudo (stairH k) (stairV k) := by
  simp [nearStairH, nearStairV, stairH, stairV, rotPseudo, flipW, flipLetter, List.map_append,
    List.map_replicate]

theorem nearLadder_words (k : ℕ) :
    (nearLadderH k, nearLadderV k) = rotPseudo (ladderH k) (ladderV k) := by
  simp [nearLadderH, nearLadderV, ladderH, ladderV, rotPseudo, flipW, flipLetter, List.map_append,
    List.map_replicate]

/-- The corner `(0,0)` is the lower-left vertex of the chart of the near-one stair tile. -/
theorem chartDown_nearStair_lowerLeft (d : ℤ) (hd : 3 ≤ d) :
    IsLowerLeftVertex (chartDown (paperNearStairTile d)) (0, 0) := by
  refine ⟨?_, ?_⟩
  · rw [mem_chartDown]
    unfold paperNearStairTile
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  · intro y hy
    rw [mem_chartDown] at hy
    unfold paperNearStairTile at hy
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    omega

/-- The corner `(0,0)` is the lower-left vertex of the chart of the near-one ladder tile. -/
theorem chartDown_nearLadder_lowerLeft (d : ℤ) (hd : 4 ≤ d) :
    IsLowerLeftVertex (chartDown (paperNearLadderTile d)) (0, 0) := by
  refine ⟨?_, ?_⟩
  · rw [mem_chartDown]
    unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    omega
  · intro y hy
    rw [mem_chartDown] at hy
    unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD at hy
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at hy
    omega

/-- The lower-left vertex of the doubled staircase `paperLadderTile (2k+2)` for `k ≥ 1`. -/
theorem ladder_lowerLeft_k (k : ℕ) (hk : 1 ≤ k) :
    IsLowerLeftVertex (paperLadderTile (2 * (k : ℤ) + 2)) (0, 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hd : (2 * ((m + 1 : ℕ) : ℤ) + 2) = 2 * (m : ℤ) + 4 := by push_cast; ring
  rw [hd]
  exact ⟨(ladder_lowerLeft m).1, (ladder_lowerLeft m).2⟩

/-- The near-one stair tile `paperNearStairTile (2k+3)` (in the corner-matched chart) is an
`R(q p^{k+1}, p^{2k+2} q)`-pseudo-square by transport from `paperStairTile (2k+3)`. -/
theorem nearStair_isRotPseudoSquareT (k : ℕ) :
    IsRotPseudoSquareT (chartDown (paperNearStairTile (2 * (k : ℤ) + 3))) (nearStairH k) (nearStairV k) :=
  ⟨paperStairTile (2 * (k : ℤ) + 3), stairH k, stairV k, (2 * (k : ℤ) + 3 + 1, 2 * (k : ℤ) + 3 - 2), (0, 0),
    nearStair_words k, stair_isPseudoSquareAlongT k, ⟨(stair_lowerLeft k).1, (stair_lowerLeft k).2⟩,
    chartDown_nearStair_lowerLeft _ (by omega), chartDown_nearStair _⟩

/-- The near-one ladder tile `paperNearLadderTile (2k+2)` (in the corner-matched chart) is an
`R(q p^k q p^{k+1}, p^{2k+1} q)`-pseudo-square by transport from `paperLadderTile (2k+2)`. -/
theorem nearLadder_isRotPseudoSquareT (k : ℕ) (hk : 1 ≤ k) :
    IsRotPseudoSquareT (chartDown (paperNearLadderTile (2 * (k : ℤ) + 2))) (nearLadderH k) (nearLadderV k) :=
  ⟨paperLadderTile (2 * (k : ℤ) + 2), ladderH k, ladderV k, (2 * (k : ℤ) + 2 + 1, 2 * (k : ℤ) + 2 - 2), (0, 0),
    nearLadder_words k, ladder_isPseudoSquareAlongT k hk, ladder_lowerLeft_k k hk,
    chartDown_nearLadder_lowerLeft _ (by omega), chartDown_nearLadder _⟩

end FLatticePaper.Tiles
