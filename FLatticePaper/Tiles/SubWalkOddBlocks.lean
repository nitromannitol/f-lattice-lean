import FLatticePaper.Tiles.SubWalkOdd

/-! Task Q25 (sub), the odd bottom walk: the blocks of a ceiling word.

For a word `x` of length `L ≥ 1`, the walk `gH x` is the concatenation of the blocks `blockWord x j` for `j < L − 1`, followed by
the final east step `1` (`gH_walk`). The block `j` is `[1, i]` when `ε j = 0` and `ε (j + 1) = 1`, `[i, 1]` when `ε j = 1` and
`tY ε j = 1`, and `[1, 1]` otherwise (`blockWord_eq`), where `ε = epsOf x`. Its cursor sum is `(2 k − Yc k, Yc k)` after `k` blocks
(`sum_prefix`). -/

namespace FLatticePaper.Tiles.SubWalkOddBlocks

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SubCeilOdd
  FLatticePaper.Tiles.SubWalkOdd

theorem vecOne_eq : Unit4.vec Unit4.one = gOne := rfl

theorem vecI_eq : Unit4.vec Unit4.i = gI := rfl

/-- The block of the pair of letters `j`, `j + 1` of `x`. -/
def blockWord (x : BinaryWord) (j : ℕ) : F2Word := gPair (tl x j) (tl x (j + 1))

theorem epsOf_eq_zero_iff (x : BinaryWord) (j : ℕ) : epsOf x j = 0 ↔ x.getD j .p = .p := by
  unfold epsOf
  rcases hx : x.getD j .p with _ | _ <;> simp

theorem epsOf_eq_one_iff (x : BinaryWord) (j : ℕ) : epsOf x j = 1 ↔ x.getD j .p = .q := by
  unfold epsOf
  rcases hx : x.getD j .p with _ | _ <;> simp

theorem tY_epsOf_eq_one_iff (x : BinaryWord) (j : ℕ) (hj : j < x.length) :
    tY (epsOf x) j = 1 ↔ (x.take j).getLast? = some .q := by
  cases j with
  | zero => simp [tY]
  | succ m =>
    rw [tY_succ, epsOf_eq_one_iff, getLast_take_succ x m (by omega)]
    simp

theorem blockWord_eq (x : BinaryWord) (j : ℕ) (hj : j + 1 < x.length) :
    blockWord x j = if epsOf x j = 0 ∧ epsOf x (j + 1) = 1 then [Unit4.one, Unit4.i]
      else if epsOf x j = 1 ∧ tY (epsOf x) j = 1 then [Unit4.i, Unit4.one]
      else [Unit4.one, Unit4.one] := by
  unfold blockWord tl
  rw [getLast_take_succ x j (by omega), block_pair]
  simp only [epsOf_eq_zero_iff, epsOf_eq_one_iff, tY_epsOf_eq_one_iff x j (by omega)]

theorem hasNI_EN (x : BinaryWord) (j : ℕ) (h : epsOf x j = 0 ∧ epsOf x (j + 1) = 1) :
    hasNI (epsOf x) j = 1 := by
  simp [hasNI, h.1, h.2]

theorem hasNI_NE (x : BinaryWord) (j : ℕ) (h : epsOf x j = 1 ∧ tY (epsOf x) j = 1) :
    hasNI (epsOf x) j = 1 := by
  simp [hasNI, h.1, h.2]

theorem hasNI_EE (x : BinaryWord) (j : ℕ) (h1 : ¬(epsOf x j = 0 ∧ epsOf x (j + 1) = 1))
    (h2 : ¬(epsOf x j = 1 ∧ tY (epsOf x) j = 1)) : hasNI (epsOf x) j = 0 := by
  simp [hasNI, h1, h2]

theorem sum_app (u v : F2Word) : F2Word.sum (u ++ v) = F2Word.sum u + F2Word.sum v := by
  simp [F2Word.sum]

/-- The cursor vector of a block: `2 − n` east steps and `n` north steps, with `n = hasNI`. -/
theorem blockWord_sum (x : BinaryWord) (j : ℕ) (hj : j + 1 < x.length) :
    F2Word.sum (blockWord x j) = (2 - hasNI (epsOf x) j, hasNI (epsOf x) j) := by
  rw [blockWord_eq x j hj]
  split_ifs with h1 h2
  · rw [hasNI_EN x j h1]
    norm_num [F2Word.sum, vecOne_eq, vecI_eq, gOne, gI]
  · rw [hasNI_NE x j h2]
    norm_num [F2Word.sum, vecOne_eq, vecI_eq, gOne, gI]
  · rw [hasNI_EE x j h1 h2]
    norm_num [F2Word.sum, vecOne_eq, gOne]

theorem hasNI_bounds (ε : ℕ → ℤ) (j : ℕ) : 0 ≤ hasNI ε j ∧ hasNI ε j ≤ 1 := by
  unfold hasNI
  split_ifs <;> omega

theorem Yc_bounds (ε : ℕ → ℤ) (k : ℕ) : 0 ≤ Yc ε k ∧ Yc ε k ≤ k := by
  induction k with
  | zero => simp [Yc]
  | succ k ih =>
    rw [Yc_succ]
    have := hasNI_bounds ε k
    push_cast
    constructor <;> linarith [ih.1, ih.2, this.1, this.2]

theorem flatMap_range_succ (x : BinaryWord) (m : ℕ) :
    (List.range (m + 1)).flatMap (blockWord x) = (List.range m).flatMap (blockWord x) ++ blockWord x m := by
  simp [List.range_succ, List.flatMap_append]

/-- The pair map of the prefix of `m + 1` letters is the concatenation of the first `m` blocks. -/
theorem G_prefix (x : BinaryWord) : ∀ m : ℕ, m + 1 ≤ x.length →
    GHJoin.G (tileSeq (x.take (m + 1))) = (List.range m).flatMap (blockWord x) := by
  intro m
  induction m with
  | zero =>
    intro hm
    rw [tileSeq_take_succ x 0 (by omega)]
    simp [tileSeq, tileSeqAux, GHJoin.G_singleton]
  | succ m ih =>
    intro hm
    have h1 := prefixG_succ x m (by omega)
    have h2 := ih (by omega)
    rw [flatMap_range_succ, ← h2]
    exact h1

/-- The walk of a word of length `L ≥ 1`: its `L − 1` blocks, then the final east step. -/
theorem gH_walk (x : BinaryWord) (hx : 1 ≤ x.length) :
    gH x = (List.range (x.length - 1)).flatMap (blockWord x) ++ [Unit4.one] := by
  rw [GHJoin.gH_eq]
  have e : x.take (x.length - 1 + 1) = x := by
    rw [Nat.sub_add_cancel hx]
    simp
  rw [← G_prefix x (x.length - 1) (by omega), e]

/-- The cursor after the first `k` blocks: `2k − Yc` east steps and `Yc` north steps. -/
theorem sum_prefix (x : BinaryWord) (k : ℕ) (hk : k + 1 ≤ x.length) :
    F2Word.sum ((List.range k).flatMap (blockWord x)) = (2 * (k : ℤ) - Yc (epsOf x) k, Yc (epsOf x) k) := by
  induction k with
  | zero =>
    simp [F2Word.sum, Yc]
    rfl
  | succ k ih =>
    rw [flatMap_range_succ, sum_app, ih (by omega), blockWord_sum x k (by omega), Yc_succ]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]
      try push_cast
      try ring
    · simp only [Prod.snd_add]
      try ring

end FLatticePaper.Tiles.SubWalkOddBlocks
