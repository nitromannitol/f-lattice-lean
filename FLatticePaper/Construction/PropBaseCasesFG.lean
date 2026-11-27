import FLatticePaper.Construction.NearOneBaseCases

/-! # The inclusions of `prop:base_cases` (f) and (g) (surgical 7c65f09, lines 1959-2025)

For `k ≥ 1`, `T(n/d, v) = T(n/d) ∪ (T(n/d) + v)`. The reading (confirmed by the operator): the first copy of the base tile `B`
is translated by `t = c(child) − c(base) + offset`, where `c` is the lower-left vertex, except `c(T̂_{1/d}) = (0,0)`; the second
copy is that translate plus `v`. Each lemma states: a point of either copy lies in the child tile.

The eight inclusions:
* (f1) `T(3^k p) ⊃ T(q, (2k+2, 2))`, `t = 0`;
* (f2) `T̂(3^k p) ⊃ T(q, (2k+1, 3))`, `t = (−1, −1)`;
* (f3) `T̂(3^k q) ⊃ T(q, (−2k−3, −1))`, `t = (1, 1)`, with `c(T̂_{1/d}) = (0,0)`;
* (g1) `T(3^k q) ⊃ T(q, (0, 2))`, `t = 0`;
* (f4) `T(2^k q) ⊃ T(p, (−2, 2k+2))`, `t = (1, 1)`;
* (f5) `T̂(2^k q) ⊃ T(p, (−3, 2k+1))`, `t = (1, 1)`;
* (f6) `T̂(2^k p) ⊃ T(p, (−1, 2k+3))`, `t = (1, 1)`;
* (g2) `T(2^k p) ⊃ T(p, (−2, 0))`, `t = (2, 2)`.

The first three and (g1) have `T(q) = T_{1/(2k+1)}` as the base; the last four have `T(p) = T_{R(1/(2k+1))}`. -/

namespace FLatticePaper.Construction

/-- (f1) `T(3^k p) ⊃ T(q, (2k+2, 2))`, `T(3^k p) = T_{1/(2k+2)}`, base `T_{1/(2k+1)}`. -/
theorem prop_base_cases_f1 (k : ℕ) (hk : 1 ≤ k) (x1 x2 : ℤ)
    (h : (x1, x2) ∈ paperStairTile (2 * (k : ℤ) + 1) ∨
      (x1 - (2 * (k : ℤ) + 2), x2 - 2) ∈ paperStairTile (2 * (k : ℤ) + 1)) :
    (x1, x2) ∈ paperLadderTile (2 * (k : ℤ) + 2) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold paperStairTile paperLadderTile at *
  simp only [paperLadderA, paperLadderB, paperLadderC, paperLadderD, Set.mem_sdiff, Set.mem_union,
    Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h ⊢
  omega

/-- (f2) `T̂(3^k p) ⊃ T(q, (2k+1, 3))`, placed at `t = (−1,−1)` (the lower-left corner of `T̂_{1/(2k+2)}`). -/
theorem prop_base_cases_f2 (k : ℕ) (hk : 1 ≤ k) (x1 x2 : ℤ)
    (h : (x1 - (-1), x2 - (-1)) ∈ paperStairTile (2 * (k : ℤ) + 1) ∨
      (x1 - (-1) - (2 * (k : ℤ) + 1), x2 - (-1) - 3) ∈ paperStairTile (2 * (k : ℤ) + 1)) :
    (x1, x2) ∈ paperLadderAltTile (2 * (k : ℤ) + 2) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold paperStairTile paperLadderAltTile at *
  simp only [paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union,
    Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h ⊢
  omega

/-- (f3) `T̂(3^k q) ⊃ T(q, (−2k−3, −1))`, placed at `t = (1,1)`, with `c(T̂_{1/(2k+3)}) = (0,0)`. -/
theorem prop_base_cases_f3 (k : ℕ) (hk : 1 ≤ k) (x1 x2 : ℤ)
    (h : (x1 - 1, x2 - 1) ∈ paperStairTile (2 * (k : ℤ) + 1) ∨
      (x1 - 1 - (-(2 * (k : ℤ) + 3)), x2 - 1 - (-1)) ∈ paperStairTile (2 * (k : ℤ) + 1)) :
    (x1, x2) ∈ paperStairAltTile (2 * (k : ℤ) + 3) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold paperStairTile paperStairAltTile at *
  simp only [paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h ⊢
  omega

/-- (g1) `T(3^k q) ⊃ T(q, (0, 2))`, `T(3^k q) = T_{1/(2k+3)}`, base `T_{1/(2k+1)}` at offset `0`. -/
theorem prop_base_cases_g1 (k : ℕ) (hk : 1 ≤ k) (x1 x2 : ℤ)
    (h : (x1, x2) ∈ paperStairTile (2 * (k : ℤ) + 1) ∨ (x1, x2 - 2) ∈ paperStairTile (2 * (k : ℤ) + 1)) :
    (x1, x2) ∈ paperStairTile (2 * (k : ℤ) + 3) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold paperStairTile at *
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h ⊢
  omega

/-- (f4) `T(2^k q) ⊃ T(p, (−2, 2k+2))`, base `T_{R(1/(2k+1))}`, placed at `t = (1,1)`. -/
theorem prop_base_cases_f4 (k : ℕ) (hk : 1 ≤ k) (x1 x2 : ℤ)
    (h : (x1 - 1, x2 - 1) ∈ paperNearStairTile (2 * (k : ℤ) + 1) ∨
      (x1 - 1 - (-2), x2 - 1 - (2 * (k : ℤ) + 2)) ∈ paperNearStairTile (2 * (k : ℤ) + 1)) :
    (x1, x2) ∈ paperNearLadderTile (2 * (k : ℤ) + 2) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold paperNearStairTile paperNearLadderTile at *
  simp only [paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD, Set.mem_sdiff, Set.mem_union,
    Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h ⊢
  omega

/-- (f5) `T̂(2^k q) ⊃ T(p, (−3, 2k+1))`, base `T_{R(1/(2k+1))}`, placed at `t = (1,1)`. -/
theorem prop_base_cases_f5 (k : ℕ) (hk : 1 ≤ k) (x1 x2 : ℤ)
    (h : (x1 - 1, x2 - 1) ∈ paperNearStairTile (2 * (k : ℤ) + 1) ∨
      (x1 - 1 - (-3), x2 - 1 - (2 * (k : ℤ) + 1)) ∈ paperNearStairTile (2 * (k : ℤ) + 1)) :
    (x1, x2) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold paperNearStairTile paperNearLadderAltTile at *
  simp only [paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff,
    Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h ⊢
  omega

/-- (f6) `T̂(2^k p) ⊃ T(p, (−1, 2k+3))`, base `T_{R(1/(2k+1))}`, placed at `t = (1,1)`. -/
theorem prop_base_cases_f6 (k : ℕ) (hk : 1 ≤ k) (x1 x2 : ℤ)
    (h : (x1 - 1, x2 - 1) ∈ paperNearStairTile (2 * (k : ℤ) + 1) ∨
      (x1 - 1 - (-1), x2 - 1 - (2 * (k : ℤ) + 3)) ∈ paperNearStairTile (2 * (k : ℤ) + 1)) :
    (x1, x2) ∈ paperNearStairAltTile (2 * (k : ℤ) + 3) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold paperNearStairTile paperNearStairAltTile at *
  simp only [paperNearStairAltA, paperNearStairAltB, paperNearStairAltC, paperNearStairAltD, Set.mem_union,
    Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h ⊢
  omega

/-- (g2) `T(2^k p) ⊃ T(p, (−2, 0))`, base `T_{R(1/(2k+1))}`, placed at `t = (2,2)` (offset `2 v_{q,1}`). -/
theorem prop_base_cases_g2 (k : ℕ) (hk : 1 ≤ k) (x1 x2 : ℤ)
    (h : (x1 - 2, x2 - 2) ∈ paperNearStairTile (2 * (k : ℤ) + 1) ∨
      (x1 - 2 - (-2), x2 - 2 - 0) ∈ paperNearStairTile (2 * (k : ℤ) + 1)) :
    (x1, x2) ∈ paperNearStairTile (2 * (k : ℤ) + 3) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold paperNearStairTile at *
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h ⊢
  omega

end FLatticePaper.Construction
