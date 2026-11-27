import FLatticePaper.Construction.PropBaseCasesFG

/-! # The odometer equalities of `prop:base_cases` (f) and (g) (surgical 7c65f09, lines 1976-1998)

On each copy of the base tile inside the child tile, the child odometer equals the base odometer at the translated point, up to
an affine function. The operator's rule (as for eq:periodicity): a translation by `Σ cᵢ v_{r,i}` carries the affine factor
`Σ cᵢ a_{r,i}`, with `a_{r,1} = 0` and `a_{n/d,2} = (n, −d)`. The rule applies to the offset of the copy and to `v` in `T(·, v)`
(copy 2 relative to copy 1). The constants are not printed in the text and are existential.

Copy 1 has the offset of its column; copy 2 has offset plus `v`. The (g) items use the truncated copies `T^{sm}` (the tile minus
its two special points, lines 1997-2003). -/

namespace FLatticePaper.Construction

/-- The translation factor `a_{r,1}`: zero. -/
def aVec1 : ℤ × ℤ := (0, 0)

/-- The translation factor `a_{n/d,2} = (n, −d)`. -/
def aVec2 (n d : ℤ) : ℤ × ℤ := (n, -d)

/-- The affine function `a^T x` of a translation factor. -/
def affineAt (a : ℤ × ℤ) (x1 x2 : ℤ) : ℤ := a.1 * x1 + a.2 * x2

/-- `n (n+1) / 2 = chooseTwo (n+1)`. -/
theorem half_mul_succ_eq_chooseTwo (n : ℤ) : n * (n + 1) / 2 = chooseTwo (n + 1) := by
  have h := two_mul_chooseTwo (n + 1)
  have e : n * (n + 1) = 2 * chooseTwo (n + 1) := by
    linear_combination (-1 : ℤ) * h
  rw [e]
  omega

/-- `chooseTwo (m+1) = chooseTwo m + m`. -/
theorem chooseTwo_succ_eq (m : ℤ) : chooseTwo (m + 1) = chooseTwo m + m := by
  have h1 := two_mul_chooseTwo (m + 1)
  have h2 := two_mul_chooseTwo m
  have e : 2 * (chooseTwo (m + 1) - chooseTwo m - m) = 0 := by
    linear_combination h1 - h2
  omega

/-- `chooseTwo (x+1) − chooseTwo (x−1) = 2x − 1`. -/
theorem chooseTwo_succ_sub_succ (x : ℤ) : chooseTwo (x + 1) - chooseTwo (x - 1) = 2 * x - 1 := by
  have h1 := two_mul_chooseTwo (x + 1)
  have h2 := two_mul_chooseTwo (x - 1)
  have e : 2 * (chooseTwo (x + 1) - chooseTwo (x - 1)) = 2 * (2 * x - 1) := by
    linear_combination h1 - h2
  omega

/-- The floor of a shifted square: `((u − 2m)²) / 4 = u²/4 − m u + m²`. -/
theorem sq_shift_div_four (u m : ℤ) : (u - 2 * m) ^ 2 / 4 = u ^ 2 / 4 - m * u + m ^ 2 := by
  have e : (u - 2 * m) ^ 2 = u ^ 2 - 4 * (m * u) + 4 * (m ^ 2) := by ring
  rw [e]
  generalize u ^ 2 = A
  generalize m * u = B
  generalize m ^ 2 = C
  omega

/-! ### Item (f1): `T(3^k p) ⊃ T(q, (2k+2, 2))`, offset `0`, `v = v_{q,1}+v_{p,1}+v_{p,2}`, factor `a_{p,2} = (0,−1)` -/

/-- (f1), copy 1: the child odometer equals the base odometer, factor `0` (offset `0`). -/
theorem prop_base_cases_f1_odometer_copy1 (k : ℕ) (x1 x2 : ℤ)
    (h : (x1, x2) ∈ paperStairTile (2 * (k : ℤ) + 1)) :
    paperLadderValue (2 * (k : ℤ) + 2) (x1, x2) = paperStairValue (2 * (k : ℤ) + 1) (x1, x2) := by
  unfold paperStairTile at h
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  unfold paperLadderValue paperStairValue
  simp only [Set.indicator_apply, paperLadderA, paperLadderB, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  generalize x2 * (x2 + 1) / 2 = q
  split_ifs <;> omega

/-- (f1), copy 2: the child odometer equals the base odometer at `x − v` plus the affine factor of
`v = v_{q,1}+v_{p,1}+v_{p,2}`, namely `a_{q,1}+a_{p,1}+a_{p,2}`, plus a constant. -/
theorem prop_base_cases_f1_odometer_copy2 (k : ℕ) :
    ∃ b : ℤ, ∀ x1 x2 : ℤ,
      (x1 - (2 * (k : ℤ) + 2), x2 - 2) ∈ paperStairTile (2 * (k : ℤ) + 1) →
        paperLadderValue (2 * (k : ℤ) + 2) (x1, x2) =
          paperStairValue (2 * (k : ℤ) + 1) (x1 - (2 * (k : ℤ) + 2), x2 - 2) +
            affineAt (aVec1 + aVec1 + aVec2 0 1) x1 x2 + b := by
  refine ⟨2, fun x1 x2 h => ?_⟩
  have haff : affineAt (aVec1 + aVec1 + aVec2 0 1) x1 x2 = -x2 := by
    simp only [affineAt, aVec1, aVec2, Prod.fst_add, Prod.snd_add]
    ring
  rw [haff]
  unfold paperStairTile at h
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  have hX1 : x2 * (x2 + 1) / 2 = chooseTwo (x2 + 1) := half_mul_succ_eq_chooseTwo x2
  have hX2 : (x2 - 2) * (x2 - 2 + 1) / 2 = chooseTwo (x2 - 2 + 1) := half_mul_succ_eq_chooseTwo (x2 - 2)
  have hq : chooseTwo (x2 + 1) - chooseTwo (x2 - 2 + 1) = 2 * x2 - 1 := by
    have e : x2 - 2 + 1 = x2 - 1 := by ring
    rw [e]
    exact chooseTwo_succ_sub_succ x2
  unfold paperLadderValue paperStairValue
  simp only [Set.indicator_apply, paperLadderA, paperLadderB, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  rw [hX1, hX2]
  generalize chooseTwo (x2 + 1) = c1 at hq ⊢
  generalize chooseTwo (x2 - 2 + 1) = c2 at hq ⊢
  split_ifs <;> omega

/-! ### Item (f2): `T̂(3^k p) ⊃ T(q, (2k+1, 3))`, copy 1 at the corner shift `(−1,−1)` (offset `0`), copy 2 with
`v = v_{q,1}+v_{p,1}+2v_{p,2}`, factor `2 a_{p,2} = (0,−2)`. The corner shift `t = (−1,−1)` is written `x + 1`. -/

/-- (f2), copy 1: the alternate ladder odometer equals the base odometer at `x − t`, `t = (−1,−1)`, factor `0`. -/
theorem prop_base_cases_f2_odometer_copy1 (k : ℕ) (hk : 1 ≤ k) (x1 x2 : ℤ)
    (h : (x1 + 1, x2 + 1) ∈ paperStairTile (2 * (k : ℤ) + 1)) :
    paperLadderAltValue (2 * (k : ℤ) + 2) (x1, x2) =
      paperStairValue (2 * (k : ℤ) + 1) (x1 + 1, x2 + 1) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold paperStairTile at h
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  have hX1 : x2 * (x2 + 1) / 2 = chooseTwo (x2 + 1) := half_mul_succ_eq_chooseTwo x2
  have hX2 : (x2 + 1) * (x2 + 1 + 1) / 2 = chooseTwo (x2 + 1 + 1) := half_mul_succ_eq_chooseTwo (x2 + 1)
  have hX3 : chooseTwo (x2 + 1 + 1) = chooseTwo (x2 + 1) + (x2 + 1) := chooseTwo_succ_eq (x2 + 1)
  unfold paperLadderAltValue paperStairValue
  simp only [Set.indicator_apply, paperLadderAltA, paperLadderAltB, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  rw [hX1, hX2, hX3]
  have hb1 : x1 ≤ 2 * (k : ℤ) := by omega
  have hb2 : x1 + x2 ≤ 2 * (k : ℤ) + 2 := by omega
  split_ifs <;> omega

/-- (f2), copy 2: the factor `a_{q,1}+a_{p,1}+2a_{p,2}` (written `aVec1 + aVec1 + aVec2 0 1 + aVec2 0 1`), plus a constant. -/
theorem prop_base_cases_f2_odometer_copy2 (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : ℤ, ∀ x1 x2 : ℤ,
      (x1 + 1 - (2 * (k : ℤ) + 1), x2 + 1 - 3) ∈ paperStairTile (2 * (k : ℤ) + 1) →
        paperLadderAltValue (2 * (k : ℤ) + 2) (x1, x2) =
          paperStairValue (2 * (k : ℤ) + 1) (x1 + 1 - (2 * (k : ℤ) + 1), x2 + 1 - 3) +
            affineAt (aVec1 + aVec1 + aVec2 0 1 + aVec2 0 1) x1 x2 + b := by
  refine ⟨2, fun x1 x2 h => ?_⟩
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have haff : affineAt (aVec1 + aVec1 + aVec2 0 1 + aVec2 0 1) x1 x2 = -2 * x2 := by
    simp only [affineAt, aVec1, aVec2, Prod.fst_add, Prod.snd_add]
    ring
  rw [haff]
  unfold paperStairTile at h
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  have hX1 : x2 * (x2 + 1) / 2 = chooseTwo (x2 + 1) := half_mul_succ_eq_chooseTwo x2
  have hX4 : (x2 + 1 - 3) * (x2 + 1 - 3 + 1) / 2 = chooseTwo (x2 - 2 + 1) := by
    have e : x2 + 1 - 3 = x2 - 2 := by ring
    rw [e, half_mul_succ_eq_chooseTwo]
  have hq : chooseTwo (x2 + 1) - chooseTwo (x2 - 2 + 1) = 2 * x2 - 1 := by
    have e : x2 - 2 + 1 = x2 - 1 := by ring
    rw [e]
    exact chooseTwo_succ_sub_succ x2
  unfold paperLadderAltValue paperStairValue
  simp only [Set.indicator_apply, paperLadderAltA, paperLadderAltB, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  rw [hX1, hX4]
  have hd1 : 0 ≤ x1 := by omega
  have hd2 : 0 ≤ x1 + x2 - 2 * (k : ℤ) - 2 := by omega
  generalize chooseTwo (x2 + 1) = c1 at hq ⊢
  generalize chooseTwo (x2 - 2 + 1) = c2 at hq ⊢
  split_ifs <;> omega

/-- `(u − 2)² / 4 = u²/4 − u + 1`. -/
theorem sq_sub_two_div_four (u : ℤ) : (u - 2) ^ 2 / 4 = u ^ 2 / 4 - u + 1 := by
  have e : (u - 2) ^ 2 = u ^ 2 - 4 * u + 4 := by ring
  rw [e]
  generalize u ^ 2 = A
  omega

/-! ### Item (f3): `T̂(3^k q) ⊃ T(q, (−2k−3, −1))`, offset `v_{p,2}+v_{p,1}` (copy 1), factor `a_{p,2} = (0,−1)`;
copy 2 adds `−a_{q,1}−a_{p,1} = 0`. -/

/-- (f3), copy 1: the alternate staircase odometer equals the base odometer at `x − (1,1)` plus the factor `a_{p,2}+a_{p,1}`. -/
theorem prop_base_cases_f3_odometer_copy1 (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : ℤ, ∀ x1 x2 : ℤ, (x1 - 1, x2 - 1) ∈ paperStairTile (2 * (k : ℤ) + 1) →
      paperStairAltValue (2 * (k : ℤ) + 3) (x1, x2) =
        paperStairValue (2 * (k : ℤ) + 1) (x1 - 1, x2 - 1) + affineAt (aVec2 0 1 + aVec1) x1 x2 + b := by
  refine ⟨1, fun x1 x2 h => ?_⟩
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have haff : affineAt (aVec2 0 1 + aVec1) x1 x2 = -x2 := by
    simp only [affineAt, aVec1, aVec2, Prod.fst_add, Prod.snd_add]
    ring
  rw [haff]
  unfold paperStairTile at h
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  have hX1 : x2 * (x2 + 1) / 2 = chooseTwo x2 + x2 := by
    rw [half_mul_succ_eq_chooseTwo, chooseTwo_succ_eq]
  have hX2 : (x2 - 1) * (x2 - 1 + 1) / 2 = chooseTwo (x2 - 1 + 1) := half_mul_succ_eq_chooseTwo (x2 - 1)
  have hX5 : chooseTwo (x2 - 1 + 1) = chooseTwo x2 := by
    rw [show x2 - 1 + 1 = x2 by ring]
  unfold paperStairAltValue paperStairValue
  simp only [Set.indicator_apply, paperStairAltA, paperStairAltB, Set.mem_union, Set.mem_setOf_eq, Prod.mk.injEq]
  rw [hX1, hX2, hX5]
  split_ifs <;> omega

/-- (f3), copy 2: the factor of the offset plus `−a_{q,1}−a_{p,1}`, which is `a_{p,2}`, plus a constant. -/
theorem prop_base_cases_f3_odometer_copy2 (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : ℤ, ∀ x1 x2 : ℤ, (x1 + 2 * (k : ℤ) + 2, x2) ∈ paperStairTile (2 * (k : ℤ) + 1) →
      paperStairAltValue (2 * (k : ℤ) + 3) (x1, x2) =
        paperStairValue (2 * (k : ℤ) + 1) (x1 + 2 * (k : ℤ) + 2, x2) +
          affineAt (aVec2 0 1 + aVec1 + (-aVec1 - aVec1)) x1 x2 + b := by
  refine ⟨0, fun x1 x2 h => ?_⟩
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have haff : affineAt (aVec2 0 1 + aVec1 + (-aVec1 - aVec1)) x1 x2 = -x2 := by
    simp only [affineAt, aVec1, aVec2, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_sub, Prod.snd_sub]
    ring
  rw [haff]
  unfold paperStairTile at h
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  have hX1 : x2 * (x2 + 1) / 2 = chooseTwo (x2 + 1) := half_mul_succ_eq_chooseTwo x2
  unfold paperStairAltValue paperStairValue
  simp only [Set.indicator_apply, paperStairAltA, paperStairAltB, Set.mem_union, Set.mem_setOf_eq, Prod.mk.injEq]
  rw [hX1]
  split_ifs <;> omega

/-! ### Item (g1): `T(3^k q) ⊃ T(q, (0,2))` on the truncated copies `T^{sm}(q) = T(q)` minus `(0,0)` and `(2,2k+2)`;
copy 2 has `v = v_{p,1}+2v_{p,2}`, factor `2a_{p,2} = (0,−2)`, offset `0`. -/

/-- (g1), copy 1: on `T^{sm}(q)` the child odometer equals the base odometer, exactly. -/
theorem prop_base_cases_g1_odometer_copy1 (k : ℕ) (hk : 1 ≤ k) (x1 x2 : ℤ)
    (h : (x1, x2) ∈ paperStairTile (2 * (k : ℤ) + 1)) (h0 : (x1, x2) ≠ (0, 0))
    (h2 : (x1, x2) ≠ (2, 2 * (k : ℤ) + 2)) :
    paperStairValue (2 * (k : ℤ) + 3) (x1, x2) = paperStairValue (2 * (k : ℤ) + 1) (x1, x2) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold paperStairTile at h
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  simp only [ne_eq, Prod.mk.injEq] at h0 h2
  unfold paperStairValue
  simp only [Prod.mk.injEq]
  split_ifs <;> omega

/-- (g1), copy 2: on the truncated copy the child odometer equals the base at `x − (0,2)` plus `−2 x₂` and a constant. -/
theorem prop_base_cases_g1_odometer_copy2 (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : ℤ, ∀ x1 x2 : ℤ, (x1, x2 - 2) ∈ paperStairTile (2 * (k : ℤ) + 1) →
      (x1, x2 - 2) ≠ (0, 0) → (x1, x2 - 2) ≠ (2, 2 * (k : ℤ) + 2) →
      paperStairValue (2 * (k : ℤ) + 3) (x1, x2) =
        paperStairValue (2 * (k : ℤ) + 1) (x1, x2 - 2) +
          affineAt (aVec1 + aVec2 0 1 + aVec2 0 1) x1 x2 + b := by
  refine ⟨3, fun x1 x2 h h0 h2 => ?_⟩
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have haff : affineAt (aVec1 + aVec2 0 1 + aVec2 0 1) x1 x2 = -2 * x2 := by
    simp only [affineAt, aVec1, aVec2, Prod.fst_add, Prod.snd_add]
    ring
  rw [haff]
  unfold paperStairTile at h
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  simp only [ne_eq, Prod.mk.injEq] at h0 h2
  have hX1 : x2 * (x2 + 1) / 2 = chooseTwo (x2 + 1) := half_mul_succ_eq_chooseTwo x2
  have hX4 : (x2 - 2) * (x2 - 2 + 1) / 2 = chooseTwo (x2 - 2 + 1) := half_mul_succ_eq_chooseTwo (x2 - 2)
  have hq : chooseTwo (x2 + 1) - chooseTwo (x2 - 2 + 1) = 2 * x2 - 1 := by
    have e : x2 - 2 + 1 = x2 - 1 := by ring
    rw [e]
    exact chooseTwo_succ_sub_succ x2
  unfold paperStairValue
  simp only [Prod.mk.injEq]
  rw [hX1, hX4]
  generalize chooseTwo (x2 + 1) = c1 at hq ⊢
  generalize chooseTwo (x2 - 2 + 1) = c2 at hq ⊢
  split_ifs <;> omega

/-! ### Item (g2): `T(2^k p) ⊃ T(p, (−2, 0))` on the truncated copies `T^{sm}(p) = T(p)` minus `(2k+2, 2k)` and `(0, 2k+2)`;
copy 1 at `t = 2 v_{q,1}` (factor `0`), copy 2 with `v = −2v_{q,1} + v_{q,2}`, factor `a_{q,2} = (1,−1)`. -/

/-- (g2), copy 1: on the truncated copy, the child odometer equals the base odometer at `x − (2,2)`, exactly. -/
theorem prop_base_cases_g2_odometer_copy1 (k : ℕ) (hk : 1 ≤ k) (x1 x2 : ℤ)
    (h : (x1 - 2, x2 - 2) ∈ paperNearStairTile (2 * (k : ℤ) + 1))
    (h0 : (x1 - 2, x2 - 2) ≠ (2 * (k : ℤ) + 2, 2 * (k : ℤ)))
    (h2 : (x1 - 2, x2 - 2) ≠ (0, 2 * (k : ℤ) + 2)) :
    paperNearStairValue (2 * (k : ℤ) + 3) (x1, x2) = paperNearStairValue (2 * (k : ℤ) + 1) (x1 - 2, x2 - 2) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold paperNearStairTile at h
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  simp only [ne_eq, Prod.mk.injEq] at h0 h2
  simp only [paperNearStairValue, Prod.mk.injEq]
  rw [show (x2 - 2 - (x1 - 2)) ^ 2 = (x2 - x1) ^ 2 by ring]
  generalize (x2 - x1) ^ 2 = Q
  split_ifs <;> omega

/-- (g2), copy 2: on the truncated copy, the child odometer equals the base at `x − v` plus `(1,−1)·x` and a constant. -/
theorem prop_base_cases_g2_odometer_copy2 (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : ℤ, ∀ x1 x2 : ℤ, (x1, x2 - 2) ∈ paperNearStairTile (2 * (k : ℤ) + 1) →
      (x1, x2 - 2) ≠ (2 * (k : ℤ) + 2, 2 * (k : ℤ)) → (x1, x2 - 2) ≠ (0, 2 * (k : ℤ) + 2) →
      paperNearStairValue (2 * (k : ℤ) + 3) (x1, x2) =
        paperNearStairValue (2 * (k : ℤ) + 1) (x1, x2 - 2) +
          affineAt (aVec1 + aVec1 + (-aVec1 - aVec1 + aVec2 1 1)) x1 x2 + b := by
  refine ⟨1, fun x1 x2 h h0 h2 => ?_⟩
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have haff : affineAt (aVec1 + aVec1 + (-aVec1 - aVec1 + aVec2 1 1)) x1 x2 = x1 - x2 := by
    simp only [affineAt, aVec1, aVec2, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_sub, Prod.snd_sub]
    ring
  rw [haff]
  unfold paperNearStairTile at h
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  simp only [ne_eq, Prod.mk.injEq] at h0 h2
  simp only [paperNearStairValue, Prod.mk.injEq]
  rw [show (x2 - 2 - x1) ^ 2 = (x2 - x1 - 2) ^ 2 by ring, sq_sub_two_div_four (x2 - x1)]
  generalize (x2 - x1) ^ 2 = Q
  split_ifs <;> omega

end FLatticePaper.Construction
