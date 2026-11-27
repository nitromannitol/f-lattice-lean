import FLatticePaper.Construction.PropBaseCasesFG

/-! # The odometer equalities of `prop:base_cases` (f), first item (surgical 7c65f09, lines 1976-1981)

The restriction of the child odometer `o_{3^k(p)}` (`paperLadderValue (2k+2)`) to the first copy of `T(q)` equals the base
odometer `paperStairValue (2k+1)` exactly, and on the second copy `T(q) + v`, `v = (2k+2, 2)`, it equals the base odometer at
`x − v` plus `−x₂ + 2`. The affine factor `−x₂` is `a_{p,2} = (0,−1)` for `p = 0/1`, as the text's
`s(o_q^2) − s(o_q^1) = a_{p,2}` requires; the first copy has slope `0`. -/

namespace FLatticePaper.Construction

/-- `n (n+1) / 2 = chooseTwo (n+1)`. -/
theorem half_mul_succ_eq_chooseTwo (n : ℤ) : n * (n + 1) / 2 = chooseTwo (n + 1) := by
  have h := two_mul_chooseTwo (n + 1)
  have e : n * (n + 1) = 2 * chooseTwo (n + 1) := by
    linear_combination (-1 : ℤ) * h
  rw [e]
  omega

/-- The first copy: the child odometer equals the base odometer on `T_{1/(2k+1)}`. -/
theorem prop_base_cases_f1_odometer_copy1 (k : ℕ) (x1 x2 : ℤ)
    (h : (x1, x2) ∈ paperStairTile (2 * (k : ℤ) + 1)) :
    paperLadderValue (2 * (k : ℤ) + 2) (x1, x2) = paperStairValue (2 * (k : ℤ) + 1) (x1, x2) := by
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  unfold paperStairTile at h
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  unfold paperLadderValue paperStairValue
  simp only [Set.indicator_apply, paperLadderA, paperLadderB, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  generalize x2 * (x2 + 1) / 2 = q
  split_ifs <;> omega

/-- The second copy: the child odometer equals the base odometer at `(x₁ − (2k+2), x₂ − 2)` plus `−x₂ + 2`. -/
theorem prop_base_cases_f1_odometer_copy2 (k : ℕ) (x1 x2 : ℤ)
    (h : (x1 - (2 * (k : ℤ) + 2), x2 - 2) ∈ paperStairTile (2 * (k : ℤ) + 1)) :
    paperLadderValue (2 * (k : ℤ) + 2) (x1, x2) =
      paperStairValue (2 * (k : ℤ) + 1) (x1 - (2 * (k : ℤ) + 2), x2 - 2) + (-x2 + 2) := by
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  unfold paperStairTile at h
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  have hq : x2 * (x2 + 1) / 2 - (x2 - 2) * (x2 - 2 + 1) / 2 = 2 * x2 - 1 := by
    rw [half_mul_succ_eq_chooseTwo x2, half_mul_succ_eq_chooseTwo (x2 - 2)]
    have h1 := two_mul_chooseTwo (x2 + 1)
    have h2 := two_mul_chooseTwo (x2 - 2 + 1)
    have e : 2 * (chooseTwo (x2 + 1) - chooseTwo (x2 - 2 + 1)) = 2 * (2 * x2 - 1) := by
      linear_combination h1 - h2
    omega
  unfold paperLadderValue paperStairValue
  simp only [Set.indicator_apply, paperLadderA, paperLadderB, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  generalize x2 * (x2 + 1) / 2 = q1 at hq ⊢
  generalize (x2 - 2) * (x2 - 2 + 1) / 2 = q2 at hq ⊢
  split_ifs <;> omega

end FLatticePaper.Construction
