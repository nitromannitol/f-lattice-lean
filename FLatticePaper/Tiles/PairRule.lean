import Mathlib

/-! Task Q25 (2): the east-step inequality of the bottom walk, as integer arithmetic.

For the odd fraction `(n, d)` (`0 < n < d`, `L = d + n`, `C = d − n`) the pair `j` of the bottom walk has cursor `(2j − b, b)`,
where `b` is the ceiling `⌈(2nj − M)/L⌉` with `M = max(C, 2n)`; its grade is `e = 2nj − L b`, and `M − L < e ≤ M` (the ceiling).
The pair is `EE` when `e ≤ K = max(C − 2n, 0)`, `EN` when `K < e ≤ C`, and `NE` when `C < e`.

Each east step starting at `z` satisfies `k_{1−i} − d < t(z) ≤ k_i`, with `t = n x − d y`, `k_0 = C`, `k_1 = max(d − 2n, n)`
and `i` the parity of `z`. The three lemmas below give this for the first east step of a pair (cursor, `i = 0`), the second
east step of `EE` (`i = 1`), and the east step of `NE` after its north step (`i = 1`). -/

namespace FLatticePaper.Tiles.PairRule

/-- The first east step of pair `j` (from the cursor `(2j − b, b)`, even): `k_1 − d < e ≤ k_0 = C` on the `EE` and `EN`
branches. -/
theorem east_first (n d j b : ℤ) (_hn : 0 < n) (_hnd : n < d)
    (_hb1 : 2 * n * j - max (d - n) (2 * n) ≤ (d + n) * b)
    (hb2 : (d + n) * b - (d + n) < 2 * n * j - max (d - n) (2 * n))
    (he : 2 * n * j - (d + n) * b ≤ d - n) :
    max (d - 2 * n) n - d < 2 * n * j - (d + n) * b ∧ 2 * n * j - (d + n) * b ≤ d - n := by
  constructor
  · rcases le_total (d - n) (2 * n) with h | h
    · rw [max_eq_right h] at hb2
      simp only [max_def]
      split_ifs <;> omega
    · rw [max_eq_left h] at hb2
      simp only [max_def]
      split_ifs <;> omega
  · exact he

/-- The second east step of an `EE` pair (from `(2j − b + 1, b)`, odd): `k_0 − d < e + n ≤ k_1`. -/
theorem east_second_EE (n d j b : ℤ) (_hn : 0 < n) (_hnd : n < d)
    (_hb1 : 2 * n * j - max (d - n) (2 * n) ≤ (d + n) * b)
    (hb2 : (d + n) * b - (d + n) < 2 * n * j - max (d - n) (2 * n))
    (hEE : 2 * n * j - (d + n) * b ≤ max (d - n - 2 * n) 0) :
    (d - n) - d < 2 * n * j - (d + n) * b + n ∧
      2 * n * j - (d + n) * b + n ≤ max (d - 2 * n) n := by
  constructor
  · rcases le_total (d - n) (2 * n) with h | h
    · rw [max_eq_right h] at hb2
      omega
    · rw [max_eq_left h] at hb2
      omega
  · rcases le_total (d - n - 2 * n) 0 with h | h
    · rw [max_eq_right h] at hEE
      simp only [max_def]
      split_ifs <;> omega
    · rw [max_eq_left h] at hEE
      simp only [max_def]
      split_ifs <;> omega

/-- The east step of an `NE` pair after its north step (from `(2j − b, b + 1)`, odd): `k_0 − d < e − d ≤ k_1`. -/
theorem east_second_NE (n d j b : ℤ) (_hn : 0 < n) (hnd : n < d)
    (hb1 : 2 * n * j - max (d - n) (2 * n) ≤ (d + n) * b)
    (hNE : d - n < 2 * n * j - (d + n) * b) :
    (d - n) - d < 2 * n * j - (d + n) * b - d ∧
      2 * n * j - (d + n) * b - d ≤ max (d - 2 * n) n := by
  constructor
  · omega
  · rcases le_total (d - n) (2 * n) with h | h
    · rw [max_eq_right h] at hb1
      rw [max_def]
      split_ifs <;> omega
    · rw [max_eq_left h] at hb1
      rw [max_def]
      split_ifs <;> omega

end FLatticePaper.Tiles.PairRule
