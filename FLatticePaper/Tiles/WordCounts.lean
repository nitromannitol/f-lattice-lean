import FLatticePaper.Tiles.SubWalkOddBlocks
import FLatticePaper.Tiles.CeilWords

/-! Task Q25 (completeness of the seam), the letter counts of the bottom walk `gH x` of a ceiling word `x`.

For a 0/1 sequence `ε` with `ε 0 = 1` the north count `Yc ε m` satisfies `Yc ε (m + 1) = Q (m + 2) − 1 − ε m · ε (m + 1)`, where `Q` counts
the letters `1`. So a ceiling word `x` of slope `k / l` with `1 ≤ k < l` (so `x_0 = q` and `x_{l−1} = p`) has `k − 1` north letters and
`2l − k` east letters in `gH x`, with no appeal to the regime (`count_gH_i`, `count_gH_one`). -/

namespace FLatticePaper.Tiles.WordCounts

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SubCeilOdd
  FLatticePaper.Tiles.SubWalkOdd FLatticePaper.Tiles.SubWalkOddBlocks

/-- The letter counts of a block, in `ℤ`. -/
theorem count_block (x : BinaryWord) (j : ℕ) (hj : j + 1 < x.length) :
    (List.count Unit4.i (blockWord x j) : ℤ) = hasNI (epsOf x) j ∧
      (List.count Unit4.one (blockWord x j) : ℤ) = 2 - hasNI (epsOf x) j := by
  rw [blockWord_eq x j hj]
  split_ifs with h1 h2
  · rw [hasNI_EN x j h1]
    norm_num [List.count_cons]
  · rw [hasNI_NE x j h2]
    norm_num [List.count_cons]
  · rw [hasNI_EE x j h1 h2]
    norm_num [List.count_cons]

/-- The letter count of a prefix of blocks, in `ℤ`. -/
theorem count_prefix_int (x : BinaryWord) (a : Unit4) (m : ℕ) (hm : m + 1 ≤ x.length) :
    (List.count a ((List.range m).flatMap (blockWord x)) : ℤ) =
      ∑ j ∈ Finset.range m, (List.count a (blockWord x j) : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [flatMap_range_succ, List.count_append, Finset.sum_range_succ, ← ih (by omega)]
    push_cast
    ring

theorem epsOf_01 (x : BinaryWord) (j : ℕ) : epsOf x j = 0 ∨ epsOf x j = 1 := by
  unfold epsOf
  split_ifs <;> simp

/-- The north letters of `gH x` are the north count `Yc` of its blocks. -/
theorem count_gH_i (x : BinaryWord) (hx : 1 ≤ x.length) :
    (List.count Unit4.i (gH x) : ℤ) = Yc (epsOf x) (x.length - 1) := by
  rw [gH_walk x hx, List.count_append, Nat.cast_add, count_prefix_int x Unit4.i (x.length - 1) (by omega)]
  have h : ∀ j ∈ Finset.range (x.length - 1),
      (List.count Unit4.i (blockWord x j) : ℤ) = hasNI (epsOf x) j := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact (count_block x j (by omega)).1
  rw [Finset.sum_congr rfl h]
  simp [Yc]

/-- The east letters of `gH x`. -/
theorem count_gH_one (x : BinaryWord) (hx : 1 ≤ x.length) :
    (List.count Unit4.one (gH x) : ℤ) = 2 * ((x.length : ℤ) - 1) - Yc (epsOf x) (x.length - 1) + 1 := by
  rw [gH_walk x hx, List.count_append, Nat.cast_add, count_prefix_int x Unit4.one (x.length - 1) (by omega)]
  have h : ∀ j ∈ Finset.range (x.length - 1),
      (List.count Unit4.one (blockWord x j) : ℤ) = 2 - hasNI (epsOf x) j := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact (count_block x j (by omega)).2
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib]
  simp [Yc]
  omega

/-- The `hasNI` recursion at a step: the north indicator of block `m + 1`. -/
theorem hasNI_step (ε : ℕ → ℤ) (h01 : ∀ j, ε j = 0 ∨ ε j = 1) (m : ℕ) :
    hasNI ε (m + 1) = ε (m + 1 + 1) - ε (m + 1) * ε (m + 1 + 1) + ε m * ε (m + 1) := by
  unfold hasNI
  rw [tY_succ]
  rcases h01 m with a | a <;> rcases h01 (m + 1) with b | b <;> rcases h01 (m + 1 + 1) with c | c <;>
    simp [a, b, c]

/-- The north count identity: `Yc (m + 1) = Q (m + 2) − 1 − ε m ε (m + 1)` for a `0/1` sequence with `ε 0 = 1`. -/
theorem Yc_succ_formula (ε : ℕ → ℤ) (h01 : ∀ j, ε j = 0 ∨ ε j = 1) (h0 : ε 0 = 1) (m : ℕ) :
    Yc ε (m + 1) = (∑ j ∈ Finset.range (m + 2), ε j) - 1 - ε m * ε (m + 1) := by
  induction m with
  | zero =>
    simp [Yc, hasNI_zero ε h0, Finset.sum_range_succ, h0]
  | succ m ih =>
    have hq : (∑ j ∈ Finset.range (m + 1 + 2), ε j) = (∑ j ∈ Finset.range (m + 2), ε j) + ε (m + 2) := by
      rw [show m + 1 + 2 = (m + 2) + 1 by ring, Finset.sum_range_succ]
    rw [Yc_succ, ih, hasNI_step ε h01 m, hq]
    ring

/-- The north count of a `0/1` word ending with `0` is its number of `1` letters minus one. -/
theorem Yc_last (ε : ℕ → ℤ) (h01 : ∀ j, ε j = 0 ∨ ε j = 1) (h0 : ε 0 = 1) (L : ℕ) (hL : 2 ≤ L)
    (hlast : ε (L - 1) = 0) :
    Yc ε (L - 1) = (∑ j ∈ Finset.range L, ε j) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  have e : m + 2 - 1 = m + 1 := by omega
  rw [e] at hlast ⊢
  rw [Yc_succ_formula ε h01 h0 m, hlast, mul_zero, sub_zero]

/-- The first letter of a ceiling word with `1 ≤ k` is `q`. -/
theorem ceil_eps_zero (x : BinaryWord) (k l : ℤ) (hx : CeilWords.CeilWord x k l) (hk : 1 ≤ k) (hkl : k < l) :
    epsOf x 0 = 1 := by
  have hL : (x.length : ℤ) = l := hx.1
  have hlen : 0 < x.length := by omega
  have hb := hx.2 1 (by omega)
  have hq1 : CeilWords.qPrefix x 1 = epsOf x 0 := by
    have := qPrefix_succ x 0 hlen
    simpa [CeilWords.qPrefix] using this
  rw [hq1] at hb
  rcases epsOf_01 x 0 with h | h
  · rw [h] at hb
    omega
  · exact h

/-- The last letter of a ceiling word with `k < l` is `p`. -/
theorem ceil_eps_last (x : BinaryWord) (k l : ℤ) (hx : CeilWords.CeilWord x k l) (hk : 1 ≤ k) (hkl : k < l) :
    epsOf x (x.length - 1) = 0 := by
  have hL : (x.length : ℤ) = l := hx.1
  have hlen : 1 ≤ x.length := by omega
  have htot : CeilWords.qPrefix x x.length = k := CeilWords.ceil_total x k l hx (by omega)
  have hsucc := qPrefix_succ x (x.length - 1) (by omega)
  rw [show x.length - 1 + 1 = x.length by omega, htot] at hsucc
  have hb := hx.2 (x.length - 1) (by omega)
  rcases epsOf_01 x (x.length - 1) with h | h
  · exact h
  · exfalso
    rw [h] at hsucc
    have hq : CeilWords.qPrefix x (x.length - 1) = k - 1 := by linarith
    rw [hq] at hb
    have hc : ((x.length - 1 : ℕ) : ℤ) = l - 1 := by omega
    rw [hc] at hb
    nlinarith [hb.2]

/-- The letters of the walk `gH x` of a ceiling word of slope `k / l` with `1 ≤ k < l`. -/
theorem count_gH_ceil (x : BinaryWord) (k l : ℤ) (hx : CeilWords.CeilWord x k l) (hk : 1 ≤ k) (hkl : k < l) :
    (List.count Unit4.i (gH x) : ℤ) = k - 1 ∧ (List.count Unit4.one (gH x) : ℤ) = 2 * l - k := by
  have hL : (x.length : ℤ) = l := hx.1
  have hlen : 1 ≤ x.length := by omega
  have hL2 : 2 ≤ x.length := by omega
  have hsum : (∑ j ∈ Finset.range x.length, epsOf x j) = k := by
    have key : ∀ j, j ≤ x.length → CeilWords.qPrefix x j = ∑ i ∈ Finset.range j, epsOf x i := by
      intro j
      induction j with
      | zero => intro _; simp [CeilWords.qPrefix]
      | succ j ih =>
        intro hj
        rw [Finset.sum_range_succ, ← ih (by omega)]
        exact qPrefix_succ x j (by omega)
    rw [← key x.length le_rfl]
    exact CeilWords.ceil_total x k l hx (by omega)
  have hY := Yc_last (epsOf x) (epsOf_01 x) (ceil_eps_zero x k l hx hk hkl) x.length hL2 (ceil_eps_last x k l hx hk hkl)
  rw [hsum] at hY
  constructor
  · rw [count_gH_i x hlen, hY]
  · rw [count_gH_one x hlen, hY, hL]
    ring

end FLatticePaper.Tiles.WordCounts
