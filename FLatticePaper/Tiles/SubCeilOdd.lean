import FLatticePaper.Tiles.SubBlockOdd

/-! Task Q25 (sub), the odd bottom walk: the ceiling bridge in abstract form.

The childP word of the odd child is a ceiling word of slope `2N / L` with `L = 2N + C` (`C = D − N`): its letters `ε j = [x_j = q]`
and the ceiling values `g j = L · qPrefix j − 2N j` satisfy `0 ≤ g j < L` and `g (j+1) = g j + L ε j − 2N`. From these alone
(the package `CeilPack`) we derive the block data of the walk: the north-step count `Y k` of the first `k` blocks, the
grade `e k = 2Nk − L Y k` of the cursor of block `k`, and the block types. Two regimes: `2N ≤ C` (`D ≥ 3N`) and `C < 2N`. -/

namespace FLatticePaper.Tiles.SubCeilOdd

/-- The ceiling package: letters `ε` (0/1), ceiling values `g` with the step relation and the window `0 ≤ g < L`. -/
structure CeilPack (N C : ℤ) (L : ℕ) (ε g : ℕ → ℤ) : Prop where
  hε : ∀ j, ε j = 0 ∨ ε j = 1
  hg0 : g 0 = 0
  hstep : ∀ j, j < L → g (j + 1) = g j + (L : ℤ) * ε j - 2 * N
  hbd : ∀ j, j ≤ L → 0 ≤ g j ∧ g j < (L : ℤ)
  hgL : g L = 0
  hL : (L : ℤ) = 2 * N + C

/-- The previous letter indicator (`0` before the first letter). -/
def tY (ε : ℕ → ℤ) (j : ℕ) : ℤ := if j = 0 then 0 else ε (j - 1)

/-- The north-step indicator of block `j`: `1` if the block `j` contains a north step (type EN or NE). -/
def hasNI (ε : ℕ → ℤ) (j : ℕ) : ℤ :=
  (if ε j = 0 ∧ ε (j + 1) = 1 then 1 else 0) + (if ε j = 1 ∧ tY ε j = 1 then 1 else 0)

/-- The north-step count of the first `k` blocks. -/
def Yc (ε : ℕ → ℤ) (k : ℕ) : ℤ := ∑ j ∈ Finset.range k, hasNI ε j

/-- The grade of the cursor of block `k`: `e = 2Nk − L Y`. -/
def ec (N : ℤ) (L : ℕ) (ε : ℕ → ℤ) (k : ℕ) : ℤ := 2 * N * k - (L : ℤ) * Yc ε k

theorem Yc_succ (ε : ℕ → ℤ) (k : ℕ) : Yc ε (k + 1) = Yc ε k + hasNI ε k := by
  unfold Yc
  rw [Finset.sum_range_succ]

theorem ec_succ (N : ℤ) (L : ℕ) (ε : ℕ → ℤ) (k : ℕ) :
    ec N L ε (k + 1) = ec N L ε k + 2 * N - (L : ℤ) * hasNI ε k := by
  unfold ec
  rw [Yc_succ]
  push_cast
  ring

theorem tY_zero (ε : ℕ → ℤ) : tY ε 0 = 0 := by simp [tY]

theorem tY_succ (ε : ℕ → ℤ) (j : ℕ) : tY ε (j + 1) = ε j := by simp [tY]

/-- The first letter is a `q` (the ceiling word starts with `q`). -/
theorem eps_zero (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (L : ℕ) (ε g : ℕ → ℤ) (h : CeilPack N C L ε g) :
    ε 0 = 1 := by
  have h1 := h.hstep 0 (by have := h.hL; omega)
  rw [h.hg0] at h1
  have hb := h.hbd 1 (by have := h.hL; omega)
  rcases h.hε 0 with h0 | h0
  · rw [h0] at h1
    have := hb.1
    simp only [mul_zero, add_zero, zero_add] at h1
    omega
  · exact h0

/-- Regime A (`2N ≤ C`): no two consecutive `q` letters. -/
theorem noqq_A (N C : ℤ) (hA : 2 * N ≤ C) (L : ℕ) (ε g : ℕ → ℤ) (h : CeilPack N C L ε g)
    (j : ℕ) (hj : j + 2 ≤ L) : ¬ (ε j = 1 ∧ ε (j + 1) = 1) := by
  rintro ⟨h1, h2⟩
  have s1 := h.hstep j (by omega)
  have s2 := h.hstep (j + 1) (by omega)
  have b := h.hbd (j + 2) hj
  have hL := h.hL
  rw [h1] at s1
  rw [h2] at s2
  have hbj := h.hbd j (by omega)
  have : (L : ℤ) ≥ 4 * N := by omega
  linarith [b.1, b.2]

/-! ### Regime A (`2N ≤ C`): the north indicator is the next letter -/

theorem hasN_A (N C : ℤ) (hA : 2 * N ≤ C) (L : ℕ) (ε g : ℕ → ℤ) (h : CeilPack N C L ε g)
    (j : ℕ) (hj : j + 2 ≤ L) : hasNI ε j = ε (j + 1) := by
  have hq := noqq_A N C hA L ε g h j hj
  have F2 : ¬ (ε j = 1 ∧ tY ε j = 1) := by
    by_cases hj0 : j = 0
    · subst hj0
      simp [tY]
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      rw [tY_succ]
      intro hh
      exact noqq_A N C hA L ε g h m (by omega) ⟨hh.2, hh.1⟩
  unfold hasNI
  rw [if_neg F2, add_zero]
  rcases h.hε (j + 1) with h1 | h1
  · rw [h1]
    simp
  · rw [h1]
    have h0 : ε j = 0 := by
      rcases h.hε j with h0 | h0
      · exact h0
      · exact absurd ⟨h0, h1⟩ hq
    simp [h0]

/-- The grade of the cursor in regime A: `e k = C − g (k + 1)` for `k + 1 ≤ L`. -/
theorem ec_A (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (hA : 2 * N ≤ C) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPack N C L ε g) : ∀ k : ℕ, k + 1 ≤ L → ec N L ε k = C - g (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    have e0 := eps_zero N C hN hC L ε g h
    have h1 : g 1 = (L : ℤ) * ε 0 - 2 * N := by
      have := h.hstep 0 (by have := h.hL; omega)
      simpa [h.hg0] using this
    show ec N L ε 0 = C - g 1
    rw [h1, e0]
    unfold ec Yc
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero, mul_one]
    rw [h.hL]
    ring
  | succ k ih =>
    intro hk
    rw [ec_succ, ih (by omega), hasN_A N C hA L ε g h k (by omega)]
    have s := h.hstep (k + 1) (by omega)
    linarith

/-! ### Regime B (`C < 2N`): the north indicator is the previous letter -/

theorem ec_zero_eq_zero (N : ℤ) (L : ℕ) (ε : ℕ → ℤ) : ec N L ε 0 = 0 := by
  unfold ec Yc
  simp

theorem hasNI_zero (ε : ℕ → ℤ) (e0 : ε 0 = 1) : hasNI ε 0 = 0 := by
  unfold hasNI
  simp [tY, e0]

theorem hasN_B (N C : ℤ) (_hN : 1 ≤ N) (_hC : 1 ≤ C) (hB : C < 2 * N) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPack N C L ε g) (m : ℕ) (hm : m + 3 ≤ L) : hasNI ε (m + 1) = ε m := by
  have hL := h.hL
  have s1 := h.hstep m (by omega)
  have s2 := h.hstep (m + 1) (by omega)
  have s3 := h.hstep (m + 1 + 1) (by omega)
  have b0 := h.hbd m (by omega)
  have b1 := h.hbd (m + 1) (by omega)
  have b2 := h.hbd (m + 1 + 1) (by omega)
  have b3 := h.hbd (m + 1 + 1 + 1) (by omega)
  rcases h.hε m with h0 | h0 <;> rcases h.hε (m + 1) with h1 | h1 <;>
    rcases h.hε (m + 1 + 1) with h2 | h2 <;>
    simp [hasNI, tY_succ, h0, h1, h2] at s1 s2 s3 ⊢ <;> omega

/-- The grade in regime B: `e (m + 1) = 2N − g m`. -/
theorem ec_B (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (hB : C < 2 * N) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPack N C L ε g) (e0 : ε 0 = 1) :
    ∀ m : ℕ, m + 2 ≤ L → ec N L ε (m + 1) = 2 * N - g m := by
  intro m
  induction m with
  | zero =>
    intro _
    have h1 : g 1 = (L : ℤ) * ε 0 - 2 * N := by
      have := h.hstep 0 (by have := h.hL; omega)
      simpa [h.hg0] using this
    rw [ec_succ, ec_zero_eq_zero N L ε, hasNI_zero ε e0, h.hg0]
    simp
  | succ m ih =>
    intro hm
    rw [ec_succ, ih (by omega), hasN_B N C hN hC hB L ε g h m (by omega)]
    have s := h.hstep m (by omega)
    linarith

/-! ### The thresholds of the block types (both regimes) -/

/-- Regime A, the block `j` with `ε (j+1) = 0` (type EE): the cursor grade plus `N` is below `K1 = D − 2N`. -/
theorem thrA_EE (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (hA : 2 * N ≤ C) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPack N C L ε g) (j : ℕ) (hj : j + 2 ≤ L) (he : ε (j + 1) = 0) :
    ec N L ε j + N ≤ (N + C) - 2 * N := by
  rw [ec_A N C hN hC hA L ε g h j (by omega)]
  have s := h.hstep (j + 1) (by omega)
  have b := h.hbd (j + 2) hj
  rw [he] at s
  linarith [b.1]

/-- Regime A, the block `j` with `ε (j+1) = 1` (type EN): `K1 − N < e ≤ D − N`. -/
theorem thrA_EN (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (hA : 2 * N ≤ C) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPack N C L ε g) (j : ℕ) (hj : j + 2 ≤ L) (he : ε (j + 1) = 1) :
    (N + C) - 2 * N - N < ec N L ε j ∧ ec N L ε j ≤ (N + C) - N := by
  rw [ec_A N C hN hC hA L ε g h j (by omega)]
  have s := h.hstep (j + 1) (by omega)
  have b := h.hbd (j + 1) (by omega)
  have b2 := h.hbd (j + 2) hj
  rw [he] at s
  constructor <;> linarith [b.1, b2.2]

/-- Regime A, the window of block `j`: `K1 − D < e ≤ K1 + N`. -/
theorem winA (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (hA : 2 * N ≤ C) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPack N C L ε g) (j : ℕ) (hj : j + 1 ≤ L) :
    ((N + C) - 2 * N) - (N + C) < ec N L ε j ∧ ec N L ε j ≤ ((N + C) - 2 * N) + N := by
  rw [ec_A N C hN hC hA L ε g h j hj]
  have b := h.hbd (j + 1) hj
  have hL := h.hL
  constructor <;> linarith [b.1, b.2]

/-- Regime A, the last block `j = L − 1`: the grade is `C`. -/
theorem lastA (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (hA : 2 * N ≤ C) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPack N C L ε g) (hL1 : 1 ≤ L) :
    ec N L ε (L - 1) ≤ N + C - N := by
  have hk := ec_A N C hN hC hA L ε g h (L - 1) (by omega)
  have e : L - 1 + 1 = L := by omega
  rw [hk, e, h.hgL]
  linarith

/-- Regime B, the block `m + 1` with `ε m = 0` (type EE): the grade is at most `0 = K1 − N`. -/
theorem thrB_EE (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (hB : C < 2 * N) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPack N C L ε g) (e0 : ε 0 = 1) (m : ℕ) (hm : m + 2 ≤ L) (he : ε m = 0) :
    ec N L ε (m + 1) + N ≤ N := by
  rw [ec_B N C hN hC hB L ε g h e0 m hm]
  have s := h.hstep m (by omega)
  have b := h.hbd (m + 1) (by omega)
  rw [he] at s
  linarith [b.1]

/-- Regime B, the block `m + 1` with `ε m = 1`, `ε (m + 1) = 0` (type EN): `K1 − N < e ≤ D − N`. -/
theorem thrB_EN (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (hB : C < 2 * N) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPack N C L ε g) (e0 : ε 0 = 1) (m : ℕ) (hm : m + 3 ≤ L) (hm1 : ε m = 1)
    (he : ε (m + 1) = 0) :
    N - N < ec N L ε (m + 1) ∧ ec N L ε (m + 1) ≤ (N + C) - N := by
  rw [ec_B N C hN hC hB L ε g h e0 m (by omega)]
  have s1 := h.hstep m (by omega)
  have s2 := h.hstep (m + 1) (by omega)
  have b1 := h.hbd (m + 1) (by omega)
  have b2 := h.hbd (m + 2) (by omega)
  rw [hm1] at s1
  rw [he] at s2
  have hL := h.hL
  constructor <;> linarith [b1.1, b1.2, b2.1]

/-- Regime B, the block `m + 1` with `ε m = 1`, `ε (m + 1) = 1` (type NE): `C < e`. -/
theorem thrB_NE (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (hB : C < 2 * N) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPack N C L ε g) (e0 : ε 0 = 1) (m : ℕ) (hm : m + 3 ≤ L) (hm1 : ε m = 1)
    (he : ε (m + 1) = 1) :
    (N + C) - N < ec N L ε (m + 1) := by
  rw [ec_B N C hN hC hB L ε g h e0 m (by omega)]
  have s1 := h.hstep m (by omega)
  have s2 := h.hstep (m + 1) (by omega)
  have b2 := h.hbd (m + 2) (by omega)
  rw [hm1] at s1
  rw [he] at s2
  have hL := h.hL
  linarith [b2.2]

/-- Regime B, the window of block `m + 1`: `K1 − D < e ≤ K1 + N` with `K1 = N`. -/
theorem winB (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (hB : C < 2 * N) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPack N C L ε g) (e0 : ε 0 = 1) (m : ℕ) (hm : m + 2 ≤ L) :
    N - (N + C) < ec N L ε (m + 1) ∧ ec N L ε (m + 1) ≤ N + N := by
  rw [ec_B N C hN hC hB L ε g h e0 m hm]
  have b := h.hbd m (by omega)
  have hL := h.hL
  constructor <;> linarith [b.1, b.2]

/-- Regime B, the last block `L − 1`: the grade is at most `C`. -/
theorem lastB (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (hB : C < 2 * N) (L : ℕ) (ε g : ℕ → ℤ)
    (h : CeilPack N C L ε g) (e0 : ε 0 = 1) (hL2 : 2 ≤ L) :
    ec N L ε (L - 2 + 1) ≤ N + C - N := by
  have hL := h.hL
  have s1 := h.hstep (L - 1) (by omega)
  rw [show L - 1 + 1 = L by omega, h.hgL] at s1
  have b1 := h.hbd (L - 1) (by omega)
  have hε1 : ε (L - 1) = 0 := by
    rcases h.hε (L - 1) with h0 | h0
    · exact h0
    · rw [h0] at s1
      linarith [b1.1]
  have s2 := h.hstep (L - 2) (by omega)
  rw [show L - 2 + 1 = L - 1 by omega] at s2
  have b2 := h.hbd (L - 2) (by omega)
  have key : 2 * N - C ≤ g (L - 2) := by
    rw [hε1] at s1
    rcases h.hε (L - 2) with h2 | h2
    · rw [h2] at s2
      linarith
    · rw [h2] at s2
      linarith
  rw [ec_B N C hN hC hB L ε g h e0 (L - 2) (by omega)]
  linarith

end FLatticePaper.Tiles.SubCeilOdd
