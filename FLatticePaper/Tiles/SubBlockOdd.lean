import FLatticePaper.Tiles.SubCriteria

/-! Task Q25 (sub), the odd bottom walk: the arithmetic of one block.

For the odd fraction with numerator `N` and denominator `D` (`C = D − N`, `L = D + N`, `T = D² + 2DN − N²`), the four-test
bounds of the cell with lower-left corner `(x, y)` are `pB` (`cell_iff_pB`), written in the grade `t = N x − D y` and the
slope `s = L x + C y` (`pBts`). The block with cursor `(2k − Y, Y)` has grade `e = 2Nk − L Y` and slope `s0 = 2Lk − 2NY`.
Its steps are boundary edges of the cell tile when the grade lies in the window of the block type (EE, EN, NE). -/

namespace FLatticePaper.Tiles.SubBlockOdd

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.CellFourTests
  FLatticePaper.Tiles.SiteInduction

/-- The four-test bounds of a corner with grade `t` and slope `s`, at the parity `ev` (even: `ev` true). -/
def pBts (N D K1 Lam : ℤ) (ev : Prop) [Decidable ev] (t s : ℤ) : Prop :=
  if ev then
    (2 * D - (D ^ 2 + 2 * D * N - N ^ 2) - (D - N) ≤ t ∧ t ≤ D - N) ∧
      (0 ≤ s ∧ s ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N))
  else
    (2 * D - (D ^ 2 + 2 * D * N - N ^ 2) - K1 ≤ t ∧ t ≤ K1) ∧
      (Lam ≤ s ∧ s ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - Lam)

/-- The four-test bounds of the lower-left corner `(x, y)` of the odd fraction `(N, D)`. -/
def pB (N D K1 Lam x y : ℤ) : Prop :=
  pBts N D K1 Lam ((x + y) % 2 = 0) (N * x - D * y) ((D + N) * x + (D - N) * y)

theorem pB_eq (N D K1 Lam x y t s : ℤ) (ht : N * x - D * y = t) (hs : (D + N) * x + (D - N) * y = s) :
    pB N D K1 Lam x y ↔ pBts N D K1 Lam ((x + y) % 2 = 0) t s := by
  unfold pB
  rw [ht, hs]

/-- The bounds `pB` are the four-test bounds of the lower-left corner, for the odd fraction `f`. -/
theorem cell_iff_pB (f : Fraction) (hodd : (f.num + f.den) % 2 = 1) (hpos : 0 < f.num)
    (hlt : f.num < f.den) (P : Finset GInt) (hP : ∀ x : GInt, x ∈ P ↔ InH f x) (x y : ℤ) :
    cellCorners (x, y) ⊆ P ↔
      pB f.num f.den (max (f.den - 2 * f.num) f.num) (min (f.den - f.num) (3 * f.num - f.den)) x y := by
  rw [SubCriteria.cellCorners_subset_iff_bounds f hodd hpos hlt P hP (x, y)]
  unfold pB pBts
  by_cases h : (x + y) % 2 = 0
  · have hk : CellFourTests.cellK f (decide (((x, y).1 + (x, y).2) % 2 = 0)) = f.den - f.num := by
      simp [CellFourTests.cellK, h]
    have hl : lOf f (decide (((x, y).1 + (x, y).2) % 2 = 0)) = 0 := by
      simp [lOf, h]
    rw [hk, hl]
    simp [h, tOf, tCo, sCo]
  · have hk : CellFourTests.cellK f (decide (((x, y).1 + (x, y).2) % 2 = 0)) =
        max (f.den - 2 * f.num) f.num := by
      simp [CellFourTests.cellK, h]
    have hl : lOf f (decide (((x, y).1 + (x, y).2) % 2 = 0)) =
        min (f.den - f.num) (3 * f.num - f.den) := by
      simp [lOf, h]
    rw [hk, hl]
    simp [h, tOf, tCo, sCo]

/-! ### The slope bounds of a cursor

With `e = 2Nk − LY` and `s0 = 2Lk − 2NY`, the window `e ≤ K1 + N` (that is `e ≤ M`, `M = K1 + N ≤ L`) bounds the slope. -/

theorem s0_nonneg (N D k Y : ℤ) (hN : 1 ≤ N) (hk0 : 0 ≤ k) (hYk : Y ≤ k) (hND : N + 1 ≤ D) :
    0 ≤ 2 * (D + N) * k - 2 * N * Y := by
  nlinarith

end FLatticePaper.Tiles.SubBlockOdd

namespace FLatticePaper.Tiles.SubBlockOdd

/-! ### The slope of the cursor, from the window -/

theorem L_s0_le_two (N D K1 k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hkL : k + 2 ≤ D + N) (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) :
    (D + N) * (2 * (D + N) * k - 2 * N * Y) ≤
      2 * (D + N - 2) * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N * (K1 + N) := by
  have hT : 0 ≤ D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hwhi (by omega : (0:ℤ) ≤ 2 * N)
  have h2 := mul_nonneg hT (by omega : (0:ℤ) ≤ D + N - 2 - k)
  nlinarith

theorem L_s0_le_one (N D K1 k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hkL : k + 1 ≤ D + N) (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) :
    (D + N) * (2 * (D + N) * k - 2 * N * Y) ≤
      2 * (D + N - 1) * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N * (K1 + N) := by
  have hT : 0 ≤ D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hwhi (by omega : (0:ℤ) ≤ 2 * N)
  have h2 := mul_nonneg hT (by omega : (0:ℤ) ≤ D + N - 1 - k)
  nlinarith

/-- The cursor slope plus `L` (the slope after an east step) is bounded by the top of the strip. -/
theorem s0_add_L_le (N D K1 Lam k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D) (hk0 : 0 ≤ k)
    (hkL : k + 2 ≤ D + N) (hLam : Lam ≤ D - N) (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) :
    2 * (D + N) * k - 2 * N * Y + (D + N) ≤
      2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - Lam := by
  have hL : 0 < D + N := by omega
  have h := L_s0_le_two N D K1 k Y hN hND hkL hwhi
  have h1 : (D + N) * (2 * (D + N) * k - 2 * N * Y + (D + N)) ≤
      (D + N) * (2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - Lam) := by
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ D + N) (by omega : (0:ℤ) ≤ D - N - Lam),
      mul_nonneg (by omega : (0:ℤ) ≤ N) (by omega : (0:ℤ) ≤ D + N - K1 - N)]
  exact le_of_mul_le_mul_left h1 hL

/-- The cursor slope plus `C` (the slope after a north step) is bounded by the top of the strip. -/
theorem s0_add_C_le (N D K1 Lam k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D) (hk0 : 0 ≤ k)
    (hkL : k + 2 ≤ D + N) (hLam : Lam ≤ D - N) (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) :
    2 * (D + N) * k - 2 * N * Y + (D - N) ≤
      2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - Lam := by
  have hL : 0 < D + N := by omega
  have h := L_s0_le_two N D K1 k Y hN hND hkL hwhi
  have h1 : (D + N) * (2 * (D + N) * k - 2 * N * Y + (D - N)) ≤
      (D + N) * (2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - Lam) := by
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ D + N) (by omega : (0:ℤ) ≤ D - N - Lam),
      mul_nonneg (by omega : (0:ℤ) ≤ N) (by omega : (0:ℤ) ≤ D + N - K1 - N)]
  exact le_of_mul_le_mul_left h1 hL

/-- The cursor slope is bounded by the top of the strip (for the last block). -/
theorem s0_le_top (N D K1 k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D) (hk0 : 0 ≤ k)
    (hkL : k + 1 ≤ D + N) (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) :
    2 * (D + N) * k - 2 * N * Y ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) := by
  have hL : 0 < D + N := by omega
  have h := L_s0_le_one N D K1 k Y hN hND hkL hwhi
  have h1 : (D + N) * (2 * (D + N) * k - 2 * N * Y) ≤
      (D + N) * (2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N)) := by
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ N) (by omega : (0:ℤ) ≤ D + N - K1 - N)]
  exact le_of_mul_le_mul_left h1 hL


/-! ### The parity cases of `pB` -/

theorem pB_ev {N D K1 Lam x y : ℤ} (h : (x + y) % 2 = 0) :
    pB N D K1 Lam x y ↔
      ((2 * D - (D ^ 2 + 2 * D * N - N ^ 2) - (D - N) ≤ N * x - D * y ∧ N * x - D * y ≤ D - N) ∧
        (0 ≤ (D + N) * x + (D - N) * y ∧
          (D + N) * x + (D - N) * y ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N))) := by
  unfold pB pBts
  rw [if_pos h]

theorem pB_od {N D K1 Lam x y : ℤ} (h : ¬ (x + y) % 2 = 0) :
    pB N D K1 Lam x y ↔
      ((2 * D - (D ^ 2 + 2 * D * N - N ^ 2) - K1 ≤ N * x - D * y ∧ N * x - D * y ≤ K1) ∧
        (Lam ≤ (D + N) * x + (D - N) * y ∧
          (D + N) * x + (D - N) * y ≤ 2 * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - Lam)) := by
  unfold pB pBts
  rw [if_neg h]

/-- The slope of a cursor with a nonnegative cell below the odd count: `s ≥ C` on the north-east blocks. -/
theorem s_P4_ge (N D k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hk1 : 1 ≤ k) (hYk : Y ≤ k) (hY0 : 0 ≤ Y) :
    D - N ≤ (D + N) * (2 * k - Y - 1) + (D - N) * Y := by
  rcases eq_or_lt_of_le hY0 with h | h
  · subst h
    nlinarith
  · have h1 : 0 ≤ (D + N) * (2 * k - Y - 1) := by
      apply mul_nonneg <;> omega
    nlinarith

/-- The east block of type EE: the two east steps of the block are boundary edges. -/
theorem EE_block (N D K1 Lam k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D)
    (hK1lo : D - 2 * N ≤ K1) (hLam : Lam ≤ D - N) (hk0 : 0 ≤ k) (hYk : Y ≤ k)
    (hkL : k + 2 ≤ D + N) (hwlo : K1 - D < 2 * N * k - (D + N) * Y)
    (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) (hEE : 2 * N * k - (D + N) * Y + N ≤ K1) :
    pB N D K1 Lam (2 * k - Y) Y ∧ ¬ pB N D K1 Lam (2 * k - Y) (Y - 1) ∧
      pB N D K1 Lam (2 * k - Y + 1) Y ∧ ¬ pB N D K1 Lam (2 * k - Y + 1) (Y - 1) := by
  have hT : D ^ 2 + 2 * D * N - N ^ 2 ≥ D + 3 * N := by nlinarith
  have hT2 : D ^ 2 + 2 * D * N - N ^ 2 ≥ 2 * D := by nlinarith
  have hs0 := s0_nonneg N D k Y hN hk0 hYk hND
  have hs0top := s0_le_top N D K1 k Y hN hND hK1D hk0 (by omega) hwhi
  have hs1 := s0_add_L_le N D K1 Lam k Y hN hND hK1D hk0 hkL hLam hwhi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pB_ev (by omega)]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · rw [pB_od (by omega)]
    intro h
    obtain ⟨⟨_, h2⟩, _⟩ := h
    nlinarith
  · rw [pB_od (by omega)]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · rw [pB_ev (by omega)]
    intro h
    obtain ⟨⟨_, _⟩, _⟩ := h
    nlinarith

/-- The east block of type EN: the east step at the cursor and the north step after it. -/
theorem EN_block (N D K1 Lam k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D)
    (hK1lo : D - 2 * N ≤ K1) (hk0 : 0 ≤ k) (hYk : Y ≤ k)
    (hkL : k + 2 ≤ D + N) (_hwlo : K1 - D < 2 * N * k - (D + N) * Y)
    (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) (hEN1 : K1 - N < 2 * N * k - (D + N) * Y)
    (hEN2 : 2 * N * k - (D + N) * Y ≤ D - N) :
    pB N D K1 Lam (2 * k - Y) Y ∧ ¬ pB N D K1 Lam (2 * k - Y) (Y - 1) ∧
      ¬ pB N D K1 Lam (2 * k - Y + 1) Y := by
  have hT : D ^ 2 + 2 * D * N - N ^ 2 ≥ D + 3 * N := by nlinarith
  have hs0 := s0_nonneg N D k Y hN hk0 hYk hND
  have hs0top := s0_le_top N D K1 k Y hN hND hK1D hk0 (by omega) hwhi
  refine ⟨?_, ?_, ?_⟩
  · rw [pB_ev (by omega)]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · rw [pB_od (by omega)]
    intro h
    obtain ⟨⟨_, h2⟩, _⟩ := h
    nlinarith [h2]
  · rw [pB_od (by omega)]
    intro h
    obtain ⟨⟨h1, _⟩, _⟩ := h
    nlinarith

/-- The north-east block: the north step at the cursor and the east step after it. -/
theorem NE_block (N D K1 Lam k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D) (hK1N : N ≤ K1)
    (hLam : Lam ≤ D - N) (hk0 : 0 ≤ k) (hk1 : 1 ≤ k) (hY0 : 0 ≤ Y) (hYk : Y ≤ k)
    (hkL : k + 2 ≤ D + N) (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N)
    (hNE : D - N < 2 * N * k - (D + N) * Y) :
    ¬ pB N D K1 Lam (2 * k - Y) Y ∧ pB N D K1 Lam (2 * k - Y - 1) Y ∧
      pB N D K1 Lam (2 * k - Y) (Y + 1) := by
  have hT : D ^ 2 + 2 * D * N - N ^ 2 ≥ D + 3 * N := by nlinarith
  have hT2 : D ^ 2 + 2 * D * N - N ^ 2 ≥ 2 * D := by nlinarith
  have hs0 := s0_nonneg N D k Y hN hk0 hYk hND
  have hs0top := s0_le_top N D K1 k Y hN hND hK1D hk0 (by omega) hwhi
  have hs5 := s0_add_C_le N D K1 Lam k Y hN hND hK1D hk0 hkL hLam hwhi
  have hs4 := s_P4_ge N D k Y hN hND hk1 hYk hY0
  refine ⟨?_, ?_, ?_⟩
  · rw [pB_ev (by omega)]
    intro h
    obtain ⟨⟨_, h2⟩, _⟩ := h
    nlinarith
  · rw [pB_od (by omega)]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · rw [pB_od (by omega)]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith

/-- The last east step of the walk (block `L − 1`): its cell passes the tests. -/
theorem Last_block (N D K1 Lam k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D)
    (hK1lo : D - 2 * N ≤ K1) (hk0 : 0 ≤ k) (hYk : Y ≤ k) (hkL : k + 1 ≤ D + N)
    (hwlo : K1 - D < 2 * N * k - (D + N) * Y)
    (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) (he : 2 * N * k - (D + N) * Y ≤ D - N) :
    pB N D K1 Lam (2 * k - Y) Y ∧ ¬ pB N D K1 Lam (2 * k - Y) (Y - 1) := by
  have hT : D ^ 2 + 2 * D * N - N ^ 2 ≥ D + 3 * N := by nlinarith
  have hs0 := s0_nonneg N D k Y hN hk0 hYk hND
  have hs0top := s0_le_top N D K1 k Y hN hND hK1D hk0 hkL hwhi
  refine ⟨?_, ?_⟩
  · rw [pB_ev (by omega)]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · rw [pB_od (by omega)]
    intro h
    obtain ⟨⟨_, h2⟩, _⟩ := h
    nlinarith

end FLatticePaper.Tiles.SubBlockOdd
