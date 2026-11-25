import FLatticePaper.Tiles.CellFourEven
import FLatticePaper.Tiles.SubBlockOdd
import FLatticePaper.Tiles.SubCriteria

/-! Task Q25 (sub), the even bottom: the four-test bounds and the block criteria of an even fraction `(N, D)`, `N + D` even.

The bounds of the lower-left corner `(x, y)` are `pBE`: the grade `t = N x − D y` and the slope `s = (D + N) x + (D − N) y` lie in the
even strip (for even corners: `2D − T − (D−N) ≤ t ≤ D − N`, `0 ≤ s ≤ T − 2(D − N)`) or the odd strip (`2D − T − K1 ≤ t ≤ K1`,
`Lam ≤ s ≤ T − 2(D − N) − Lam`), with `T = D² + 2DN − N²`. The top of the slope strip is `T − 2(D−N)` (the odd fraction has `2T`).
The block criteria are the same as the odd ones (`SubBlockOdd`), with this top. -/

namespace FLatticePaper.Tiles.SubBlockEven

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.CellFourTests
  FLatticePaper.Tiles.SiteInduction

/-- The four-test bounds of a corner with grade `t` and slope `s`, at the parity `ev` (even corners: `ev` true). -/
def pBEts (N D K1 Lam : ℤ) (ev : Prop) [Decidable ev] (t s : ℤ) : Prop :=
  if ev then
    (2 * D - (D ^ 2 + 2 * D * N - N ^ 2) - (D - N) ≤ t ∧ t ≤ D - N) ∧
      (0 ≤ s ∧ s ≤ (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N))
  else
    (2 * D - (D ^ 2 + 2 * D * N - N ^ 2) - K1 ≤ t ∧ t ≤ K1) ∧
      (Lam ≤ s ∧ s ≤ (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - Lam)

/-- The four-test bounds of the lower-left corner `(x, y)` of the even fraction `(N, D)`. -/
def pBE (N D K1 Lam x y : ℤ) : Prop :=
  pBEts N D K1 Lam ((x + y) % 2 = 0) (N * x - D * y) ((D + N) * x + (D - N) * y)

theorem pBE_ev {N D K1 Lam x y : ℤ} (h : (x + y) % 2 = 0) :
    pBE N D K1 Lam x y ↔
      ((2 * D - (D ^ 2 + 2 * D * N - N ^ 2) - (D - N) ≤ N * x - D * y ∧ N * x - D * y ≤ D - N) ∧
        (0 ≤ (D + N) * x + (D - N) * y ∧
          (D + N) * x + (D - N) * y ≤ (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N))) := by
  unfold pBE pBEts
  rw [if_pos h]

theorem pBE_od {N D K1 Lam x y : ℤ} (h : ¬ (x + y) % 2 = 0) :
    pBE N D K1 Lam x y ↔
      ((2 * D - (D ^ 2 + 2 * D * N - N ^ 2) - K1 ≤ N * x - D * y ∧ N * x - D * y ≤ K1) ∧
        (Lam ≤ (D + N) * x + (D - N) * y ∧
          (D + N) * x + (D - N) * y ≤ (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - Lam)) := by
  unfold pBE pBEts
  rw [if_neg h]

/-- The even four-test bounds are the membership of the cell with lower-left corner `(x, y)` in the even fraction's tile. -/
theorem cellCorners_subset_iff_bounds_even (f : Fraction) (hev : (f.num + f.den) % 2 = 0) (hpos : 0 < f.num)
    (hlt : f.num < f.den) (P : Finset GInt) (hP : ∀ x : GInt, x ∈ P ↔ InH f x) (z : GInt) :
    cellCorners z ⊆ P ↔
      ((2 * f.den - tOf f - cellK f (decide ((z.1 + z.2) % 2 = 0)) ≤ tCo f z ∧
          tCo f z ≤ cellK f (decide ((z.1 + z.2) % 2 = 0))) ∧
        (lOf f (decide ((z.1 + z.2) % 2 = 0)) ≤ sCo f z ∧
          sCo f z ≤ tOf f - 2 * (f.den - f.num) - lOf f (decide ((z.1 + z.2) % 2 = 0)))) := by
  rw [← CellFourEven.cell_four_tests_even f hev hpos hlt z]
  have e1 : z + gOne = (z.1 + 1, z.2) := Prod.ext (by simp [gOne]) (by simp [gOne])
  have e2 : z + gI = (z.1, z.2 + 1) := Prod.ext (by simp [gI]) (by simp [gI])
  have e3 : z + (gOne + gI) = (z.1 + 1, z.2 + 1) := Prod.ext (by simp [gOne, gI]) (by simp [gOne, gI])
  simp only [cellCorners, Finset.insert_subset_iff, Finset.singleton_subset_iff, hP, e1, e2, e3]

/-- The bounds `pBE` are the four-test bounds of the lower-left corner, for the even fraction `f`. -/
theorem cell_iff_pBE (f : Fraction) (hev : (f.num + f.den) % 2 = 0) (hpos : 0 < f.num)
    (hlt : f.num < f.den) (P : Finset GInt) (hP : ∀ x : GInt, x ∈ P ↔ InH f x) (x y : ℤ) :
    cellCorners (x, y) ⊆ P ↔
      pBE f.num f.den (max (f.den - 2 * f.num) f.num) (min (f.den - f.num) (3 * f.num - f.den)) x y := by
  rw [cellCorners_subset_iff_bounds_even f hev hpos hlt P hP (x, y)]
  unfold pBE pBEts
  by_cases h : (x + y) % 2 = 0
  · have hk : cellK f (decide (((x, y).1 + (x, y).2) % 2 = 0)) = f.den - f.num := by
      simp [cellK, h]
    have hl : lOf f (decide (((x, y).1 + (x, y).2) % 2 = 0)) = 0 := by
      simp [lOf, h]
    rw [hk, hl]
    simp [h, tOf, tCo, sCo]
  · have hk : cellK f (decide (((x, y).1 + (x, y).2) % 2 = 0)) =
        max (f.den - 2 * f.num) f.num := by
      simp [cellK, h]
    have hl : lOf f (decide (((x, y).1 + (x, y).2) % 2 = 0)) =
        min (f.den - f.num) (3 * f.num - f.den) := by
      simp [lOf, h]
    rw [hk, hl]
    simp [h, tOf, tCo, sCo]

/-! ### The slope of the cursor, with the even top `T − 2(D − N)` -/

theorem L_s0_le_two_E (N D K1 k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hkM : 2 * k + 4 ≤ D + N)
    (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) :
    (D + N) * (2 * (D + N) * k - 2 * N * Y) ≤
      (D + N - 4) * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N * (K1 + N) := by
  have hT : 0 ≤ D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hwhi (by omega : (0:ℤ) ≤ 2 * N)
  have h2 := mul_nonneg hT (by omega : (0:ℤ) ≤ D + N - 4 - 2 * k)
  nlinarith

theorem L_s0_le_one_E (N D K1 k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hkM : 2 * k + 2 ≤ D + N)
    (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) :
    (D + N) * (2 * (D + N) * k - 2 * N * Y) ≤
      (D + N - 2) * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N * (K1 + N) := by
  have hT : 0 ≤ D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hwhi (by omega : (0:ℤ) ≤ 2 * N)
  have h2 := mul_nonneg hT (by omega : (0:ℤ) ≤ D + N - 2 - 2 * k)
  nlinarith

theorem s0_add_L_le_E (N D K1 Lam k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D) (hk0 : 0 ≤ k)
    (hkM : 2 * k + 4 ≤ D + N) (hLam : Lam ≤ D - N) (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) :
    2 * (D + N) * k - 2 * N * Y + (D + N) ≤
      (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - Lam := by
  have hL : 0 < D + N := by omega
  have h := L_s0_le_two_E N D K1 k Y hN hND hkM hwhi
  have h1 : (D + N) * (2 * (D + N) * k - 2 * N * Y + (D + N)) ≤
      (D + N) * ((D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - Lam) := by
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ D + N) (by omega : (0:ℤ) ≤ D - N - Lam),
      mul_nonneg (by omega : (0:ℤ) ≤ N) (by omega : (0:ℤ) ≤ D + N - K1 - N)]
  exact le_of_mul_le_mul_left h1 hL

theorem s0_add_C_le_E (N D K1 Lam k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D) (hk0 : 0 ≤ k)
    (hkM : 2 * k + 4 ≤ D + N) (hLam : Lam ≤ D - N) (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) :
    2 * (D + N) * k - 2 * N * Y + (D - N) ≤
      (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - Lam := by
  have hL : 0 < D + N := by omega
  have h := L_s0_le_two_E N D K1 k Y hN hND hkM hwhi
  have h1 : (D + N) * (2 * (D + N) * k - 2 * N * Y + (D - N)) ≤
      (D + N) * ((D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - Lam) := by
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ D + N) (by omega : (0:ℤ) ≤ D - N - Lam),
      mul_nonneg (by omega : (0:ℤ) ≤ N) (by omega : (0:ℤ) ≤ D + N - K1 - N)]
  exact le_of_mul_le_mul_left h1 hL

theorem s0_le_top_E (N D K1 k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D) (hk0 : 0 ≤ k)
    (hkM : 2 * k + 2 ≤ D + N) (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) :
    2 * (D + N) * k - 2 * N * Y ≤ (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) := by
  have hL : 0 < D + N := by omega
  have h := L_s0_le_one_E N D K1 k Y hN hND hkM hwhi
  have h1 : (D + N) * (2 * (D + N) * k - 2 * N * Y) ≤
      (D + N) * ((D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N)) := by
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ N) (by omega : (0:ℤ) ≤ D + N - K1 - N)]
  exact le_of_mul_le_mul_left h1 hL

/-! ### The block criteria of the even fraction (the same blocks as the odd ones) -/

/-- The east block of type EE: the two east steps of the block are boundary edges. -/
theorem EE_blockE (N D K1 Lam k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D)
    (hK1lo : D - 2 * N ≤ K1) (hLam : Lam ≤ D - N) (hk0 : 0 ≤ k) (hYk : Y ≤ k)
    (hkL : 2 * k + 4 ≤ D + N) (hwlo : K1 - D < 2 * N * k - (D + N) * Y)
    (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) (hEE : 2 * N * k - (D + N) * Y + N ≤ K1) :
    pBE N D K1 Lam (2 * k - Y) Y ∧ ¬ pBE N D K1 Lam (2 * k - Y) (Y - 1) ∧
      pBE N D K1 Lam (2 * k - Y + 1) Y ∧ ¬ pBE N D K1 Lam (2 * k - Y + 1) (Y - 1) := by
  have hT : D ^ 2 + 2 * D * N - N ^ 2 ≥ D + 3 * N := by nlinarith
  have hT2 : D ^ 2 + 2 * D * N - N ^ 2 ≥ 2 * D := by nlinarith
  have hs0 := SubBlockOdd.s0_nonneg N D k Y hN hk0 hYk hND
  have hs0top := s0_le_top_E N D K1 k Y hN hND hK1D hk0 (by omega) hwhi
  have hs1 := s0_add_L_le_E N D K1 Lam k Y hN hND hK1D hk0 hkL hLam hwhi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pBE_ev (by omega)]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · rw [pBE_od (by omega)]
    intro h
    obtain ⟨⟨_, h2⟩, _⟩ := h
    nlinarith
  · rw [pBE_od (by omega)]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · rw [pBE_ev (by omega)]
    intro h
    obtain ⟨⟨_, _⟩, _⟩ := h
    nlinarith

/-- The east block of type EN: the east step at the cursor and the north step after it. -/
theorem EN_blockE (N D K1 Lam k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D)
    (hK1lo : D - 2 * N ≤ K1) (hk0 : 0 ≤ k) (hYk : Y ≤ k)
    (hkL : 2 * k + 4 ≤ D + N) (_hwlo : K1 - D < 2 * N * k - (D + N) * Y)
    (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) (hEN1 : K1 - N < 2 * N * k - (D + N) * Y)
    (hEN2 : 2 * N * k - (D + N) * Y ≤ D - N) :
    pBE N D K1 Lam (2 * k - Y) Y ∧ ¬ pBE N D K1 Lam (2 * k - Y) (Y - 1) ∧
      ¬ pBE N D K1 Lam (2 * k - Y + 1) Y := by
  have hT : D ^ 2 + 2 * D * N - N ^ 2 ≥ D + 3 * N := by nlinarith
  have hs0 := SubBlockOdd.s0_nonneg N D k Y hN hk0 hYk hND
  have hs0top := s0_le_top_E N D K1 k Y hN hND hK1D hk0 (by omega) hwhi
  refine ⟨?_, ?_, ?_⟩
  · rw [pBE_ev (by omega)]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · rw [pBE_od (by omega)]
    intro h
    obtain ⟨⟨_, h2⟩, _⟩ := h
    nlinarith [h2]
  · rw [pBE_od (by omega)]
    intro h
    obtain ⟨⟨h1, _⟩, _⟩ := h
    nlinarith

/-- The north-east block: the north step at the cursor and the east step after it. -/
theorem NE_blockE (N D K1 Lam k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D) (hK1N : N ≤ K1)
    (hLam : Lam ≤ D - N) (hk0 : 0 ≤ k) (hk1 : 1 ≤ k) (hY0 : 0 ≤ Y) (hYk : Y ≤ k)
    (hkL : 2 * k + 4 ≤ D + N) (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N)
    (hNE : D - N < 2 * N * k - (D + N) * Y) :
    ¬ pBE N D K1 Lam (2 * k - Y) Y ∧ pBE N D K1 Lam (2 * k - Y - 1) Y ∧
      pBE N D K1 Lam (2 * k - Y) (Y + 1) := by
  have hT : D ^ 2 + 2 * D * N - N ^ 2 ≥ D + 3 * N := by nlinarith
  have hT2 : D ^ 2 + 2 * D * N - N ^ 2 ≥ 2 * D := by nlinarith
  have hs0 := SubBlockOdd.s0_nonneg N D k Y hN hk0 hYk hND
  have hs0top := s0_le_top_E N D K1 k Y hN hND hK1D hk0 (by omega) hwhi
  have hs5 := s0_add_C_le_E N D K1 Lam k Y hN hND hK1D hk0 hkL hLam hwhi
  have hs4 := SubBlockOdd.s_P4_ge N D k Y hN hND hk1 hYk hY0
  refine ⟨?_, ?_, ?_⟩
  · rw [pBE_ev (by omega)]
    intro h
    obtain ⟨⟨_, h2⟩, _⟩ := h
    nlinarith
  · rw [pBE_od (by omega)]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · rw [pBE_od (by omega)]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith

/-- The last east step of the walk (block `L − 1`): its cell passes the tests. -/
theorem Last_blockE (N D K1 Lam k Y : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hK1D : K1 ≤ D)
    (hK1lo : D - 2 * N ≤ K1) (hk0 : 0 ≤ k) (hYk : Y ≤ k) (hkL : 2 * k + 2 ≤ D + N)
    (hwlo : K1 - D < 2 * N * k - (D + N) * Y)
    (hwhi : 2 * N * k - (D + N) * Y ≤ K1 + N) (he : 2 * N * k - (D + N) * Y ≤ D - N) :
    pBE N D K1 Lam (2 * k - Y) Y ∧ ¬ pBE N D K1 Lam (2 * k - Y) (Y - 1) := by
  have hT : D ^ 2 + 2 * D * N - N ^ 2 ≥ D + 3 * N := by nlinarith
  have hs0 := SubBlockOdd.s0_nonneg N D k Y hN hk0 hYk hND
  have hs0top := s0_le_top_E N D K1 k Y hN hND hK1D hk0 (by omega) hwhi
  refine ⟨?_, ?_⟩
  · rw [pBE_ev (by omega)]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · rw [pBE_od (by omega)]
    intro h
    obtain ⟨⟨_, h2⟩, _⟩ := h
    nlinarith

end FLatticePaper.Tiles.SubBlockEven
