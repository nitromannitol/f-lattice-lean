import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.TwosPieces
import FLatticePaper.Plane.Induction.TwosLaplacianTile

/-! # The W1 forcing at the twos children (task 72, W1 base at `2^(k+1)`, lead's (2))

The twos child of `2^(k+1)` is `(2k+3)/(2k+5)`, with `a = 2k+4` (`twos_child_num_den`). Its strict interior is the closed
parallelogram below, in the atoms `u = a x + y` and `t = (a−1) x − (a+1) y`. -/

namespace FLatticePaper.W1Twos

open FLatticePaper FLatticePaper.W1

/-- The strict interior of the twos child `(a−1)/(a+1)`: the band `a ≤ a x + y ≤ a² + 2a − 2`, with the parity-resolved range of
`t = (a−1) x − (a+1) y`. -/
theorem strictInterior_twos_iff {n d a : ℤ} (hn : n = a - 1) (hd : d = a + 1) (x y : ℤ) :
    StrictInterior n d (x, y) ↔
      (a ≤ a * x + y ∧ a * x + y ≤ a * a + 2 * a - 2) ∧
      ((x + y) % 2 = 0 → 2 * a - 1 - (2 * (a * a) + 4 * a - 2) ≤ (a - 1) * x - (a + 1) * y ∧
        (a - 1) * x - (a + 1) * y ≤ 1) ∧
      ((x + y) % 2 ≠ 0 → a + 2 - (2 * (a * a) + 4 * a - 2) ≤ (a - 1) * x - (a + 1) * y ∧
        (a - 1) * x - (a + 1) * y ≤ a - 2) := by
  have es : (d + n) * x + (d - n) * y = 2 * (a * x + y) := by subst hn hd; ring
  have et : n * x - d * y = (a - 1) * x - (a + 1) * y := by subst hn hd; ring
  have eT : d ^ 2 + 2 * d * n - n ^ 2 = 2 * (a * a) + 4 * a - 2 := by subst hn hd; ring
  unfold StrictInterior w1b w1T w1t w1a w1s w1h w1c
  dsimp only
  rw [es, et, eT]
  split_ifs with he
  · have he' : (x + y) % 2 = 0 := he
    omega
  · have he' : ¬ (x + y) % 2 = 0 := he
    omega


/-! ## The native box and the Laplacian of the twos field on the strict interior. -/

open FLatticePaper.TwosEPolicy FLatticePaper.Induction FLatticePaper.Construction Farey
/-- The native box from the uniform bounds of the twos strict interior: `D x = (a+1)u + t`, `D y = (a−1)u − a t`,
`D (y − x) = −2u − (a+1)t`, with `D = a² + 2a − 1`, `u = a x + y`, `t = (a−1) x − (a+1) y`. -/
theorem nativeT_of_bounds {a x y : ℤ} (ha : 4 ≤ a)
    (hu1 : a ≤ a * x + y) (hu2 : a * x + y ≤ a * a + 2 * a - 2)
    (ht1 : a + 2 - (2 * (a * a) + 4 * a - 2) ≤ (a - 1) * x - (a + 1) * y)
    (ht2 : (a - 1) * x - (a + 1) * y ≤ a - 2) :
    NativeT a x y := by
  obtain ⟨u, hu⟩ : ∃ u, u = a * x + y := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (a - 1) * x - (a + 1) * y := ⟨_, rfl⟩
  rw [← hu] at hu1 hu2
  rw [← ht] at ht1 ht2
  have hD : (0 : ℤ) < a * a + 2 * a - 1 := by nlinarith
  have hDx : (a * a + 2 * a - 1) * x = (a + 1) * u + t := by rw [hu, ht]; ring
  have hDy : (a * a + 2 * a - 1) * y = (a - 1) * u - a * t := by rw [hu, ht]; ring
  have hDyx : (a * a + 2 * a - 1) * (y - x) = -2 * u - (a + 1) * t := by rw [hu, ht]; ring
  have hx0 : 0 ≤ x := by
    by_contra h
    have h1 : x ≤ -1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left h1 hD.le]
  have hxa : x ≤ a := by
    by_contra h
    have h1 : a + 1 ≤ x := by omega
    nlinarith [mul_le_mul_of_nonneg_left h1 hD.le]
  have hy0 : 0 ≤ y := by
    by_contra h
    have h1 : y ≤ -1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left h1 hD.le, mul_nonneg (show (0 : ℤ) ≤ a - 1 by omega) (sub_nonneg.mpr hu1),
      mul_nonneg (show (0 : ℤ) ≤ a by omega) (sub_nonneg.mpr ht2)]
  have hy3 : y ≤ 3 * a - 2 := by
    by_contra h
    have h1 : 3 * a - 1 ≤ y := by omega
    nlinarith [mul_le_mul_of_nonneg_left h1 hD.le, mul_nonneg (show (0 : ℤ) ≤ a - 1 by omega) (sub_nonneg.mpr hu2),
      mul_nonneg (show (0 : ℤ) ≤ a by omega) (sub_nonneg.mpr ht1)]
  have hyx1 : -2 ≤ y - x := by
    by_contra h
    have h1 : y - x ≤ -3 := by omega
    nlinarith [mul_le_mul_of_nonneg_left h1 hD.le, mul_nonneg (show (0 : ℤ) ≤ 2 by norm_num) (sub_nonneg.mpr hu2),
      mul_nonneg (show (0 : ℤ) ≤ a + 1 by omega) (sub_nonneg.mpr ht2)]
  have hyx2 : y - x ≤ 2 * a := by
    by_contra h
    have h1 : 2 * a + 1 ≤ y - x := by omega
    nlinarith [mul_le_mul_of_nonneg_left h1 hD.le, mul_nonneg (show (0 : ℤ) ≤ 2 by norm_num) (sub_nonneg.mpr hu1),
      mul_nonneg (show (0 : ℤ) ≤ a + 1 by omega) (sub_nonneg.mpr ht1)]
  unfold NativeT
  refine Or.inl ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, ?_⟩
  rintro (⟨e, -⟩ | ⟨e, -⟩) <;> omega


theorem native_of_si_twos {k : ℕ} {x y : ℤ} (hS : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y)) :
    NativeT (2 * (k : ℤ) + 4) x y := by
  obtain ⟨hu, hE, hO⟩ := (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x y).1 hS
  by_cases hp : (x + y) % 2 = 0
  · obtain ⟨h1, h2⟩ := hE hp
    exact nativeT_of_bounds (by omega) hu.1 hu.2 (by linarith) (by linarith)
  · obtain ⟨h1, h2⟩ := hO hp
    exact nativeT_of_bounds (by omega) hu.1 hu.2 h1 h2

/-- The native black/white rule of the twos standard field (`laplacian_twos_native`), with the extension obtained inside. -/
theorem laplacian_twos_std_native {k : ℕ} {x y : ℤ} (hu : NativeT (2 * (k : ℤ) + 4) x y) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) =
      if EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) (x, y)) then
        (if LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) (x, y))
          then -1 else 0)
      else
        (if LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) (x, y))
          then 0 else -1) := by
  have hvalid : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) := ⟨by omega, by omega⟩
  obtain ⟨S, hagree, hperiod, -⟩ := ladderOdd_exists_extension hvalid
  exact laplacian_twos_native k hagree hperiod hu

end FLatticePaper.W1Twos
