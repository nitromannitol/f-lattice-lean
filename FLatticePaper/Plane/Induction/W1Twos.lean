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


/-! ## The classification of the twos strict interior (lead (C)): the whites are the classes `E`, `W` (even) and `L`, `U` (odd). -/

open FLatticePaper.Construction FLatticePaper.Induction FLatticePaper.TwosEPolicy Farey
/-- The linear bounds of the strict interior (both parities): `0 ≤ x ≤ a`, `0 ≤ y ≤ 3a−2`, `−2 ≤ y−x ≤ 2a`. -/
theorem si_linear_bounds {a x y : ℤ} (ha : 4 ≤ a)
    (hu1 : a ≤ a * x + y) (hu2 : a * x + y ≤ a * a + 2 * a - 2)
    (ht1 : a + 2 - (2 * (a * a) + 4 * a - 2) ≤ (a - 1) * x - (a + 1) * y)
    (ht2 : (a - 1) * x - (a + 1) * y ≤ a - 2) :
    0 ≤ x ∧ x ≤ a ∧ 0 ≤ y ∧ y ≤ 3 * a - 2 ∧ -2 ≤ y - x ∧ y - x ≤ 2 * a := by
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
  exact ⟨hx0, hxa, hy0, hy3, hyx1, hyx2⟩

/-- The class `E`: even, `h = a - 2`, `2 ≤ x ≤ a`. -/
def TwosClE (a x y : ℤ) : Prop := (x + y) % 2 = 0 ∧ y - x = a - 2 ∧ 2 ≤ x ∧ x ≤ a
/-- The class `W`: even, `h = a`, `0 ≤ x ≤ a - 2`. -/
def TwosClW (a x y : ℤ) : Prop := (x + y) % 2 = 0 ∧ y - x = a ∧ 0 ≤ x ∧ x ≤ a - 2
/-- The class `L` with arrow `S`: odd, `-1 ≤ h ≤ a - 3`, `1 ≤ x ≤ a`, `y < a - 1`, not `(x, h) = (1, -1)`. -/
def TwosClLS (a x y : ℤ) : Prop :=
  (x + y) % 2 ≠ 0 ∧ -1 ≤ y - x ∧ y - x ≤ a - 3 ∧ 1 ≤ x ∧ x ≤ a ∧ y < a - 1 ∧ ¬ (x = 1 ∧ y - x = -1)
/-- The class `L` with arrow `N`: as `TwosClLS` with `a - 1 < y`. -/
def TwosClLN (a x y : ℤ) : Prop :=
  (x + y) % 2 ≠ 0 ∧ -1 ≤ y - x ∧ y - x ≤ a - 3 ∧ 1 ≤ x ∧ x ≤ a ∧ a - 1 < y ∧ ¬ (x = 1 ∧ y - x = -1)
/-- The class `U` with arrow `S`: odd, `a + 1 ≤ h ≤ 2a - 1`, `0 ≤ x ≤ a - 1`, `y < 2a - 1`, not `(x, h) = (a-1, 2a-1)`. -/
def TwosClUS (a x y : ℤ) : Prop :=
  (x + y) % 2 ≠ 0 ∧ a + 1 ≤ y - x ∧ y - x ≤ 2 * a - 1 ∧ 0 ≤ x ∧ x ≤ a - 1 ∧ y < 2 * a - 1 ∧
    ¬ (x = a - 1 ∧ y - x = 2 * a - 1)
/-- The class `U` with arrow `N`: as `TwosClUS` with `2a - 1 < y`. -/
def TwosClUN (a x y : ℤ) : Prop :=
  (x + y) % 2 ≠ 0 ∧ a + 1 ≤ y - x ∧ y - x ≤ 2 * a - 1 ∧ 0 ≤ x ∧ x ≤ a - 1 ∧ 2 * a - 1 < y ∧
    ¬ (x = a - 1 ∧ y - x = 2 * a - 1)

/-- The even whites of the strict interior: the ladder predicate at the rotated point is the class `E` or `W`. -/
theorem ladder_oddodd_even {a x y : ℤ} (ha : 4 ≤ a) (ha2 : a % 2 = 0)
    (hu1 : a ≤ a * x + y) (hu2 : a * x + y ≤ a * a + 2 * a - 2)
    (ht1 : 2 * a - 1 - (2 * (a * a) + 4 * a - 2) ≤ (a - 1) * x - (a + 1) * y)
    (ht2 : (a - 1) * x - (a + 1) * y ≤ 1) (hp : (x + y) % 2 = 0) :
    LadderOddOddWhite a (2 * a - y, x + 1) ↔ (TwosClE a x y ∨ TwosClW a x y) := by
  obtain ⟨hx0, hxa, hy0, hy3, hyx1, hyx2⟩ :=
    si_linear_bounds ha hu1 hu2 (by linarith) (by linarith)
  unfold LadderOddOddWhite LadderOddLowerBoundary reflectLadderOdd
  dsimp only
  simp only [Prod.fst_sub, Prod.snd_sub]
  constructor
  · rintro ((⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) | (⟨h4, h5, h6⟩ | ⟨h4, h5, h6⟩ | ⟨h4, h5, h6⟩) |
      ⟨h7, h8, h9⟩ | ⟨h10, h11, h12⟩ | ⟨h13, h14⟩ | ⟨h15, h16⟩)
    · -- L1: y = x + 2a, which forces `t ≤ -2a^2 - 2a` against the lower bound
      exfalso
      obtain rfl : y = x + 2 * a := by omega
      nlinarith
    · exfalso
      omega
    · -- L3: x = 0 and y = a: the class W
      right
      obtain rfl : x = 0 := by omega
      have hya : y = a := by linarith
      exact ⟨by omega, by omega, by omega, by omega⟩
    · -- R1: x = y + 2 with y ≤ a - 3, against the upper bound of t
      exfalso
      obtain rfl : x = y + 2 := by omega
      nlinarith
    · exfalso
      omega
    · -- R3: x = a and y = 2a - 2: the class E
      left
      obtain rfl : x = a := by omega
      exact ⟨by omega, by omega, by omega, by omega⟩
    · -- A: y - x = a and 0 ≤ x ≤ a - 2: the class W
      right
      exact ⟨by omega, by omega, by omega, by omega⟩
    · -- B: y - x = a - 2 and 2 ≤ x ≤ a: the class E
      left
      exact ⟨by omega, by omega, by omega, by omega⟩
    · -- C: y = 2a and x = 0 against the lower bound of t
      exfalso
      obtain rfl : y = 2 * a := by omega
      obtain rfl : x = 0 := by omega
      nlinarith
    · -- D: y = a - 2 and x = a: t = 2 against the upper bound
      exfalso
      obtain rfl : y = a - 2 := by omega
      obtain rfl : x = a := by omega
      nlinarith
  · rintro (⟨-, h1, h2, h3⟩ | ⟨-, h1, h2, h3⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))

/-- The odd whites of the strict interior: the ladder predicate at the rotated point is one of the four odd classes. -/
theorem ladder_evenblack_odd {a x y : ℤ} (ha : 4 ≤ a) (ha2 : a % 2 = 0)
    (hu1 : a ≤ a * x + y) (hu2 : a * x + y ≤ a * a + 2 * a - 2)
    (ht1 : a + 2 - (2 * (a * a) + 4 * a - 2) ≤ (a - 1) * x - (a + 1) * y)
    (ht2 : (a - 1) * x - (a + 1) * y ≤ a - 2) (hp : ¬ (x + y) % 2 = 0) :
    ¬ LadderOddEvenBlack a (2 * a - y, x + 1) ↔
      (TwosClLS a x y ∨ TwosClLN a x y ∨ TwosClUS a x y ∨ TwosClUN a x y) := by
  obtain ⟨hx0, hxa, hy0, hy3, hyx1, hyx2⟩ := si_linear_bounds ha hu1 hu2 ht1 ht2
  unfold LadderOddEvenBlack
  dsimp only
  constructor
  · intro hb
    have n1 : ¬ (2 * a - y = 1 ∧ 1 ≤ x + 1 ∧ x + 1 ≤ a - 1) := fun h => hb (Or.inl h)
    have n2 : ¬ (2 * a - y = a + 1 ∧ 3 ≤ x + 1 ∧ x + 1 ≤ a + 1) := fun h => hb (Or.inr (Or.inl h))
    have n3 : ¬ (2 * a - y + (x + 1) = a + 2 ∧ 2 ≤ x + 1 ∧ x + 1 ≤ a) := fun h => hb (Or.inr (Or.inr h))
    rcases (show x = 0 ∨ x = a ∨ (1 ≤ x ∧ x ≤ a - 1) by omega) with hx | hx | ⟨hx1, hx2⟩
    · -- x = 0: the U class (the odd y lies in [a+1, 2a-1])
      obtain rfl := hx
      rcases lt_trichotomy y (2 * a - 1) with h | h | h
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))
      · exact absurd (n1 ⟨by omega, by omega, by omega⟩) id
      · exfalso
        omega
    · -- x = a: the L class (y = a + h with h odd in [-1, a-3])
      subst x
      have hyl : y ≤ 2 * a - 2 := by nlinarith
      by_cases hy : y < a - 1
      · exact Or.inl ⟨by omega, by omega, by omega, by omega, by omega, hy, by omega⟩
      · exact Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    · -- 1 ≤ x ≤ a - 1: the L class for h ≤ a-3 and the U class for h ≥ a+1
      by_cases hL : y - x ≤ a - 3
      · by_cases hy : y < a - 1
        · refine Or.inl ⟨by omega, by omega, by omega, by omega, by omega, hy, ?_⟩
          rintro ⟨e1, e2⟩
          subst e1
          nlinarith
        · refine Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
      · have hU : a + 1 ≤ y - x := by omega
        by_cases hy : y < 2 * a - 1
        · refine Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, hy, ?_⟩))
          rintro ⟨e1, e2⟩
          subst e1
          nlinarith
        · refine Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩))
          rintro ⟨e1, e2⟩
          subst e1
          nlinarith
  · intro h hb
    rcases hb with ⟨e1, e2, e3⟩ | ⟨e4, e5, e6⟩ | ⟨e7, e8, e9⟩
    · rcases h with ⟨-, f1, f2, f3, f4, f5, f6⟩ | ⟨-, f1, f2, f3, f4, f5, f6⟩ | ⟨-, f1, f2, f3, f4, f5, f6⟩ |
        ⟨-, f1, f2, f3, f4, f5, f6⟩ <;> omega
    · rcases h with ⟨-, f1, f2, f3, f4, f5, f6⟩ | ⟨-, f1, f2, f3, f4, f5, f6⟩ | ⟨-, f1, f2, f3, f4, f5, f6⟩ |
        ⟨-, f1, f2, f3, f4, f5, f6⟩ <;> omega
    · rcases h with ⟨-, f1, f2, f3, f4, f5, f6⟩ | ⟨-, f1, f2, f3, f4, f5, f6⟩ | ⟨-, f1, f2, f3, f4, f5, f6⟩ |
        ⟨-, f1, f2, f3, f4, f5, f6⟩ <;> omega

/-- The Laplacian of the twos field at an even strict-interior site vanishes iff the site is in the classes `E` or `W`. -/
theorem twos_lap_even_iff {k : ℕ} {x y : ℤ}
    (hS : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y)) (hp : (x + y) % 2 = 0) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = 0 ↔
      (TwosClE (2 * (k : ℤ) + 4) x y ∨ TwosClW (2 * (k : ℤ) + 4) x y) := by
  obtain ⟨⟨hu1, hu2⟩, hE, -⟩ := (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x y).1 hS
  obtain ⟨h1, h2⟩ := hE hp
  have hN := native_of_si_twos hS
  rw [laplacian_twos_std_native hN, quarterTurn_offset_apply]
  dsimp only
  rw [if_neg (show ¬ EvenSite (2 * (2 * (k : ℤ) + 4) - y, x + 1) by unfold EvenSite; dsimp only; omega)]
  have key := ladder_oddodd_even (a := 2 * (k : ℤ) + 4) (by omega) (by omega) hu1 hu2 h1 h2 hp
  by_cases hP : LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1)
  · rw [if_pos hP]
    exact ⟨fun _ => key.1 hP, fun _ => rfl⟩
  · rw [if_neg hP]
    exact ⟨fun h => absurd h (by norm_num), fun hc => absurd (key.2 hc) hP⟩

/-- The Laplacian of the twos field at an odd strict-interior site vanishes iff the site is in one of the four odd classes. -/
theorem twos_lap_odd_iff {k : ℕ} {x y : ℤ}
    (hS : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y)) (hp : ¬ (x + y) % 2 = 0) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = 0 ↔
      (TwosClLS (2 * (k : ℤ) + 4) x y ∨ TwosClLN (2 * (k : ℤ) + 4) x y ∨
        TwosClUS (2 * (k : ℤ) + 4) x y ∨ TwosClUN (2 * (k : ℤ) + 4) x y) := by
  obtain ⟨⟨hu1, hu2⟩, -, hO⟩ := (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x y).1 hS
  obtain ⟨h1, h2⟩ := hO hp
  have hN := native_of_si_twos hS
  rw [laplacian_twos_std_native hN, quarterTurn_offset_apply]
  dsimp only
  rw [if_pos (show EvenSite (2 * (2 * (k : ℤ) + 4) - y, x + 1) by unfold EvenSite; dsimp only; omega)]
  have key := ladder_evenblack_odd (a := 2 * (k : ℤ) + 4) (by omega) (by omega) hu1 hu2 h1 h2 hp
  by_cases hB : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1)
  · rw [if_pos hB]
    exact ⟨fun h => absurd h (by norm_num), fun hc => absurd hB (key.2 hc)⟩
  · rw [if_neg hB]
    exact ⟨fun _ => key.1 hB, fun _ => rfl⟩

end FLatticePaper.W1Twos
