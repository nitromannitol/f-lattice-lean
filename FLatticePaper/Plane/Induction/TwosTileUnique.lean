import FLatticePaper.Plane.Induction.TwosEPolicy
import Mathlib.Tactic.LinearCombination

/-! Uniqueness of the tile point of each class: two tile points with the same key coincide.

Box facts: for a native point `(x, y)`, `−1 ≤ x ≤ a+1`, `0 ≤ y ≤ 3a−2`, `−3 ≤ y−x ≤ 2a+1`. A tile point `p` and a translate
`p+U` or `p+V` cannot both be native unless `p` is free and `p+U` (resp. `p+V`) is not; the exclusion of `TwosTile` then removes
the translate. Two native points differ by `U`, `V` or `U+V` only if this box fact holds, and `p`, `p+U+V` are never both native. -/

namespace FLatticePaper.TwosEPolicy

theorem tu_nat_bounds {a x y : ℤ} (ha : 4 ≤ a) (hN : NativeT a x y) :
    -1 ≤ x ∧ x ≤ a + 1 ∧ 0 ≤ y ∧ y ≤ 3 * a - 2 ∧ -3 ≤ y - x ∧ y - x ≤ 2 * a + 1 := by
  unfold NativeT at hN
  rcases hN with ⟨⟨h1, h2, h3, h4, h5, h6⟩, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · omega
  · omega
  · omega

theorem tu_box_V {a x y : ℤ} (ha : 4 ≤ a) (hN : NativeT a x y) (hN' : NativeT a (x - 2) (y + 2 * a)) :
    FreeSite a x y ∧ ¬ FreeSite a (x - 2) (y + 2 * a) := by
  unfold NativeT at hN hN'
  unfold FreeSite FreeHSite FreeVSite
  rcases hN with ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hN' with ⟨⟨k1, k2, k3, k4, k5, k6⟩, ks⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ <;>
    exact ⟨by omega, by omega⟩

theorem tu_box_U {a x y : ℤ} (ha : 4 ≤ a) (hN : NativeT a x y)
    (hN' : NativeT a (x + (a + 1)) (y + (a - 1))) :
    FreeSite a x y ∧ ¬ FreeSite a (x + (a + 1)) (y + (a - 1)) := by
  unfold NativeT at hN hN'
  unfold FreeSite FreeHSite FreeVSite
  rcases hN with ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hN' with ⟨⟨k1, k2, k3, k4, k5, k6⟩, ks⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ <;>
    exact ⟨by omega, by omega⟩

theorem tu_box_UV {a x y : ℤ} (ha : 4 ≤ a) (hN : NativeT a x y)
    (hN' : NativeT a (x + (a - 1)) (y + (3 * a - 1))) : False := by
  unfold NativeT at hN hN'
  rcases hN with ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hN' with ⟨⟨k1, k2, k3, k4, k5, k6⟩, ks⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ <;>
    omega

theorem tu_no_V {a x y : ℤ} (ha : 4 ≤ a) (hp : TwosTile a (x, y)) (hq : TwosTile a (x - 2, y + 2 * a)) :
    False := by
  obtain ⟨hF, hnF⟩ := tu_box_V ha hp.1 hq.1
  exact hq.2 ⟨⟨(x, y), hF, hp.1, Or.inr rfl⟩, hnF⟩

theorem tu_no_U {a x y : ℤ} (ha : 4 ≤ a) (hp : TwosTile a (x, y))
    (hq : TwosTile a (x + (a + 1), y + (a - 1))) : False := by
  obtain ⟨hF, hnF⟩ := tu_box_U ha hp.1 hq.1
  exact hq.2 ⟨⟨(x, y), hF, hp.1, Or.inl rfl⟩, hnF⟩

/-- The key difference of two tile points with `m = 1` is impossible. -/
theorem tu_pos {a x y x' y' : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0)
    (hp : TwosTile a (x, y)) (hq : TwosTile a (x', y'))
    (hE : -2 * (x - x') - (a + 1) * ((y - x) - (y' - x')) = 2 * a * a + 4 * a - 2) : False := by
  have bp : -1 ≤ x ∧ x ≤ a + 1 ∧ 0 ≤ y ∧ y ≤ 3 * a - 2 ∧ -3 ≤ y - x ∧ y - x ≤ 2 * a + 1 :=
    tu_nat_bounds ha hp.1
  have bq : -1 ≤ x' ∧ x' ≤ a + 1 ∧ 0 ≤ y' ∧ y' ≤ 3 * a - 2 ∧ -3 ≤ y' - x' ∧ y' - x' ≤ 2 * a + 1 :=
    tu_nat_bounds ha hq.1
  obtain ⟨e, he_def⟩ : ∃ e, e = ((y - x) - (y' - x')) + 2 * a + 2 := ⟨_, rfl⟩
  have he : (a + 1) * e = 4 - 2 * (x - x') := by
    rw [he_def]
    linear_combination (-1 : ℤ) * hE
  have hdx : x - x' ≤ a + 2 := by omega
  have hdx' : -(a + 2) ≤ x - x' := by omega
  have he_lo : -1 ≤ e := by
    by_contra h
    have h2 : e ≤ -2 := by omega
    have h3 : (a + 1) * e ≤ (a + 1) * (-2) := mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have he_hi : e ≤ 3 := by
    by_contra h
    have h2 : 4 ≤ e := by omega
    have h3 : (a + 1) * 4 ≤ (a + 1) * e := mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  interval_cases e
  · omega
  · -- e = 0: δx = 2, δy = −2a: q = p + V
    have e1 : x' = x - 2 := by omega
    have e2 : y' = y + 2 * a := by omega
    subst e1
    subst e2
    exact (tu_no_V ha hp hq).elim
  · omega
  · -- e = 2: δx = 1 − a, δy = 1 − 3a: q = p + U + V
    have e1 : x' = x + (a - 1) := by omega
    have e2 : y' = y + (3 * a - 1) := by omega
    subst e1
    subst e2
    exact (tu_box_UV ha hp.1 hq.1).elim
  · omega

/-- Two tile points with the same key coincide. -/
theorem tile_unique {a x y x' y' : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0)
    (hp : TwosTile a (x, y)) (hq : TwosTile a (x', y'))
    (hk : classKey a (x, y) = classKey a (x', y')) : x = x' ∧ y = y' := by
  have hk' : ((a - 1) * x - (a + 1) * y) % (2 * a * a + 4 * a - 2) =
      ((a - 1) * x' - (a + 1) * y') % (2 * a * a + 4 * a - 2) := hk
  have hd : (2 * a * a + 4 * a - 2) ∣ ((a - 1) * x - (a + 1) * y) - ((a - 1) * x' - (a + 1) * y') := by
    apply Int.dvd_of_emod_eq_zero
    rw [Int.sub_emod, hk', sub_self, Int.zero_emod]
  obtain ⟨m, hm⟩ := hd
  have hE : -2 * (x - x') - (a + 1) * ((y - x) - (y' - x')) = (2 * a * a + 4 * a - 2) * m := by
    linear_combination hm
  have bp : -1 ≤ x ∧ x ≤ a + 1 ∧ 0 ≤ y ∧ y ≤ 3 * a - 2 ∧ -3 ≤ y - x ∧ y - x ≤ 2 * a + 1 :=
    tu_nat_bounds ha hp.1
  have bq : -1 ≤ x' ∧ x' ≤ a + 1 ∧ 0 ≤ y' ∧ y' ≤ 3 * a - 2 ∧ -3 ≤ y' - x' ∧ y' - x' ≤ 2 * a + 1 :=
    tu_nat_bounds ha hq.1
  have hT0 : (0 : ℤ) < 2 * a * a + 4 * a - 2 := by nlinarith
  have ha2 : 16 ≤ a * a := by nlinarith
  have hdh1 : -(2 * a + 4) ≤ (y - x) - (y' - x') := by omega
  have hdh2 : (y - x) - (y' - x') ≤ 2 * a + 4 := by omega
  have hdx1 : -(a + 2) ≤ x - x' := by omega
  have hdx2 : x - x' ≤ a + 2 := by omega
  have hb1 : (a + 1) * ((y - x) - (y' - x')) ≤ (a + 1) * (2 * a + 4) :=
    mul_le_mul_of_nonneg_left hdh2 (by linarith)
  have hb2 : (a + 1) * (-(2 * a + 4)) ≤ (a + 1) * ((y - x) - (y' - x')) :=
    mul_le_mul_of_nonneg_left hdh1 (by linarith)
  have hm1 : m ≤ 1 := by
    by_contra h
    have h2 : (2 : ℤ) ≤ m := by omega
    have h3 : (2 * a * a + 4 * a - 2) * 2 ≤ (2 * a * a + 4 * a - 2) * m :=
      mul_le_mul_of_nonneg_left h2 hT0.le
    nlinarith
  have hm2 : -1 ≤ m := by
    by_contra h
    have h2 : m ≤ -2 := by omega
    have h3 : (2 * a * a + 4 * a - 2) * m ≤ (2 * a * a + 4 * a - 2) * (-2) :=
      mul_le_mul_of_nonneg_left h2 hT0.le
    nlinarith
  interval_cases m
  · -- m = -1: the swapped pair has m = 1
    exact (tu_pos ha he2 hq hp (by linear_combination (-1 : ℤ) * hE)).elim
  · -- m = 0: the difference is 0, ±U, or 0 from the parity of a+1
    obtain ⟨d, hd_def⟩ : ∃ d, d = (y - x) - (y' - x') := ⟨_, rfl⟩
    rw [← hd_def] at hE
    have hd2 : d ≤ 2 := by
      by_contra h
      have h3 : (a + 1) * 3 ≤ (a + 1) * d := mul_le_mul_of_nonneg_left (by omega) (by linarith)
      linarith
    have hd_2 : -2 ≤ d := by
      by_contra h
      have h3 : (a + 1) * d ≤ (a + 1) * (-3) := mul_le_mul_of_nonneg_left (by omega) (by linarith)
      linarith
    interval_cases d
    · -- d = -2: δx = a+1, so p = q + U
      have e1 : x = x' + (a + 1) := by omega
      have e2 : y = y' + (a - 1) := by omega
      subst e1
      subst e2
      exact (tu_no_U ha hq hp).elim
    · omega
    · omega
    · omega
    · -- d = 2: δx = -(a+1), so q = p + U
      have e1 : x' = x + (a + 1) := by omega
      have e2 : y' = y + (a - 1) := by omega
      subst e1
      subst e2
      exact (tu_no_U ha hp hq).elim
  · -- m = 1
    exact (tu_pos ha he2 hp hq (by linear_combination hE)).elim

end FLatticePaper.TwosEPolicy
