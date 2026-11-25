import FLatticePaper.Plane.Induction.TwosTileCoverA

/-! The tile covering, part B: the families at `r = 1` and `r = 0`, the covering of every class, and the `tilePoint` spec.

For `a ≥ 4` and `(a−1) r − (a+1) y = n` with `0 ≤ r ≤ a`, `0 ≤ n < T`, one of the following points is in the tile, and has key `n`:
`C0 = (r, y)` when `n ≤ (a−1) r` and `n ≤ 2a+2−2r`; otherwise `V = (r−2, y+2a)` when `r ≥ 2`; for `r = 1`, `V` when
`2a ≤ n ≤ a²+a−2` and `UV = (a, y+3a−1)` above; for `r = 0`, `U = (a+1, y+a−1)` at `n = a+1` (where `y = −1`), and `UV = (a−1, y+3a−1)`
for `n ≥ 2a+2`. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper

/-- A point `(−1, y+2a)` with `y < 1−a` is not `NativeT` (the strip `x = −1, y+1 ≤ a+1` removes it). -/
theorem tc_not_native_neg1 {a y : ℤ} (ha : 4 ≤ a) (hy : y < 1 - a) : ¬ NativeT a (-1) (y + 2 * a) := by
  intro hN
  unfold NativeT at hN
  rcases hN with ⟨-, hns⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hns (Or.inl ⟨rfl, by omega⟩)
  · omega
  · omega

/-- The family `V` at `r = 1`: `(1−2, y+2a) = (−1, y+2a)` for `2a ≤ n ≤ a²+a−2`. -/
theorem tc_tile_V1 {a y n : ℤ} (ha : 4 ≤ a) (hid : (a - 1) * 1 - (a + 1) * y = n)
    (hn2 : 2 * a ≤ n) (hn3 : n ≤ a * a + a - 2) : TwosTile a (1 - 2, y + 2 * a) := by
  have ha1 : (0 : ℤ) < a + 1 := by linarith
  have F : (a + 1) * y = a - 1 - n := by linear_combination (-1 : ℤ) * hid
  have hyl : 1 - a ≤ y := le_of_mul_le_mul_left (by nlinarith) ha1
  have hyu : y ≤ -1 := le_of_mul_le_mul_left (by nlinarith) ha1
  have hN : NativeT a (1 - 2) (y + 2 * a) := by
    unfold NativeT
    refine Or.inl ⟨⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩, ?_⟩
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith
  refine tc_tile_of_noAlias hN (Or.inr ?_)
  intro v hv _
  obtain ⟨v1, v2⟩ := v
  simp only [FreeSite, FreeHSite, FreeVSite] at hv
  constructor
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rcases hv with (⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2⟩) | (⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩)
    all_goals omega
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rcases hv with (⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2⟩) | (⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩)
    · have hy : y = 0 := by omega
      subst hy
      nlinarith
    all_goals omega

/-- The family `UV` at `r = 1`: `(a, y+3a−1)` for `n > a²+a−2`. -/
theorem tc_tile_UV1 {a y n : ℤ} (ha : 4 ≤ a) (hid : (a - 1) * 1 - (a + 1) * y = n)
    (hn2 : a * a + a - 2 < n) (hnT : n < 2 * a * a + 4 * a - 2) :
    TwosTile a (1 + a - 1, y + (3 * a - 1)) := by
  have ha1 : (0 : ℤ) < a + 1 := by linarith
  have F : (a + 1) * y = a - 1 - n := by linear_combination (-1 : ℤ) * hid
  have hyu : y ≤ -1 := le_of_mul_le_mul_left
    (by nlinarith [mul_le_mul_of_nonneg_left ha (show (0 : ℤ) ≤ a by linarith)]) ha1
  have hyl : -2 * a - 1 ≤ y := le_of_mul_le_mul_left (by nlinarith) ha1
  have hyl' : y < 1 - a := lt_of_mul_lt_mul_left (by nlinarith) ha1.le
  have hN : NativeT a (1 + a - 1) (y + (3 * a - 1)) := by
    unfold NativeT
    refine Or.inl ⟨⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩, ?_⟩
    rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> linarith
  refine tc_tile_of_noAlias hN (Or.inr ?_)
  intro v hv hvN
  obtain ⟨v1, v2⟩ := v
  dsimp only at hv hvN
  simp only [FreeSite, FreeHSite, FreeVSite] at hv
  constructor
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rcases hv with (⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2⟩) | (⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩)
    · omega
    · omega
    · omega
    · omega
    · have e2' : v2 = y + 2 * a := by omega
      rw [e2'] at hvN
      rw [e1] at hvN
      exact absurd hvN (tc_not_native_neg1 ha hyl')
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rcases hv with (⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2⟩) | (⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩)
    all_goals omega

/-- The family `U` at `r = 0`: `(a+1, a−2)` when `y = −1` (that is, `n = a+1`); this point is free. -/
theorem tc_tile_U0 {a y : ℤ} (hy : y = -1) :
    TwosTile a (0 + a + 1, y + a - 1) := by
  have hN : NativeT a (0 + a + 1) (y + a - 1) := by
    unfold NativeT
    right
    right
    exact ⟨by omega, by omega⟩
  refine tc_tile_of_noAlias hN (Or.inl ?_)
  show FreeSite a (0 + a + 1) (y + a - 1)
  unfold FreeSite FreeHSite
  left
  right
  right
  exact ⟨by omega, by omega⟩

/-- The family `UV` at `r = 0`: `(a−1, y+3a−1)` for `n ≥ 2a+2`. -/
theorem tc_tile_UV0 {a y n : ℤ} (ha : 4 ≤ a) (hid : (a - 1) * 0 - (a + 1) * y = n)
    (hn : 2 * a + 2 ≤ n) (hnT : n < 2 * a * a + 4 * a - 2) :
    TwosTile a (0 + a - 1, y + (3 * a - 1)) := by
  have ha1 : (0 : ℤ) < a + 1 := by linarith
  have F : (a + 1) * y = -n := by linear_combination (-1 : ℤ) * hid
  have hy2 : y ≤ -2 := le_of_mul_le_mul_left (by nlinarith) ha1
  have hyl : -2 * a - 2 ≤ y := le_of_mul_le_mul_left (by nlinarith [sq_nonneg a]) ha1
  have hN : NativeT a (0 + a - 1) (y + (3 * a - 1)) := by
    unfold NativeT
    refine Or.inl ⟨⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩, ?_⟩
    rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> linarith
  refine tc_tile_of_noAlias hN (Or.inr ?_)
  intro v hv _
  obtain ⟨v1, v2⟩ := v
  dsimp only at hv
  simp only [FreeSite, FreeHSite, FreeVSite] at hv
  constructor
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rcases hv with (⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2⟩) | (⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩)
    all_goals omega
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rcases hv with (⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2⟩) | (⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩)
    all_goals omega

/-- **The tile covering.** Every class `n ∈ [0, T)` has a tile point `p` with `classKey a p = n`. -/
theorem tc_cover_abstract {a r y n : ℤ} (ha : 4 ≤ a) (hr0 : 0 ≤ r) (hra : r ≤ a)
    (hid : (a - 1) * r - (a + 1) * y = n) (hn0 : 0 ≤ n) (hnT : n < 2 * a * a + 4 * a - 2) :
    ∃ p : Site, TwosTile a p ∧ classKey a p = n % (2 * a * a + 4 * a - 2) := by
  have ha1 : (0 : ℤ) < a + 1 := by linarith
  by_cases hA : n ≤ (a - 1) * r ∧ n ≤ 2 * a + 2 - 2 * r
  · exact ⟨(r, y), tc_tile_C0 ha hr0 hra hid hn0 hA.1 hA.2, tc_key_C0 hid⟩
  by_cases hr2 : 2 ≤ r
  · exact ⟨(r - 2, y + 2 * a), tc_tile_V ha hr2 hra hid hnT hA, tc_key_V hid⟩
  have hr01 : r = 0 ∨ r = 1 := by omega
  rcases hr01 with rfl | rfl
  · -- r = 0: n > 0, (a+1) y = −n
    have hn_pos : 0 < n := by
      rcases lt_or_eq_of_le hn0 with h | h
      · exact h
      · exact (hA ⟨by linarith, by linarith⟩).elim
    have hy_lt : y < 0 := lt_of_mul_lt_mul_left (by nlinarith) ha1.le
    rcases (show y = -1 ∨ y ≤ -2 by omega) with hy | hy2
    · exact ⟨(0 + a + 1, y + a - 1), tc_tile_U0 hy, tc_key_U hid⟩
    · have hn2 : 2 * a + 2 ≤ n := by
        nlinarith [mul_nonneg ha1.le (show (0 : ℤ) ≤ -y - 2 by linarith)]
      exact ⟨(0 + a - 1, y + (3 * a - 1)), tc_tile_UV0 ha hid hn2 hnT, tc_key_UV hid⟩
  · -- r = 1: n ≥ a, so n ≥ 2a
    have hn_a : a - 1 < n := by
      by_contra h
      exact hA ⟨by linarith [not_lt.mp h], by linarith [not_lt.mp h]⟩
    have hy_neg : y ≤ -1 := by
      by_contra h
      have h0 : 0 ≤ y := by omega
      have : 0 ≤ (a + 1) * y := mul_nonneg ha1.le h0
      linarith
    have hn2 : 2 * a ≤ n := by
      have h1 : (a + 1) * y ≤ (a + 1) * (-1) := mul_le_mul_of_nonneg_left hy_neg ha1.le
      linarith
    by_cases hn3 : n ≤ a * a + a - 2
    · exact ⟨(1 - 2, y + 2 * a), tc_tile_V1 ha hid hn2 hn3, tc_key_V hid⟩
    · exact ⟨(1 + a - 1, y + (3 * a - 1)), tc_tile_UV1 ha hid (not_le.mp hn3) hnT, tc_key_UV hid⟩

/-- The integer quotient, remainder and `y` of the class `n` at `a = 2k+4`. -/
def tcQ (k : ℕ) (n : ℤ) : ℤ := ((k : ℤ) + 2) * n / (2 * (k : ℤ) + 5)

def tcR (k : ℕ) (n : ℤ) : ℤ := ((k : ℤ) + 2) * n % (2 * (k : ℤ) + 5)

def tcY (k : ℕ) (n : ℤ) : ℤ := ((k : ℤ) + 1) * n - (2 * (k : ℤ) + 3) * tcQ k n

theorem tcR_nonneg (k : ℕ) (n : ℤ) : 0 ≤ tcR k n := by
  unfold tcR
  exact Int.emod_nonneg _ (by omega)

theorem tcR_le (k : ℕ) (n : ℤ) : tcR k n ≤ 2 * (k : ℤ) + 4 := by
  unfold tcR
  have := Int.emod_lt_of_pos (((k : ℤ) + 2) * n) (show (0 : ℤ) < 2 * (k : ℤ) + 5 by omega)
  omega

theorem tcR_identity (k : ℕ) (n : ℤ) :
    (2 * (k : ℤ) + 4 - 1) * tcR k n - (2 * (k : ℤ) + 4 + 1) * tcY k n = n := by
  have hr : tcR k n = ((k : ℤ) + 2) * n - (2 * (k : ℤ) + 5) * tcQ k n := by
    unfold tcR tcQ
    rw [Int.emod_def]
  unfold tcY
  rw [hr]
  ring

/-- **The tile covering at `a = 2k+4`:** every class `n ∈ [0, T)` has a tile point. -/
theorem tc_cover_k (k : ℕ) {n : ℤ} (hn0 : 0 ≤ n)
    (hnT : n < 2 * (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 4 * (2 * (k : ℤ) + 4) - 2) :
    ∃ p : Site, TwosTile (2 * (k : ℤ) + 4) p ∧ classKey (2 * (k : ℤ) + 4) p = n := by
  obtain ⟨p, hp, hk⟩ := tc_cover_abstract (a := 2 * (k : ℤ) + 4) (r := tcR k n) (y := tcY k n)
    (by omega) (tcR_nonneg k n) (tcR_le k n) (tcR_identity k n) hn0 hnT
  exact ⟨p, hp, by rw [hk, Int.emod_eq_of_lt hn0 hnT]⟩

/-- **The spec of `tilePoint`:** the chosen point of the class `c` is a tile point with key `c`. -/
theorem tc_tilePoint_spec (k : ℕ) {c : ℤ} (hc0 : 0 ≤ c)
    (hcT : c < 2 * (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 4 * (2 * (k : ℤ) + 4) - 2) :
    TwosTile (2 * (k : ℤ) + 4) (tilePoint (2 * (k : ℤ) + 4) c) ∧
      classKey (2 * (k : ℤ) + 4) (tilePoint (2 * (k : ℤ) + 4) c) = c := by
  obtain ⟨p, hp, hk⟩ := tc_cover_k k hc0 hcT
  unfold tilePoint
  exact Classical.epsilon_spec (show ∃ q : Site, TwosTile (2 * (k : ℤ) + 4) q ∧
    classKey (2 * (k : ℤ) + 4) q = c from ⟨p, hp, hk⟩)

end FLatticePaper.TwosEPolicy
