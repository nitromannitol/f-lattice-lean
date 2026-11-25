import FLatticePaper.Plane.Induction.TwosEPolicy
import Mathlib.Tactic.LinearCombination

/-! The tile covering, part A: the class keys of the lattice translates, the exclusion helper, and the families `C0` and `V`.

With `T = 2a²+4a−2`, a point `(r, y)` with `(a−1) r − (a+1) y = n` has key `n` (mod `T`), and the translates by the period vectors
`V = (−2, 2a)` and `U = (a+1, a−1)` keep it. A point of `NativeT` is in `TwosTile` unless it is a copy `v+U` or `v+V` of a free site
`v` that is not itself free. The families below are the points used by the covering; their `NativeT` and exclusion proofs are
linear in `r`, `y`, `n` once the products with `a` are supplied as hints. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper

/-- Adding a multiple of the period `T` leaves the residue unchanged. -/
theorem tc_emod_shift (x T : ℤ) : (x + (-1) * T) % T = x % T := by
  rw [Int.add_emod, Int.mul_emod_left, add_zero, Int.emod_emod]

/-- The base point `(r, y)` has key `n`. -/
theorem tc_key_C0 {a r y n : ℤ} (hid : (a - 1) * r - (a + 1) * y = n) :
    classKey a (r, y) = n % (2 * a * a + 4 * a - 2) := by
  show ((a - 1) * r - (a + 1) * y) % (2 * a * a + 4 * a - 2) = _
  rw [hid]

/-- The translate `(r, y) − V = (r−2, y+2a)` has key `n`. -/
theorem tc_key_V {a r y n : ℤ} (hid : (a - 1) * r - (a + 1) * y = n) :
    classKey a (r - 2, y + 2 * a) = n % (2 * a * a + 4 * a - 2) := by
  show ((a - 1) * (r - 2) - (a + 1) * (y + 2 * a)) % (2 * a * a + 4 * a - 2) = _
  have e : (a - 1) * (r - 2) - (a + 1) * (y + 2 * a) = n + (-1) * (2 * a * a + 4 * a - 2) := by
    linear_combination hid
  rw [e, tc_emod_shift]

/-- The translate `(r, y) + U + V = (r+a−1, y+3a−1)` has key `n`. -/
theorem tc_key_UV {a r y n : ℤ} (hid : (a - 1) * r - (a + 1) * y = n) :
    classKey a (r + a - 1, y + (3 * a - 1)) = n % (2 * a * a + 4 * a - 2) := by
  show ((a - 1) * (r + a - 1) - (a + 1) * (y + (3 * a - 1))) % (2 * a * a + 4 * a - 2) = _
  have e : (a - 1) * (r + a - 1) - (a + 1) * (y + (3 * a - 1)) = n + (-1) * (2 * a * a + 4 * a - 2) := by
    linear_combination hid
  rw [e, tc_emod_shift]

/-- The translate `(r, y) + U = (r+a+1, y+a−1)` has key `n`. -/
theorem tc_key_U {a r y n : ℤ} (hid : (a - 1) * r - (a + 1) * y = n) :
    classKey a (r + a + 1, y + a - 1) = n % (2 * a * a + 4 * a - 2) := by
  show ((a - 1) * (r + a + 1) - (a + 1) * (y + a - 1)) % (2 * a * a + 4 * a - 2) = _
  have e : (a - 1) * (r + a + 1) - (a + 1) * (y + a - 1) = n := by
    linear_combination hid
  rw [e]

/-- A point of `NativeT` is in the tile unless it is a copy `v+U` or `v+V` of a free site `v` (and not free itself). -/
theorem tc_tile_of_noAlias {a : ℤ} {p : Site} (hN : NativeT a p.1 p.2)
    (hex : FreeSite a p.1 p.2 ∨ ∀ v : Site, FreeSite a v.1 v.2 →
      p ≠ (v.1 + (a + 1), v.2 + (a - 1)) ∧ p ≠ (v.1 - 2, v.2 + 2 * a)) : TwosTile a p := by
  refine ⟨hN, ?_⟩
  rintro ⟨⟨v, hvF, -, hp⟩, hnF⟩
  rcases hex with h | h
  · exact hnF h
  · rcases hp with hp | hp
    · exact (h v hvF).1 hp
    · exact (h v hvF).2 hp

/-- The family `C0`: the point `(r, y)` is in the tile when `n ≤ (a−1) r` and `n ≤ 2a+2−2r`. -/
theorem tc_tile_C0 {a r y n : ℤ} (ha : 4 ≤ a) (hr0 : 0 ≤ r) (hra : r ≤ a)
    (hid : (a - 1) * r - (a + 1) * y = n) (hn0 : 0 ≤ n)
    (hA1 : n ≤ (a - 1) * r) (hA2 : n ≤ 2 * a + 2 - 2 * r) : TwosTile a (r, y) := by
  have ha1 : (0 : ℤ) < a + 1 := by linarith
  have F : (a + 1) * y = (a - 1) * r - n := by linear_combination (-1 : ℤ) * hid
  have hr_a : (a - 1) * r ≤ (a - 1) * a := mul_le_mul_of_nonneg_left hra (by linarith)
  have hy0 : 0 ≤ y := le_of_mul_le_mul_left (by nlinarith) ha1
  have hy1 : y ≤ 3 * a - 2 := le_of_mul_le_mul_left (by nlinarith [sq_nonneg a]) ha1
  have hy2 : r - 2 ≤ y := le_of_mul_le_mul_left (by nlinarith) ha1
  have hy3 : y ≤ 2 * a + r := le_of_mul_le_mul_left (by nlinarith [sq_nonneg a]) ha1
  have hyU : y < 2 * a - 1 := lt_of_mul_lt_mul_left (by nlinarith [sq_nonneg a]) ha1.le
  have hN : NativeT a (r, y).1 (r, y).2 := by
    show NativeT a r y
    unfold NativeT
    refine Or.inl ⟨⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩, ?_⟩
    rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> linarith
  refine tc_tile_of_noAlias hN (Or.inr ?_)
  intro v hv
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
    · omega
    · have hy : y = 2 * a + r := by omega
      subst hy
      nlinarith [sq_nonneg a]
    · have hy : y = 3 * a - 2 := by omega
      have hr : r = a - 1 := by omega
      subst hy
      subst hr
      nlinarith [sq_nonneg a]
    · omega
    · omega

/-- The family `V`: for `r ≥ 2` and `n` above the `C0` region, the point `(r−2, y+2a)` is in the tile. -/
theorem tc_tile_V {a r y n : ℤ} (ha : 4 ≤ a) (hr2 : 2 ≤ r) (hra : r ≤ a)
    (hid : (a - 1) * r - (a + 1) * y = n) (hnT : n < 2 * a * a + 4 * a - 2)
    (hnot : ¬ (n ≤ (a - 1) * r ∧ n ≤ 2 * a + 2 - 2 * r)) : TwosTile a (r - 2, y + 2 * a) := by
  have ha1 : (0 : ℤ) < a + 1 := by linarith
  have F : (a + 1) * y = (a - 1) * r - n := by linear_combination (-1 : ℤ) * hid
  have hr_a : (a - 1) * (2 : ℤ) ≤ (a - 1) * r := mul_le_mul_of_nonneg_left hr2 (by linarith)
  have hA2 : 2 * a + 2 - 2 * r ≤ n := by
    by_contra h
    have h' : n < 2 * a + 2 - 2 * r := not_le.mp h
    apply hnot
    constructor
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ a + 1 by linarith) (show (0 : ℤ) ≤ r - 2 by linarith)]
    · linarith
  have hy_up : y ≤ r - 2 := le_of_mul_le_mul_left (by nlinarith) ha1
  have hy_lo1 : -2 * a ≤ y := le_of_mul_le_mul_left (by nlinarith [sq_nonneg a]) ha1
  have hy_lo2 : r - 2 * a - 4 ≤ y := le_of_mul_le_mul_left (by nlinarith [sq_nonneg a]) ha1
  have hN : NativeT a (r - 2, y + 2 * a).1 (r - 2, y + 2 * a).2 := by
    show NativeT a (r - 2) (y + 2 * a)
    unfold NativeT
    refine Or.inl ⟨⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩, ?_⟩
    rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> linarith
  refine tc_tile_of_noAlias hN (Or.inr ?_)
  intro v hv
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
    · omega
    · have hy : y = r - 2 := by omega
      subst hy
      have hn : n = 2 * a + 2 - 2 * r := by linear_combination (-1 : ℤ) * hid
      exact hnot ⟨by nlinarith [mul_nonneg (show (0 : ℤ) ≤ a + 1 by linarith) (show (0 : ℤ) ≤ r - 2 by linarith)], hn.le⟩
    · omega
    · omega
    · omega

end FLatticePaper.TwosEPolicy
