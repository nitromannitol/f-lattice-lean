import FLatticePaper.Plane.Induction.TwosSquareShift
import FLatticePaper.Plane.Induction.TwosPriceDelta

/-! Task 72 / twos base: the primitive price `P` does not increase along the selected inputs of the twos signed policy.

On the native box (`TwosKey`) the price is two-valued, `P = c₀ − δ` with `δ` the three bands `TwosDelta` (`twos_price_delta`).
The price changes by `−1` under `U` and is unchanged under `V` (`twos_price_drift_kernel`, `twos_price_drift_transverse`), so a
difference of prices is invariant under lattice translation. A selected edge is therefore a band implication on a native pair:
the centre of a native black, free or candidate edge is checked by `omega` on the linear bands. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey

/-- The primitive price of the twos standard field of `2^(k+1)`. -/
noncomputable def twosP (k : ℕ) (z : Site) : ℤ :=
  (frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) z

/-- The price drops by one under the kernel `U = (2k+5, 2k+3)`. -/
theorem twosP_U (k : ℕ) (x y : ℤ) :
    twosP k (x + (2 * (k : ℤ) + 5), y + (2 * (k : ℤ) + 3)) = twosP k (x, y) - 1 := by
  have h := twos_price_drift_kernel k (x, y)
  rw [twos_kernel_explicit] at h
  have e : ((x, y) : Site) + ((2 * (k : ℤ) + 5), (2 * (k : ℤ) + 3)) =
      (x + (2 * (k : ℤ) + 5), y + (2 * (k : ℤ) + 3)) := rfl
  rw [e] at h
  unfold twosP
  linarith

/-- The price is unchanged under the transverse `V = (-2, 4k+8)`. -/
theorem twosP_V (k : ℕ) (x y : ℤ) :
    twosP k (x + (-2), y + (4 * (k : ℤ) + 8)) = twosP k (x, y) := by
  have h := twos_price_drift_transverse k (x, y)
  rw [twos_transverse_explicit] at h
  have e : ((x, y) : Site) + ((-2 : ℤ), (4 * (k : ℤ) + 8)) = (x + (-2), y + (4 * (k : ℤ) + 8)) := rfl
  rw [e] at h
  unfold twosP
  linarith

/-- A native site is a `TwosKey` point (the native box is contained in the key set). -/
theorem twosKey_of_native {a x y : ℤ} (h : NativeT a x y) : TwosKey a x y := by
  unfold NativeT at h
  unfold TwosKey
  omega

/-- **The price on the key set.** If `x` and `y` are `TwosKey` points and the band of `x` implies the band of `y`, then the
price does not increase from `x` to `y`. -/
theorem twosP_le_of_band (k : ℕ) {x y : ℤ × ℤ} (hx : TwosKey (2 * (k : ℤ) + 4) x.1 x.2)
    (hy : TwosKey (2 * (k : ℤ) + 4) y.1 y.2) (h : TwosDelta k x.1 x.2 → TwosDelta k y.1 y.2) :
    twosP k y ≤ twosP k x := by
  unfold twosP
  rcases twos_price_delta k hx with ⟨hx1, _⟩ | ⟨hx1, hx2⟩
  · rcases twos_price_delta k hy with ⟨hy1, _⟩ | ⟨hy1, _⟩ <;> linarith
  · have hy' := h hx2
    rcases twos_price_delta k hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact absurd hy' hy2
    · linarith

/-- The candidate displacement on the low band, below the middle row: the input is `(x, y-1)`. -/
theorem cand_mono_low_down (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hL : CandLow (2 * (k : ℤ) + 4) x y) (hm : y < 2 * (k : ℤ) + 4 - 1) :
    twosP k (x + 0, y + -1) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (twosKey_of_native hn) ?_ ?_
  · unfold TwosKey; unfold CandLow NativeT at *; omega
  · unfold TwosDelta; unfold CandLow NativeT at *; omega

/-- The candidate displacement on the low band, above the middle row: the input is `(x, y+1)`. -/
theorem cand_mono_low_up (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hL : CandLow (2 * (k : ℤ) + 4) x y) (hm : ¬ y < 2 * (k : ℤ) + 4 - 1) :
    twosP k (x + 0, y + 1) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (twosKey_of_native hn) ?_ ?_
  · unfold TwosKey; unfold CandLow NativeT at *; omega
  · unfold TwosDelta; unfold CandLow NativeT at *; omega

/-- The candidate displacement on the high band, below the middle row `2a-1`: the input is `(x, y-1)`. -/
theorem cand_mono_high_down (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hH : CandHigh (2 * (k : ℤ) + 4) x y) (hm : y < 2 * (2 * (k : ℤ) + 4) - 1) :
    twosP k (x + 0, y + -1) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (twosKey_of_native hn) ?_ ?_
  · unfold TwosKey; unfold CandHigh NativeT at *; omega
  · unfold TwosDelta; unfold CandHigh NativeT at *; omega

/-- The candidate displacement on the high band, above the middle row: the input is `(x, y+1)`. -/
theorem cand_mono_high_up (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hH : CandHigh (2 * (k : ℤ) + 4) x y) (hm : ¬ y < 2 * (2 * (k : ℤ) + 4) - 1) :
    twosP k (x + 0, y + 1) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (twosKey_of_native hn) ?_ ?_
  · unfold TwosKey; unfold CandHigh NativeT at *; omega
  · unfold TwosDelta; unfold CandHigh NativeT at *; omega

/-- The east diagonal: the input is `(x+1, y)`. -/
theorem cand_mono_E (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hE : CandE (2 * (k : ℤ) + 4) x y) : twosP k (x + 1, y + 0) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (twosKey_of_native hn) ?_ ?_
  · unfold TwosKey; unfold CandE NativeT at *; omega
  · unfold TwosDelta; unfold CandE NativeT at *; omega

/-- The west diagonal: the input is `(x-1, y)`. -/
theorem cand_mono_W (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hW : CandW (2 * (k : ℤ) + 4) x y) : twosP k (x + -1, y + 0) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (twosKey_of_native hn) ?_ ?_
  · unfold TwosKey; unfold CandW NativeT at *; omega
  · unfold TwosDelta; unfold CandW NativeT at *; omega

/-- **The candidate branch.** At a native candidate centre under the candidate guard, the candidate input does not raise the
price. -/
theorem cand_mono (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hg : CandGuard (2 * (k : ℤ) + 4) x y) :
    twosP k (x + (candDisp (2 * (k : ℤ) + 4) x y).1, y + (candDisp (2 * (k : ℤ) + 4) x y).2) ≤ twosP k (x, y) := by
  rcases hg with hL | hH | hE | hW
  · by_cases hm : y < 2 * (k : ℤ) + 4 - 1
    · rw [candDisp_low_down hL hm]; exact cand_mono_low_down k hn hL hm
    · rw [candDisp_low_up hL hm]; exact cand_mono_low_up k hn hL hm
  · by_cases hm : y < 2 * (2 * (k : ℤ) + 4) - 1
    · rw [candDisp_high_down hH hm]; exact cand_mono_high_down k hn hH hm
    · rw [candDisp_high_up hH hm]; exact cand_mono_high_up k hn hH hm
  · rw [candDisp_E hE]; exact cand_mono_E k hn hE
  · rw [candDisp_W hW]; exact cand_mono_W k hn hW

/-- A shift by `V` does not change the comparison of prices. -/
theorem twosP_le_of_V {k : ℕ} {x y p q : ℤ}
    (h : twosP k (p + (-2), q + (4 * (k : ℤ) + 8)) ≤ twosP k (x + (-2), y + (4 * (k : ℤ) + 8))) :
    twosP k (p, q) ≤ twosP k (x, y) := by
  have h1 := twosP_V k p q
  have h2 := twosP_V k x y
  linarith

/-- A shift by `U` lowers both prices by one. -/
theorem twosP_le_of_U {k : ℕ} {x y p q : ℤ}
    (h : twosP k (p + (2 * (k : ℤ) + 5), q + (2 * (k : ℤ) + 3)) ≤ twosP k (x + (2 * (k : ℤ) + 5), y + (2 * (k : ℤ) + 3))) :
    twosP k (p, q) ≤ twosP k (x, y) := by
  have h1 := twosP_U k p q
  have h2 := twosP_U k x y
  linarith

/-! ### The free branch: the displacement of the free table, by its class and its shift in the lattice. -/

/-- Free family `p/H0` (sign 1): the displacement `(0, -1)`, shift `V`. -/
theorem free_p_H0 (k : ℕ) {x y : ℤ} (h : x = 1 ∧ y = 0) :
    twosP k (x + (0), y + (-1)) ≤ twosP k (x, y) := by
  apply twosP_le_of_V
  refine twosP_le_of_band k (x := (x + -2, y + (4 * (k : ℤ) + 8))) (y := (x + (0) + -2, y + (-1) + (4 * (k : ℤ) + 8))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `p/Hlt` (sign 1): the displacement `(1, 0)`, shift `V`. -/
theorem free_p_Hlt (k : ℕ) {x y : ℤ} (h : 2 ≤ x ∧ x ≤ 2 * (k : ℤ) + 3 ∧ y = x - 2) :
    twosP k (x + (1), y + (0)) ≤ twosP k (x, y) := by
  apply twosP_le_of_V
  refine twosP_le_of_band k (x := (x + -2, y + (4 * (k : ℤ) + 8))) (y := (x + (1) + -2, y + (0) + (4 * (k : ℤ) + 8))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `p/Heq` (sign 1): the displacement `(1, 0)`, shift `0`. -/
theorem free_p_Heq (k : ℕ) {x y : ℤ} (h : x = 2 * (k : ℤ) + 4 ∧ y = 2 * (k : ℤ) + 2) :
    twosP k (x + (1), y + (0)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (1), y + (0))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `p/Hodd` (sign 1): the displacement `(0, 1)`, shift `0`. -/
theorem free_p_Hodd (k : ℕ) {x y : ℤ} (h : x = 2 * (k : ℤ) + 5 ∧ y = 2 * (k : ℤ) + 2) :
    twosP k (x + (0), y + (1)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (0), y + (1))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `p/V0` (sign 1): the displacement `(1, 0)`, shift `0`. -/
theorem free_p_V0 (k : ℕ) {x y : ℤ} (h : x = 0 ∧ y = 0) :
    twosP k (x + (1), y + (0)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (1), y + (0))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `p/Ve0` (sign 1): the displacement `(1, 0)`, shift `0`. -/
theorem free_p_Ve0 (k : ℕ) {x y : ℤ} (h : x = 0 ∧ 0 < y ∧ y < 2 * (k : ℤ) + 4 ∧ (y % 2 = 0)) :
    twosP k (x + (1), y + (0)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (1), y + (0))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `p/Vo0` (sign 1): the displacement `(0, -1)`, shift `0`. -/
theorem free_p_Vo0 (k : ℕ) {x y : ℤ} (h : x = 0 ∧ 0 < y ∧ y < 2 * (k : ℤ) + 4 ∧ (y % 2 = 1)) :
    twosP k (x + (0), y + (-1)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (0), y + (-1))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `p/Ve1` (sign 1): the displacement `(1, 0)`, shift `0`. -/
theorem free_p_Ve1 (k : ℕ) {x y : ℤ} (h : x = -1 ∧ 2 * (k : ℤ) + 4 ≤ y ∧ y < 2 * (2 * (k : ℤ) + 4) ∧ (y % 2 = 1)) :
    twosP k (x + (1), y + (0)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (1), y + (0))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `p/Vo1a` (sign 1): the displacement `(0, -1)`, shift `U`. -/
theorem free_p_Vo1a (k : ℕ) {x y : ℤ} (h : x = -1 ∧ y = 2 * (k : ℤ) + 4) :
    twosP k (x + (0), y + (-1)) ≤ twosP k (x, y) := by
  apply twosP_le_of_U
  refine twosP_le_of_band k (x := (x + (2 * (k : ℤ) + 5), y + (2 * (k : ℤ) + 3))) (y := (x + (0) + (2 * (k : ℤ) + 5), y + (-1) + (2 * (k : ℤ) + 3))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `p/Vo1` (sign 1): the displacement `(0, -1)`, shift `0`. -/
theorem free_p_Vo1 (k : ℕ) {x y : ℤ} (h : x = -1 ∧ 2 * (k : ℤ) + 4 < y ∧ y < 2 * (2 * (k : ℤ) + 4) ∧ (y % 2 = 0)) :
    twosP k (x + (0), y + (-1)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (0), y + (-1))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `m/H0` (sign -1): the displacement `(0, 1)`, shift `0`. -/
theorem free_m_H0 (k : ℕ) {x y : ℤ} (h : x = 1 ∧ y = 0) :
    twosP k (x + (0), y + (1)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (0), y + (1))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `m/Hlt` (sign -1): the displacement `(1, 0)`, shift `V`. -/
theorem free_m_Hlt (k : ℕ) {x y : ℤ} (h : 2 ≤ x ∧ x ≤ 2 * (k : ℤ) + 3 ∧ y = x - 2) :
    twosP k (x + (1), y + (0)) ≤ twosP k (x, y) := by
  apply twosP_le_of_V
  refine twosP_le_of_band k (x := (x + -2, y + (4 * (k : ℤ) + 8))) (y := (x + (1) + -2, y + (0) + (4 * (k : ℤ) + 8))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `m/Heq` (sign -1): the displacement `(1, 0)`, shift `0`. -/
theorem free_m_Heq (k : ℕ) {x y : ℤ} (h : x = 2 * (k : ℤ) + 4 ∧ y = 2 * (k : ℤ) + 2) :
    twosP k (x + (1), y + (0)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (1), y + (0))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `m/Hodd` (sign -1): the displacement `(0, 1)`, shift `0`. -/
theorem free_m_Hodd (k : ℕ) {x y : ℤ} (h : x = 2 * (k : ℤ) + 5 ∧ y = 2 * (k : ℤ) + 2) :
    twosP k (x + (0), y + (1)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (0), y + (1))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `m/V0` (sign -1): the displacement `(1, 0)`, shift `0`. -/
theorem free_m_V0 (k : ℕ) {x y : ℤ} (h : x = 0 ∧ y = 0) :
    twosP k (x + (1), y + (0)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (1), y + (0))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `m/Ve0` (sign -1): the displacement `(-1, 0)`, shift `U`. -/
theorem free_m_Ve0 (k : ℕ) {x y : ℤ} (h : x = 0 ∧ 0 < y ∧ y < 2 * (k : ℤ) + 4 ∧ (y % 2 = 0)) :
    twosP k (x + (-1), y + (0)) ≤ twosP k (x, y) := by
  apply twosP_le_of_U
  refine twosP_le_of_band k (x := (x + (2 * (k : ℤ) + 5), y + (2 * (k : ℤ) + 3))) (y := (x + (-1) + (2 * (k : ℤ) + 5), y + (0) + (2 * (k : ℤ) + 3))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `m/Vo0` (sign -1): the displacement `(0, 1)`, shift `0`. -/
theorem free_m_Vo0 (k : ℕ) {x y : ℤ} (h : x = 0 ∧ 0 < y ∧ y < 2 * (k : ℤ) + 4 ∧ (y % 2 = 1)) :
    twosP k (x + (0), y + (1)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (0), y + (1))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `m/Ve1` (sign -1): the displacement `(-1, 0)`, shift `U`. -/
theorem free_m_Ve1 (k : ℕ) {x y : ℤ} (h : x = -1 ∧ 2 * (k : ℤ) + 4 ≤ y ∧ y < 2 * (2 * (k : ℤ) + 4) ∧ (y % 2 = 1)) :
    twosP k (x + (-1), y + (0)) ≤ twosP k (x, y) := by
  apply twosP_le_of_U
  refine twosP_le_of_band k (x := (x + (2 * (k : ℤ) + 5), y + (2 * (k : ℤ) + 3))) (y := (x + (-1) + (2 * (k : ℤ) + 5), y + (0) + (2 * (k : ℤ) + 3))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega

/-- Free family `m/Vo1` (sign -1): the displacement `(0, 1)`, shift `0`. -/
theorem free_m_Vo1 (k : ℕ) {x y : ℤ} (h : x = -1 ∧ 2 * (k : ℤ) + 4 ≤ y ∧ y < 2 * (2 * (k : ℤ) + 4) ∧ (y % 2 = 0)) :
    twosP k (x + (0), y + (1)) ≤ twosP k (x, y) := by
  refine twosP_le_of_band k (x := (x, y)) (y := (x + (0), y + (1))) ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro hδ; dsimp only at hδ ⊢; unfold TwosDelta at *; omega


/-- **The free branch.** At a free site the free displacement does not raise the price. -/
theorem free_mono (k : ℕ) {η : ℤ} (hη : η = 1 ∨ η = -1) {x y : ℤ}
    (hF : FreeSite (2 * (k : ℤ) + 4) x y) :
    twosP k (x + (freeDisp (2 * (k : ℤ) + 4) η x y).1, y + (freeDisp (2 * (k : ℤ) + 4) η x y).2) ≤ twosP k (x, y) := by
  have hF' := hF
  unfold FreeSite FreeHSite FreeVSite at hF'
  rcases hη with rfl | rfl
  · rcases hF' with (h | h | h) | (h | h)
    · rw [freeDisp_H0 h]; exact free_p_H0 k h
    · rw [freeDisp_Heven (by unfold FreeHSite; omega) (by omega) (by unfold EvenSite; dsimp only; omega)]
      by_cases hea : x = 2 * (k : ℤ) + 4
      · exact free_p_Heq k ⟨hea, by omega⟩
      · exact free_p_Hlt k ⟨by omega, by omega, by omega⟩
    · rw [freeDisp_Hodd (by unfold FreeHSite; omega) (by omega) (by unfold EvenSite; dsimp only; omega)]
      exact free_p_Hodd k ⟨by omega, by omega⟩
    · by_cases hz : x = 0 ∧ y = 0
      · rw [freeDisp_V0 hz]; exact free_p_V0 k hz
      · by_cases he : EvenSite (x, y)
        · rw [freeDisp_Veven (by unfold FreeVSite; omega) hz he]
          exact free_p_Ve0 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
        · rw [freeDisp_Vodd (by unfold FreeVSite; omega) hz he]
          exact free_p_Vo0 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
    · by_cases he : EvenSite (x, y)
      · rw [freeDisp_Veven (by unfold FreeVSite; omega) (by omega) he]
        exact free_p_Ve1 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
      · rw [freeDisp_Vodd (by unfold FreeVSite; omega) (by omega) he]
        by_cases hay : y = 2 * (k : ℤ) + 4
        · exact free_p_Vo1a k ⟨by omega, hay⟩
        · exact free_p_Vo1 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
  · rcases hF' with (h | h | h) | (h | h)
    · rw [freeDisp_H0 h]; exact free_m_H0 k h
    · rw [freeDisp_Heven (by unfold FreeHSite; omega) (by omega) (by unfold EvenSite; dsimp only; omega)]
      by_cases hea : x = 2 * (k : ℤ) + 4
      · exact free_m_Heq k ⟨hea, by omega⟩
      · exact free_m_Hlt k ⟨by omega, by omega, by omega⟩
    · rw [freeDisp_Hodd (by unfold FreeHSite; omega) (by omega) (by unfold EvenSite; dsimp only; omega)]
      exact free_m_Hodd k ⟨by omega, by omega⟩
    · by_cases hz : x = 0 ∧ y = 0
      · rw [freeDisp_V0 hz]; exact free_m_V0 k hz
      · by_cases he : EvenSite (x, y)
        · rw [freeDisp_Veven (by unfold FreeVSite; omega) hz he]
          exact free_m_Ve0 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
        · rw [freeDisp_Vodd (by unfold FreeVSite; omega) hz he]
          exact free_m_Vo0 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
    · by_cases he : EvenSite (x, y)
      · rw [freeDisp_Veven (by unfold FreeVSite; omega) (by omega) he]
        exact free_m_Ve1 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
      · rw [freeDisp_Vodd (by unfold FreeVSite; omega) (by omega) he]
        exact free_m_Vo1 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩

/-! ### The black branch: the native centres of charge `-1`. -/

/-- The inverse shifts of the price. -/
theorem twosP_negU (k : ℕ) (x y : ℤ) :
    twosP k (x - (2 * (k : ℤ) + 5), y - (2 * (k : ℤ) + 3)) = twosP k (x, y) + 1 := by
  have h := twosP_U k (x - (2 * (k : ℤ) + 5)) (y - (2 * (k : ℤ) + 3))
  have e1 : x - (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 5) = x := by ring
  have e2 : y - (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) = y := by ring
  rw [e1, e2] at h
  linarith

/-- The black region of a native centre, from the charge table (`laplacian_twos_native`): the rotated point is even and an
`LadderOddEvenBlack`, or odd and not an `LadderOddOddWhite`. -/
theorem black_region_of_lap (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hl : laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = -1) :
    (EvenSite (2 * (2 * (k : ℤ) + 4) - y, x + 1) ∧ LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1)) ∨
      (¬ EvenSite (2 * (2 * (k : ℤ) + 4) - y, x + 1) ∧
        ¬ LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1)) := by
  rw [laplacian_twos_native k hagree hperiod hn, quarterTurn_offset_apply] at hl
  split_ifs at hl <;> first
    | exact Or.inl ⟨by assumption, by assumption⟩
    | exact Or.inr ⟨by assumption, by assumption⟩

set_option maxHeartbeats 400000 in
/-- **The black key at an odd centre.** The rotated point is even, so the black condition is `LadderOddEvenBlack`. -/
theorem black_key_odd (k : ℕ) {x y j1 j2 : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : ¬ EvenSite (x, y))
    (hB : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1))
    (he : Edge (j1, j2) (x, y)) :
    TwosKey (2 * (k : ℤ) + 4) j1 j2 ∧ (TwosDelta k x y → TwosDelta k j1 j2) := by
  unfold LadderOddEvenBlack at hB
  try dsimp only at hB
  unfold NativeT at hn
  unfold EvenSite at hp
  try dsimp only at hp
  unfold Edge incomingNeg incomingPos at he
  simp only [EvenSite, hp, if_false] at he
  rcases he with he | he
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨by unfold TwosKey; omega, fun hδ => by unfold TwosDelta at *; omega⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨by unfold TwosKey; omega, fun hδ => by unfold TwosDelta at *; omega⟩

set_option maxHeartbeats 400000 in
/-- A positive white strip gives the white condition of the rotated point. -/
theorem ow_of_regions (k : ℕ) {x y : ℤ} (h : (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2) ∨ ((x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1) ∨ ((x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4)) ∨ ((y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3) ∨ ((x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3) ∨ ((x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2) ∨ ((y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2) ∨ ((y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4)) ∨ ((x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4)) ∨ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2)))))))))) :
    LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
  unfold LadderOddOddWhite LadderOddLowerBoundary reflectLadderOdd
  simp only [Prod.fst_sub, Prod.snd_sub]
  try dsimp only
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl ⟨by omega, by omega, by omega⟩)
  · exact Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
  · exact Or.inl (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))
  · exact Or.inr (Or.inl (Or.inl ⟨by omega, by omega, by omega⟩))
  · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
  · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))

set_option maxHeartbeats 400000 in
/-- The left input `(x-1, y)` of an even black centre: the key point and the band, given that the ten white strips are excluded. -/
theorem even_left_key (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (_n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2)) (_n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1)) (_n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4))) (_n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3)) (_n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (_n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2)) (_n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2)) (_n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4))) (_n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4))) (_n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2)) :
    TwosKey (2 * (k : ℤ) + 4) (x - 1) y ∧ (TwosDelta k x y → TwosDelta k (x - 1) y) := by
  unfold NativeT at hn
  refine ⟨Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun hδ => ?_⟩
  · clear _n1 _n3 _n4 _n5 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n3 _n4 _n5 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n3 _n4 _n5 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n3 _n4 _n5 _n6 _n7 _n8 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n3 _n4 _n5 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n3 _n4 _n5 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n4 _n5 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n3 _n4 _n5 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n5 _n6 _n7 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> (try unfold TwosDelta at *) <;> omega)


set_option maxHeartbeats 400000 in
/-- The right input `(x+1, y)` of an even black centre. -/
theorem even_right_key (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (_n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2)) (_n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1)) (_n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4))) (_n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3)) (_n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (_n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2)) (_n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2)) (_n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4))) (_n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4))) (_n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2)) :
    TwosKey (2 * (k : ℤ) + 4) (x + 1) y ∧ (TwosDelta k x y → TwosDelta k (x + 1) y) := by
  unfold NativeT at hn
  refine ⟨Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun hδ => ?_⟩
  · clear _n1 _n2 _n3 _n4 _n5 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n3 _n4 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n3 _n6 _n7 _n8 _n9; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n3 _n4 _n5 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n3 _n4 _n5 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n3 _n4 _n5 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n3 _n4 _n5 _n6 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n3 _n4 _n5 _n7 _n8 _n9 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> omega)
  · clear _n1 _n2 _n7 _n10; (rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> (try unfold TwosDelta at *) <;> omega)


/-- The two incoming inputs of an even centre `(x, y)`. -/
theorem edge_even_cases (x y j1 j2 : ℤ) (h : EvenSite (x, y)) (he : Edge (j1, j2) (x, y)) :
    (j1 = x - 1 ∧ j2 = y) ∨ (j1 = x + 1 ∧ j2 = y) := by
  unfold Edge incomingNeg incomingPos at he
  simp only [if_pos h] at he
  rcases he with he | he
  · exact Or.inl (Prod.mk.inj he)
  · exact Or.inr (Prod.mk.inj he)

set_option maxHeartbeats 400000 in
/-- **The black key at an even centre.** -/
theorem black_key_even (k : ℕ) {x y j1 j2 : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : EvenSite (x, y))
    (hW : ¬ LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1))
    (he : Edge (j1, j2) (x, y)) :
    TwosKey (2 * (k : ℤ) + 4) j1 j2 ∧ (TwosDelta k x y → TwosDelta k j1 j2) := by
  have n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2) := fun h => hW (ow_of_regions k (Or.inl h))
  have n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1) := fun h => hW (ow_of_regions k (Or.inr (Or.inl h)))
  have n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4)) := fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inl h))))
  have n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3) := fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3) := fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  have n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2) := fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  have n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2) := fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  have n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4)) := fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
  have n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4)) := fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
  have n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2) := fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))))))))
  have hp' : (x + y) % 2 = 0 := hp
  rcases edge_even_cases x y j1 j2 hp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1 h2
    exact even_left_key k hn hp' n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
  · subst h1 h2
    exact even_right_key k hn hp' n1 n2 n3 n4 n5 n6 n7 n8 n9 n10

/-- The rotated point of a site has the opposite parity. -/
theorem evenSite_rot (a x y : ℤ) : EvenSite (2 * a - y, x + 1) ↔ ¬ EvenSite (x, y) := by
  unfold EvenSite
  simp only
  omega

set_option maxHeartbeats 400000 in
/-- **The black branch.** A native centre of charge `-1` does not raise the price along its incoming inputs. -/
theorem black_mono (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y j1 j2 : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hl : laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = -1)
    (he : Edge (j1, j2) (x, y)) :
    twosP k (j1, j2) ≤ twosP k (x, y) := by
  have hR := black_region_of_lap k hagree hperiod hn hl
  obtain ⟨hK, hB⟩ : TwosKey (2 * (k : ℤ) + 4) j1 j2 ∧ (TwosDelta k x y → TwosDelta k j1 j2) := by
    by_cases hp : EvenSite (x, y)
    · have hW : ¬ LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
        rcases hR with ⟨hE, _⟩ | ⟨_, hW⟩
        · exact absurd ((evenSite_rot (2 * (k : ℤ) + 4) x y).mp hE) (not_not.mpr hp)
        · exact hW
      exact black_key_even k hn hp hW he
    · have hB : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
        rcases hR with ⟨_, hB⟩ | ⟨hNE, _⟩
        · exact hB
        · exact absurd ((evenSite_rot (2 * (k : ℤ) + 4) x y).mpr hp) hNE
      exact black_key_odd k hn hp hB he
  exact twosP_le_of_band k (twosKey_of_native hn) hK hB

/-! ### Lattice shifts of the price, by integer induction. -/

/-- The price along the kernel, for every integer multiple. -/
theorem twosP_U_int (k : ℕ) (i : ℤ) (x y : ℤ) :
    twosP k (x + i * (2 * (k : ℤ) + 5), y + i * (2 * (k : ℤ) + 3)) = twosP k (x, y) - i := by
  induction i using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have h := twosP_U k (x + (n : ℤ) * (2 * (k : ℤ) + 5)) (y + (n : ℤ) * (2 * (k : ℤ) + 3))
    have e1 : x + ((n : ℤ) + 1) * (2 * (k : ℤ) + 5) = x + (n : ℤ) * (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 5) := by ring
    have e2 : y + ((n : ℤ) + 1) * (2 * (k : ℤ) + 3) = y + (n : ℤ) * (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) := by ring
    rw [e1, e2, h, ih]
    ring
  | pred n ih =>
    have e1 : x + (-(n : ℤ) - 1) * (2 * (k : ℤ) + 5) = (x + (-(n : ℤ)) * (2 * (k : ℤ) + 5)) - (2 * (k : ℤ) + 5) := by ring
    have e2 : y + (-(n : ℤ) - 1) * (2 * (k : ℤ) + 3) = (y + (-(n : ℤ)) * (2 * (k : ℤ) + 3)) - (2 * (k : ℤ) + 3) := by ring
    rw [e1, e2, twosP_negU k _ _, ih]
    ring

/-! ### Transport along aliases, and the price of the twos policy. -/

/-- The inverse vertical shift. -/
theorem twosP_negV (k : ℕ) (x y : ℤ) :
    twosP k (x - (-2), y - (4 * (k : ℤ) + 8)) = twosP k (x, y) := by
  have h := twosP_V k (x - (-2)) (y - (4 * (k : ℤ) + 8))
  have e1 : x - (-2) + (-2) = x := by ring
  have e2 : y - (4 * (k : ℤ) + 8) + (4 * (k : ℤ) + 8) = y := by ring
  rw [e1, e2] at h
  exact h.symm

/-- The price along the transverse, for every integer multiple. -/
theorem twosP_V_int (k : ℕ) (l : ℤ) (x y : ℤ) :
    twosP k (x + l * (-2), y + l * (4 * (k : ℤ) + 8)) = twosP k (x, y) := by
  induction l using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have h := twosP_V k (x + (n : ℤ) * (-2)) (y + (n : ℤ) * (4 * (k : ℤ) + 8))
    have e1 : x + ((n : ℤ) + 1) * (-2) = x + (n : ℤ) * (-2) + (-2) := by ring
    have e2 : y + ((n : ℤ) + 1) * (4 * (k : ℤ) + 8) = y + (n : ℤ) * (4 * (k : ℤ) + 8) + (4 * (k : ℤ) + 8) := by ring
    rw [e1, e2, h, ih]
  | pred n ih =>
    have e1 : x + (-(n : ℤ) - 1) * (-2) = (x + (-(n : ℤ)) * (-2)) - (-2) := by ring
    have e2 : y + (-(n : ℤ) - 1) * (4 * (k : ℤ) + 8) = (y + (-(n : ℤ)) * (4 * (k : ℤ) + 8)) - (4 * (k : ℤ) + 8) := by ring
    rw [e1, e2, twosP_negV k _ _, ih]

/-- **The shift along an alias.** For the lattice vector `(p, q)`, the translate of `(x, y)` has price `P(x, y) + p`. -/
theorem twosP_shift (k : ℕ) (p q x y : ℤ) :
    twosP k (x - p * (2 * (k : ℤ) + 4 + 1) + 2 * q, y - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q) =
      twosP k (x, y) + p := by
  have h1 := twosP_U_int k (-p) x y
  have h2 := twosP_V_int k (-q) (x + (-p) * (2 * (k : ℤ) + 5)) (y + (-p) * (2 * (k : ℤ) + 3))
  have e1 : x - p * (2 * (k : ℤ) + 4 + 1) + 2 * q = x + (-p) * (2 * (k : ℤ) + 5) + (-q) * (-2) := by ring
  have e2 : y - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q =
      y + (-p) * (2 * (k : ℤ) + 3) + (-q) * (4 * (k : ℤ) + 8) := by ring
  rw [e1, e2, h2, h1]
  ring

/-- Transport of a price comparison along an alias. -/
theorem twosP_le_of_alias (k : ℕ) (p q i1 i2 c1 c2 u1 u2 j1 j2 : ℤ)
    (hu1 : u1 = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q)
    (hu2 : u2 = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q)
    (hj1 : j1 = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q)
    (hj2 : j2 = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q)
    (h : twosP k (j1, j2) ≤ twosP k (u1, u2)) :
    twosP k (i1, i2) ≤ twosP k (c1, c2) := by
  have a1 := twosP_shift k p q i1 i2
  have a2 := twosP_shift k p q c1 c2
  rw [← hj1, ← hj2] at a1
  rw [← hu1, ← hu2] at a2
  linarith

/-- **The primitive price does not increase along the selected inputs of the twos signed policy.** -/
theorem twosP_nonincreasing (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {η : ℤ} (hη : η = 1 ∨ η = -1) {c i : Site}
    (hT : TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) c i) :
    twosP k i ≤ twosP k c := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨i1, i2⟩ := i
  have ha2 : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  have hvalid := ladderOdd_valid_twos k
  rcases hT with ⟨hl, he⟩ | ⟨hl, ⟨u, hu, hF, hi⟩ | ⟨hnf, u, hu, hn, hg, hi⟩⟩
  · -- black centres: both inputs are kept, and the native copy is black too
    obtain ⟨u, hA, hn⟩ := native_copy_exists ha2 hvalid (c1, c2)
    have hlu := laplacian_twos_alias hagree hperiod hA
    obtain ⟨u1, u2⟩ := u
    obtain ⟨p, q, hpq⟩ := hA
    have hu1 : u1 = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := congrArg Prod.fst hpq
    have hu2 : u2 = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := congrArg Prod.snd hpq
    have hlu' : laplacian (standardField (List.replicate (k + 1) Digit.two)) (u1, u2) = -1 := by
      rw [hlu]; exact hl
    obtain ⟨j1, hj1⟩ : ∃ j : ℤ, j = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := ⟨_, rfl⟩
    obtain ⟨j2, hj2⟩ : ∃ j : ℤ, j = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := ⟨_, rfl⟩
    have hμ : (-p * (2 * (k : ℤ) + 4 + 1) + 2 * q + (-p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q)) % 2 = 0 := by
      have e : -p * (2 * (k : ℤ) + 4 + 1) + 2 * q + (-p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q) =
          2 * (-p * (2 * (k : ℤ) + 4) + q - (2 * (k : ℤ) + 4) * q) := by ring
      rw [e]
      exact Int.mul_emod_right _ _
    have hE := (edge_add (i1, i2) (c1, c2) (-p * (2 * (k : ℤ) + 4 + 1) + 2 * q)
      (-p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q) hμ).mpr he
    dsimp only at hE
    have hE' : Edge (j1, j2) (u1, u2) := by
      rw [hj1, hj2, hu1, hu2]
      rw [show i1 + (-p * (2 * (k : ℤ) + 4 + 1) + 2 * q) = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q by ring,
        show i2 + (-p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q) = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q by ring,
        show c1 + (-p * (2 * (k : ℤ) + 4 + 1) + 2 * q) = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q by ring,
        show c2 + (-p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q) = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q by ring] at hE
      exact hE
    have hb := black_mono k hagree hperiod hn hlu' hE'
    exact twosP_le_of_alias k p q i1 i2 c1 c2 u1 u2 j1 j2 hu1 hu2 hj1 hj2 hb
  · -- free centres: the free table at the free alias
    obtain ⟨u1, u2⟩ := u
    obtain ⟨p, q, hpq⟩ := hu
    have hu1 : u1 = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := congrArg Prod.fst hpq
    have hu2 : u2 = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := congrArg Prod.snd hpq
    have hi1 : i1 = c1 + (freeDisp (2 * (k : ℤ) + 4) η u1 u2).1 := congrArg Prod.fst hi
    have hi2 : i2 = c2 + (freeDisp (2 * (k : ℤ) + 4) η u1 u2).2 := congrArg Prod.snd hi
    have hfree := free_mono k hη (x := u1) (y := u2) hF
    obtain ⟨j1, hj1⟩ : ∃ j : ℤ, j = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := ⟨_, rfl⟩
    obtain ⟨j2, hj2⟩ : ∃ j : ℤ, j = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := ⟨_, rfl⟩
    have hj1' : j1 = u1 + (freeDisp (2 * (k : ℤ) + 4) η u1 u2).1 := by
      rw [hj1, hi1]; linarith
    have hj2' : j2 = u2 + (freeDisp (2 * (k : ℤ) + 4) η u1 u2).2 := by
      rw [hj2, hi2]; linarith
    have hb : twosP k (j1, j2) ≤ twosP k (u1, u2) := by
      rw [hj1', hj2']; exact hfree
    exact twosP_le_of_alias k p q i1 i2 c1 c2 u1 u2 j1 j2 hu1 hu2 hj1 hj2 hb
  · -- non-free centres: the candidate displacement at the native copy
    obtain ⟨u1, u2⟩ := u
    obtain ⟨p, q, hpq⟩ := hu
    have hu1 : u1 = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := congrArg Prod.fst hpq
    have hu2 : u2 = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := congrArg Prod.snd hpq
    have hi1 : i1 = c1 + (candDisp (2 * (k : ℤ) + 4) u1 u2).1 := congrArg Prod.fst hi
    have hi2 : i2 = c2 + (candDisp (2 * (k : ℤ) + 4) u1 u2).2 := congrArg Prod.snd hi
    have hcand := cand_mono k (x := u1) (y := u2) hn hg
    obtain ⟨j1, hj1⟩ : ∃ j : ℤ, j = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := ⟨_, rfl⟩
    obtain ⟨j2, hj2⟩ : ∃ j : ℤ, j = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := ⟨_, rfl⟩
    have hj1' : j1 = u1 + (candDisp (2 * (k : ℤ) + 4) u1 u2).1 := by
      rw [hj1, hi1]; linarith
    have hj2' : j2 = u2 + (candDisp (2 * (k : ℤ) + 4) u1 u2).2 := by
      rw [hj2, hi2]; linarith
    have hb : twosP k (j1, j2) ≤ twosP k (u1, u2) := by
      rw [hj1', hj2']; exact hcand
    exact twosP_le_of_alias k p q i1 i2 c1 c2 u1 u2 j1 j2 hu1 hu2 hj1 hj2 hb

end FLatticePaper.TwosEPolicy

