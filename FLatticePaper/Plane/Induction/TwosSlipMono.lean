import FLatticePaper.Plane.Induction.TwosPriceMono
import FLatticePaper.Plane.Induction.TwosSlipLattice

/-! Task 72 / twos base: the slip `D = F(z) − F(z + σ)` (sign `η = +1`) does not increase along the selected inputs of the
twos signed policy, and the rounded slip `J = (D + 1)/2` does not increase either.

On the key set (`TwosKey`) the slip takes the three values `0, 1, 2` on the bands `TwosSlipZ0`, `TwosSlipZ2` (`twos_slip_value`).
Along a lattice translate the slip moves by `2j` (`twosSlip_lattice`), so a difference of slips is invariant under lattice
translation, and a selected edge reduces to a native pair with two band implications: `Z2` of the input gives `Z2` of the
centre, and `¬ Z0` of the input gives `¬ Z0` of the centre. The black, free and candidate branches are those of the price
(`TwosPriceMono`), with the same family table and the same white-strip hypotheses. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey

/-- The shift by `V` raises the slip by `2`. -/
theorem twosSlip_V (k : ℕ) (x y : ℤ) :
    twosSlip k (x + (-2), y + (4 * (k : ℤ) + 8)) = twosSlip k (x, y) + 2 :=
  twosSlip_add_V k (x, y)

/-- The shift by `U` does not change the slip. -/
theorem twosSlip_U (k : ℕ) (x y : ℤ) :
    twosSlip k (x + (2 * (k : ℤ) + 5), y + (2 * (k : ℤ) + 3)) = twosSlip k (x, y) := by
  have h := twosSlip_lattice k (x, y) 1 0
  have e : ((x, y) : ℤ × ℤ) + (1 * (2 * (k : ℤ) + 5) + 0 * (-2), 1 * (2 * (k : ℤ) + 3) + 0 * (4 * (k : ℤ) + 8)) =
      (x + (2 * (k : ℤ) + 5), y + (2 * (k : ℤ) + 3)) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  rw [e] at h
  linarith

/-- A shift by `V` does not change the comparison of slips (both sides rise by `2`). -/
theorem twosSlip_le_of_V {k : ℕ} {x y p q : ℤ}
    (h : twosSlip k (p + (-2), q + (4 * (k : ℤ) + 8)) ≤ twosSlip k (x + (-2), y + (4 * (k : ℤ) + 8))) :
    twosSlip k (p, q) ≤ twosSlip k (x, y) := by
  have h1 := twosSlip_V k p q
  have h2 := twosSlip_V k x y
  linarith

/-- A shift by `U` does not change the comparison of slips. -/
theorem twosSlip_le_of_U {k : ℕ} {x y p q : ℤ}
    (h : twosSlip k (p + (2 * (k : ℤ) + 5), q + (2 * (k : ℤ) + 3)) ≤
      twosSlip k (x + (2 * (k : ℤ) + 5), y + (2 * (k : ℤ) + 3))) :
    twosSlip k (p, q) ≤ twosSlip k (x, y) := by
  rw [twosSlip_U k p q, twosSlip_U k x y] at h
  exact h

/-- **The two band implications bound the slip.** On key points, the slip of the input `y` does not exceed the slip of the
centre `x` when `Z2` of the input gives `Z2` of the centre and `¬ Z0` of the input gives `¬ Z0` of the centre. -/
theorem twosSlip_le_of_bands (k : ℕ) {x y : ℤ × ℤ} (hx : TwosKey (2 * (k : ℤ) + 4) x.1 x.2)
    (hy : TwosKey (2 * (k : ℤ) + 4) y.1 y.2)
    (h2 : TwosSlipZ2 (2 * (k : ℤ) + 4) y.1 y.2 → TwosSlipZ2 (2 * (k : ℤ) + 4) x.1 x.2)
    (h0 : ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) y.1 y.2 → ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) x.1 x.2) :
    twosSlip k y ≤ twosSlip k x := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  dsimp only at hx hy h2 h0 ⊢
  have disj : ∀ z1 z2 : ℤ, TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2 → ¬ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2 := by
    intro z1 z2 hz0 hz2
    unfold TwosSlipZ0 at hz0
    unfold TwosSlipZ2 at hz2
    omega
  rcases twos_slip_value k hy with ⟨hy0, hyZ0⟩ | ⟨hy1, hyn0, _⟩ | ⟨hy2, hyZ2⟩ <;>
    rcases twos_slip_value k hx with ⟨hx0, hxZ0⟩ | ⟨hx1, _, hxn2⟩ | ⟨hx2, hxZ2⟩
  · omega
  · omega
  · omega
  · exact absurd hxZ0 (h0 hyn0)
  · omega
  · omega
  · exact absurd (h2 hyZ2) (disj _ _ hxZ0)
  · exact absurd (h2 hyZ2) hxn2
  · omega

/-! ### Transport of the slip along aliases. -/

/-- **The shift of the slip along an alias.** The lattice vector `(-p)U + (-q)V` lowers the slip by `2q`. -/
theorem twosSlip_shift (k : ℕ) (p q x y : ℤ) :
    twosSlip k (x - p * (2 * (k : ℤ) + 4 + 1) + 2 * q, y - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q) =
      twosSlip k (x, y) - 2 * q := by
  have h := twosSlip_lattice k (x, y) (-p) (-q)
  have e : ((x, y) : ℤ × ℤ) + ((-p) * (2 * (k : ℤ) + 5) + (-q) * (-2), (-p) * (2 * (k : ℤ) + 3) + (-q) * (4 * (k : ℤ) + 8)) =
      (x - p * (2 * (k : ℤ) + 4 + 1) + 2 * q, y - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  rw [e] at h
  linarith

/-- Transport of a slip comparison along an alias. -/
theorem twosSlip_le_of_alias (k : ℕ) (p q i1 i2 c1 c2 u1 u2 j1 j2 : ℤ)
    (hu1 : u1 = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q)
    (hu2 : u2 = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q)
    (hj1 : j1 = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q)
    (hj2 : j2 = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q)
    (h : twosSlip k (j1, j2) ≤ twosSlip k (u1, u2)) :
    twosSlip k (i1, i2) ≤ twosSlip k (c1, c2) := by
  have a1 := twosSlip_shift k p q i1 i2
  have a2 := twosSlip_shift k p q c1 c2
  rw [← hj1, ← hj2] at a1
  rw [← hu1, ← hu2] at a2
  linarith

/-! ### The candidate branch for the slip. -/

/-- The candidate displacement on the low band, below the middle row: the input is `(x, y-1)`. -/
theorem candD_mono_low_down (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hL : CandLow (2 * (k : ℤ) + 4) x y) (hm : y < 2 * (k : ℤ) + 4 - 1) :
    twosSlip k (x + 0, y + -1) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (twosKey_of_native hn) ?_ ?_ ?_
  · unfold TwosKey; unfold CandLow NativeT at *; omega
  · intro h; unfold TwosSlipZ2 at *; unfold CandLow NativeT at *; omega
  · intro h; unfold TwosSlipZ0 at *; unfold CandLow NativeT at *; omega

/-- The candidate displacement on the low band, above the middle row: the input is `(x, y+1)`. -/
theorem candD_mono_low_up (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hL : CandLow (2 * (k : ℤ) + 4) x y) (hm : ¬ y < 2 * (k : ℤ) + 4 - 1) :
    twosSlip k (x + 0, y + 1) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (twosKey_of_native hn) ?_ ?_ ?_
  · unfold TwosKey; unfold CandLow NativeT at *; omega
  · intro h; unfold TwosSlipZ2 at *; unfold CandLow NativeT at *; omega
  · intro h; unfold TwosSlipZ0 at *; unfold CandLow NativeT at *; omega

/-- The candidate displacement on the high band, below the middle row `2a-1`: the input is `(x, y-1)`. -/
theorem candD_mono_high_down (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hH : CandHigh (2 * (k : ℤ) + 4) x y) (hm : y < 2 * (2 * (k : ℤ) + 4) - 1) :
    twosSlip k (x + 0, y + -1) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (twosKey_of_native hn) ?_ ?_ ?_
  · unfold TwosKey; unfold CandHigh NativeT at *; omega
  · intro h; unfold TwosSlipZ2 at *; unfold CandHigh NativeT at *; omega
  · intro h; unfold TwosSlipZ0 at *; unfold CandHigh NativeT at *; omega

/-- The candidate displacement on the high band, above the middle row: the input is `(x, y+1)`. -/
theorem candD_mono_high_up (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hH : CandHigh (2 * (k : ℤ) + 4) x y) (hm : ¬ y < 2 * (2 * (k : ℤ) + 4) - 1) :
    twosSlip k (x + 0, y + 1) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (twosKey_of_native hn) ?_ ?_ ?_
  · unfold TwosKey; unfold CandHigh NativeT at *; omega
  · intro h; unfold TwosSlipZ2 at *; unfold CandHigh NativeT at *; omega
  · intro h; unfold TwosSlipZ0 at *; unfold CandHigh NativeT at *; omega

/-- The east diagonal: the input is `(x+1, y)`. -/
theorem candD_mono_E (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hE : CandE (2 * (k : ℤ) + 4) x y) : twosSlip k (x + 1, y + 0) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (twosKey_of_native hn) ?_ ?_ ?_
  · unfold TwosKey; unfold CandE NativeT at *; omega
  · intro h; unfold TwosSlipZ2 at *; unfold CandE NativeT at *; omega
  · intro h; unfold TwosSlipZ0 at *; unfold CandE NativeT at *; omega

/-- The west diagonal: the input is `(x-1, y)`. -/
theorem candD_mono_W (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hW : CandW (2 * (k : ℤ) + 4) x y) : twosSlip k (x + -1, y + 0) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (twosKey_of_native hn) ?_ ?_ ?_
  · unfold TwosKey; unfold CandW NativeT at *; omega
  · intro h; unfold TwosSlipZ2 at *; unfold CandW NativeT at *; omega
  · intro h; unfold TwosSlipZ0 at *; unfold CandW NativeT at *; omega

/-- **The candidate branch.** At a native candidate centre under the candidate guard, the candidate input does not raise the
price. -/
theorem candD_mono (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hg : CandGuard (2 * (k : ℤ) + 4) x y) :
    twosSlip k (x + (candDisp (2 * (k : ℤ) + 4) x y).1, y + (candDisp (2 * (k : ℤ) + 4) x y).2) ≤ twosSlip k (x, y) := by
  rcases hg with hL | hH | hE | hW
  · by_cases hm : y < 2 * (k : ℤ) + 4 - 1
    · rw [candDisp_low_down hL hm]; exact candD_mono_low_down k hn hL hm
    · rw [candDisp_low_up hL hm]; exact candD_mono_low_up k hn hL hm
  · by_cases hm : y < 2 * (2 * (k : ℤ) + 4) - 1
    · rw [candDisp_high_down hH hm]; exact candD_mono_high_down k hn hH hm
    · rw [candDisp_high_up hH hm]; exact candD_mono_high_up k hn hH hm
  · rw [candDisp_E hE]; exact candD_mono_E k hn hE
  · rw [candDisp_W hW]; exact candD_mono_W k hn hW


/-! ### The free branch for the slip. -/

/-- Free family `p/H0` (sign 1): the displacement `(0, -1)`, shift `V`. -/
theorem freeD_p_H0 (k : ℕ) {x y : ℤ} (h : x = 1 ∧ y = 0) :
    twosSlip k (x + (0), y + (-1)) ≤ twosSlip k (x, y) := by
  apply twosSlip_le_of_V
  refine twosSlip_le_of_bands k (x := (x + -2, y + (4 * (k : ℤ) + 8))) (y := (x + (0) + -2, y + (-1) + (4 * (k : ℤ) + 8))) ?_ ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ2 at *; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ0 at *; omega

/-- Free family `p/Hlt` (sign 1): the displacement `(1, 0)`, shift `V`. -/
theorem freeD_p_Hlt (k : ℕ) {x y : ℤ} (h : 2 ≤ x ∧ x ≤ 2 * (k : ℤ) + 3 ∧ y = x - 2) :
    twosSlip k (x + (1), y + (0)) ≤ twosSlip k (x, y) := by
  apply twosSlip_le_of_V
  refine twosSlip_le_of_bands k (x := (x + -2, y + (4 * (k : ℤ) + 8))) (y := (x + (1) + -2, y + (0) + (4 * (k : ℤ) + 8))) ?_ ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ2 at *; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ0 at *; omega

/-- Free family `p/Heq` (sign 1): the displacement `(1, 0)`, shift `0`. -/
theorem freeD_p_Heq (k : ℕ) {x y : ℤ} (h : x = 2 * (k : ℤ) + 4 ∧ y = 2 * (k : ℤ) + 2) :
    twosSlip k (x + (1), y + (0)) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (x := (x, y)) (y := (x + (1), y + (0))) ?_ ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ2 at *; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ0 at *; omega

/-- Free family `p/Hodd` (sign 1): the displacement `(0, 1)`, shift `0`. -/
theorem freeD_p_Hodd (k : ℕ) {x y : ℤ} (h : x = 2 * (k : ℤ) + 5 ∧ y = 2 * (k : ℤ) + 2) :
    twosSlip k (x + (0), y + (1)) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (x := (x, y)) (y := (x + (0), y + (1))) ?_ ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ2 at *; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ0 at *; omega

/-- Free family `p/V0` (sign 1): the displacement `(1, 0)`, shift `0`. -/
theorem freeD_p_V0 (k : ℕ) {x y : ℤ} (h : x = 0 ∧ y = 0) :
    twosSlip k (x + (1), y + (0)) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (x := (x, y)) (y := (x + (1), y + (0))) ?_ ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ2 at *; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ0 at *; omega

/-- Free family `p/Ve0` (sign 1): the displacement `(1, 0)`, shift `0`. -/
theorem freeD_p_Ve0 (k : ℕ) {x y : ℤ} (h : x = 0 ∧ 0 < y ∧ y < 2 * (k : ℤ) + 4 ∧ (y % 2 = 0)) :
    twosSlip k (x + (1), y + (0)) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (x := (x, y)) (y := (x + (1), y + (0))) ?_ ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ2 at *; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ0 at *; omega

/-- Free family `p/Vo0` (sign 1): the displacement `(0, -1)`, shift `0`. -/
theorem freeD_p_Vo0 (k : ℕ) {x y : ℤ} (h : x = 0 ∧ 0 < y ∧ y < 2 * (k : ℤ) + 4 ∧ (y % 2 = 1)) :
    twosSlip k (x + (0), y + (-1)) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (x := (x, y)) (y := (x + (0), y + (-1))) ?_ ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ2 at *; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ0 at *; omega

/-- Free family `p/Ve1` (sign 1): the displacement `(1, 0)`, shift `0`. -/
theorem freeD_p_Ve1 (k : ℕ) {x y : ℤ} (h : x = -1 ∧ 2 * (k : ℤ) + 4 ≤ y ∧ y < 2 * (2 * (k : ℤ) + 4) ∧ (y % 2 = 1)) :
    twosSlip k (x + (1), y + (0)) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (x := (x, y)) (y := (x + (1), y + (0))) ?_ ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ2 at *; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ0 at *; omega

/-- Free family `p/Vo1a` (sign 1): the displacement `(0, -1)`, shift `U`. -/
theorem freeD_p_Vo1a (k : ℕ) {x y : ℤ} (h : x = -1 ∧ y = 2 * (k : ℤ) + 4) :
    twosSlip k (x + (0), y + (-1)) ≤ twosSlip k (x, y) := by
  apply twosSlip_le_of_U
  refine twosSlip_le_of_bands k (x := (x + (2 * (k : ℤ) + 5), y + (2 * (k : ℤ) + 3))) (y := (x + (0) + (2 * (k : ℤ) + 5), y + (-1) + (2 * (k : ℤ) + 3))) ?_ ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ2 at *; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ0 at *; omega

/-- Free family `p/Vo1` (sign 1): the displacement `(0, -1)`, shift `0`. -/
theorem freeD_p_Vo1 (k : ℕ) {x y : ℤ} (h : x = -1 ∧ 2 * (k : ℤ) + 4 < y ∧ y < 2 * (2 * (k : ℤ) + 4) ∧ (y % 2 = 0)) :
    twosSlip k (x + (0), y + (-1)) ≤ twosSlip k (x, y) := by
  refine twosSlip_le_of_bands k (x := (x, y)) (y := (x + (0), y + (-1))) ?_ ?_ ?_ ?_
  · dsimp only; unfold TwosKey; omega
  · dsimp only; unfold TwosKey; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ2 at *; omega
  · intro h; dsimp only at h ⊢; unfold TwosSlipZ0 at *; omega


/-- **The free branch for the slip.** At a free site the free displacement of sign `+1` does not raise the slip. -/
theorem freeD_mono (k : ℕ) {x y : ℤ} (hF : FreeSite (2 * (k : ℤ) + 4) x y) :
    twosSlip k (x + (freeDisp (2 * (k : ℤ) + 4) 1 x y).1, y + (freeDisp (2 * (k : ℤ) + 4) 1 x y).2) ≤
      twosSlip k (x, y) := by
  have hF' := hF
  unfold FreeSite FreeHSite FreeVSite at hF'
  · rcases hF' with (h | h | h) | (h | h)
    · rw [freeDisp_H0 h]; exact freeD_p_H0 k h
    · rw [freeDisp_Heven (by unfold FreeHSite; omega) (by omega) (by unfold EvenSite; dsimp only; omega)]
      by_cases hea : x = 2 * (k : ℤ) + 4
      · exact freeD_p_Heq k ⟨hea, by omega⟩
      · exact freeD_p_Hlt k ⟨by omega, by omega, by omega⟩
    · rw [freeDisp_Hodd (by unfold FreeHSite; omega) (by omega) (by unfold EvenSite; dsimp only; omega)]
      exact freeD_p_Hodd k ⟨by omega, by omega⟩
    · by_cases hz : x = 0 ∧ y = 0
      · rw [freeDisp_V0 hz]; exact freeD_p_V0 k hz
      · by_cases he : EvenSite (x, y)
        · rw [freeDisp_Veven (by unfold FreeVSite; omega) hz he]
          exact freeD_p_Ve0 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
        · rw [freeDisp_Vodd (by unfold FreeVSite; omega) hz he]
          exact freeD_p_Vo0 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
    · by_cases he : EvenSite (x, y)
      · rw [freeDisp_Veven (by unfold FreeVSite; omega) (by omega) he]
        exact freeD_p_Ve1 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
      · rw [freeDisp_Vodd (by unfold FreeVSite; omega) (by omega) he]
        by_cases hay : y = 2 * (k : ℤ) + 4
        · exact freeD_p_Vo1a k ⟨by omega, hay⟩
        · exact freeD_p_Vo1 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩


/-! ### The black branch for the slip. -/

/-- The edge cases of an odd centre. -/
theorem edge_odd_cases (x y j1 j2 : ℤ) (h : ¬ EvenSite (x, y)) (he : Edge (j1, j2) (x, y)) :
    (j1 = x ∧ j2 = y - 1) ∨ (j1 = x ∧ j2 = y + 1) := by
  unfold Edge incomingNeg incomingPos at he
  simp only [if_neg h] at he
  rcases he with he | he
  · exact Or.inl (Prod.mk.inj he)
  · exact Or.inr (Prod.mk.inj he)

/-- The ten white strips of an even centre, as negations (from `¬ LadderOddOddWhite`). -/
theorem even_negs (k : ℕ) {x y : ℤ}
    (hW : ¬ LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1)) :
    ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2) ∧
    ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1) ∧
    ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4)) ∧
    ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3) ∧
    ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3) ∧
    ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2) ∧
    ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2) ∧
    ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4)) ∧
    ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4)) ∧
    ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2) := by
  exact ⟨fun h => hW (ow_of_regions k (Or.inl h)),
    fun h => hW (ow_of_regions k (Or.inr (Or.inl h))),
    fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inl h)))),
    fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inl h))))),
    fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))),
    fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),
    fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))),
    fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))),
    fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))),
    fun h => hW (ow_of_regions k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))))))))⟩

set_option maxHeartbeats 400000 in
/-- The left input `(x-1, y)` of an even black centre: the slip bands. -/
theorem even_left_D (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (_n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2)) (_n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1)) (_n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4))) (_n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3)) (_n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (_n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2)) (_n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2)) (_n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4))) (_n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4))) (_n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2)) :
    (TwosSlipZ2 (2 * (k : ℤ) + 4) (x - 1) y → TwosSlipZ2 (2 * (k : ℤ) + 4) x y) ∧
      (¬ TwosSlipZ0 (2 * (k : ℤ) + 4) (x - 1) y → ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) x y) := by
  unfold NativeT at hn
  constructor
  · intro h
    rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> (unfold TwosSlipZ2 at *; omega)
  · intro h
    rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> (unfold TwosSlipZ0 at *; omega)

set_option maxHeartbeats 400000 in
/-- The right input `(x+1, y)` of an even black centre: the slip bands. -/
theorem even_right_D (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (_n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2)) (_n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1)) (_n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4))) (_n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3)) (_n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (_n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2)) (_n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2)) (_n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4))) (_n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4))) (_n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2)) :
    (TwosSlipZ2 (2 * (k : ℤ) + 4) (x + 1) y → TwosSlipZ2 (2 * (k : ℤ) + 4) x y) ∧
      (¬ TwosSlipZ0 (2 * (k : ℤ) + 4) (x + 1) y → ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) x y) := by
  unfold NativeT at hn
  constructor
  · intro h
    rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> (unfold TwosSlipZ2 at *; omega)
  · intro h
    rcases hn with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ | h8 | h9 <;> (unfold TwosSlipZ0 at *; omega)

set_option maxHeartbeats 400000 in
/-- **The slip claims at an odd black centre.** The rotated point is even, so the black condition is `LadderOddEvenBlack`. -/
theorem black_key_odd_D (k : ℕ) {x y j1 j2 : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : ¬ EvenSite (x, y))
    (hB : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1))
    (he : Edge (j1, j2) (x, y)) :
    (TwosSlipZ2 (2 * (k : ℤ) + 4) j1 j2 → TwosSlipZ2 (2 * (k : ℤ) + 4) x y) ∧
      (¬ TwosSlipZ0 (2 * (k : ℤ) + 4) j1 j2 → ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) x y) := by
  rcases edge_odd_cases x y j1 j2 hp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
  all_goals
    unfold LadderOddEvenBlack at hB
    try dsimp only at hB
    unfold NativeT at hn
    constructor
    · intro h
      unfold TwosSlipZ2 at *
      omega
    · intro h
      unfold TwosSlipZ0 at *
      omega

set_option maxHeartbeats 400000 in
/-- **The slip claims at an even black centre**, from the ten white strips and the two even inputs. -/
theorem black_key_even_D (k : ℕ) {x y j1 j2 : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : EvenSite (x, y))
    (hW : ¬ LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1))
    (he : Edge (j1, j2) (x, y)) :
    TwosKey (2 * (k : ℤ) + 4) j1 j2 ∧
      (TwosSlipZ2 (2 * (k : ℤ) + 4) j1 j2 → TwosSlipZ2 (2 * (k : ℤ) + 4) x y) ∧
      (¬ TwosSlipZ0 (2 * (k : ℤ) + 4) j1 j2 → ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) x y) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := even_negs k hW
  have hp' : (x + y) % 2 = 0 := hp
  rcases edge_even_cases x y j1 j2 hp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1
    subst h2
    exact ⟨(even_left_key k hn hp' n1 n2 n3 n4 n5 n6 n7 n8 n9 n10).1,
      even_left_D k hn hp' n1 n2 n3 n4 n5 n6 n7 n8 n9 n10⟩
  · subst h1
    subst h2
    exact ⟨(even_right_key k hn hp' n1 n2 n3 n4 n5 n6 n7 n8 n9 n10).1,
      even_right_D k hn hp' n1 n2 n3 n4 n5 n6 n7 n8 n9 n10⟩

/-- **The black branch for the slip.** A native centre of charge `-1` does not raise the slip along its incoming inputs. -/
theorem black_D (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y j1 j2 : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hl : laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = -1)
    (he : Edge (j1, j2) (x, y)) :
    twosSlip k (j1, j2) ≤ twosSlip k (x, y) := by
  have hR := black_region_of_lap k hagree hperiod hn hl
  obtain ⟨hK, hB2, hB0⟩ : TwosKey (2 * (k : ℤ) + 4) j1 j2 ∧
      (TwosSlipZ2 (2 * (k : ℤ) + 4) j1 j2 → TwosSlipZ2 (2 * (k : ℤ) + 4) x y) ∧
      (¬ TwosSlipZ0 (2 * (k : ℤ) + 4) j1 j2 → ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) x y) := by
    by_cases hp : EvenSite (x, y)
    · have hW : ¬ LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
        rcases hR with ⟨hE, _⟩ | ⟨_, hW⟩
        · exact absurd ((evenSite_rot (2 * (k : ℤ) + 4) x y).mp hE) (not_not.mpr hp)
        · exact hW
      exact black_key_even_D k hn hp hW he
    · have hB : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
        rcases hR with ⟨_, hB⟩ | ⟨hNE, _⟩
        · exact hB
        · exact absurd ((evenSite_rot (2 * (k : ℤ) + 4) x y).mpr hp) hNE
      exact ⟨(black_key_odd k hn hp hB he).1, black_key_odd_D k hn hp hB he⟩
  exact twosSlip_le_of_bands k (x := (x, y)) (y := (j1, j2)) (twosKey_of_native hn) hK hB2 hB0

/-! ### The slip of the twos signed policy. -/


theorem twosSlip_nonincreasing (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {c i : Site}
    (hT : TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) c i) :
    twosSlip k i ≤ twosSlip k c := by
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
    have hb := black_D k hagree hperiod hn hlu' hE'
    exact twosSlip_le_of_alias k p q i1 i2 c1 c2 u1 u2 j1 j2 hu1 hu2 hj1 hj2 hb
  · -- free centres: the free table at the free alias
    obtain ⟨u1, u2⟩ := u
    obtain ⟨p, q, hpq⟩ := hu
    have hu1 : u1 = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := congrArg Prod.fst hpq
    have hu2 : u2 = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := congrArg Prod.snd hpq
    have hi1 : i1 = c1 + (freeDisp (2 * (k : ℤ) + 4) 1 u1 u2).1 := congrArg Prod.fst hi
    have hi2 : i2 = c2 + (freeDisp (2 * (k : ℤ) + 4) 1 u1 u2).2 := congrArg Prod.snd hi
    have hfree := freeD_mono k (x := u1) (y := u2) hF
    obtain ⟨j1, hj1⟩ : ∃ j : ℤ, j = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := ⟨_, rfl⟩
    obtain ⟨j2, hj2⟩ : ∃ j : ℤ, j = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := ⟨_, rfl⟩
    have hj1' : j1 = u1 + (freeDisp (2 * (k : ℤ) + 4) 1 u1 u2).1 := by
      rw [hj1, hi1]; linarith
    have hj2' : j2 = u2 + (freeDisp (2 * (k : ℤ) + 4) 1 u1 u2).2 := by
      rw [hj2, hi2]; linarith
    have hb : twosSlip k (j1, j2) ≤ twosSlip k (u1, u2) := by
      rw [hj1', hj2']; exact hfree
    exact twosSlip_le_of_alias k p q i1 i2 c1 c2 u1 u2 j1 j2 hu1 hu2 hj1 hj2 hb
  · -- non-free centres: the candidate displacement at the native copy
    obtain ⟨u1, u2⟩ := u
    obtain ⟨p, q, hpq⟩ := hu
    have hu1 : u1 = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := congrArg Prod.fst hpq
    have hu2 : u2 = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := congrArg Prod.snd hpq
    have hi1 : i1 = c1 + (candDisp (2 * (k : ℤ) + 4) u1 u2).1 := congrArg Prod.fst hi
    have hi2 : i2 = c2 + (candDisp (2 * (k : ℤ) + 4) u1 u2).2 := congrArg Prod.snd hi
    have hcand := candD_mono k (x := u1) (y := u2) hn hg
    obtain ⟨j1, hj1⟩ : ∃ j : ℤ, j = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := ⟨_, rfl⟩
    obtain ⟨j2, hj2⟩ : ∃ j : ℤ, j = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := ⟨_, rfl⟩
    have hj1' : j1 = u1 + (candDisp (2 * (k : ℤ) + 4) u1 u2).1 := by
      rw [hj1, hi1]; linarith
    have hj2' : j2 = u2 + (candDisp (2 * (k : ℤ) + 4) u1 u2).2 := by
      rw [hj2, hi2]; linarith
    have hb : twosSlip k (j1, j2) ≤ twosSlip k (u1, u2) := by
      rw [hj1', hj2']; exact hcand
    exact twosSlip_le_of_alias k p q i1 i2 c1 c2 u1 u2 j1 j2 hu1 hu2 hj1 hj2 hb


/-! ### The rounded slip `J` of the twos policy (sign `+1`). -/

/-- The slip of the frame at sign `+1` is the twos slip. -/
theorem twos_frame_slip_one (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) 1 z =
      twosSlip k z := by
  unfold ChildFrame.slip twosSlip
  rw [one_smul]

/-- The rounded slip of the frame at sign `+1`. -/
theorem twos_roundedSlip_one (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).roundedSlip (standardField (List.replicate (k + 1) Digit.two)) 1 z =
      (twosSlip k z + 1) / 2 := by
  unfold ChildFrame.roundedSlip
  rw [twos_frame_slip_one]

/-- **The rounded slip `J` does not increase along the selected inputs (sign `+1`).** -/
theorem twos_roundedSlip_nonincreasing (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {c i : Site}
    (hT : TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) c i) :
    (frameAt (List.replicate (k + 1) Digit.two)).roundedSlip (standardField (List.replicate (k + 1) Digit.two)) 1 i ≤
      (frameAt (List.replicate (k + 1) Digit.two)).roundedSlip (standardField (List.replicate (k + 1) Digit.two)) 1 c := by
  rw [twos_roundedSlip_one, twos_roundedSlip_one]
  have h := twosSlip_nonincreasing k hagree hperiod hT
  omega

end FLatticePaper.TwosEPolicy
