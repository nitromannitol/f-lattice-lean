import FLatticePaper.Plane.Induction.TwosMinusOddBlack

/-! Twos flatness, sign `-1`, the even black centres: the potential exclusions. On the even black tile points the horizontal
neighbour fails to drop the rank only on four families (`x = 0` with `a+2 ≤ y ≤ 3a/2`; `x = 1` with `y` odd, `2y ≤ a`; the
diagonal `x = y` with `2 ≤ x`, `2x ≤ a+2`; and `(a, a)`). On each family the two sign `-1` potentials differ, by the level
formula `chainM_native_level` and the slip at the points, which are carried into the key region by the kernel shift `U`
(`twosSlip_add_U`). -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- A key point which is in the upper slip band has slip `2`. -/
theorem twosSlip_eq_two_of (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h2 : TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) (h0 : ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2) :
    twosSlip k (z1, z2) = 2 := by
  rcases twos_slip_value k hk with ⟨hs, hz⟩ | ⟨hs, -, hz2⟩ | ⟨hs, hz⟩
  · exact absurd hz h0
  · exact absurd h2 hz2
  · exact hs

/-- A key point which is in the lower slip band has slip `0`. -/
theorem twosSlip_eq_zero_of (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h0 : TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2) (h2 : ¬ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) :
    twosSlip k (z1, z2) = 0 := by
  rcases twos_slip_value k hk with ⟨hs, -⟩ | ⟨hs, hz0, -⟩ | ⟨hs, hz2⟩
  · exact hs
  · unfold TwosSlipZ0 at hz0
    unfold TwosSlipZ0 at h0
    unfold TwosSlipZ2 at h2
    omega
  · exact absurd hz2 h2

/-- The slip at a point `w` is the slip at `w + U` (the kernel shift `U = (2k+5, 2k+3) = (a+1, a-1)`). -/
theorem twosSlip_shift_U (k : ℕ) (w1 w2 : ℤ) :
    twosSlip k (w1 + (2 * (k : ℤ) + 5), w2 + (2 * (k : ℤ) + 3)) = twosSlip k (w1, w2) :=
  twosSlip_add_U k (w1, w2)

/-- The left family `x = 0`: the potential of `(0, y)` is `C-3` and that of `(-1, y)` is `C-4`. -/
theorem even_left_ne_a (k : ℕ) {x y : ℤ} (hx : x = 0) (h1 : 2 * (k : ℤ) + 6 ≤ y) (h2 : 2 * y ≤ 3 * (2 * (k : ℤ) + 4)) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x - 1, y) ≠
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x, y) := by
  subst hx
  have hNp : NativeT (2 * (k : ℤ) + 4) 0 y := by
    unfold NativeT
    omega
  have hNi : NativeT (2 * (k : ℤ) + 4) (0 - 1) y := by
    unfold NativeT
    omega
  rw [chainM_native_level k hNi (by omega), chainM_native_level k hNp (by omega)]
  intro h
  have hkp : TwosKey (2 * (k : ℤ) + 4) (0 - 1) (y - 1) := by
    unfold TwosKey
    omega
  have sp := twosSlip_eq_one_of k hkp (by unfold TwosSlipZ0; omega) (by unfold TwosSlipZ2; omega)
  have hU := twosSlip_shift_U k (0 - 1 - 1) (y - 1)
  have hki : TwosKey (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 - 1) (y + (2 * (k : ℤ) + 4) - 2) := by
    unfold TwosKey
    omega
  have si : twosSlip k (0 - 1 - 1, y - 1) = 2 := by
    rw [← hU]
    rw [show (0 - 1 - 1 : ℤ) + (2 * (k : ℤ) + 5) = 2 * (k : ℤ) + 4 - 1 by ring,
      show (y - 1 : ℤ) + (2 * (k : ℤ) + 3) = y + (2 * (k : ℤ) + 4) - 2 by ring]
    exact twosSlip_eq_two_of k hki (by unfold TwosSlipZ2; omega) (by unfold TwosSlipZ0; omega)
  have dp : ¬ TwosDelta k (0 - 1) (y - 1) := by
    unfold TwosDelta
    omega
  have di : ¬ TwosDelta k (0 - 1 - 1) (y - 1) := by
    unfold TwosDelta
    omega
  rw [if_neg dp, if_neg di, sp, si] at h
  omega

/-- The left family `x = 1`: the potential of `(0, y)` is `C-3` and that of `(1, y)` is `C-2`. -/
theorem even_left_ne_b (k : ℕ) {x y : ℤ} (hx : x = 1) (hy1 : 1 ≤ y) (hy2 : 2 * y ≤ 2 * (k : ℤ) + 4) (hodd : y % 2 = 1) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x - 1, y) ≠
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x, y) := by
  subst hx
  have hNp : NativeT (2 * (k : ℤ) + 4) 1 y := by
    unfold NativeT
    omega
  have hNi : NativeT (2 * (k : ℤ) + 4) (1 - 1) y := by
    unfold NativeT
    omega
  rw [chainM_native_level k hNi (by omega), chainM_native_level k hNp (by omega)]
  intro h
  have sp := twosSlip_eq_zero_of k (z1 := 1 - 1) (z2 := y - 1) (by unfold TwosKey; omega)
    (by unfold TwosSlipZ0; omega) (by unfold TwosSlipZ2; omega)
  have hU := twosSlip_shift_U k (1 - 1 - 1) (y - 1)
  have hki : TwosKey (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4) (y + (2 * (k : ℤ) + 4) - 2) := by
    unfold TwosKey
    omega
  have si : twosSlip k (1 - 1 - 1, y - 1) = 1 := by
    rw [← hU]
    rw [show (1 - 1 - 1 : ℤ) + (2 * (k : ℤ) + 5) = 2 * (k : ℤ) + 4 by ring,
      show (y - 1 : ℤ) + (2 * (k : ℤ) + 3) = y + (2 * (k : ℤ) + 4) - 2 by ring]
    exact twosSlip_eq_one_of k hki (by unfold TwosSlipZ0; omega) (by unfold TwosSlipZ2; omega)
  have dp : ¬ TwosDelta k (1 - 1) (y - 1) := by
    unfold TwosDelta
    omega
  have di : ¬ TwosDelta k (1 - 1 - 1) (y - 1) := by
    unfold TwosDelta
    omega
  rw [if_neg dp, if_neg di, sp, si] at h
  omega

end FLatticePaper.TwosEPolicy
