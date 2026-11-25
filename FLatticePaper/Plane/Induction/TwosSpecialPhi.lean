import FLatticePaper.Plane.Induction.TwosChainMono
import FLatticePaper.Plane.Induction.TwosSlipForm
import FLatticePaper.Plane.Induction.TwosPriceMono
import FLatticePaper.Plane.Induction.TwosFlatReduce
import FLatticePaper.Plane.Induction.TwosFlatClass

/-! Twos flatness, the potential at the three special tile points (sign `+1`), with `C = (k+2)(k+3)`:
`Φ(a, 2a-2) = C`, `Φ(a, 2a-1) = C`, `Φ(a+1, a-2) = C - 1`, where `a = 2k+4`.

Each is `Φ(z) = D(z) + P(z + (1,1)) + 1` (`chainP_eq`), with the slip `D` from the slip band lemmas and the price `P` from the
key-point formula at a lattice translate (`twosP_U`, `twosP_eq_sub`). The levels are `0`, `1 - 1 = 0`-corrected, and `-1`. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The price at `(0, a)` and `(0, a+1)`: both key points with no price band, so the price is `k²+5k+5`. -/
theorem twosP_zero_a (k : ℕ) : twosP k (0, 2 * (k : ℤ) + 4) = (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  have hk : TwosKey (2 * (k : ℤ) + 4) 0 (2 * (k : ℤ) + 4) := by
    unfold TwosKey
    left
    omega
  have hnd : ¬ TwosDelta k 0 (2 * (k : ℤ) + 4) := by
    unfold TwosDelta
    omega
  rw [twosP_eq_sub k hk _ rfl]
  simp only [twosDi, if_neg hnd, sub_zero]

theorem twosP_zero_a1 (k : ℕ) : twosP k (0, 2 * (k : ℤ) + 4 + 1) = (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  have hk : TwosKey (2 * (k : ℤ) + 4) 0 (2 * (k : ℤ) + 4 + 1) := by
    unfold TwosKey
    left
    omega
  have hnd : ¬ TwosDelta k 0 (2 * (k : ℤ) + 4 + 1) := by
    unfold TwosDelta
    omega
  rw [twosP_eq_sub k hk _ rfl]
  simp only [twosDi, if_neg hnd, sub_zero]

/-- `Φ(a, 2a-2) = C`. -/
theorem phi_spec_2a2 (k : ℕ) :
    twosPhi k 1 (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4) - 2) = ((k : ℤ) + 2) * ((k : ℤ) + 3) := by
  unfold twosPhi
  rw [chainP_eq]
  have hD := twos_slip_U_dB k
  have hP := twosP_U k 0 (2 * (k : ℤ) + 4)
  rw [show (0 : ℤ) + (2 * (k : ℤ) + 5) = 2 * (k : ℤ) + 4 + 1 by ring,
    show 2 * (k : ℤ) + 4 + (2 * (k : ℤ) + 3) = 2 * (2 * (k : ℤ) + 4) - 1 by ring,
    twosP_zero_a k] at hP
  dsimp only
  rw [show 2 * (2 * (k : ℤ) + 4) - 2 + 1 = 2 * (2 * (k : ℤ) + 4) - 1 by ring, hD, hP]
  ring

/-- `Φ(a, 2a-1) = C`: the slip is `1` (neither band), the price at `(a+1, 2a)` is `k²+5k+4`. -/
theorem phi_spec_2a1 (k : ℕ) :
    twosPhi k 1 (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4) - 1) = ((k : ℤ) + 2) * ((k : ℤ) + 3) := by
  unfold twosPhi
  rw [chainP_eq]
  have hD : twosSlip k (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4) - 1) = 1 := by
    rcases twos_slip_U_dhi k (2 * (2 * (k : ℤ) + 4) - 1) (by omega) (by omega) with
      ⟨h, h0⟩ | ⟨h, -, -⟩ | ⟨h, h2⟩
    · exfalso
      unfold TwosSlipZ0 at h0
      omega
    · exact h
    · exfalso
      unfold TwosSlipZ2 at h2
      omega
  have hP := twosP_U k 0 (2 * (k : ℤ) + 4 + 1)
  rw [show (0 : ℤ) + (2 * (k : ℤ) + 5) = 2 * (k : ℤ) + 4 + 1 by ring,
    show 2 * (k : ℤ) + 4 + 1 + (2 * (k : ℤ) + 3) = 2 * (2 * (k : ℤ) + 4) by ring,
    twosP_zero_a1 k] at hP
  dsimp only
  rw [show 2 * (2 * (k : ℤ) + 4) - 1 + 1 = 2 * (2 * (k : ℤ) + 4) by ring, hD, hP]
  ring

/-- `Φ(a+1, a-2) = C - 1`: the slip is `0` (`twos_slip_U_dp1lo`), the price at `(a+2, a-1)` is `k²+5k+4`. -/
theorem phi_spec_ap1 (k : ℕ) :
    twosPhi k 1 (2 * (k : ℤ) + 4 + 1, 2 * (k : ℤ) + 4 - 2) = ((k : ℤ) + 2) * ((k : ℤ) + 3) - 1 := by
  unfold twosPhi
  rw [chainP_eq]
  have hD := twos_slip_U_dp1lo k
  have hk1 : TwosKey (2 * (k : ℤ) + 4) 1 0 := by
    unfold TwosKey
    left
    omega
  have hnd : ¬ TwosDelta k 1 0 := by
    unfold TwosDelta
    omega
  have hP10 : twosP k (1, 0) = (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
    rw [twosP_eq_sub k hk1 _ rfl]
    simp only [twosDi, if_neg hnd, sub_zero]
  have hP := twosP_U k 1 0
  rw [show (1 : ℤ) + (2 * (k : ℤ) + 5) = 2 * (k : ℤ) + 4 + 1 + 1 by ring,
    show (0 : ℤ) + (2 * (k : ℤ) + 3) = 2 * (k : ℤ) + 4 - 1 by ring, hP10] at hP
  dsimp only
  rw [show 2 * (k : ℤ) + 4 - 2 + 1 = 2 * (k : ℤ) + 4 - 1 by ring, hD, hP]
  ring

/-- The special right neighbour `(a, 2a-1)` of `(a-1, 2a-1)` is never flat: the levels `0` and `1` differ. -/
theorem right_special_nonflat {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4)
    (hp : TwosTile a (a - 1, 2 * a - 1))
    (hΦ : twosPhi k 1 (a, 2 * a - 1) = twosPhi k 1 (a - 1, 2 * a - 1)) : False := by
  have ep := phi_tile_lev hk hp (by omega) (by omega) (by omega)
  have hl : twosLev a (a - 1) (2 * a - 1) = 1 := by
    unfold twosLev
    rw [if_pos (by omega), if_neg (by omega)]
    norm_num
  have e1 := phi_spec_2a1 k
  rw [show 2 * (k : ℤ) + 4 = a by omega] at e1
  linarith

end FLatticePaper.TwosEPolicy
