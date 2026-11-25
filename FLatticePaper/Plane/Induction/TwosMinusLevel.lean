import FLatticePaper.Plane.Induction.TwosChainMinus
import FLatticePaper.Plane.Induction.TwosChainMono
import FLatticePaper.Plane.Induction.TwosPriceMono

/-! Twos flatness, sign `-1`: the level of the chain potential at the native points.

With `a = 2k+4`, `C = (k+2)(k+3)` and `w = (x-1, y-1)`, a native point `(x, y)` other than `(-1, a+1)` has
`Φ₋₁(x, y) = C - 2 - (δ(w) + S(w))`, where `δ` is the indicator of `TwosDelta` and `S` is the twos slip.
The price identity `P(w) = c₀ - δ(w)` (`c₀ = k²+5k+5`) holds on the key points (`twosP_eq_sub`); at the other native shifted
points it is carried to a key point by the kernel shift `U` (the price drops by `1`) or the transverse shift `V` (the price is
unchanged). The exception `(-2, a)` (that is, the point `(-1, a+1)`) is excluded. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- A native shifted point which is not a key point lies in one of the families of the shift analysis. -/
theorem native_nonkey_family (k : ℕ) {w1 w2 : ℤ}
    (hN : NativeT (2 * (k : ℤ) + 4) (w1 + 1) (w2 + 1))
    (hK : ¬ TwosKey (2 * (k : ℤ) + 4) w1 w2) (hne : ¬ (w1 = -2 ∧ w2 = 2 * (k : ℤ) + 4)) :
    (w1 = -2 ∧ 2 * (k : ℤ) + 5 ≤ w2 ∧ w2 ≤ 2 * (2 * (k : ℤ) + 4) - 1) ∨
      (w1 = -1 ∧ -1 ≤ w2 ∧ w2 ≤ 2 * (k : ℤ) + 3) ∨ (w1 = 0 ∧ w2 = -1) ∨
      (w1 = 1 ∧ w2 = -1) ∨ (w1 = 2 * (k : ℤ) + 4 ∧ w2 = 2 * (k : ℤ) + 1) := by
  have hw : -2 ≤ w1 ∧ w1 ≤ 2 * (k : ℤ) + 4 := by
    unfold NativeT at hN
    omega
  unfold NativeT at hN
  unfold TwosKey at hK
  by_cases h1 : w1 = -2
  · subst h1
    left
    omega
  by_cases h2 : w1 = -1
  · subst h2
    right; left
    omega
  by_cases h3 : w1 = 0
  · subst h3
    right; right; left
    omega
  by_cases h4 : w1 = 1
  · subst h4
    right; right; right; left
    omega
  by_cases h5 : w1 = 2 * (k : ℤ) + 4
  · subst h5
    right; right; right; right
    omega
  exfalso
  omega

/-- The price identity from a key point one kernel step away: `P(w) = P(w+U) + 1`. -/
theorem identity_of_U (k : ℕ) {w1 w2 : ℤ}
    (hk : TwosKey (2 * (k : ℤ) + 4) (w1 + (2 * (k : ℤ) + 5)) (w2 + (2 * (k : ℤ) + 3)))
    (hd1 : TwosDelta k (w1 + (2 * (k : ℤ) + 5)) (w2 + (2 * (k : ℤ) + 3)))
    (hd0 : ¬ TwosDelta k w1 w2) :
    twosP k (w1, w2) = (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - twosDi k w1 w2 := by
  have hU := twosP_U k w1 w2
  have e := twosP_eq_sub k hk _ rfl
  unfold twosDi at e ⊢
  rw [if_pos hd1] at e
  rw [if_neg hd0]
  linarith

/-- The price identity from a transverse shift, when the two points have the same delta. -/
theorem identity_of_V (k : ℕ) {w1 w2 : ℤ}
    (hk : TwosKey (2 * (k : ℤ) + 4) (w1 + -2) (w2 + (4 * (k : ℤ) + 8)))
    (hd : twosDi k (w1 + -2) (w2 + (4 * (k : ℤ) + 8)) = twosDi k w1 w2) :
    twosP k (w1, w2) = (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - twosDi k w1 w2 := by
  have hV := twosP_shiftVp k w1 w2
  have e := twosP_eq_sub k hk _ rfl
  rw [← hd]
  rw [add_zero] at hV
  linarith

/-- The price identity at the native shifted points, except `(-2, a)`: `P(w) = c₀ - δ(w)`. -/
theorem twosP_native_identity (k : ℕ) {w1 w2 : ℤ}
    (hN : NativeT (2 * (k : ℤ) + 4) (w1 + 1) (w2 + 1)) (hne : ¬ (w1 = -2 ∧ w2 = 2 * (k : ℤ) + 4)) :
    twosP k (w1, w2) = (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - twosDi k w1 w2 := by
  by_cases hK : TwosKey (2 * (k : ℤ) + 4) w1 w2
  · exact twosP_eq_sub k hK _ rfl
  · rcases native_nonkey_family k hN hK hne with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1
      exact identity_of_U k (by unfold TwosKey; omega) (by unfold TwosDelta; omega) (by unfold TwosDelta; omega)
    · subst h1
      exact identity_of_U k (by unfold TwosKey; omega) (by unfold TwosDelta; omega) (by unfold TwosDelta; omega)
    · subst h1; subst h2
      exact identity_of_U k (by unfold TwosKey; omega) (by unfold TwosDelta; omega) (by unfold TwosDelta; omega)
    · subst h1; subst h2
      have n1 : ¬ TwosDelta k (1 + -2) (-1 + (4 * (k : ℤ) + 8)) := by unfold TwosDelta; omega
      have n0 : ¬ TwosDelta k 1 (-1) := by unfold TwosDelta; omega
      exact identity_of_V k (by unfold TwosKey; omega) (by unfold twosDi; rw [if_neg n1, if_neg n0])
    · subst h1; subst h2
      have p1 : TwosDelta k (2 * (k : ℤ) + 4 + -2) (2 * (k : ℤ) + 1 + (4 * (k : ℤ) + 8)) := by
        unfold TwosDelta; omega
      have p0 : TwosDelta k (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 1) := by unfold TwosDelta; omega
      exact identity_of_V k (by unfold TwosKey; omega) (by unfold twosDi; rw [if_pos p1, if_pos p0])

/-- **The sign `-1` chain potential at a native point, other than `(-1, a+1)`.** With `w = (x-1, y-1)`:
`Φ₋₁(x, y) = C - 2 - (δ(w) + S(w))`, `C = (k+2)(k+3)`. -/
theorem chainM_native_level (k : ℕ) {x y : ℤ} (hN : NativeT (2 * (k : ℤ) + 4) x y)
    (hne : ¬ (x = -1 ∧ y = 2 * (k : ℤ) + 5)) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) (x, y) =
      ((k : ℤ) + 2) * ((k : ℤ) + 3) - 2 -
        ((if TwosDelta k (x - 1) (y - 1) then 1 else 0) + FLatticePaper.Induction.twosSlip k (x - 1, y - 1)) := by
  have hN' : NativeT (2 * (k : ℤ) + 4) (x - 1 + 1) (y - 1 + 1) := by
    rw [show x - 1 + 1 = x by ring, show y - 1 + 1 = y by ring]
    exact hN
  have hne' : ¬ (x - 1 = -2 ∧ y - 1 = 2 * (k : ℤ) + 4) := by
    rintro ⟨h1, h2⟩
    exact hne ⟨by omega, by omega⟩
  rw [chainM_eq]
  dsimp only
  unfold twosPsi
  rw [twosP_native_identity k hN' hne']
  unfold twosDi
  ring

end FLatticePaper.TwosEPolicy
