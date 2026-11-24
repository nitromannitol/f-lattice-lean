import FLatticePaper.Plane.Induction.TwosSlipMinusMono

/-! Task 72 / twos base: the chain potential of sign `−1`, `Φ₋₁ = D₋₁ + P(· − σ)`, in the translate coordinates of `(1,1)`.

Since `σ = (1,1) − U`, the slip of sign `−1` is `−D(z − (1,1))` (`twos_slip_minus_eq`) and the price drops by one under the
kernel (`twosP_U`), so `Φ₋₁(z) = Ψ(z − (1,1)) − 1` with `Ψ = P − D` (`chainM_eq`). The claim `Φ₋₁(i) ≤ Φ₋₁(c)` along the sign
`−1` selected edges is therefore `Ψ(i − (1,1)) ≤ Ψ(c − (1,1))`, a band comparison of the price and the slip. -/

namespace FLatticePaper.TwosEPolicy
open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey

/-- The shifted chain quantity `Ψ = P − D` at the site `(x, y)`. -/
noncomputable def twosPsi (k : ℕ) (x y : ℤ) : ℤ := twosP k (x, y) - FLatticePaper.Induction.twosSlip k (x, y)

/-- **The chain potential of sign `−1` in the translate coordinates:** `Φ₋₁(z) = Ψ(z − (1,1)) − 1`. -/
theorem chainM_eq (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) z =
      twosPsi k (z.1 - 1) (z.2 - 1) - 1 := by
  unfold ChildFrame.chainPotential
  rw [twos_slip_minus_eq]
  have e : z + (-1 : ℤ) • (frameAt (List.replicate (k + 1) Digit.two)).shortShift =
      (z.1 - 1 + (2 * (k : ℤ) + 5), z.2 - 1 + (2 * (k : ℤ) + 3)) := by
    rw [neg_one_smul, twos_shortShift_explicit]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_neg]
      ring
    · simp only [Prod.snd_add, Prod.snd_neg]
      ring
  rw [e]
  have hP := twosP_U k (z.1 - 1) (z.2 - 1)
  unfold twosPsi
  unfold twosP at hP ⊢
  linarith


/-- The shifted chain quantity under the kernel: `Ψ(x + U) = Ψ(x) − 1`. -/
theorem twosPsi_U (k : ℕ) (x y : ℤ) :
    twosPsi k (x + (2 * (k : ℤ) + 5)) (y + (2 * (k : ℤ) + 3)) = twosPsi k x y - 1 := by
  have hP := twosP_U k x y
  have hS := twosSlip_add_U k (x, y)
  unfold twosPsi
  rw [hP]
  have e : (x, y) + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) = (x + (2 * (k : ℤ) + 5), y + (2 * (k : ℤ) + 3)) := rfl
  rw [e] at hS
  rw [hS]
  ring

/-- The shifted chain quantity under the transverse period: `Ψ(x − 2, y + 4k+8) = Ψ(x, y) − 2`. -/
theorem twosPsi_V (k : ℕ) (x y : ℤ) :
    twosPsi k (x + (-2)) (y + (4 * (k : ℤ) + 8)) = twosPsi k x y - 2 := by
  have hP := twosP_V k x y
  have hS := twosSlip_add_V k (x, y)
  unfold twosPsi
  rw [hP]
  have e : (x, y) + (-2, 4 * (k : ℤ) + 8) = (x + (-2), y + (4 * (k : ℤ) + 8)) := rfl
  rw [e] at hS
  rw [hS]
  ring

set_option maxHeartbeats 400000 in
theorem twosPsi_cand_low_down_U (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hG : CandLow (2 * (k : ℤ) + 4) u1 u2) (hm : u2 < 2 * (k : ℤ) + 4 - 1) (hc : u1 = 1) :
    twosPsi k (u1 - 1 + 0) (u2 - 1 + -1) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  unfold CandLow at hG
  have eX := twosPsi_U k (u1 - 1 + 0) (u2 - 1 + -1)
  have eY := twosPsi_U k (u1 - 1) (u2 - 1)
  have key : twosPsi k (u1 - 1 + 0 + (2 * (k : ℤ) + 5)) (u2 - 1 + -1 + (2 * (k : ℤ) + 3)) ≤ twosPsi k (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 0 + (2 * (k : ℤ) + 5)) (u2 - 1 + -1 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  linarith [eX, eY, key]

set_option maxHeartbeats 400000 in
theorem twosPsi_cand_low_down_V (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hG : CandLow (2 * (k : ℤ) + 4) u1 u2) (_hm : u2 < 2 * (k : ℤ) + 4 - 1) (hc : u1 = 2 ∧ u2 = 1) :
    twosPsi k (u1 - 1 + 0) (u2 - 1 + -1) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  unfold CandLow at hG
  have eX := twosPsi_V k (u1 - 1 + 0) (u2 - 1 + -1)
  have eY := twosPsi_V k (u1 - 1) (u2 - 1)
  have key : twosPsi k (u1 - 1 + 0 + -2) (u2 - 1 + -1 + (4 * (k : ℤ) + 8)) ≤ twosPsi k (u1 - 1 + -2) (u2 - 1 + (4 * (k : ℤ) + 8)) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 0 + -2) (u2 - 1 + -1 + (4 * (k : ℤ) + 8)) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + -2) (u2 - 1 + (4 * (k : ℤ) + 8)) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  linarith [eX, eY, key]

set_option maxHeartbeats 400000 in
theorem twosPsi_cand_low_down_0 (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hG : CandLow (2 * (k : ℤ) + 4) u1 u2) (hm : u2 < 2 * (k : ℤ) + 4 - 1) (hc : ¬ u1 = 1 ∧ ¬ (u1 = 2 ∧ u2 = 1)) :
    twosPsi k (u1 - 1 + 0) (u2 - 1 + -1) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  unfold CandLow at hG
  have key : twosPsi k (u1 - 1 + 0) (u2 - 1 + -1) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 0) (u2 - 1 + -1) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1) (u2 - 1) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  exact key

set_option maxHeartbeats 400000 in
theorem twosPsi_cand_low_up_0 (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hG : CandLow (2 * (k : ℤ) + 4) u1 u2) (hm : ¬ u2 < 2 * (k : ℤ) + 4 - 1) :
    twosPsi k (u1 - 1 + 0) (u2 - 1 + 1) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  unfold CandLow at hG
  have key : twosPsi k (u1 - 1 + 0) (u2 - 1 + 1) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 0) (u2 - 1 + 1) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1) (u2 - 1) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  exact key

set_option maxHeartbeats 400000 in
theorem twosPsi_cand_high_down_U (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hG : CandHigh (2 * (k : ℤ) + 4) u1 u2) (hm : u2 < 2 * (2 * (k : ℤ) + 4) - 1) (hc : u1 = 0) :
    twosPsi k (u1 - 1 + 0) (u2 - 1 + -1) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  unfold CandHigh at hG
  have eX := twosPsi_U k (u1 - 1 + 0) (u2 - 1 + -1)
  have eY := twosPsi_U k (u1 - 1) (u2 - 1)
  have key : twosPsi k (u1 - 1 + 0 + (2 * (k : ℤ) + 5)) (u2 - 1 + -1 + (2 * (k : ℤ) + 3)) ≤ twosPsi k (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 0 + (2 * (k : ℤ) + 5)) (u2 - 1 + -1 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  linarith [eX, eY, key]

set_option maxHeartbeats 400000 in
theorem twosPsi_cand_high_down_0 (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hG : CandHigh (2 * (k : ℤ) + 4) u1 u2) (hm : u2 < 2 * (2 * (k : ℤ) + 4) - 1) (hc : ¬ u1 = 0) :
    twosPsi k (u1 - 1 + 0) (u2 - 1 + -1) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  unfold CandHigh at hG
  have key : twosPsi k (u1 - 1 + 0) (u2 - 1 + -1) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 0) (u2 - 1 + -1) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1) (u2 - 1) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  exact key

set_option maxHeartbeats 400000 in
theorem twosPsi_cand_high_up_0 (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hG : CandHigh (2 * (k : ℤ) + 4) u1 u2) (hm : ¬ u2 < 2 * (2 * (k : ℤ) + 4) - 1) :
    twosPsi k (u1 - 1 + 0) (u2 - 1 + 1) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  unfold CandHigh at hG
  have key : twosPsi k (u1 - 1 + 0) (u2 - 1 + 1) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 0) (u2 - 1 + 1) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1) (u2 - 1) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  exact key

set_option maxHeartbeats 400000 in
theorem twosPsi_cand_E_0 (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hG : CandE (2 * (k : ℤ) + 4) u1 u2)  :
    twosPsi k (u1 - 1 + 1) (u2 - 1 + 0) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  unfold CandE at hG
  have key : twosPsi k (u1 - 1 + 1) (u2 - 1 + 0) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 1) (u2 - 1 + 0) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1) (u2 - 1) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  exact key

set_option maxHeartbeats 400000 in
theorem twosPsi_cand_W_U (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hG : CandW (2 * (k : ℤ) + 4) u1 u2) (hc : u1 = 0) :
    twosPsi k (u1 - 1 + -1) (u2 - 1 + 0) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  unfold CandW at hG
  have eX := twosPsi_U k (u1 - 1 + -1) (u2 - 1 + 0)
  have eY := twosPsi_U k (u1 - 1) (u2 - 1)
  have key : twosPsi k (u1 - 1 + -1 + (2 * (k : ℤ) + 5)) (u2 - 1 + 0 + (2 * (k : ℤ) + 3)) ≤ twosPsi k (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + -1 + (2 * (k : ℤ) + 5)) (u2 - 1 + 0 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  linarith [eX, eY, key]

set_option maxHeartbeats 400000 in
theorem twosPsi_cand_W_0 (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hG : CandW (2 * (k : ℤ) + 4) u1 u2) (hc : ¬ u1 = 0) :
    twosPsi k (u1 - 1 + -1) (u2 - 1 + 0) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  unfold CandW at hG
  have key : twosPsi k (u1 - 1 + -1) (u2 - 1 + 0) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + -1) (u2 - 1 + 0) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1) (u2 - 1) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  exact key


set_option maxHeartbeats 400000 in
/-- **The candidate branch of the sign `−1` chain claim:** `Ψ(cp + δ) ≤ Ψ(cp)` at a native candidate centre. -/
theorem twosPsi_cand (k : ℕ) {u1 u2 : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) u1 u2)
    (hg : CandGuard (2 * (k : ℤ) + 4) u1 u2) :
    twosPsi k (u1 - 1 + (candDisp (2 * (k : ℤ) + 4) u1 u2).1) (u2 - 1 + (candDisp (2 * (k : ℤ) + 4) u1 u2).2) ≤
      twosPsi k (u1 - 1) (u2 - 1) := by
  rcases hg with hL | hH | hE | hW
  · by_cases hm : u2 < 2 * (k : ℤ) + 4 - 1
    · rw [candDisp_low_down hL hm]
      dsimp only
      by_cases hc1 : u1 = 1
      · exact twosPsi_cand_low_down_U k hn hL hm hc1
      · by_cases hc2 : u1 = 2 ∧ u2 = 1
        · exact twosPsi_cand_low_down_V k hn hL hm hc2
        · exact twosPsi_cand_low_down_0 k hn hL hm ⟨hc1, hc2⟩
    · rw [candDisp_low_up hL hm]
      dsimp only
      exact twosPsi_cand_low_up_0 k hn hL hm
  · by_cases hm : u2 < 2 * (2 * (k : ℤ) + 4) - 1
    · rw [candDisp_high_down hH hm]
      dsimp only
      by_cases hc : u1 = 0
      · exact twosPsi_cand_high_down_U k hn hH hm hc
      · exact twosPsi_cand_high_down_0 k hn hH hm hc
    · rw [candDisp_high_up hH hm]
      dsimp only
      exact twosPsi_cand_high_up_0 k hn hH hm
  · rw [candDisp_E hE]
    dsimp only
    exact twosPsi_cand_E_0 k hn hE
  · rw [candDisp_W hW]
    dsimp only
    by_cases hc : u1 = 0
    · exact twosPsi_cand_W_U k hn hW hc
    · exact twosPsi_cand_W_0 k hn hW hc


/-- The lattice law of `Ψ`: `Ψ(a + iU + jV) = Ψ(a) − i − 2j`. -/
theorem twosPsi_lattice (k : ℕ) (a b i j : ℤ) :
    twosPsi k (a + (i * (2 * (k : ℤ) + 5) + j * (-2))) (b + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) =
      twosPsi k a b - i - 2 * j := by
  have h1 := twos_price_lattice k a b i j
  have h2 : twosSlip k (a + (i * (2 * (k : ℤ) + 5) + j * (-2)), b + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) =
      twosSlip k (a, b) + 2 * j := twosSlip_lattice k (a, b) i j
  unfold twosPsi
  unfold twosP
  linarith [h1, h2]

set_option maxHeartbeats 400000 in
/-- **The candidate branch of the sign `−1` chain potential:** `Φ₋₁(i) ≤ Φ₋₁(c)` for a candidate selection of sign `−1`. -/
theorem chainM_cand (k : ℕ) {c i : Site}
    (hT : ∃ u : Site, AliasOf (2 * (k : ℤ) + 4) c u ∧ NativeT (2 * (k : ℤ) + 4) u.1 u.2 ∧
      CandGuard (2 * (k : ℤ) + 4) u.1 u.2 ∧
      i = (c.1 + (candDisp (2 * (k : ℤ) + 4) u.1 u.2).1, c.2 + (candDisp (2 * (k : ℤ) + 4) u.1 u.2).2)) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) i ≤
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) c := by
  obtain ⟨⟨u1, u2⟩, ⟨i', l, hu⟩, hn, hg, hi⟩ := hT
  have hu1 : u1 = c.1 - i' * (2 * (k : ℤ) + 4 + 1) + 2 * l := congrArg Prod.fst hu
  have hu2 : u2 = c.2 - i' * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * l := congrArg Prod.snd hu
  have key := twosPsi_cand k hn hg
  rw [chainM_eq, chainM_eq]
  have e1 : i.1 - 1 = u1 - 1 + (candDisp (2 * (k : ℤ) + 4) u1 u2).1 + (i' * (2 * (k : ℤ) + 5) + l * (-2)) := by
    rw [hi]
    dsimp only
    rw [hu1]
    ring
  have e2 : i.2 - 1 = u2 - 1 + (candDisp (2 * (k : ℤ) + 4) u1 u2).2 + (i' * (2 * (k : ℤ) + 3) + l * (4 * (k : ℤ) + 8)) := by
    rw [hi]
    dsimp only
    rw [hu2]
    ring
  have e3 : c.1 - 1 = u1 - 1 + (i' * (2 * (k : ℤ) + 5) + l * (-2)) := by
    rw [hu1]
    ring
  have e4 : c.2 - 1 = u2 - 1 + (i' * (2 * (k : ℤ) + 3) + l * (4 * (k : ℤ) + 8)) := by
    rw [hu2]
    ring
  rw [e1, e2, e3, e4, twosPsi_lattice, twosPsi_lattice]
  linarith [key]


set_option maxHeartbeats 400000 in
theorem twosPsi_free_H0 (k : ℕ) {u1 u2 : ℤ} (h1 : u1 = 1) (h2 : u2 = 0) :
    twosPsi k (u1 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).1) (u2 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).2) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  rw [freeDisp_H0 (η := -1) ⟨h1, h2⟩]
  dsimp only
  have eX := twosPsi_U k (u1 - 1 + 0) (u2 - 1 + -(-1))
  have eY := twosPsi_U k (u1 - 1) (u2 - 1)
  have key : twosPsi k (u1 - 1 + 0 + (2 * (k : ℤ) + 5)) (u2 - 1 + -(-1) + (2 * (k : ℤ) + 3)) ≤ twosPsi k (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 0 + (2 * (k : ℤ) + 5)) (u2 - 1 + -(-1) + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  linarith [eX, eY, key]

set_option maxHeartbeats 400000 in
theorem twosPsi_free_Ha1 (k : ℕ) {u1 u2 : ℤ} (h1 : u1 = 2 * (k : ℤ) + 4 + 1) (h2 : u2 = 2 * (k : ℤ) + 4 - 2) :
    twosPsi k (u1 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).1) (u2 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).2) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  rw [freeDisp_Hodd (η := -1) (Or.inr (Or.inr ⟨h1, h2⟩)) (by omega) (by show ¬ (u1 + u2) % 2 = 0; omega)]
  dsimp only
  have eX := twosPsi_V k (u1 - 1 + 0) (u2 - 1 + 1)
  have eY := twosPsi_V k (u1 - 1) (u2 - 1)
  have key : twosPsi k (u1 - 1 + 0 + -2) (u2 - 1 + 1 + (4 * (k : ℤ) + 8)) ≤ twosPsi k (u1 - 1 + -2) (u2 - 1 + (4 * (k : ℤ) + 8)) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 0 + -2) (u2 - 1 + 1 + (4 * (k : ℤ) + 8)) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + -2) (u2 - 1 + (4 * (k : ℤ) + 8)) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  linarith [eX, eY, key]

set_option maxHeartbeats 400000 in
theorem twosPsi_free_V0 (k : ℕ) {u1 u2 : ℤ} (h1 : u1 = 0) (h2 : u2 = 0) :
    twosPsi k (u1 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).1) (u2 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).2) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  rw [freeDisp_V0 (η := -1) ⟨h1, h2⟩]
  dsimp only
  have eX := twosPsi_U k (u1 - 1 + 1) (u2 - 1 + 0)
  have eY := twosPsi_U k (u1 - 1) (u2 - 1)
  have key : twosPsi k (u1 - 1 + 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + 0 + (2 * (k : ℤ) + 3)) ≤ twosPsi k (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + 0 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  linarith [eX, eY, key]

set_option maxHeartbeats 400000 in
theorem twosPsi_free_H (k : ℕ) {u1 u2 : ℤ} (hx1 : 2 ≤ u1) (hx2 : u1 ≤ 2 * (k : ℤ) + 4) (h2 : u2 = u1 - 2) :
    twosPsi k (u1 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).1) (u2 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).2) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  rw [freeDisp_Heven (η := -1) (Or.inr (Or.inl ⟨hx1, hx2, h2⟩)) (by omega) (by show (u1 + u2) % 2 = 0; omega)]
  dsimp only
  have eX := twosPsi_V k (u1 - 1 + 1) (u2 - 1 + 0)
  have eY := twosPsi_V k (u1 - 1) (u2 - 1)
  have key : twosPsi k (u1 - 1 + 1 + -2) (u2 - 1 + 0 + (4 * (k : ℤ) + 8)) ≤ twosPsi k (u1 - 1 + -2) (u2 - 1 + (4 * (k : ℤ) + 8)) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 1 + -2) (u2 - 1 + 0 + (4 * (k : ℤ) + 8)) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + -2) (u2 - 1 + (4 * (k : ℤ) + 8)) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  linarith [eX, eY, key]

set_option maxHeartbeats 400000 in
theorem twosPsi_free_V0e (k : ℕ) {u1 u2 : ℤ} (h1 : u1 = 0) (hy1 : 1 ≤ u2) (hy2 : u2 ≤ 2 * (k : ℤ) + 4 - 1) (hp : u2 % 2 = 0) :
    twosPsi k (u1 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).1) (u2 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).2) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  rw [freeDisp_Veven (η := -1) (Or.inl ⟨h1, by omega, by omega⟩) (by omega) (by show (u1 + u2) % 2 = 0; omega)]
  dsimp only
  have eX := twosPsi_U k (u1 - 1 + -1) (u2 - 1 + 0)
  have eY := twosPsi_U k (u1 - 1) (u2 - 1)
  have key : twosPsi k (u1 - 1 + -1 + (2 * (k : ℤ) + 5)) (u2 - 1 + 0 + (2 * (k : ℤ) + 3)) ≤ twosPsi k (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + -1 + (2 * (k : ℤ) + 5)) (u2 - 1 + 0 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  linarith [eX, eY, key]

set_option maxHeartbeats 400000 in
theorem twosPsi_free_V0o (k : ℕ) {u1 u2 : ℤ} (h1 : u1 = 0) (hy1 : 1 ≤ u2) (hy2 : u2 ≤ 2 * (k : ℤ) + 4 - 1) (hp : u2 % 2 = 1) :
    twosPsi k (u1 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).1) (u2 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).2) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  rw [freeDisp_Vodd (η := -1) (Or.inl ⟨h1, by omega, by omega⟩) (by omega) (by show ¬ (u1 + u2) % 2 = 0; omega)]
  dsimp only
  have eX := twosPsi_U k (u1 - 1 + 0) (u2 - 1 + -(-1))
  have eY := twosPsi_U k (u1 - 1) (u2 - 1)
  have key : twosPsi k (u1 - 1 + 0 + (2 * (k : ℤ) + 5)) (u2 - 1 + -(-1) + (2 * (k : ℤ) + 3)) ≤ twosPsi k (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 0 + (2 * (k : ℤ) + 5)) (u2 - 1 + -(-1) + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  linarith [eX, eY, key]

set_option maxHeartbeats 400000 in
theorem twosPsi_free_V1e (k : ℕ) {u1 u2 : ℤ} (h1 : u1 = -1) (hy1 : 2 * (k : ℤ) + 4 ≤ u2) (hy2 : u2 < 2 * (2 * (k : ℤ) + 4)) (hp : (u2 - 1) % 2 = 0) :
    twosPsi k (u1 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).1) (u2 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).2) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  rw [freeDisp_Veven (η := -1) (Or.inr ⟨h1, by omega, by omega⟩) (by omega) (by show (u1 + u2) % 2 = 0; omega)]
  dsimp only
  have eX := twosPsi_U k (u1 - 1 + -1) (u2 - 1 + 0)
  have eY := twosPsi_U k (u1 - 1) (u2 - 1)
  have key : twosPsi k (u1 - 1 + -1 + (2 * (k : ℤ) + 5)) (u2 - 1 + 0 + (2 * (k : ℤ) + 3)) ≤ twosPsi k (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + -1 + (2 * (k : ℤ) + 5)) (u2 - 1 + 0 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  linarith [eX, eY, key]

set_option maxHeartbeats 400000 in
theorem twosPsi_free_V1o (k : ℕ) {u1 u2 : ℤ} (h1 : u1 = -1) (hy1 : 2 * (k : ℤ) + 4 ≤ u2) (hy2 : u2 < 2 * (2 * (k : ℤ) + 4)) (hp : (u2 - 1) % 2 = 1) :
    twosPsi k (u1 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).1) (u2 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).2) ≤ twosPsi k (u1 - 1) (u2 - 1) := by
  rw [freeDisp_Vodd (η := -1) (Or.inr ⟨h1, by omega, by omega⟩) (by omega) (by show ¬ (u1 + u2) % 2 = 0; omega)]
  dsimp only
  have eX := twosPsi_U k (u1 - 1 + 0) (u2 - 1 + -(-1))
  have eY := twosPsi_U k (u1 - 1) (u2 - 1)
  have key : twosPsi k (u1 - 1 + 0 + (2 * (k : ℤ) + 5)) (u2 - 1 + -(-1) + (2 * (k : ℤ) + 3)) ≤ twosPsi k (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
    have hkX : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + 0 + (2 * (k : ℤ) + 5)) (u2 - 1 + -(-1) + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hkY : TwosKey (2 * (k : ℤ) + 4) (u1 - 1 + (2 * (k : ℤ) + 5)) (u2 - 1 + (2 * (k : ℤ) + 3)) := by
      rw [twosKey_pos]
      omega
    have hpX := twos_price_delta k hkX
    have hpY := twos_price_delta k hkY
    unfold TwosDelta at hpX hpY
    have hsX := twos_slip_value k hkX
    have hsY := twos_slip_value k hkY
    unfold TwosSlipZ0 TwosSlipZ2 at hsX hsY
    unfold twosPsi twosP
    omega
  linarith [eX, eY, key]


set_option maxHeartbeats 400000 in
/-- **The free branch of the sign `−1` chain claim:** the free displacement of sign `−1` does not raise `Ψ`. -/
theorem twosPsi_free (k : ℕ) {u1 u2 : ℤ} (hF : FreeSite (2 * (k : ℤ) + 4) u1 u2) :
    twosPsi k (u1 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).1) (u2 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).2) ≤
      twosPsi k (u1 - 1) (u2 - 1) := by
  rcases hF with hH | hV
  · rcases hH with ⟨h1, h2⟩ | ⟨hx1, hx2, h2⟩ | ⟨h1, h2⟩
    · exact twosPsi_free_H0 k h1 h2
    · exact twosPsi_free_H k hx1 hx2 h2
    · exact twosPsi_free_Ha1 k h1 h2
  · rcases hV with ⟨h1, hy1, hy2⟩ | ⟨h1, hy1, hy2⟩
    · rcases eq_or_lt_of_le hy1 with h0 | hpos
      · exact twosPsi_free_V0 k h1 h0.symm
      · by_cases hp : u2 % 2 = 0
        · exact twosPsi_free_V0e k h1 (by omega) (by omega) hp
        · exact twosPsi_free_V0o k h1 (by omega) (by omega) (by omega)
    · by_cases hp : (u2 - 1) % 2 = 0
      · exact twosPsi_free_V1e k h1 hy1 hy2 hp
      · exact twosPsi_free_V1o k h1 hy1 hy2 (by omega)

set_option maxHeartbeats 400000 in
/-- **The free branch of the sign `−1` chain potential:** `Φ₋₁(i) ≤ Φ₋₁(c)` for a free selection of sign `−1`. -/
theorem chainM_free (k : ℕ) {c i : Site}
    (hT : ∃ u : Site, AliasOf (2 * (k : ℤ) + 4) c u ∧ FreeSite (2 * (k : ℤ) + 4) u.1 u.2 ∧
      i = (c.1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u.1 u.2).1, c.2 + (freeDisp (2 * (k : ℤ) + 4) (-1) u.1 u.2).2)) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) i ≤
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) c := by
  obtain ⟨⟨u1, u2⟩, ⟨i', l, hu⟩, hF, hi⟩ := hT
  have hF' : FreeSite (2 * (k : ℤ) + 4) u1 u2 := hF
  have hu1 : u1 = c.1 - i' * (2 * (k : ℤ) + 4 + 1) + 2 * l := congrArg Prod.fst hu
  have hu2 : u2 = c.2 - i' * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * l := congrArg Prod.snd hu
  have key := twosPsi_free k hF'
  rw [chainM_eq, chainM_eq]
  have e1 : i.1 - 1 = u1 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).1 + (i' * (2 * (k : ℤ) + 5) + l * (-2)) := by
    rw [hi]
    dsimp only
    rw [hu1]
    ring
  have e2 : i.2 - 1 = u2 - 1 + (freeDisp (2 * (k : ℤ) + 4) (-1) u1 u2).2 + (i' * (2 * (k : ℤ) + 3) + l * (4 * (k : ℤ) + 8)) := by
    rw [hi]
    dsimp only
    rw [hu2]
    ring
  have e3 : c.1 - 1 = u1 - 1 + (i' * (2 * (k : ℤ) + 5) + l * (-2)) := by
    rw [hu1]
    ring
  have e4 : c.2 - 1 = u2 - 1 + (i' * (2 * (k : ℤ) + 3) + l * (4 * (k : ℤ) + 8)) := by
    rw [hu2]
    ring
  rw [e1, e2, e3, e4, twosPsi_lattice, twosPsi_lattice]
  linarith [key]

end FLatticePaper.TwosEPolicy
