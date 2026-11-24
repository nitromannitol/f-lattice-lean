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


open Classical in
/-- The price on the polygon: `P = c₀ − [TwosDelta]`. -/
theorem twos_price_ite (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2) :
    twosP k (z1, z2) = ((k : ℤ) ^ 2 + 5 * (k : ℤ) + 5) - (if TwosDelta k z1 z2 then 1 else 0) := by
  by_cases hd : TwosDelta k z1 z2
  · rw [if_pos hd]
    rcases twos_price_delta k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd hd h2
    · unfold twosP
      linarith
  · rw [if_neg hd]
    rcases twos_price_delta k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · unfold twosP
      linarith
    · exact absurd h2 hd

open Classical in
/-- The band form of `Ψ`: `Ψ(q) ≤ Ψ(p)` when `δ(p) + D(p) ≤ δ(q) + D(q)` on polygon points. -/
theorem psi_le_of_band (k : ℕ) {p1 p2 q1 q2 : ℤ} (hp : TwosKey (2 * (k : ℤ) + 4) p1 p2)
    (hq : TwosKey (2 * (k : ℤ) + 4) q1 q2)
    (h : (if TwosDelta k p1 p2 then (1 : ℤ) else 0) + twosSlip k (p1, p2) ≤
      (if TwosDelta k q1 q2 then (1 : ℤ) else 0) + twosSlip k (q1, q2)) :
    twosPsi k q1 q2 ≤ twosPsi k p1 p2 := by
  unfold twosPsi
  rw [twos_price_ite k hp, twos_price_ite k hq]
  linarith

/-- `Ψ` is invariant up to the constant `−1` under the kernel translate `U`. -/
theorem psi_U_shift (k : ℕ) (a b : ℤ) :
    twosPsi k (a + (2 * (k : ℤ) + 5)) (b + (2 * (k : ℤ) + 3)) = twosPsi k a b - 1 := by
  have e1 : a + (2 * (k : ℤ) + 5) = a + (1 * (2 * (k : ℤ) + 5) + 0 * (-2)) := by ring
  have e2 : b + (2 * (k : ℤ) + 3) = b + (1 * (2 * (k : ℤ) + 3) + 0 * (4 * (k : ℤ) + 8)) := by ring
  rw [e1, e2, twosPsi_lattice]
  ring

theorem even_black_negs (k : ℕ) {x y : ℤ}
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
  exact ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩

set_option maxHeartbeats 400000 in
/-- **Even native centre, west input, `x = 0`:** the translate `U` brings both shifted points into the polygon. -/
theorem chainM_black_evenL_zero (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (hW : ¬ LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1)) (hx : x = 0) :
    twosPsi k (x - 2) (y - 1) ≤ twosPsi k (x - 1) (y - 1) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := even_black_negs k hW
  unfold NativeT at hn
  subst hx
  obtain ⟨hb1, hb2⟩ : 0 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) := by
    clear n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
    omega
  have hyr : 2 * (k : ℤ) + 4 + 2 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 2 := by
    clear n1 n2 n4 n5 n6 n7 n8 n10 hn
    omega
  obtain ⟨hy1, hy2⟩ := hyr
  clear n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 hW hn
  have hq : TwosKey (2 * (k : ℤ) + 4) ((0 - 2) + (2 * (k : ℤ) + 5)) ((y - 1) + (2 * (k : ℤ) + 3)) := by
    rw [twosKey_pos]
    omega
  have hpK : TwosKey (2 * (k : ℤ) + 4) ((0 - 1) + (2 * (k : ℤ) + 5)) ((y - 1) + (2 * (k : ℤ) + 3)) := by
    rw [twosKey_pos]
    omega
  have key : twosPsi k ((0 - 2) + (2 * (k : ℤ) + 5)) ((y - 1) + (2 * (k : ℤ) + 3)) ≤
      twosPsi k ((0 - 1) + (2 * (k : ℤ) + 5)) ((y - 1) + (2 * (k : ℤ) + 3)) := by
    apply psi_le_of_band k hpK hq
    have hv := twos_slip_value k hpK
    have hw := twos_slip_value k hq
    unfold TwosSlipZ0 TwosSlipZ2 at hv hw
    rcases hv with ⟨v1, v2⟩ | ⟨v1, v2, v3⟩ | ⟨v1, v2⟩ <;>
      rcases hw with ⟨w1, w2⟩ | ⟨w1, w2, w3⟩ | ⟨w1, w2⟩ <;>
      split_ifs <;> (try unfold TwosDelta at *) <;> omega
  rw [psi_U_shift, psi_U_shift] at key
  linarith

end FLatticePaper.TwosEPolicy
