import FLatticePaper.Plane.Induction.TwosSlipLattice

/-! Task 118, base slip at `2^(k+1)`: `F1_unitSlip` (unit increments of the slip on every edge). -/

namespace FLatticePaper.Induction
open Farey Construction

set_option maxHeartbeats 400000 in
/-- The left unit step: `D(y − (1,0)) − D(y)` is in `[−1, 1]`. -/
theorem twos_slip_unit_m (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) :
    -1 ≤ twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) ∧ twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) ≤ 1 := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  rcases twos_cover_m k hy with h0 | hU | hV
  · have hv0 := twos_slip_value k h0
    have hcp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp h0
    simp only [TwosSlipZ0, TwosSlipZ2] at hv hv0
    omega
  · have hv0 := twos_slip_value k hU
    have hcp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hU
    have e := twosSlip_add_U k (y1 - 1, y2)
    have hpt : (y1 - 1, y2) + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) =
        (y1 - 1 + (2 * (k : ℤ) + 5), y2 + (2 * (k : ℤ) + 3)) := rfl
    rw [hpt] at e
    simp only [TwosSlipZ0, TwosSlipZ2] at hv hv0
    omega
  · have hv0 := twos_slip_value k hV
    have hcp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hV
    have e := twosSlip_add_V k (y1 - 1 + 2, y2 - (4 * (k : ℤ) + 8))
    have hpt : (y1 - 1 + 2, y2 - (4 * (k : ℤ) + 8)) + (-2, 4 * (k : ℤ) + 8) = (y1 - 1, y2) :=
      Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
    rw [hpt] at e
    simp only [TwosSlipZ0, TwosSlipZ2] at hv hv0
    omega

set_option maxHeartbeats 400000 in
/-- The right unit step: `D(y + (1,0)) − D(y)` is in `[−1, 1]`. -/
theorem twos_slip_unit_p (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) :
    -1 ≤ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) ≤ 1 := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  rcases twos_cover_p k hy with h0 | hU | hV
  · have hv0 := twos_slip_value k h0
    have hcp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp h0
    simp only [TwosSlipZ0, TwosSlipZ2] at hv hv0
    omega
  · have hv0 := twos_slip_value k hU
    have hcp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hU
    have e := twosSlip_add_U k (y1 + 1 - (2 * (k : ℤ) + 5), y2 - (2 * (k : ℤ) + 3))
    have hpt : (y1 + 1 - (2 * (k : ℤ) + 5), y2 - (2 * (k : ℤ) + 3)) + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) =
        (y1 + 1, y2) :=
      Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
    rw [hpt] at e
    simp only [TwosSlipZ0, TwosSlipZ2] at hv hv0
    omega
  · have hv0 := twos_slip_value k hV
    have hcp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hV
    have e := twosSlip_add_V k (y1 + 1, y2)
    have hpt : (y1 + 1, y2) + (-2, 4 * (k : ℤ) + 8) = (y1 + 1 - 2, y2 + (4 * (k : ℤ) + 8)) :=
      Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add])
    rw [hpt] at e
    simp only [TwosSlipZ0, TwosSlipZ2] at hv hv0
    omega

set_option maxHeartbeats 400000 in
/-- The upper unit step: `D(y + (0,1)) − D(y)` is in `[−1, 1]`. -/
theorem twos_slip_unit_q (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) :
    -1 ≤ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) ≤ 1 := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  rcases twos_cover_q k hy with h0 | hV | hU
  · have hv0 := twos_slip_value k h0
    have hcp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp h0
    simp only [TwosSlipZ0, TwosSlipZ2] at hv hv0
    omega
  · have hv0 := twos_slip_value k hV
    have hcp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hV
    have e := twosSlip_add_V k (y1 + 2, y2 + 1 - (4 * (k : ℤ) + 8))
    have hpt : (y1 + 2, y2 + 1 - (4 * (k : ℤ) + 8)) + (-2, 4 * (k : ℤ) + 8) = (y1, y2 + 1) :=
      Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
    rw [hpt] at e
    simp only [TwosSlipZ0, TwosSlipZ2] at hv hv0
    omega
  · have hv0 := twos_slip_value k hU
    have hcp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hU
    have e := twosSlip_add_U k (y1 - (2 * (k : ℤ) + 5), y2 + 1 - (2 * (k : ℤ) + 3))
    have hpt : (y1 - (2 * (k : ℤ) + 5), y2 + 1 - (2 * (k : ℤ) + 3)) + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) =
        (y1, y2 + 1) :=
      Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
    rw [hpt] at e
    simp only [TwosSlipZ0, TwosSlipZ2] at hv hv0
    omega

set_option maxHeartbeats 400000 in
/-- The lower unit step: `D(y − (0,1)) − D(y)` is in `[−1, 1]`. -/
theorem twos_slip_unit_r (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) :
    -1 ≤ twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) ∧ twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) ≤ 1 := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  rcases twos_cover_r k hy with h0 | hU | hV
  · have hv0 := twos_slip_value k h0
    have hcp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp h0
    simp only [TwosSlipZ0, TwosSlipZ2] at hv hv0
    omega
  · have hv0 := twos_slip_value k hU
    have hcp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hU
    have e := twosSlip_add_U k (y1, y2 - 1)
    have hpt : (y1, y2 - 1) + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) =
        (y1 + (2 * (k : ℤ) + 5), y2 - 1 + (2 * (k : ℤ) + 3)) := rfl
    rw [hpt] at e
    simp only [TwosSlipZ0, TwosSlipZ2] at hv hv0
    omega
  · have hv0 := twos_slip_value k hV
    have hcp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hV
    have e := twosSlip_add_V k (y1, y2 - 1)
    have hpt : (y1, y2 - 1) + (-2, 4 * (k : ℤ) + 8) = (y1 - 2, y2 - 1 + (4 * (k : ℤ) + 8)) :=
      Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add])
    rw [hpt] at e
    simp only [TwosSlipZ0, TwosSlipZ2] at hv hv0
    omega

set_option maxHeartbeats 400000 in
/-- **`F1_unitSlip` at `2^(k+1)`:** the slip has unit increments on every edge. -/
theorem twos_slipUnit (k : ℕ) :
    HasUnitSlip (standardField (List.replicate (k + 1) Digit.two))
      (fun z => standardField (List.replicate (k + 1) Digit.two) (z + (frameAt (List.replicate (k + 1) Digit.two)).shortShift)) := by
  intro center input hE
  change -1 ≤ twosSlip k input - twosSlip k center ∧ twosSlip k input - twosSlip k center ≤ 1
  obtain ⟨y, hy, i, j, hc⟩ := (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon_covers center
  have hyT : TwosKey (2 * (k : ℤ) + 4) y.1 y.2 := twos_E_key k y hy
  have hcomb : (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.combine i j =
      (i * (2 * (k : ℤ) + 5) + j * (-2), i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)) := by
    unfold PeriodDeck.combine
    rw [twos_kernel_explicit, twos_transverse_explicit]
  rw [hcomb] at hc
  obtain ⟨y1, y2⟩ := y
  obtain ⟨c1, c2⟩ := center
  have hc1 : c1 = y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)) := by
    have := congrArg Prod.fst hc
    simpa using this
  have hc2 : c2 = y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)) := by
    have := congrArg Prod.snd hc
    simpa using this
  rcases hE with hE | hE
  · unfold incomingNeg at hE
    split_ifs at hE with hev
    · rw [hE]
      have hA : twosSlip k (c1 - 1, c2) = twosSlip k (y1 - 1, y2) + 2 * j := by
        rw [show (c1 - 1, c2) = (y1 - 1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]; ring) (by rw [hc2])]
        exact twosSlip_lattice k (y1 - 1, y2) i j
      have hB : twosSlip k (c1, c2) = twosSlip k (y1, y2) + 2 * j := by
        rw [show (c1, c2) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2])]
        exact twosSlip_lattice k (y1, y2) i j
      rw [hA, hB]
      have := twos_slip_unit_m k hyT
      constructor <;> linarith [this.1, this.2]
    · rw [hE]
      have hA : twosSlip k (c1, c2 - 1) = twosSlip k (y1, y2 - 1) + 2 * j := by
        rw [show (c1, c2 - 1) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 - 1 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2]; ring)]
        exact twosSlip_lattice k (y1, y2 - 1) i j
      have hB : twosSlip k (c1, c2) = twosSlip k (y1, y2) + 2 * j := by
        rw [show (c1, c2) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2])]
        exact twosSlip_lattice k (y1, y2) i j
      rw [hA, hB]
      have := twos_slip_unit_r k hyT
      constructor <;> linarith [this.1, this.2]
  · unfold incomingPos at hE
    split_ifs at hE with hev
    · rw [hE]
      have hA : twosSlip k (c1 + 1, c2) = twosSlip k (y1 + 1, y2) + 2 * j := by
        rw [show (c1 + 1, c2) = (y1 + 1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]; ring) (by rw [hc2])]
        exact twosSlip_lattice k (y1 + 1, y2) i j
      have hB : twosSlip k (c1, c2) = twosSlip k (y1, y2) + 2 * j := by
        rw [show (c1, c2) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2])]
        exact twosSlip_lattice k (y1, y2) i j
      rw [hA, hB]
      have := twos_slip_unit_p k hyT
      constructor <;> linarith [this.1, this.2]
    · rw [hE]
      have hA : twosSlip k (c1, c2 + 1) = twosSlip k (y1, y2 + 1) + 2 * j := by
        rw [show (c1, c2 + 1) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + 1 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2]; ring)]
        exact twosSlip_lattice k (y1, y2 + 1) i j
      have hB : twosSlip k (c1, c2) = twosSlip k (y1, y2) + 2 * j := by
        rw [show (c1, c2) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2])]
        exact twosSlip_lattice k (y1, y2) i j
      rw [hA, hB]
      have := twos_slip_unit_q k hyT
      constructor <;> linarith [this.1, this.2]

end FLatticePaper.Induction
