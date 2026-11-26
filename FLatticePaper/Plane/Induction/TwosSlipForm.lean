import FLatticePaper.Plane.Induction.TwosSlipForm1

-- TwosSlipForm: part 2 of 2; declarations from twos_slip_band0_dm1 to twos_slip_value.
namespace FLatticePaper.Induction
open Farey Construction

set_option maxHeartbeats 400000 in
/-- The class-`0` slip band on the column region `z1 = 2 * (k : ℤ) + 4 - 1`. -/
theorem twos_slip_band0_dm1 (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h0 : (z1 + 1, z2 + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) (hz : z1 = 2 * (k : ℤ) + 4 - 1) :
    (twosSlip k (z1, z2) = 0 ∧ TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2) ∨
      (twosSlip k (z1, z2) = 1 ∧ ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2 ∧ ¬ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) ∨
      (twosSlip k (z1, z2) = 2 ∧ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) := by
  rw [twos_slip_class0 k hk h0, twos_H_pieces, twos_H_pieces]
  dsimp only
  have q : (z2 + 2 - (z1 + 1)) ^ 2 / 4 = (z2 + 1 - z1) ^ 2 / 4 := by
    congr 1
    ring
  rw [q]
  have m1 := twos_minpart0 (2 * (k : ℤ) + 4) z2
  have m2 : max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 - max (z2 + 2 - (z1 + 1) - (2 * (k : ℤ) + 4)) 0 = 0 := by
    rw [show z2 + 2 - (z1 + 1) - (2 * (k : ℤ) + 4) = z2 + 1 - z1 - (2 * (k : ℤ) + 4) by ring, sub_self]
  have s1 := twosInd_spec (2 * (k : ℤ) + 4) z1 (z2 + 1)
  have s2 := twosInd_spec (2 * (k : ℤ) + 4) (z1 + 1) (z2 + 2)
  rw [twos_tile_iff] at h0
  have hkp := (twosKey_pos (2 * (k : ℤ) + 4) z1 z2).mp hk
  unfold TwosSlipZ0 TwosSlipZ2
  generalize (z2 + 1 - z1) ^ 2 / 4 = Q at *
  generalize min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) = a1 at *
  generalize min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) = a2 at *
  generalize min 0 (2 * (k : ℤ) + 4 - (z2 + 2)) = a3 at *
  generalize min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 2)) = a4 at *
  generalize max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 = b1 at *
  generalize max (z2 + 2 - (z1 + 1) - (2 * (k : ℤ) + 4)) 0 = b2 at *
  generalize twosInd (2 * (k : ℤ) + 4) (z1, z2 + 1) = I1 at *
  generalize twosInd (2 * (k : ℤ) + 4) (z1 + 1, z2 + 2) = I2 at *
  split_ifs at m1 <;> omega

set_option maxHeartbeats 400000 in
/-- The class-`0` slip band on the column region `z1 = 2 * (k : ℤ) + 4`. -/
theorem twos_slip_band0_d (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h0 : (z1 + 1, z2 + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) (hz : z1 = 2 * (k : ℤ) + 4) :
    (twosSlip k (z1, z2) = 0 ∧ TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2) ∨
      (twosSlip k (z1, z2) = 1 ∧ ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2 ∧ ¬ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) ∨
      (twosSlip k (z1, z2) = 2 ∧ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) := by
  rw [twos_slip_class0 k hk h0, twos_H_pieces, twos_H_pieces]
  dsimp only
  have q : (z2 + 2 - (z1 + 1)) ^ 2 / 4 = (z2 + 1 - z1) ^ 2 / 4 := by
    congr 1
    ring
  rw [q]
  have m1 := twos_minpart0 (2 * (k : ℤ) + 4) z2
  have m2 : max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 - max (z2 + 2 - (z1 + 1) - (2 * (k : ℤ) + 4)) 0 = 0 := by
    rw [show z2 + 2 - (z1 + 1) - (2 * (k : ℤ) + 4) = z2 + 1 - z1 - (2 * (k : ℤ) + 4) by ring, sub_self]
  have s1 := twosInd_spec (2 * (k : ℤ) + 4) z1 (z2 + 1)
  have s2 := twosInd_spec (2 * (k : ℤ) + 4) (z1 + 1) (z2 + 2)
  rw [twos_tile_iff] at h0
  have hkp := (twosKey_pos (2 * (k : ℤ) + 4) z1 z2).mp hk
  unfold TwosSlipZ0 TwosSlipZ2
  generalize (z2 + 1 - z1) ^ 2 / 4 = Q at *
  generalize min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) = a1 at *
  generalize min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) = a2 at *
  generalize min 0 (2 * (k : ℤ) + 4 - (z2 + 2)) = a3 at *
  generalize min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 2)) = a4 at *
  generalize max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 = b1 at *
  generalize max (z2 + 2 - (z1 + 1) - (2 * (k : ℤ) + 4)) 0 = b2 at *
  generalize twosInd (2 * (k : ℤ) + 4) (z1, z2 + 1) = I1 at *
  generalize twosInd (2 * (k : ℤ) + 4) (z1 + 1, z2 + 2) = I2 at *
  split_ifs at m1 <;> omega

set_option maxHeartbeats 400000 in
/-- The class-`0` slip band on the column `z₁ = d + 1`: the tile point `(z₁+1, z₂+2)` is outside the tile, so it is vacuous. -/
theorem twos_slip_band0_dp1 (k : ℕ) {z1 z2 : ℤ} (_hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h0 : (z1 + 1, z2 + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) (hz : z1 = 2 * (k : ℤ) + 4 + 1) :
    (twosSlip k (z1, z2) = 0 ∧ TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2) ∨
      (twosSlip k (z1, z2) = 1 ∧ ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2 ∧ ¬ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) ∨
      (twosSlip k (z1, z2) = 2 ∧ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) := by
  exfalso
  rw [twos_tile_iff] at h0
  omega

/-- The `z₂`-part of the class-`U` closed form, as threshold steps. -/
theorem twos_minpartU (d z2 : ℤ) :
    min 0 (d - (z2 + 1)) + min 0 (2 * d - (z2 + 1)) - (min 0 (d - (z2 - d + 3)) + min 0 (2 * d - (z2 - d + 3))) =
      -(if d - 1 ≤ z2 then z2 - (d - 1) else 0) - (if 2 * d - 1 ≤ z2 then z2 - (2 * d - 1) else 0) +
        (if 2 * d - 3 ≤ z2 then z2 - (2 * d - 3) else 0) + (if 3 * d - 3 ≤ z2 then z2 - (3 * d - 3) else 0) := by
  split_ifs <;> omega

/-- The `z₁`-part of the class-`U` closed form: the two max terms differ by a threshold in `z₂ − z₁`. -/
theorem twos_maxpartU (d z1 z2 : ℤ) :
    max (z2 + 1 - z1 - d) 0 - max (z2 - d + 3 - (z1 - d) - d) 0 =
      (if 0 ≤ z2 + 1 - z1 - d then -2 else if z2 + 1 - z1 - d = -1 then -1 else 0) := by
  split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- The class-`0` slip band, by the column of `z₁`. -/
theorem twos_slip_band0 (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h0 : (z1 + 1, z2 + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    (twosSlip k (z1, z2) = 0 ∧ TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2) ∨
      (twosSlip k (z1, z2) = 1 ∧ ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2 ∧ ¬ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) ∨
      (twosSlip k (z1, z2) = 2 ∧ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) := by
  have hkp := (twosKey_pos (2 * (k : ℤ) + 4) z1 z2).mp hk
  rcases (by omega : z1 = -1 ∨ z1 = 0 ∨ (1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 4 - 2) ∨ z1 = 2 * (k : ℤ) + 4 - 1 ∨
      z1 = 2 * (k : ℤ) + 4 ∨ z1 = 2 * (k : ℤ) + 4 + 1) with h | h | h | h | h | h
  · exact twos_slip_band0_m1 k hk h0 h
  · exact twos_slip_band0_0 k hk h0 h
  · exact twos_slip_band0_mid k hk h0 h
  · exact twos_slip_band0_dm1 k hk h0 h
  · exact twos_slip_band0_d k hk h0 h
  · exact twos_slip_band0_dp1 k hk h0 h

/-- The slip is invariant under the kernel period: `D(z + U) = D(z)`. -/
theorem twosSlip_add_U (k : ℕ) (a : Site) :
    twosSlip k (a + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3)) = twosSlip k a := by
  have hP := twos_standardField_hasPeriods k
  have h1 := period_kernel_apply hP a
  rw [twos_kernel_explicit] at h1
  have h2 := period_kernel_apply hP (a + (frameAt (List.replicate (k + 1) Digit.two)).shortShift)
  rw [twos_kernel_explicit] at h2
  unfold twosSlip
  rw [show a + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) + (frameAt (List.replicate (k + 1) Digit.two)).shortShift =
      a + (frameAt (List.replicate (k + 1) Digit.two)).shortShift + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) by abel, h2, h1]

set_option maxHeartbeats 400000 in
/-- The class-`U` cases of the closed polygon with class-`0` failing: the exceptional points and the column strips. -/
theorem twos_slip_Ulist (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (hn : (z1 + 1, z2 + 2) ∉ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    (z1 = -1 ∧ z2 = 2 * (2 * (k : ℤ) + 4)) ∨ (z1 = 2 * (k : ℤ) + 4 - 2 ∧ z2 = 3 * (2 * (k : ℤ) + 4) - 2) ∨
      z1 = 2 * (k : ℤ) + 4 + 1 ∨ (z1 = 2 * (k : ℤ) + 4 ∧ 2 * (2 * (k : ℤ) + 4) - 3 ≤ z2) ∨
      (z1 = 2 * (k : ℤ) + 4 - 1 ∧ z2 = 3 * (2 * (k : ℤ) + 4) - 2) := by
  rw [twosKey_pos] at hk
  rw [twos_tile_iff] at hn
  omega

/-- The exceptional point `(d+1, d−2)` has slip `0`. -/
theorem twos_slip_U_dp1lo (k : ℕ) : twosSlip k (2 * (k : ℤ) + 4 + 1, 2 * (k : ℤ) + 4 - 2) = 0 := by
  have hk : TwosKey (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + 1) (2 * (k : ℤ) + 4 - 2) := by
    rw [twosKey_pos]
    omega
  have hU : (2 * (k : ℤ) + 4 + 1 - (2 * (k : ℤ) + 4), 2 * (k : ℤ) + 4 - 2 - (2 * (k : ℤ) + 4) + 3) ∈
      paperNearLadderTile (2 * (k : ℤ) + 4) := by
    rw [twos_tile_iff]
    omega
  rw [twos_slip_classU k hk hU, twos_H_pieces, twos_H_pieces]
  dsimp only
  have s1 := twosInd_spec (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + 1) (2 * (k : ℤ) + 4 - 2 + 1)
  have s2 := twosInd_spec (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + 1 - (2 * (k : ℤ) + 4))
    (2 * (k : ℤ) + 4 - 2 - (2 * (k : ℤ) + 4) + 3)
  have q1 : (2 * (k : ℤ) + 4 - 2 + 1 - (2 * (k : ℤ) + 4 + 1)) ^ 2 / 4 = 1 := by
    rw [show 2 * (k : ℤ) + 4 - 2 + 1 - (2 * (k : ℤ) + 4 + 1) = -2 by ring]
    norm_num
  have q2 : (2 * (k : ℤ) + 4 - 2 - (2 * (k : ℤ) + 4) + 3 - (2 * (k : ℤ) + 4 + 1 - (2 * (k : ℤ) + 4))) ^ 2 / 4 = 0 := by
    rw [show 2 * (k : ℤ) + 4 - 2 - (2 * (k : ℤ) + 4) + 3 - (2 * (k : ℤ) + 4 + 1 - (2 * (k : ℤ) + 4)) = 0 by ring]
    norm_num
  omega


/-- **The slip at `η = −1`** is the slip at `η = +1` translated by `−σ`, with the opposite sign:
`D₋₁(z) = F(z) − F(z − σ) = −D₊₁(z − σ)`. -/
theorem twos_slip_neg (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) (-1) z =
      -twosSlip k (z + (-1 : ℤ) • (frameAt (List.replicate (k + 1) Digit.two)).shortShift) := by
  unfold ChildFrame.slip twosSlip
  rw [neg_one_smul]
  have e : z + -(frameAt (List.replicate (k + 1) Digit.two)).shortShift +
      (frameAt (List.replicate (k + 1) Digit.two)).shortShift = z := by
    abel
  rw [e]
  ring

/-- The class-`U` value at `(d, 2d−3)`: `D = 1`. -/
theorem twos_slip_U_dA (k : ℕ) : twosSlip k ((2 * (k : ℤ) + 4), 2 * (2 * (k : ℤ) + 4) - 3) = 1 := by
  have hk : TwosKey (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - 3) := by
    rw [twosKey_pos]
    omega
  have hU : ((2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4), 2 * (2 * (k : ℤ) + 4) - 3 - (2 * (k : ℤ) + 4) + 3) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    rw [twos_tile_iff]
    omega
  rw [twos_slip_classU k hk hU, twos_H_pieces, twos_H_pieces]
  dsimp only
  have s1 := twosInd_spec (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - 3 + 1)
  have s2 := twosInd_spec (2 * (k : ℤ) + 4) ((2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4)) (2 * (2 * (k : ℤ) + 4) - 3 - (2 * (k : ℤ) + 4) + 3)
  have q1 : (2 * (2 * (k : ℤ) + 4) - 3 + 1 - (2 * (k : ℤ) + 4)) ^ 2 / 4 = ((k : ℤ) + 1) ^ 2 := by
    rw [show 2 * (2 * (k : ℤ) + 4) - 3 + 1 - (2 * (k : ℤ) + 4) = 2 * ((k : ℤ) + 1) by ring,
      show (2 * ((k : ℤ) + 1)) ^ 2 = 4 * ((k : ℤ) + 1) ^ 2 by ring]
    omega
  have q2 : (2 * (2 * (k : ℤ) + 4) - 3 - (2 * (k : ℤ) + 4) + 3 - ((2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4))) ^ 2 / 4 = ((k : ℤ) + 2) ^ 2 := by
    rw [show 2 * (2 * (k : ℤ) + 4) - 3 - (2 * (k : ℤ) + 4) + 3 - ((2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4)) = 2 * ((k : ℤ) + 2) by ring,
      show (2 * ((k : ℤ) + 2)) ^ 2 = 4 * ((k : ℤ) + 2) ^ 2 by ring]
    omega
  have ex : ((k : ℤ) + 2) ^ 2 = ((k : ℤ) + 1) ^ 2 + 2 * (k : ℤ) + 3 := by ring
  omega

/-- The class-`U` value at `(d, 2d−2)`: `D = 1`. -/
theorem twos_slip_U_dB (k : ℕ) : twosSlip k ((2 * (k : ℤ) + 4), 2 * (2 * (k : ℤ) + 4) - 2) = 1 := by
  have hk : TwosKey (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - 2) := by
    rw [twosKey_pos]
    omega
  have hU : ((2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4), 2 * (2 * (k : ℤ) + 4) - 2 - (2 * (k : ℤ) + 4) + 3) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    rw [twos_tile_iff]
    omega
  rw [twos_slip_classU k hk hU, twos_H_pieces, twos_H_pieces]
  dsimp only
  have s1 := twosInd_spec (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - 2 + 1)
  have s2 := twosInd_spec (2 * (k : ℤ) + 4) ((2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4)) (2 * (2 * (k : ℤ) + 4) - 2 - (2 * (k : ℤ) + 4) + 3)
  have q1 : (2 * (2 * (k : ℤ) + 4) - 2 + 1 - (2 * (k : ℤ) + 4)) ^ 2 / 4 = ((k : ℤ) + 1) ^ 2 + ((k : ℤ) + 1) := by
    rw [show 2 * (2 * (k : ℤ) + 4) - 2 + 1 - (2 * (k : ℤ) + 4) = 2 * (k : ℤ) + 3 by ring,
      show (2 * (k : ℤ) + 3) ^ 2 = 4 * (((k : ℤ) + 1) ^ 2 + ((k : ℤ) + 1)) + 1 by ring]
    omega
  have q2 : (2 * (2 * (k : ℤ) + 4) - 2 - (2 * (k : ℤ) + 4) + 3 - ((2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4))) ^ 2 / 4 = ((k : ℤ) + 2) ^ 2 + ((k : ℤ) + 2) := by
    rw [show 2 * (2 * (k : ℤ) + 4) - 2 - (2 * (k : ℤ) + 4) + 3 - ((2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4)) = 2 * (k : ℤ) + 5 by ring,
      show (2 * (k : ℤ) + 5) ^ 2 = 4 * (((k : ℤ) + 2) ^ 2 + ((k : ℤ) + 2)) + 1 by ring]
    omega
  have ex : ((k : ℤ) + 2) ^ 2 = ((k : ℤ) + 1) ^ 2 + 2 * (k : ℤ) + 3 := by ring
  omega

/-- The class-`U` value at `(d−1, 3d−2)`: `D = 2`. -/
theorem twos_slip_U_dM (k : ℕ) : twosSlip k ((2 * (k : ℤ) + 4) - 1, 3 * (2 * (k : ℤ) + 4) - 2) = 2 := by
  have hk : TwosKey (2 * (k : ℤ) + 4) ((2 * (k : ℤ) + 4) - 1) (3 * (2 * (k : ℤ) + 4) - 2) := by
    rw [twosKey_pos]
    omega
  have hU : ((2 * (k : ℤ) + 4) - 1 - (2 * (k : ℤ) + 4), 3 * (2 * (k : ℤ) + 4) - 2 - (2 * (k : ℤ) + 4) + 3) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    rw [twos_tile_iff]
    omega
  rw [twos_slip_classU k hk hU, twos_H_pieces, twos_H_pieces]
  dsimp only
  have s1 := twosInd_spec (2 * (k : ℤ) + 4) ((2 * (k : ℤ) + 4) - 1) (3 * (2 * (k : ℤ) + 4) - 2 + 1)
  have s2 := twosInd_spec (2 * (k : ℤ) + 4) ((2 * (k : ℤ) + 4) - 1 - (2 * (k : ℤ) + 4)) (3 * (2 * (k : ℤ) + 4) - 2 - (2 * (k : ℤ) + 4) + 3)
  have q1 : (3 * (2 * (k : ℤ) + 4) - 2 + 1 - ((2 * (k : ℤ) + 4) - 1)) ^ 2 / 4 = (2 * (k : ℤ) + 4) ^ 2 := by
    rw [show 3 * (2 * (k : ℤ) + 4) - 2 + 1 - ((2 * (k : ℤ) + 4) - 1) = 2 * (2 * (k : ℤ) + 4) by ring,
      show (2 * (2 * (k : ℤ) + 4)) ^ 2 = 4 * (2 * (k : ℤ) + 4) ^ 2 by ring]
    omega
  have q2 : (3 * (2 * (k : ℤ) + 4) - 2 - (2 * (k : ℤ) + 4) + 3 - ((2 * (k : ℤ) + 4) - 1 - (2 * (k : ℤ) + 4))) ^ 2 / 4 = (2 * (k : ℤ) + 5) ^ 2 := by
    rw [show 3 * (2 * (k : ℤ) + 4) - 2 - (2 * (k : ℤ) + 4) + 3 - ((2 * (k : ℤ) + 4) - 1 - (2 * (k : ℤ) + 4)) = 2 * (2 * (k : ℤ) + 5) by ring,
      show (2 * (2 * (k : ℤ) + 5)) ^ 2 = 4 * (2 * (k : ℤ) + 5) ^ 2 by ring]
    omega
  have ex : (2 * (k : ℤ) + 5) ^ 2 = (2 * (k : ℤ) + 4) ^ 2 + 4 * (k : ℤ) + 9 := by ring
  omega

set_option maxHeartbeats 400000 in
/-- The class-`U` column `d+1`, strip `d−1 ≤ z₂ ≤ 2d−2`: `D(z) = D(z − U)`, and `z − U = (0, z₂−d+1)` is a class-`0` point. -/
theorem twos_slip_U_dp1hi (k : ℕ) (z2 : ℤ) (h1 : (2 * (k : ℤ) + 4) - 1 ≤ z2) (h2 : z2 ≤ 2 * (2 * (k : ℤ) + 4) - 2) :
    (twosSlip k ((2 * (k : ℤ) + 4 + 1), z2) = 0 ∧ TwosSlipZ0 (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + 1) z2) ∨
      (twosSlip k ((2 * (k : ℤ) + 4 + 1), z2) = 1 ∧ ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + 1) z2 ∧ ¬ TwosSlipZ2 (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + 1) z2) ∨
      (twosSlip k ((2 * (k : ℤ) + 4 + 1), z2) = 2 ∧ TwosSlipZ2 (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + 1) z2) := by
  have hw : TwosKey (2 * (k : ℤ) + 4) 0 (z2 - (2 * (k : ℤ) + 4) + 1) := by
    rw [twosKey_pos]
    omega
  have hw0 : (0 + 1, z2 - (2 * (k : ℤ) + 4) + 1 + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    rw [twos_tile_iff]
    omega
  have hb := twos_slip_band0 k hw hw0
  have hzeq : ((2 * (k : ℤ) + 4) + 1, z2) = (0, z2 - (2 * (k : ℤ) + 4) + 1) + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) :=
    Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  have hD : twosSlip k ((2 * (k : ℤ) + 4) + 1, z2) = twosSlip k (0, z2 - (2 * (k : ℤ) + 4) + 1) := by
    rw [hzeq, twosSlip_add_U]
  rcases hb with ⟨e1, c1⟩ | ⟨e1, n1, n2⟩ | ⟨e1, c2⟩
  · left
    refine ⟨by rw [hD, e1], ?_⟩
    unfold TwosSlipZ0
    omega
  · exfalso
    unfold TwosSlipZ0 at n1
    omega
  · exfalso
    unfold TwosSlipZ2 at c2
    omega

set_option maxHeartbeats 400000 in
/-- The class-`U` column `d`, strip `2d−1 ≤ z₂ ≤ 3d−2`: `D(z) = D(z − U)`, `z − U = (−1, z₂−d+1)`. -/
theorem twos_slip_U_dhi (k : ℕ) (z2 : ℤ) (h1 : 2 * (2 * (k : ℤ) + 4) - 1 ≤ z2) (h2 : z2 ≤ 3 * (2 * (k : ℤ) + 4) - 2) :
    (twosSlip k ((2 * (k : ℤ) + 4), z2) = 0 ∧ TwosSlipZ0 (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4) z2) ∨
      (twosSlip k ((2 * (k : ℤ) + 4), z2) = 1 ∧ ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4) z2 ∧ ¬ TwosSlipZ2 (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4) z2) ∨
      (twosSlip k ((2 * (k : ℤ) + 4), z2) = 2 ∧ TwosSlipZ2 (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4) z2) := by
  have hw : TwosKey (2 * (k : ℤ) + 4) (-1) (z2 - (2 * (k : ℤ) + 4) + 1) := by
    rw [twosKey_pos]
    omega
  have hw0 : (-1 + 1, z2 - (2 * (k : ℤ) + 4) + 1 + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    rw [twos_tile_iff]
    omega
  have hb := twos_slip_band0 k hw hw0
  have hzeq : ((2 * (k : ℤ) + 4), z2) = (-1, z2 - (2 * (k : ℤ) + 4) + 1) + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) :=
    Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  have hD : twosSlip k ((2 * (k : ℤ) + 4), z2) = twosSlip k (-1, z2 - (2 * (k : ℤ) + 4) + 1) := by
    rw [hzeq, twosSlip_add_U]
  rcases hb with ⟨e1, c1⟩ | ⟨e1, n1, n2⟩ | ⟨e1, c2⟩
  · exfalso
    unfold TwosSlipZ0 at c1
    omega
  · refine Or.inr (Or.inl ⟨by rw [hD, e1], ?_, ?_⟩)
    · unfold TwosSlipZ0
      omega
    · unfold TwosSlipZ2
      unfold TwosSlipZ2 at n2
      omega
  · refine Or.inr (Or.inr ⟨by rw [hD, e1], ?_⟩)
    unfold TwosSlipZ2
    unfold TwosSlipZ2 at c2
    omega

set_option maxHeartbeats 400000 in
/-- **The slip band on the closed polygon.** Every point of `TwosKey` has `D ∈ {0,1,2}` with the threshold conditions. -/
theorem twos_slip_value (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2) :
    (twosSlip k (z1, z2) = 0 ∧ TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2) ∨
      (twosSlip k (z1, z2) = 1 ∧ ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2 ∧ ¬ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) ∨
      (twosSlip k (z1, z2) = 2 ∧ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) := by
  have hkp := (twosKey_pos (2 * (k : ℤ) + 4) z1 z2).mp hk
  by_cases hT0 : (z1 + 1, z2 + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)
  · exact twos_slip_band0 k hk hT0
  · rcases twos_slip_Ulist k hk hT0 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2
      right; right
      exact ⟨twos_slip_special1 k, by unfold TwosSlipZ2; omega⟩
    · subst h1 h2
      right; right
      exact ⟨twos_slip_special2 k, by unfold TwosSlipZ2; omega⟩
    · subst h1
      rcases (by omega : z2 = 2 * (k : ℤ) + 4 - 2 ∨
          (2 * (k : ℤ) + 4 - 1 ≤ z2 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 2)) with h | h
      · subst h
        left
        exact ⟨twos_slip_U_dp1lo k, by unfold TwosSlipZ0; omega⟩
      · exact twos_slip_U_dp1hi k z2 h.1 h.2
    · subst h1
      rcases (by omega : z2 = 2 * (2 * (k : ℤ) + 4) - 3 ∨ z2 = 2 * (2 * (k : ℤ) + 4) - 2 ∨
          (2 * (2 * (k : ℤ) + 4) - 1 ≤ z2 ∧ z2 ≤ 3 * (2 * (k : ℤ) + 4) - 2)) with h | h | h
      · subst h
        right; left
        exact ⟨twos_slip_U_dA k, by unfold TwosSlipZ0; omega, by unfold TwosSlipZ2; omega⟩
      · subst h
        right; left
        exact ⟨twos_slip_U_dB k, by unfold TwosSlipZ0; omega, by unfold TwosSlipZ2; omega⟩
      · exact twos_slip_U_dhi k z2 h.1 h.2
    · subst h1 h2
      right; right
      exact ⟨twos_slip_U_dM k, by unfold TwosSlipZ2; omega⟩

end FLatticePaper.Induction

