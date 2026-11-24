import FLatticePaper.Plane.Induction.TwosSlipUnit

/-! Task 118, base slip at `2^(k+1)`: `F1_noSlipSaddle` (no even slip saddle).

At a polygon point `y` with `D(y)` even, the two incoming slip increments are not opposite unit steps. The horizontal pair (at an
even `y`) or the vertical pair (at an odd `y`) of incoming neighbours each has a cover candidate in the polygon, related to the
neighbour by a kernel shift (`D` unchanged) or a transverse shift (`D` shifted by `2`); the bands of `twos_slip_value` decide each
of the nine case combinations (`omega`). -/

namespace FLatticePaper.Induction
open Farey Construction

/-- The kernel shift in coordinates: `D(a) = D(c)` when `c = a + U`. -/
theorem twosSlip_U_of' (k : ℕ) (a1 a2 c1 c2 : ℤ) (h1 : c1 = a1 + (2 * (k : ℤ) + 5))
    (h2 : c2 = a2 + (2 * (k : ℤ) + 3)) : twosSlip k (a1, a2) = twosSlip k (c1, c2) := by
  subst h1 h2
  exact (twosSlip_add_U k (a1, a2)).symm

/-- The transverse shift in coordinates: `D(c) = D(a) + 2` when `c = a + V`. -/
theorem twosSlip_V_of' (k : ℕ) (a1 a2 c1 c2 : ℤ) (h1 : c1 = a1 + -2)
    (h2 : c2 = a2 + (4 * (k : ℤ) + 8)) : twosSlip k (c1, c2) = twosSlip k (a1, a2) + 2 := by
  subst h1 h2
  exact twosSlip_add_V k (a1, a2)

set_option maxHeartbeats 400000 in
theorem twos_saddle_h_00 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 0)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 - 1) (y2))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 + 1) (y2)) :
    ¬((twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_h_01 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 0)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 - 1) (y2))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 + 1 - (2 * (k : ℤ) + 5)) (y2 - (2 * (k : ℤ) + 3))) :
    ¬((twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have rb := twosSlip_U_of' k (y1 + 1 - (2 * (k : ℤ) + 5)) (y2 - (2 * (k : ℤ) + 3)) (y1 + 1) y2 (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_h_02 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 0)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 - 1) (y2))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 + 1 - 2) (y2 + (4 * (k : ℤ) + 8))) :
    ¬((twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have rb := twosSlip_V_of' k (y1 + 1) y2 (y1 + 1 - 2) (y2 + (4 * (k : ℤ) + 8)) (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_h_10 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 0)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 - 1 + (2 * (k : ℤ) + 5)) (y2 + (2 * (k : ℤ) + 3)))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 + 1) (y2)) :
    ¬((twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have ra := twosSlip_U_of' k (y1 - 1) y2 (y1 - 1 + (2 * (k : ℤ) + 5)) (y2 + (2 * (k : ℤ) + 3)) (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_h_11 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 0)
    (_hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 - 1 + (2 * (k : ℤ) + 5)) (y2 + (2 * (k : ℤ) + 3)))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 + 1 - (2 * (k : ℤ) + 5)) (y2 - (2 * (k : ℤ) + 3))) :
    ¬((twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have ra := twosSlip_U_of' k (y1 - 1) y2 (y1 - 1 + (2 * (k : ℤ) + 5)) (y2 + (2 * (k : ℤ) + 3)) (by ring) (by ring)
  have rb := twosSlip_U_of' k (y1 + 1 - (2 * (k : ℤ) + 5)) (y2 - (2 * (k : ℤ) + 3)) (y1 + 1) y2 (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_h_12 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 0)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 - 1 + (2 * (k : ℤ) + 5)) (y2 + (2 * (k : ℤ) + 3)))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 + 1 - 2) (y2 + (4 * (k : ℤ) + 8))) :
    ¬((twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have ra := twosSlip_U_of' k (y1 - 1) y2 (y1 - 1 + (2 * (k : ℤ) + 5)) (y2 + (2 * (k : ℤ) + 3)) (by ring) (by ring)
  have rb := twosSlip_V_of' k (y1 + 1) y2 (y1 + 1 - 2) (y2 + (4 * (k : ℤ) + 8)) (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_h_20 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 0)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 - 1 + 2) (y2 - (4 * (k : ℤ) + 8)))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 + 1) (y2)) :
    ¬((twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have ra := twosSlip_V_of' k (y1 - 1 + 2) (y2 - (4 * (k : ℤ) + 8)) (y1 - 1) y2 (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_h_21 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 0)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 - 1 + 2) (y2 - (4 * (k : ℤ) + 8)))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 + 1 - (2 * (k : ℤ) + 5)) (y2 - (2 * (k : ℤ) + 3))) :
    ¬((twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have ra := twosSlip_V_of' k (y1 - 1 + 2) (y2 - (4 * (k : ℤ) + 8)) (y1 - 1) y2 (by ring) (by ring)
  have rb := twosSlip_U_of' k (y1 + 1 - (2 * (k : ℤ) + 5)) (y2 - (2 * (k : ℤ) + 3)) (y1 + 1) y2 (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_h_22 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 0)
    (_hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 - 1 + 2) (y2 - (4 * (k : ℤ) + 8)))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 + 1 - 2) (y2 + (4 * (k : ℤ) + 8))) :
    ¬((twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have ra := twosSlip_V_of' k (y1 - 1 + 2) (y2 - (4 * (k : ℤ) + 8)) (y1 - 1) y2 (by ring) (by ring)
  have rb := twosSlip_V_of' k (y1 + 1) y2 (y1 + 1 - 2) (y2 + (4 * (k : ℤ) + 8)) (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
/-- The horizontal saddle at an even polygon point with even slip. -/
theorem twos_saddle_h (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 0)
    (hD : twosSlip k (y1, y2) % 2 = 0) :
    ¬((twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1 - 1, y2) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1 + 1, y2) - twosSlip k (y1, y2) = -1)) := by
  rcases twos_cover_m k hy with hA0 | hA1 | hA2 <;> rcases twos_cover_p k hy with hB0 | hB1 | hB2
  · exact twos_saddle_h_00 k hy hpar hD hA0 hB0
  · exact twos_saddle_h_01 k hy hpar hD hA0 hB1
  · exact twos_saddle_h_02 k hy hpar hD hA0 hB2
  · exact twos_saddle_h_10 k hy hpar hD hA1 hB0
  · exact twos_saddle_h_11 k hy hpar hD hA1 hB1
  · exact twos_saddle_h_12 k hy hpar hD hA1 hB2
  · exact twos_saddle_h_20 k hy hpar hD hA2 hB0
  · exact twos_saddle_h_21 k hy hpar hD hA2 hB1
  · exact twos_saddle_h_22 k hy hpar hD hA2 hB2

set_option maxHeartbeats 400000 in
theorem twos_saddle_v_00 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 1)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1) (y2 - 1))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1) (y2 + 1)) :
    ¬((twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_v_01 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 1)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1) (y2 - 1))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 + 2) (y2 + 1 - (4 * (k : ℤ) + 8))) :
    ¬((twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have rb := twosSlip_V_of' k (y1 + 2) (y2 + 1 - (4 * (k : ℤ) + 8)) y1 (y2 + 1) (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_v_02 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 1)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1) (y2 - 1))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 - (2 * (k : ℤ) + 5)) (y2 + 1 - (2 * (k : ℤ) + 3))) :
    ¬((twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have rb := twosSlip_U_of' k (y1 - (2 * (k : ℤ) + 5)) (y2 + 1 - (2 * (k : ℤ) + 3)) y1 (y2 + 1) (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_v_10 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 1)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 + (2 * (k : ℤ) + 5)) (y2 - 1 + (2 * (k : ℤ) + 3)))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1) (y2 + 1)) :
    ¬((twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have ra := twosSlip_U_of' k y1 (y2 - 1) (y1 + (2 * (k : ℤ) + 5)) (y2 - 1 + (2 * (k : ℤ) + 3)) (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_v_11 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 1)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 + (2 * (k : ℤ) + 5)) (y2 - 1 + (2 * (k : ℤ) + 3)))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 + 2) (y2 + 1 - (4 * (k : ℤ) + 8))) :
    ¬((twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have ra := twosSlip_U_of' k y1 (y2 - 1) (y1 + (2 * (k : ℤ) + 5)) (y2 - 1 + (2 * (k : ℤ) + 3)) (by ring) (by ring)
  have rb := twosSlip_V_of' k (y1 + 2) (y2 + 1 - (4 * (k : ℤ) + 8)) y1 (y2 + 1) (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_v_12 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 1)
    (_hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 + (2 * (k : ℤ) + 5)) (y2 - 1 + (2 * (k : ℤ) + 3)))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 - (2 * (k : ℤ) + 5)) (y2 + 1 - (2 * (k : ℤ) + 3))) :
    ¬((twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have ra := twosSlip_U_of' k y1 (y2 - 1) (y1 + (2 * (k : ℤ) + 5)) (y2 - 1 + (2 * (k : ℤ) + 3)) (by ring) (by ring)
  have rb := twosSlip_U_of' k (y1 - (2 * (k : ℤ) + 5)) (y2 + 1 - (2 * (k : ℤ) + 3)) y1 (y2 + 1) (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_v_20 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 1)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 - 2) (y2 - 1 + (4 * (k : ℤ) + 8)))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1) (y2 + 1)) :
    ¬((twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have ra := twosSlip_V_of' k y1 (y2 - 1) (y1 - 2) (y2 - 1 + (4 * (k : ℤ) + 8)) (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_v_21 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 1)
    (_hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 - 2) (y2 - 1 + (4 * (k : ℤ) + 8)))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 + 2) (y2 + 1 - (4 * (k : ℤ) + 8))) :
    ¬((twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have ra := twosSlip_V_of' k y1 (y2 - 1) (y1 - 2) (y2 - 1 + (4 * (k : ℤ) + 8)) (by ring) (by ring)
  have rb := twosSlip_V_of' k (y1 + 2) (y2 + 1 - (4 * (k : ℤ) + 8)) y1 (y2 + 1) (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
theorem twos_saddle_v_22 (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 1)
    (hD : twosSlip k (y1, y2) % 2 = 0)
    (hA : TwosKey (2 * (k : ℤ) + 4) (y1 - 2) (y2 - 1 + (4 * (k : ℤ) + 8)))
    (hB : TwosKey (2 * (k : ℤ) + 4) (y1 - (2 * (k : ℤ) + 5)) (y2 + 1 - (2 * (k : ℤ) + 3))) :
    ¬((twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = -1)) := by
  have hv := twos_slip_value k hy
  have hyp := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hy
  have ba := twos_slip_value k hA
  have bb := twos_slip_value k hB
  have pa := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hA
  have pb := (twosKey_pos (2 * (k : ℤ) + 4) _ _).mp hB
  have ra := twosSlip_V_of' k y1 (y2 - 1) (y1 - 2) (y2 - 1 + (4 * (k : ℤ) + 8)) (by ring) (by ring)
  have rb := twosSlip_U_of' k (y1 - (2 * (k : ℤ) + 5)) (y2 + 1 - (2 * (k : ℤ) + 3)) y1 (y2 + 1) (by ring) (by ring)
  simp only [TwosSlipZ0, TwosSlipZ2] at hv ba bb
  omega
set_option maxHeartbeats 400000 in
/-- The vertical saddle at an odd polygon point with even slip. -/
theorem twos_saddle_v (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) y1 y2) (hpar : (y1 + y2) % 2 = 1)
    (hD : twosSlip k (y1, y2) % 2 = 0) :
    ¬((twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = -1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = 1) ∨ (twosSlip k (y1, y2 - 1) - twosSlip k (y1, y2) = 1 ∧ twosSlip k (y1, y2 + 1) - twosSlip k (y1, y2) = -1)) := by
  rcases twos_cover_r k hy with hA0 | hA1 | hA2 <;> rcases twos_cover_q k hy with hB0 | hB1 | hB2
  · exact twos_saddle_v_00 k hy hpar hD hA0 hB0
  · exact twos_saddle_v_01 k hy hpar hD hA0 hB1
  · exact twos_saddle_v_02 k hy hpar hD hA0 hB2
  · exact twos_saddle_v_10 k hy hpar hD hA1 hB0
  · exact twos_saddle_v_11 k hy hpar hD hA1 hB1
  · exact twos_saddle_v_12 k hy hpar hD hA1 hB2
  · exact twos_saddle_v_20 k hy hpar hD hA2 hB0
  · exact twos_saddle_v_21 k hy hpar hD hA2 hB1
  · exact twos_saddle_v_22 k hy hpar hD hA2 hB2

/-- The incoming slip increments of the twos slip are the slip differences at the incoming sites. -/
theorem twos_slipIncrement_eq (k : ℕ) (c i : Site) :
    slipIncrement (standardField (List.replicate (k + 1) Digit.two))
      (fun z => standardField (List.replicate (k + 1) Digit.two) (z + (frameAt (List.replicate (k + 1) Digit.two)).shortShift))
      c i = twosSlip k i - twosSlip k c := rfl

set_option maxHeartbeats 400000 in
/-- **`F1_noSlipSaddle` at `2^(k+1)`:** at an even slip the two incoming increments are not opposite unit steps. -/
theorem twos_noSlipSaddle (k : ℕ) :
    NoEvenSlipSaddle (standardField (List.replicate (k + 1) Digit.two))
      (fun z => standardField (List.replicate (k + 1) Digit.two) (z + (frameAt (List.replicate (k + 1) Digit.two)).shortShift)) := by
  intro site hpar
  have hpar' : twosSlip k site % 2 = 0 := hpar
  dsimp only
  simp only [twos_slipIncrement_eq]
  obtain ⟨y, hy, i, j, hc⟩ := (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon_covers site
  have hyT : TwosKey (2 * (k : ℤ) + 4) y.1 y.2 := twos_E_key k y hy
  have hcomb : (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.combine i j =
      (i * (2 * (k : ℤ) + 5) + j * (-2), i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)) := by
    unfold PeriodDeck.combine
    rw [twos_kernel_explicit, twos_transverse_explicit]
  rw [hcomb] at hc
  obtain ⟨y1, y2⟩ := y
  obtain ⟨c1, c2⟩ := site
  have hc1 : c1 = y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)) := by
    have := congrArg Prod.fst hc
    simpa using this
  have hc2 : c2 = y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)) := by
    have := congrArg Prod.snd hc
    simpa using this
  have hS : twosSlip k (c1, c2) = twosSlip k (y1, y2) + 2 * j := by
    rw [show (c1, c2) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)))
      from Prod.ext (by rw [hc1]) (by rw [hc2])]
    exact twosSlip_lattice k (y1, y2) i j
  have hyD : twosSlip k (y1, y2) % 2 = 0 := by
    rw [hS] at hpar'
    omega
  have hsum : (c1 + c2) % 2 = (y1 + y2) % 2 := by
    rw [hc1, hc2, show y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)) + (y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)))
      = (y1 + y2) + 2 * (i * (2 * (k : ℤ) + 4) + j * (2 * (k : ℤ) + 3)) by ring]
    exact Int.add_mul_emod_self_left _ _ _
  by_cases hev : (c1 + c2) % 2 = 0
  · have hev' : EvenSite (c1, c2) := hev
    have hyev : (y1 + y2) % 2 = 0 := by omega
    simp only [incomingNeg, incomingPos, if_pos hev']
    have hA : twosSlip k (c1 - 1, c2) = twosSlip k (y1 - 1, y2) + 2 * j := by
      rw [show (c1 - 1, c2) = (y1 - 1 + (i * (2 * (k : ℤ) + 5) + j * (-2)),
        y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]; ring) (by rw [hc2])]
      exact twosSlip_lattice k (y1 - 1, y2) i j
    have hB : twosSlip k (c1 + 1, c2) = twosSlip k (y1 + 1, y2) + 2 * j := by
      rw [show (c1 + 1, c2) = (y1 + 1 + (i * (2 * (k : ℤ) + 5) + j * (-2)),
        y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]; ring) (by rw [hc2])]
      exact twosSlip_lattice k (y1 + 1, y2) i j
    rw [hA, hB, hS]
    have key := twos_saddle_h k hyT hyev hyD
    intro hcon
    apply key
    rcases hcon with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · have hev' : ¬ EvenSite (c1, c2) := hev
    have hyodd : (y1 + y2) % 2 = 1 := by omega
    simp only [incomingNeg, incomingPos, if_neg hev']
    have hA : twosSlip k (c1, c2 - 1) = twosSlip k (y1, y2 - 1) + 2 * j := by
      rw [show (c1, c2 - 1) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)),
        y2 - 1 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2]; ring)]
      exact twosSlip_lattice k (y1, y2 - 1) i j
    have hB : twosSlip k (c1, c2 + 1) = twosSlip k (y1, y2 + 1) + 2 * j := by
      rw [show (c1, c2 + 1) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)),
        y2 + 1 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2]; ring)]
      exact twosSlip_lattice k (y1, y2 + 1) i j
    rw [hA, hB, hS]
    have key := twos_saddle_v k hyT hyodd hyD
    intro hcon
    apply key
    rcases hcon with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩

end FLatticePaper.Induction
