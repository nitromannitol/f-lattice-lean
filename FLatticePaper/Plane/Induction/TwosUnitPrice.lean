import FLatticePaper.Plane.Induction.TwosPriceDelta
import FLatticePaper.Plane.Induction.StrongEstimates

/-! Task 118, base inputs at `2^(k+1)`: `F1_unitPrice` (the primitive price has unit increments on every edge).

On the closed polygon the price is `c₀ − δ` with the bands `TwosDelta` (`twos_price_delta`). A unit step from a polygon point
lands, after a lattice shift `±U` or `±V` (the kernel and transverse periods, `twos_price_U_step`, `twos_price_V_step`), again in the
polygon (`twos_cover_*`, by explicit decision trees). Each unit step is then a finite case analysis on the bands (`omega`). Arbitrary
centres reduce to the polygon by `closedPolygon_covers`, and the price along the lattice is `P(w + iU + jV) = P w − i`
(`twos_price_lattice`). -/

namespace FLatticePaper.Induction
open Farey Construction

set_option maxHeartbeats 400000 in
/-- The kernel step: `P(a + U) = P(a) − 1`, `U = (2k+5, 2k+3)`. -/
theorem twos_price_U_step (k : ℕ) (a b : ℤ) :
    ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (a + (2 * (k : ℤ) + 5), b + (2 * (k : ℤ) + 3))) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (a, b)) - 1 := by
  have h := twos_price_drift_kernel k (a, b)
  rw [twos_kernel_explicit] at h
  simp only [Prod.mk_add_mk] at h
  linarith

set_option maxHeartbeats 400000 in
/-- The transverse step: `P(a − 2, b + 4k+8) = P(a, b)`. -/
theorem twos_price_V_step (k : ℕ) (a b : ℤ) :
    ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (a - 2, b + (4 * (k : ℤ) + 8))) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (a, b)) := by
  have h := twos_price_drift_transverse k (a, b)
  rw [twos_transverse_explicit] at h
  simp only [Prod.mk_add_mk] at h
  have e1 : a + -2 = a - 2 := by ring
  rw [e1] at h
  linarith

set_option maxHeartbeats 400000 in
/-- Integer powers of the kernel step. -/
theorem twos_price_shiftU (k : ℕ) (i : ℤ) : ∀ a b : ℤ,
    ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (a + i * (2 * (k : ℤ) + 5), b + i * (2 * (k : ℤ) + 3))) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (a, b)) - i := by
  induction i using Int.induction_on with
  | zero => intro a b; simp
  | succ n ih =>
    intro a b
    have h := twos_price_U_step k (a + (n : ℤ) * (2 * (k : ℤ) + 5)) (b + (n : ℤ) * (2 * (k : ℤ) + 3))
    have e1 : a + ((n : ℤ) + 1) * (2 * (k : ℤ) + 5) = a + (n : ℤ) * (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 5) := by ring
    have e2 : b + ((n : ℤ) + 1) * (2 * (k : ℤ) + 3) = b + (n : ℤ) * (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) := by ring
    rw [e1, e2, h, ih a b]
    ring
  | pred n ih =>
    intro a b
    have h := twos_price_U_step k (a + (-(n : ℤ) - 1) * (2 * (k : ℤ) + 5)) (b + (-(n : ℤ) - 1) * (2 * (k : ℤ) + 3))
    have e1 : a + (-(n : ℤ) - 1) * (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 5) = a + (-(n : ℤ)) * (2 * (k : ℤ) + 5) := by ring
    have e2 : b + (-(n : ℤ) - 1) * (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) = b + (-(n : ℤ)) * (2 * (k : ℤ) + 3) := by ring
    rw [e1, e2] at h
    have := ih a b
    linarith

set_option maxHeartbeats 400000 in
/-- Integer powers of the transverse step. -/
theorem twos_price_shiftV (k : ℕ) (j : ℤ) : ∀ a b : ℤ,
    ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (a + j * (-2), b + j * (4 * (k : ℤ) + 8))) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (a, b)) := by
  induction j using Int.induction_on with
  | zero => intro a b; simp
  | succ n ih =>
    intro a b
    have h := twos_price_V_step k (a + (n : ℤ) * (-2)) (b + (n : ℤ) * (4 * (k : ℤ) + 8))
    have e1 : a + ((n : ℤ) + 1) * (-2) = a + (n : ℤ) * (-2) - 2 := by ring
    have e2 : b + ((n : ℤ) + 1) * (4 * (k : ℤ) + 8) = b + (n : ℤ) * (4 * (k : ℤ) + 8) + (4 * (k : ℤ) + 8) := by ring
    rw [e1, e2, h]
    exact ih a b
  | pred n ih =>
    intro a b
    have h := twos_price_V_step k (a + (-(n : ℤ) - 1) * (-2)) (b + (-(n : ℤ) - 1) * (4 * (k : ℤ) + 8))
    have e1 : a + (-(n : ℤ) - 1) * (-2) - 2 = a + (-(n : ℤ)) * (-2) := by ring
    have e2 : b + (-(n : ℤ) - 1) * (4 * (k : ℤ) + 8) + (4 * (k : ℤ) + 8) = b + (-(n : ℤ)) * (4 * (k : ℤ) + 8) := by ring
    rw [e1, e2] at h
    rw [← h]
    exact ih a b

set_option maxHeartbeats 400000 in
/-- The price along the lattice: `P(w + iU + jV) = P(w) − i`. -/
theorem twos_price_lattice (k : ℕ) (a b i j : ℤ) :
    ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (a + (i * (2 * (k : ℤ) + 5) + j * (-2)), b + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)))) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (a, b)) - i := by
  have e1 : a + (i * (2 * (k : ℤ) + 5) + j * (-2)) = (a + i * (2 * (k : ℤ) + 5)) + j * (-2) := by ring
  have e2 : b + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)) = (b + i * (2 * (k : ℤ) + 3)) + j * (4 * (k : ℤ) + 8) := by ring
  rw [e1, e2, twos_price_shiftV k j (a + i * (2 * (k : ℤ) + 5)) (b + i * (2 * (k : ℤ) + 3)), twos_price_shiftU k i a b]

set_option maxHeartbeats 400000 in
/-- The positive form of `TwosKey`: the main box with two linear exclusions, and the four special points. -/
theorem twosKey_pos (d z1 z2 : ℤ) :
    TwosKey d z1 z2 ↔
      ((-1 ≤ z1 ∧ z1 ≤ d + 1 ∧ -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * d ∧ 0 ≤ z2 ∧ z2 ≤ 3 * d - 2) ∧
        (0 ≤ z1 ∨ d + 1 ≤ z2) ∧ (z1 ≤ d ∨ z2 ≤ 2 * d - 3)) ∨
      (z1 = -1 ∧ z2 = 2 * d) ∨ (z1 = d + 1 ∧ z2 = d - 2) ∨ (z1 = -1 ∧ z2 = d) ∨ (z1 = d + 1 ∧ z2 = 2 * d - 2) := by
  unfold TwosKey
  constructor <;> intro h <;> omega

set_option maxHeartbeats 400000 in
/-- Cover for the left step `x = y − (1,0)`: `x`, `x + U` or `x − V` is in the closed polygon. -/
theorem twos_cover_m (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) (y1) (y2)) :
    TwosKey (2 * (k : ℤ) + 4) (y1 - 1) (y2) ∨ TwosKey (2 * (k : ℤ) + 4) (y1 - 1 + (2 * (k : ℤ) + 5)) (y2 + (2 * (k : ℤ) + 3)) ∨ TwosKey (2 * (k : ℤ) + 4) (y1 - 1 + 2) (y2 - (4 * (k : ℤ) + 8)) := by
  rw [twosKey_pos] at hy
  rcases hy with ⟨hb, hm1, hm2⟩ | hs1 | hs2 | hs3 | hs4
  · by_cases h0 : y1 = -1
    · exact Or.inr (Or.inl (by rw [twosKey_pos]; omega))
    · by_cases h1 : y1 = 0 ∧ y2 ≤ 2 * (k : ℤ) + 3
      · exact Or.inr (Or.inl (by rw [twosKey_pos]; omega))
      · by_cases h2 : y2 - y1 = 2 * (2 * (k : ℤ) + 4) ∧ 1 ≤ y1
        · exact Or.inr (Or.inr (by rw [twosKey_pos]; omega))
        · exact Or.inl (by rw [twosKey_pos]; omega)
  · exact Or.inr (Or.inr (by rw [twosKey_pos]; omega))
  · exact Or.inl (by rw [twosKey_pos]; omega)
  · exact Or.inr (Or.inl (by rw [twosKey_pos]; omega))
  · exact Or.inl (by rw [twosKey_pos]; omega)

set_option maxHeartbeats 400000 in
/-- Cover for the right step `x = y + (1,0)`: `x`, `x − U` or `x + V` is in the closed polygon. -/
theorem twos_cover_p (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) (y1) (y2)) :
    TwosKey (2 * (k : ℤ) + 4) (y1 + 1) (y2) ∨ TwosKey (2 * (k : ℤ) + 4) (y1 + 1 - (2 * (k : ℤ) + 5)) (y2 - (2 * (k : ℤ) + 3)) ∨ TwosKey (2 * (k : ℤ) + 4) (y1 + 1 - 2) (y2 + (4 * (k : ℤ) + 8)) := by
  rw [twosKey_pos] at hy
  rcases hy with ⟨hb, hm1, hm2⟩ | hs1 | hs2 | hs3 | hs4
  · by_cases h0 : y1 = 2 * (k : ℤ) + 5
    · exact Or.inr (Or.inl (by rw [twosKey_pos]; omega))
    · by_cases h1 : y1 = 2 * (k : ℤ) + 4 ∧ 2 * (2 * (k : ℤ) + 4) - 1 ≤ y2
      · exact Or.inr (Or.inl (by rw [twosKey_pos]; omega))
      · by_cases h2 : y2 - y1 = -2 ∧ 2 ≤ y1
        · exact Or.inr (Or.inr (by rw [twosKey_pos]; omega))
        · exact Or.inl (by rw [twosKey_pos]; omega)
  · exact Or.inl (by rw [twosKey_pos]; omega)
  · exact Or.inr (Or.inr (by rw [twosKey_pos]; omega))
  · exact Or.inl (by rw [twosKey_pos]; omega)
  · exact Or.inr (Or.inl (by rw [twosKey_pos]; omega))

set_option maxHeartbeats 400000 in
/-- Cover for the upper step `x = y + (0,1)`: `x`, `x − V` or `x − U` is in the closed polygon. -/
theorem twos_cover_q (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) (y1) (y2)) :
    TwosKey (2 * (k : ℤ) + 4) (y1) (y2 + 1) ∨ TwosKey (2 * (k : ℤ) + 4) (y1 + 2) (y2 + 1 - (4 * (k : ℤ) + 8)) ∨ TwosKey (2 * (k : ℤ) + 4) (y1 - (2 * (k : ℤ) + 5)) (y2 + 1 - (2 * (k : ℤ) + 3)) := by
  rw [twosKey_pos] at hy
  rcases hy with ⟨hb, hm1, hm2⟩ | hs1 | hs2 | hs3 | hs4
  · by_cases h0 : y1 = 2 * (k : ℤ) + 4 ∧ y2 = 3 * (2 * (k : ℤ) + 4) - 2
    · exact Or.inr (Or.inr (by rw [twosKey_pos]; omega))
    · by_cases h1 : y1 = 2 * (k : ℤ) + 5 ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y2
      · exact Or.inr (Or.inr (by rw [twosKey_pos]; omega))
      · by_cases h2 : 2 * (2 * (k : ℤ) + 4) ≤ y2 - y1 ∨ 3 * (2 * (k : ℤ) + 4) - 2 ≤ y2
        · exact Or.inr (Or.inl (by rw [twosKey_pos]; omega))
        · exact Or.inl (by rw [twosKey_pos]; omega)
  · exact Or.inr (Or.inl (by rw [twosKey_pos]; omega))
  · exact Or.inl (by rw [twosKey_pos]; omega)
  · exact Or.inl (by rw [twosKey_pos]; omega)
  · exact Or.inr (Or.inr (by rw [twosKey_pos]; omega))

set_option maxHeartbeats 400000 in
/-- Cover for the lower step `x = y − (0,1)`: `x`, `x + U` or `x + V` is in the closed polygon. -/
theorem twos_cover_r (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) (y1) (y2)) :
    TwosKey (2 * (k : ℤ) + 4) (y1) (y2 - 1) ∨ TwosKey (2 * (k : ℤ) + 4) (y1 + (2 * (k : ℤ) + 5)) (y2 - 1 + (2 * (k : ℤ) + 3)) ∨ TwosKey (2 * (k : ℤ) + 4) (y1 - 2) (y2 - 1 + (4 * (k : ℤ) + 8)) := by
  rw [twosKey_pos] at hy
  rcases hy with ⟨hb, hm1, hm2⟩ | hs1 | hs2 | hs3 | hs4
  · by_cases h0 : y1 = 2 * (k : ℤ) + 5 ∧ y2 - y1 = -3
    · exact Or.inr (Or.inr (by rw [twosKey_pos]; omega))
    · by_cases h1 : y1 = -1 ∧ y2 = 2 * (k : ℤ) + 4
      · exact Or.inr (Or.inl (by rw [twosKey_pos]; omega))
      · by_cases h2 : y1 = 0 ∧ y2 = 0
        · exact Or.inr (Or.inl (by rw [twosKey_pos]; omega))
        · by_cases h3 : y2 = 0 ∧ 1 ≤ y1
          · exact Or.inr (Or.inr (by rw [twosKey_pos]; omega))
          · by_cases h4 : y2 - y1 = -2 ∧ 2 ≤ y1
            · exact Or.inr (Or.inr (by rw [twosKey_pos]; omega))
            · exact Or.inl (by rw [twosKey_pos]; omega)
  · exact Or.inl (by rw [twosKey_pos]; omega)
  · exact Or.inr (Or.inr (by rw [twosKey_pos]; omega))
  · exact Or.inr (Or.inl (by rw [twosKey_pos]; omega))
  · exact Or.inl (by rw [twosKey_pos]; omega)

set_option maxHeartbeats 400000 in
/-- The left unit step at a polygon point. -/
theorem twos_unit_m (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) (y1) (y2)) :
    -1 ≤ ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1 - 1, y2)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) ∧ ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1 - 1, y2)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) ≤ 1 := by
  have hd := twos_price_delta k hy
  rcases twos_cover_m k hy with h0 | hU | hV
  · have hx := twos_price_delta k h0
    unfold TwosDelta at hd hx
    omega
  · have hx := twos_price_delta k hU
    have hr := twos_price_U_step k (y1 - 1) y2
    unfold TwosDelta at hd hx
    omega
  · have hx := twos_price_delta k hV
    have hr := twos_price_V_step k (y1 - 1 + 2) (y2 - (4 * (k : ℤ) + 8))
    rw [show y1 - 1 + 2 - 2 = y1 - 1 by ring, show y2 - (4 * (k : ℤ) + 8) + (4 * (k : ℤ) + 8) = y2 by ring] at hr
    unfold TwosDelta at hd hx
    omega

set_option maxHeartbeats 400000 in
/-- The right unit step at a polygon point. -/
theorem twos_unit_p (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) (y1) (y2)) :
    -1 ≤ ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1 + 1, y2)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) ∧ ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1 + 1, y2)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) ≤ 1 := by
  have hd := twos_price_delta k hy
  rcases twos_cover_p k hy with h0 | hU | hV
  · have hx := twos_price_delta k h0
    unfold TwosDelta at hd hx
    omega
  · have hx := twos_price_delta k hU
    have hr := twos_price_U_step k (y1 + 1 - (2 * (k : ℤ) + 5)) (y2 - (2 * (k : ℤ) + 3))
    rw [show y1 + 1 - (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 5) = y1 + 1 by ring, show y2 - (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) = y2 by ring] at hr
    unfold TwosDelta at hd hx
    omega
  · have hx := twos_price_delta k hV
    have hr := twos_price_V_step k (y1 + 1) y2
    unfold TwosDelta at hd hx
    omega

set_option maxHeartbeats 400000 in
/-- The upper unit step at a polygon point. -/
theorem twos_unit_q (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) (y1) (y2)) :
    -1 ≤ ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2 + 1)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) ∧ ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2 + 1)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) ≤ 1 := by
  have hd := twos_price_delta k hy
  rcases twos_cover_q k hy with h0 | hV | hU
  · have hx := twos_price_delta k h0
    unfold TwosDelta at hd hx
    omega
  · have hx := twos_price_delta k hV
    have hr := twos_price_V_step k (y1 + 2) (y2 + 1 - (4 * (k : ℤ) + 8))
    rw [show y1 + 2 - 2 = y1 by ring, show y2 + 1 - (4 * (k : ℤ) + 8) + (4 * (k : ℤ) + 8) = y2 + 1 by ring] at hr
    unfold TwosDelta at hd hx
    omega
  · have hx := twos_price_delta k hU
    have hr := twos_price_U_step k (y1 - (2 * (k : ℤ) + 5)) (y2 + 1 - (2 * (k : ℤ) + 3))
    rw [show y1 - (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 5) = y1 by ring, show y2 + 1 - (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) = y2 + 1 by ring] at hr
    unfold TwosDelta at hd hx
    omega

set_option maxHeartbeats 400000 in
/-- The lower unit step at a polygon point. -/
theorem twos_unit_r (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) (y1) (y2)) :
    -1 ≤ ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2 - 1)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) ∧ ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2 - 1)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) ≤ 1 := by
  have hd := twos_price_delta k hy
  rcases twos_cover_r k hy with h0 | hU | hV
  · have hx := twos_price_delta k h0
    unfold TwosDelta at hd hx
    omega
  · have hx := twos_price_delta k hU
    have hr := twos_price_U_step k (y1) (y2 - 1)
    unfold TwosDelta at hd hx
    omega
  · have hx := twos_price_delta k hV
    have hr := twos_price_V_step k (y1) (y2 - 1)
    unfold TwosDelta at hd hx
    omega

set_option maxHeartbeats 400000 in
/-- **`F1_unitPrice` at `2^(k+1)`:** the primitive price has unit increments on every edge. -/
theorem twos_unitPrice (k : ℕ) :
    HasUnitPrice (frameAt (List.replicate (k + 1) Digit.two)) (standardField (List.replicate (k + 1) Digit.two)) := by
  intro center input hE
  unfold priceIncrement
  obtain ⟨y, hy, i, j, hc⟩ := (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon_covers center
  have hyT : TwosKey (2 * (k : ℤ) + 4) (y.1) (y.2) := twos_E_key k y hy
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
      have hA : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1 - 1, c2)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1 - 1, y2)) - i := by
        rw [show (c1 - 1, c2) = ((y1 - 1) + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from
          Prod.ext (by rw [hc1]; ring) (by rw [hc2])]
        exact twos_price_lattice k (y1 - 1) y2 i j
      have hB : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1, c2)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) - i := by
        rw [show (c1, c2) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2])]
        exact twos_price_lattice k y1 y2 i j
      rw [hA, hB]
      have := twos_unit_m k hyT
      constructor <;> linarith [this.1, this.2]
    · rw [hE]
      have hA : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1, c2 - 1)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2 - 1)) - i := by
        rw [show (c1, c2 - 1) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), (y2 - 1) + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from
          Prod.ext (by rw [hc1]) (by rw [hc2]; ring)]
        exact twos_price_lattice k y1 (y2 - 1) i j
      have hB : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1, c2)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) - i := by
        rw [show (c1, c2) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2])]
        exact twos_price_lattice k y1 y2 i j
      rw [hA, hB]
      have := twos_unit_r k hyT
      constructor <;> linarith [this.1, this.2]
  · unfold incomingPos at hE
    split_ifs at hE with hev
    · rw [hE]
      have hA : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1 + 1, c2)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1 + 1, y2)) - i := by
        rw [show (c1 + 1, c2) = ((y1 + 1) + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from
          Prod.ext (by rw [hc1]; ring) (by rw [hc2])]
        exact twos_price_lattice k (y1 + 1) y2 i j
      have hB : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1, c2)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) - i := by
        rw [show (c1, c2) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2])]
        exact twos_price_lattice k y1 y2 i j
      rw [hA, hB]
      have := twos_unit_p k hyT
      constructor <;> linarith [this.1, this.2]
    · rw [hE]
      have hA : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1, c2 + 1)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2 + 1)) - i := by
        rw [show (c1, c2 + 1) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), (y2 + 1) + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from
          Prod.ext (by rw [hc1]) (by rw [hc2]; ring)]
        exact twos_price_lattice k y1 (y2 + 1) i j
      have hB : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1, c2)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) - i := by
        rw [show (c1, c2) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2])]
        exact twos_price_lattice k y1 y2 i j
      rw [hA, hB]
      have := twos_unit_q k hyT
      constructor <;> linarith [this.1, this.2]

end FLatticePaper.Induction
