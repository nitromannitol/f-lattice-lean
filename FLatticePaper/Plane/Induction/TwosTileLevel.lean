import FLatticePaper.Plane.Induction.TwosFlatReduce
import FLatticePaper.Plane.Induction.TwosPriceBand
import FLatticePaper.Plane.Induction.TwosSlipForm
import FLatticePaper.Plane.Induction.TwosPriceForm
import FLatticePaper.Plane.Induction.TwosNativeCover

/-! The chain potential of sign `+1` on the tile, in closed form (step (i) of the flatness claim).

For a native point `p = (x, y)` with `TwosKey (x+1, y+1)`, `Φ(p) = (k+2)(k+3) + twosLev (2k+4) x y`. The combination
`(slip class 0, price class 0)` gives this on the polygon `dom_s0p0` (the region of the native-key points where both memberships hold);
the other three combinations are handled by the cover lemmas. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The two points and the strip of `A ∪ B`, as linear conditions. -/
theorem mem_AB_iff (d x y : ℤ) : (x, y) ∈ paperNearLadderA d ∪ paperNearLadderB d ↔
    ((x = -1 ∧ y = 2 * d + 1) ∨ (x = d + 1 ∧ y = d - 1) ∨ (y - x = d ∧ 0 < x ∧ x < d)) := by
  simp only [paperNearLadderA, paperNearLadderB, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_setOf_eq, Prod.mk.injEq]
  tauto

/-- The near-ladder value with the indicator decided. -/
theorem pnv_lin (d x y : ℤ) : paperNearLadderValue d (x, y) = -((y - x) ^ 2 / 4) + min 0 (d - y) + min 0 (2 * d - y) +
    max ((y - x) - d) 0 + (if ((x = -1 ∧ y = 2 * d + 1) ∨ (x = d + 1 ∧ y = d - 1) ∨ (y - x = d ∧ 0 < x ∧ x < d))
      then 1 else 0) := by
  rw [pnv_eq]
  simp only [mem_AB_iff]

/-- The level of the tile in the chain potential (the `±1` rule). -/
def twosLev (a x y : ℤ) : ℤ :=
  (if (y - x ≥ a ∨ (y - x = a - 1 ∧ x ≠ 0)) then 1 else 0) - (if (x - y ≥ 1 ∧ ¬ (x = a ∧ y = a - 1)) then 1 else 0)

set_option maxHeartbeats 400000 in
/-- The polygon of the combination `(slip class 0, price class 0)`: the native-key points at which both memberships hold lie in
`0 ≤ x ≤ a`, `0 ≤ y ≤ 2a−2`, `−2 ≤ y−x ≤ a`, and `x = a → y < 2a−3`. -/
theorem dom_s0p0 (k : ℤ) (x y : ℤ) (hN : NativeT (2 * k + 4) x y) (hk : TwosKey (2 * k + 4) (x + 1) (y + 1))
    (hs : (x + 1, y + 2) ∈ paperNearLadderTile (2 * k + 4))
    (hp : (x, y + (2 * k + 4) + 1) ∈ paperNearLadderTile (2 * k + 4)) :
    0 ≤ x ∧ x ≤ 2 * k + 4 ∧ 0 ≤ y ∧ y ≤ 2 * (2 * k + 4) - 2 ∧ -2 ≤ y - x ∧ y - x ≤ 2 * k + 4 ∧
      (x = 2 * k + 4 → y < 2 * (2 * k + 4) - 3) := by
  rw [mem_pnTile_iff] at hs hp
  unfold NativeT at hN
  unfold TwosKey at hk
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, fun h => by omega⟩

set_option maxHeartbeats 400000 in
/-- The arithmetic of the combination `(slip class 0, price class 0)` on its polygon: after the telescoping, the two
near-ladder values left add up to the level. -/
theorem level_arith (k : ℤ) (hk0 : 0 ≤ k) (x y : ℤ) (hx1 : 0 ≤ x) (hx2 : x ≤ 2 * k + 4) (hy1 : 0 ≤ y)
    (hy2 : y ≤ 2 * (2 * k + 4) - 2) (hd1 : -2 ≤ y - x) (hd2 : y - x ≤ 2 * k + 4) :
    (-((y + 1 - x) ^ 2 / 4) + min 0 (2 * k + 4 - (y + 1)) + min 0 (2 * (2 * k + 4) - (y + 1)) +
        max ((y + 1 - x) - (2 * k + 4)) 0 +
        (if ((x = -1 ∧ y + 1 = 2 * (2 * k + 4) + 1) ∨ (x = 2 * k + 4 + 1 ∧ y + 1 = (2 * k + 4) - 1) ∨
          (y + 1 - x = 2 * k + 4 ∧ 0 < x ∧ x < 2 * k + 4)) then 1 else 0)) -
      (-((y + 1 + (2 * k + 3) + 1 - x) ^ 2 / 4) + min 0 (2 * k + 4 - (y + 1 + (2 * k + 3) + 1)) +
        min 0 (2 * (2 * k + 4) - (y + 1 + (2 * k + 3) + 1)) +
        max ((y + 1 + (2 * k + 3) + 1 - x) - (2 * k + 4)) 0 +
        (if ((x = -1 ∧ y + 1 + (2 * k + 3) + 1 = 2 * (2 * k + 4) + 1) ∨
          (x = 2 * k + 4 + 1 ∧ y + 1 + (2 * k + 3) + 1 = (2 * k + 4) - 1) ∨
          (y + 1 + (2 * k + 3) + 1 - x = 2 * k + 4 ∧ 0 < x ∧ x < 2 * k + 4)) then 1 else 0)) +
      ((k + 1) * (x + 1) - (k + 2) * (y + 1)) + 1 =
    (k + 2) * (k + 3) + ((if (y - x ≥ 2 * k + 4 ∨ (y - x = 2 * k + 4 - 1 ∧ x ≠ 0)) then 1 else 0) -
      (if (x - y ≥ 1 ∧ ¬ (x = 2 * k + 4 ∧ y = 2 * k + 4 - 1)) then 1 else 0)) := by
  have hsq : (y + 1 + (2 * k + 3) + 1 - x) ^ 2 / 4 =
      (y + 1 - x) ^ 2 / 4 + (k + 2) * (y + 1 - x) + (k + 2) ^ 2 := by
    have e : y + 1 + (2 * k + 3) + 1 - x = (y + 1 - x) + 2 * (k + 2) := by ring
    rw [e, sq_shift_pos]
  have hm2 : min 0 (2 * (2 * k + 4) - (y + 1)) = 0 := min_eq_left (by omega)
  have hm4 : min 0 (2 * k + 4 - (y + 1 + (2 * k + 3) + 1)) = 2 * k + 4 - (y + 1 + (2 * k + 3) + 1) :=
    min_eq_right (by omega)
  rw [hsq, hm2, hm4]
  rcases le_total (y + 1) (2 * k + 4) with hy | hy
  · rw [min_eq_left (show (0 : ℤ) ≤ 2 * k + 4 - (y + 1) by omega),
      min_eq_left (show (0 : ℤ) ≤ 2 * (2 * k + 4) - (y + 1 + (2 * k + 3) + 1) by omega)]
    simp only [max_def]
    split_ifs <;> first | ring1 | (ring_nf; done) | (ring_nf; omega)
  · rw [min_eq_right (show 2 * k + 4 - (y + 1) ≤ (0 : ℤ) by omega),
      min_eq_right (show 2 * (2 * k + 4) - (y + 1 + (2 * k + 3) + 1) ≤ (0 : ℤ) by omega)]
    simp only [max_def]
    split_ifs <;> first | ring1 | (ring_nf; done) | (ring_nf; omega)

set_option maxHeartbeats 400000 in
/-- The combination `(slip class 0, price class 0)`: on its polygon, `Φ = (k+2)(k+3) + twosLev`. -/
theorem phi_s0p0 (k : ℕ) {x y : ℤ} (hN : NativeT (2 * (k : ℤ) + 4) x y)
    (hk : TwosKey (2 * (k : ℤ) + 4) (x + 1) (y + 1))
    (hs : (x + 1, y + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4))
    (hp : (x, y + (2 * (k : ℤ) + 4) + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    twosPhi k 1 (x, y) = ((k : ℤ) + 2) * ((k : ℤ) + 3) + twosLev (2 * (k : ℤ) + 4) x y := by
  have hkp := twosKey_of_native hN
  have h0 : (x + 1 - 1, y + 1 + (2 * (k : ℤ) + 3) + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    have e1 : x + 1 - 1 = x := by ring
    have e2 : y + 1 + (2 * (k : ℤ) + 3) + 1 = y + (2 * (k : ℤ) + 4) + 1 := by ring
    rw [e1, e2]
    exact hp
  unfold twosPhi
  rw [chainP_eq]
  unfold twosP
  simp only
  rw [twos_slip_class0 k hkp hs, twos_price_class0 k hk h0]
  have eB : (x + 1, y + 1 + 1) = (x + 1, y + 2) := by
    congr 1
    ring
  have eC : (x + 1 - 1, y + 1 + (2 * (k : ℤ) + 3) + 1) = (x, y + 1 + (2 * (k : ℤ) + 3) + 1) := by
    congr 1
    ring
  rw [eB, eC]
  have key : ∀ A B C L : ℤ, A - B + (B - C + L) + 1 = A - C + L + 1 := by
    intro A B C L
    ring
  rw [key]
  rw [pnv_lin (2 * (k : ℤ) + 4) x (y + 1), pnv_lin (2 * (k : ℤ) + 4) x (y + 1 + (2 * (k : ℤ) + 3) + 1)]
  obtain ⟨d1, d2, d3, d4, d5, d6, -⟩ := dom_s0p0 (k : ℤ) x y hN hk hs hp
  unfold twosLev
  exact level_arith (k : ℤ) (by positivity) x y d1 d2 d3 d4 d5 d6

set_option maxHeartbeats 400000 in
/-- The polygon of the combination `(slip class 0, price class V)`: `-1 ≤ x ≤ a-1`, `a-1 ≤ y - x ≤ 2a`, `a ≤ y+1 ≤ 3a-2`. -/
theorem dom_s0pV (k : ℤ) (x y : ℤ) (hN : NativeT (2 * k + 4) x y) (hk : TwosKey (2 * k + 4) (x + 1) (y + 1))
    (hpV : (x + 2, y + 1 - (2 * k + 4)) ∈ paperNearLadderTile (2 * k + 4)) :
    -1 ≤ x ∧ x ≤ 2 * k + 4 - 1 ∧ (2 * k + 4 ≤ y - x ∨ (x = 2 * k + 4 - 1 ∧ y = 2 * (2 * k + 4) - 2)) ∧
      y - x ≤ 2 * (2 * k + 4) ∧ 2 * k + 4 ≤ y ∧
      y ≤ 3 * (2 * k + 4) - 3 := by
  rw [mem_pnTile_iff] at hpV
  unfold NativeT at hN
  unfold TwosKey at hk
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 400000 in
/-- The arithmetic of the combination `(slip class 0, price class V)` on its polygon. -/
theorem level_s0pV (k : ℤ) (hk0 : 0 ≤ k) (x y : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 2 * k + 4 - 1)
    (h3 : 2 * k + 4 ≤ y - x ∨ (x = 2 * k + 4 - 1 ∧ y = 2 * (2 * k + 4) - 2))
    (h4 : y - x ≤ 2 * (2 * k + 4)) (h6 : 2 * k + 4 ≤ y)
    (h5 : y ≤ 3 * (2 * k + 4) - 3) :
    (-((y + 1 - x) ^ 2 / 4) + min 0 (2 * k + 4 - (y + 1)) + min 0 (2 * (2 * k + 4) - (y + 1)) +
        max ((y + 1 - x) - (2 * k + 4)) 0 +
        (if ((x = -1 ∧ y + 1 = 2 * (2 * k + 4) + 1) ∨ (x = 2 * k + 4 + 1 ∧ y + 1 = (2 * k + 4) - 1) ∨
          (y + 1 - x = 2 * k + 4 ∧ 0 < x ∧ x < 2 * k + 4)) then 1 else 0)) -
      (-((y + 1 - (2 * k + 4) - (x + 2)) ^ 2 / 4) + min 0 (2 * k + 4 - (y + 1 - (2 * k + 4))) +
        min 0 (2 * (2 * k + 4) - (y + 1 - (2 * k + 4))) +
        max ((y + 1 - (2 * k + 4) - (x + 2)) - (2 * k + 4)) 0 +
        (if ((x + 2 = -1 ∧ y + 1 - (2 * k + 4) = 2 * (2 * k + 4) + 1) ∨
          (x + 2 = 2 * k + 4 + 1 ∧ y + 1 - (2 * k + 4) = (2 * k + 4) - 1) ∨
          (y + 1 - (2 * k + 4) - (x + 2) = 2 * k + 4 ∧ 0 < x + 2 ∧ x + 2 < 2 * k + 4)) then 1 else 0)) -
      (1 - (2 * k + 4) ^ 2 - 3 * (2 * k + 4)) + ((2 * k + 5) * (y + 1 - (2 * k + 4) - 1) - (2 * k + 3) * (x + 2)) +
      ((k + 1) * (x + 1) - (k + 2) * (y + 1)) + 1 =
    (k + 2) * (k + 3) + ((if (y - x ≥ 2 * k + 4 ∨ (y - x = 2 * k + 4 - 1 ∧ x ≠ 0)) then 1 else 0) -
      (if (x - y ≥ 1 ∧ ¬ (x = 2 * k + 4 ∧ y = 2 * k + 4 - 1)) then 1 else 0)) := by
  have hsq : (y + 1 - (2 * k + 4) - (x + 2)) ^ 2 / 4 =
      (y + 1 - x) ^ 2 / 4 - (k + 3) * (y + 1 - x) + (k + 3) ^ 2 := by
    have e : y + 1 - (2 * k + 4) - (x + 2) = (y + 1 - x) - 2 * (k + 3) := by ring
    rw [e, sq_shift_neg]
  rw [hsq]
  have hm1 : min 0 (2 * k + 4 - (y + 1)) = 2 * k + 4 - (y + 1) := min_eq_right (by omega)
  have hm3 : min 0 (2 * (2 * k + 4) - (y + 1 - (2 * k + 4))) = 0 := min_eq_left (by omega)
  have hmx1 : max ((y + 1 - x) - (2 * k + 4)) 0 = (y + 1 - x) - (2 * k + 4) := max_eq_left (by omega)
  have hmx2 : max ((y + 1 - (2 * k + 4) - (x + 2)) - (2 * k + 4)) 0 = 0 := max_eq_right (by omega)
  rw [hm1, hm3, hmx1, hmx2]
  rcases le_total (y + 1) (2 * (2 * k + 4)) with hy | hy
  · rw [min_eq_left (show (0 : ℤ) ≤ 2 * (2 * k + 4) - (y + 1) by omega),
      min_eq_left (show (0 : ℤ) ≤ 2 * k + 4 - (y + 1 - (2 * k + 4)) by omega)]
    split_ifs <;> first | ring1 | (ring_nf; done) | (ring_nf; omega)
  · rw [min_eq_right (show 2 * (2 * k + 4) - (y + 1) ≤ (0 : ℤ) by omega),
      min_eq_right (show 2 * k + 4 - (y + 1 - (2 * k + 4)) ≤ (0 : ℤ) by omega)]
    split_ifs <;> first | ring1 | (ring_nf; done) | (ring_nf; omega)

set_option maxHeartbeats 400000 in
/-- The combination `(slip class 0, price class V)`: on its polygon, `Φ = (k+2)(k+3) + twosLev`. -/
theorem phi_s0pV (k : ℕ) {x y : ℤ} (hN : NativeT (2 * (k : ℤ) + 4) x y)
    (hk : TwosKey (2 * (k : ℤ) + 4) (x + 1) (y + 1))
    (hs : (x + 1, y + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4))
    (hpV : (x + 2, y + 1 - (2 * (k : ℤ) + 4)) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    twosPhi k 1 (x, y) = ((k : ℤ) + 2) * ((k : ℤ) + 3) + twosLev (2 * (k : ℤ) + 4) x y := by
  have hkp := twosKey_of_native hN
  have hV : (x + 1 + 1, y + 1 - (2 * (k : ℤ) + 4)) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    have e1 : x + 1 + 1 = x + 2 := by ring
    rw [e1]
    exact hpV
  unfold twosPhi
  rw [chainP_eq]
  unfold twosP
  simp only
  rw [twos_slip_class0 k hkp hs, twos_price_classV k hk hV]
  have eB : (x + 1, y + 1 + 1) = (x + 1, y + 2) := by
    congr 1
    ring
  have eD : (x + 1 + 1, y + 1 - (2 * (k : ℤ) + 4)) = (x + 2, y + 1 - (2 * (k : ℤ) + 4)) := by
    congr 1
    ring
  rw [eB, eD]
  rw [pnv_lin (2 * (k : ℤ) + 4) x (y + 1), pnv_lin (2 * (k : ℤ) + 4) (x + 2) (y + 1 - (2 * (k : ℤ) + 4))]
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := dom_s0pV (k : ℤ) x y hN hk hpV
  unfold twosLev
  have core := level_s0pV (k : ℤ) (by positivity) x y d1 d2 d3 d4 d5 d6
  linarith [core]

end FLatticePaper.TwosEPolicy
