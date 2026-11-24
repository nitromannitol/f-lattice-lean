import FLatticePaper.Plane.Induction.TwosTileCover
import FLatticePaper.Plane.Induction.TwosDrifts

/-! Task 72 / twos base: the price range of `standardField (2^(k+1))` on its closed polygon, from the native tile.

On the closed polygon `E`, with `d = 2k+4`, `m = k+2`, the price is `P(z) = F(z) − F(z − v) + ((k+1) z₁ − (k+2) z₂)` for the
parent shift `v = (1, −(d−1))`. The three shifts of `twos_shift_cover` give `F(z − v)` as the near-one closed form at a shifted
point (case A: `z − v`; case B: `z − v − V`, with the transverse constant `cV = 1 − d² − 3d` and the transverse grade; case C:
`z − v + U`). The quadratic terms of the closed form cancel exactly (`sq_div4_add`), and what is left is a piecewise linear
bound on `E`. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- `(q + 2c)²/4 = q²/4 + q c + c²` (exact: the difference is a multiple of four). -/
theorem sq_div4_add (q c : ℤ) : (q + 2 * c) ^ 2 / 4 = q ^ 2 / 4 + q * c + c ^ 2 := by
  have h : (q + 2 * c) ^ 2 = q ^ 2 + 4 * (q * c + c ^ 2) := by ring
  rw [h, Int.add_mul_ediv_left _ (q * c + c ^ 2) (by norm_num : (4 : ℤ) ≠ 0)]
  ring

/-- The cut price of `2^(k+1)`: `k² + 5k + 5`. -/
theorem twos_cutPrice (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).cutPrice = (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  unfold ChildFrame.cutPrice
  rw [twos_eps_explicit, twos_parents_explicit]
  simp [Fraction.periodDenominator]
  ring_nf
  omega

/-- The price of `2^(k+1)` in explicit form: `P(z) = F z − F(z₁−1, z₂+2k+3) + ((k+1) z₁ − (k+2) z₂)`. -/
theorem twos_price_unfold (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) z =
      standardField (List.replicate (k + 1) Digit.two) z -
        standardField (List.replicate (k + 1) Digit.two) (z.1 - 1, z.2 + (2 * (k : ℤ) + 3)) +
        (((k : ℤ) + 1) * z.1 - ((k : ℤ) + 2) * z.2) := by
  unfold ChildFrame.price
  rw [twos_eps_explicit, twos_parentSlope_explicit, twos_parentShift_explicit]
  have hs : z - (1, -(2 * (k : ℤ) + 3)) = (z.1 - 1, z.2 + (2 * (k : ℤ) + 3)) := by
    ext
    · simp
    · simp
      ring
  rw [hs]
  ring

/-- The closed-polygon arithmetic of `twos_E_arith` (with `v = z₂ − z₁`), as one predicate. -/
def TwosKey (d z1 z2 : ℤ) : Prop :=
  (-1 ≤ z1 ∧ z1 ≤ d + 1 ∧ -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * d ∧ 0 ≤ z1 + (z2 - z1) ∧
      z1 + (z2 - z1) ≤ 3 * d - 2 ∧ ¬(z1 = -1 ∧ z1 + (z2 - z1) ≤ d) ∧
      ¬(z1 = d + 1 ∧ 2 * d - 2 ≤ z1 + (z2 - z1))) ∨
    (z1 = -1 ∧ z2 - z1 = 2 * d + 1) ∨ (z1 = d + 1 ∧ z2 - z1 = -3) ∨
    (z1 = -1 ∧ z1 + (z2 - z1) = d) ∨ (z1 = d + 1 ∧ z1 + (z2 - z1) = 2 * d - 2)

/-- The main closed-polygon case of `TwosKey`. -/
def KeyMain (d z1 z2 : ℤ) : Prop :=
  (-1 ≤ z1 ∧ z1 ≤ d + 1 ∧ -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * d ∧ 0 ≤ z1 + (z2 - z1) ∧
      z1 + (z2 - z1) ≤ 3 * d - 2 ∧ ¬(z1 = -1 ∧ z1 + (z2 - z1) ≤ d) ∧ ¬(z1 = d + 1 ∧ 2 * d - 2 ≤ z1 + (z2 - z1)))

/-- The special closed-polygon case `s1` of `TwosKey`. -/
def KeyS1 (d z1 z2 : ℤ) : Prop :=
  (z1 = -1 ∧ z2 - z1 = 2 * d + 1)

/-- The special closed-polygon case `s2` of `TwosKey`. -/
def KeyS2 (d z1 z2 : ℤ) : Prop :=
  (z1 = d + 1 ∧ z2 - z1 = -3)

/-- The special closed-polygon case `s3` of `TwosKey`. -/
def KeyS3 (d z1 z2 : ℤ) : Prop :=
  (z1 = -1 ∧ z1 + (z2 - z1) = d)

/-- The special closed-polygon case `s4` of `TwosKey`. -/
def KeyS4 (d z1 z2 : ℤ) : Prop :=
  (z1 = d + 1 ∧ z1 + (z2 - z1) = 2 * d - 2)

/-- The closed polygon of `2^(k+1)` satisfies `TwosKey` (the output of `twos_E_arith`). -/
theorem twos_E_key (k : ℕ) (z : Site)
    (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon) :
    TwosKey (2 * (k : ℤ) + 4) z.1 z.2 := by
  obtain ⟨hn, hd⟩ := twos_child_num_den k
  have hT : (frameAt (List.replicate (k + 1) Digit.two)).child.periodDenominator =
      2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) := by
    simp only [Fraction.periodDenominator, hn, hd]
    ring
  obtain ⟨z1, z2⟩ := z
  rw [ChildFrame.mem_closedPolygon_iff] at hz
  simp only [ChildFrame.tGrade, ChildFrame.sGrade, hn, hd, hT, EvenSite] at hz
  have hu0 : 0 ≤ (2 * (k : ℤ) + 4 + 1) * z1 + (z2 - z1) := by
    rcases hz with ⟨_, _, _, h3, _⟩ | ⟨_, _, _, h3, _⟩ <;> linarith
  have huP : (2 * (k : ℤ) + 4 + 1) * z1 + (z2 - z1) ≤
      (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1 + (2 * (k : ℤ) + 4) - 1 := by
    rcases hz with ⟨_, _, _, _, h4⟩ | ⟨_, _, _, _, h4⟩ <;> linarith
  have hev : (z2 - z1) % 2 = 0 → 2 - 2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) ≤
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ∧
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ≤ 2 * (2 * (k : ℤ) + 4) - 2 := by
    intro hv
    rcases hz with ⟨_, h1, h2, _, _⟩ | ⟨ho, _⟩
    · exact ⟨by linarith, by linarith⟩
    · exfalso
      omega
  have hod : (z2 - z1) % 2 = 1 → (2 * (k : ℤ) + 4) - 1 - 2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) ≤
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ∧
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ≤ (2 * (k : ℤ) + 4) + 1 := by
    intro hv
    rcases hz with ⟨he, _, _, _, _⟩ | ⟨_, h1, h2, _, _⟩
    · exfalso
      omega
    · exact ⟨by linarith, by linarith⟩
  exact twos_E_arith (2 * (k : ℤ) + 4) z1 (z2 - z1) (by omega) hu0 huP hev hod

set_option maxHeartbeats 400000 in
theorem priceA_main (k : ℕ) (z1 z2 : ℤ) (hk : KeyMain (2 * (k : ℤ) + 4) z1 z2)
    (hP0 : 0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyMain at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 + (2 * (k : ℤ) + 4) - (z1 - 1) = (z2 + 1 - z1) + 2 * ((k : ℤ) + 2) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  obtain ⟨hP0a, hP0b, hP0c⟩ := hP0
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceA_s1 (k : ℕ) (z1 z2 : ℤ) (hk : KeyS1 (2 * (k : ℤ) + 4) z1 z2)
    (hP0 : 0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyS1 at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 + (2 * (k : ℤ) + 4) - (z1 - 1) = (z2 + 1 - z1) + 2 * ((k : ℤ) + 2) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  obtain ⟨hP0a, hP0b, hP0c⟩ := hP0
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceA_s2 (k : ℕ) (z1 z2 : ℤ) (hk : KeyS2 (2 * (k : ℤ) + 4) z1 z2)
    (hP0 : 0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyS2 at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 + (2 * (k : ℤ) + 4) - (z1 - 1) = (z2 + 1 - z1) + 2 * ((k : ℤ) + 2) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  obtain ⟨hP0a, hP0b, hP0c⟩ := hP0
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceA_s3 (k : ℕ) (z1 z2 : ℤ) (hk : KeyS3 (2 * (k : ℤ) + 4) z1 z2)
    (hP0 : 0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyS3 at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 + (2 * (k : ℤ) + 4) - (z1 - 1) = (z2 + 1 - z1) + 2 * ((k : ℤ) + 2) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  obtain ⟨hP0a, hP0b, hP0c⟩ := hP0
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceA_s4 (k : ℕ) (z1 z2 : ℤ) (hk : KeyS4 (2 * (k : ℤ) + 4) z1 z2)
    (hP0 : 0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyS4 at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 + (2 * (k : ℤ) + 4) - (z1 - 1) = (z2 + 1 - z1) + 2 * ((k : ℤ) + 2) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  obtain ⟨hP0a, hP0b, hP0c⟩ := hP0
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceB_main (k : ℕ) (z1 z2 : ℤ) (hk : KeyMain (2 * (k : ℤ) + 4) z1 z2)
    (hA : ¬(0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (hC : ¬((z1 = -1 ∧ z2 - z1 = 2 * (k : ℤ) + 4 + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1))) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) -
          ((1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4)) -
            ((2 * (k : ℤ) + 5) * (z2 - (2 * (k : ℤ) + 5)) - (2 * (k : ℤ) + 3) * (z1 + 1))) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) -
          ((1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4)) -
            ((2 * (k : ℤ) + 5) * (z2 - (2 * (k : ℤ) + 5)) - (2 * (k : ℤ) + 3) * (z1 + 1))) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyMain at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 - (2 * (k : ℤ) + 4) - (z1 + 1) = (z2 + 1 - z1) + 2 * (-((k : ℤ) + 3)) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceB_s1 (k : ℕ) (z1 z2 : ℤ) (hk : KeyS1 (2 * (k : ℤ) + 4) z1 z2)
    (_hA : ¬(0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (_hC : ¬((z1 = -1 ∧ z2 - z1 = 2 * (k : ℤ) + 4 + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1))) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) -
          ((1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4)) -
            ((2 * (k : ℤ) + 5) * (z2 - (2 * (k : ℤ) + 5)) - (2 * (k : ℤ) + 3) * (z1 + 1))) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) -
          ((1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4)) -
            ((2 * (k : ℤ) + 5) * (z2 - (2 * (k : ℤ) + 5)) - (2 * (k : ℤ) + 3) * (z1 + 1))) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyS1 at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 - (2 * (k : ℤ) + 4) - (z1 + 1) = (z2 + 1 - z1) + 2 * (-((k : ℤ) + 3)) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceB_s2 (k : ℕ) (z1 z2 : ℤ) (hk : KeyS2 (2 * (k : ℤ) + 4) z1 z2)
    (hA : ¬(0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (hC : ¬((z1 = -1 ∧ z2 - z1 = 2 * (k : ℤ) + 4 + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1))) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) -
          ((1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4)) -
            ((2 * (k : ℤ) + 5) * (z2 - (2 * (k : ℤ) + 5)) - (2 * (k : ℤ) + 3) * (z1 + 1))) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) -
          ((1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4)) -
            ((2 * (k : ℤ) + 5) * (z2 - (2 * (k : ℤ) + 5)) - (2 * (k : ℤ) + 3) * (z1 + 1))) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyS2 at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 - (2 * (k : ℤ) + 4) - (z1 + 1) = (z2 + 1 - z1) + 2 * (-((k : ℤ) + 3)) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceB_s3 (k : ℕ) (z1 z2 : ℤ) (hk : KeyS3 (2 * (k : ℤ) + 4) z1 z2)
    (_hA : ¬(0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (_hC : ¬((z1 = -1 ∧ z2 - z1 = 2 * (k : ℤ) + 4 + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1))) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) -
          ((1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4)) -
            ((2 * (k : ℤ) + 5) * (z2 - (2 * (k : ℤ) + 5)) - (2 * (k : ℤ) + 3) * (z1 + 1))) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) -
          ((1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4)) -
            ((2 * (k : ℤ) + 5) * (z2 - (2 * (k : ℤ) + 5)) - (2 * (k : ℤ) + 3) * (z1 + 1))) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyS3 at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 - (2 * (k : ℤ) + 4) - (z1 + 1) = (z2 + 1 - z1) + 2 * (-((k : ℤ) + 3)) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceB_s4 (k : ℕ) (z1 z2 : ℤ) (hk : KeyS4 (2 * (k : ℤ) + 4) z1 z2)
    (hA : ¬(0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (hC : ¬((z1 = -1 ∧ z2 - z1 = 2 * (k : ℤ) + 4 + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1))) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) -
          ((1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4)) -
            ((2 * (k : ℤ) + 5) * (z2 - (2 * (k : ℤ) + 5)) - (2 * (k : ℤ) + 3) * (z1 + 1))) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) -
          ((1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4)) -
            ((2 * (k : ℤ) + 5) * (z2 - (2 * (k : ℤ) + 5)) - (2 * (k : ℤ) + 3) * (z1 + 1))) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyS4 at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 - (2 * (k : ℤ) + 4) - (z1 + 1) = (z2 + 1 - z1) + 2 * (-((k : ℤ) + 3)) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceC_main (k : ℕ) (z1 z2 : ℤ) (hk : KeyMain (2 * (k : ℤ) + 4) z1 z2)
    (hC : (z1 = -1 ∧ z2 - z1 = 2 * (k : ℤ) + 4 + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1)) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyMain at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 + 2 * (2 * (k : ℤ) + 4) - 1 - (z1 + (2 * (k : ℤ) + 4)) = (z2 + 1 - z1) + 2 * ((k : ℤ) + 1) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceC_s1 (k : ℕ) (z1 z2 : ℤ) (hk : KeyS1 (2 * (k : ℤ) + 4) z1 z2)
    (_hC : (z1 = -1 ∧ z2 - z1 = 2 * (k : ℤ) + 4 + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1)) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyS1 at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 + 2 * (2 * (k : ℤ) + 4) - 1 - (z1 + (2 * (k : ℤ) + 4)) = (z2 + 1 - z1) + 2 * ((k : ℤ) + 1) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceC_s2 (k : ℕ) (z1 z2 : ℤ) (hk : KeyS2 (2 * (k : ℤ) + 4) z1 z2)
    (hC : (z1 = -1 ∧ z2 - z1 = 2 * (k : ℤ) + 4 + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1)) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyS2 at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 + 2 * (2 * (k : ℤ) + 4) - 1 - (z1 + (2 * (k : ℤ) + 4)) = (z2 + 1 - z1) + 2 * ((k : ℤ) + 1) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceC_s3 (k : ℕ) (z1 z2 : ℤ) (hk : KeyS3 (2 * (k : ℤ) + 4) z1 z2)
    (_hC : (z1 = -1 ∧ z2 - z1 = 2 * (k : ℤ) + 4 + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1)) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyS3 at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 + 2 * (2 * (k : ℤ) + 4) - 1 - (z1 + (2 * (k : ℤ) + 4)) = (z2 + 1 - z1) + 2 * ((k : ℤ) + 1) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor <;> ring_nf <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem priceC_s4 (k : ℕ) (z1 z2 : ℤ) (hk : KeyS4 (2 * (k : ℤ) + 4) z1 z2)
    (hC : (z1 = -1 ∧ z2 - z1 = 2 * (k : ℤ) + 4 + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1)) :
    (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 - 1 ≤
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ∧
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) +
          (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) ≤ (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  classical
  unfold KeyS4 at hk
  unfold paperNearLadderValue
  dsimp only
  rw [show z2 + 2 * (2 * (k : ℤ) + 4) - 1 - (z1 + (2 * (k : ℤ) + 4)) = (z2 + 1 - z1) + 2 * ((k : ℤ) + 1) by ring, sq_div4_add]
  simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor <;> ring_nf <;> split_ifs <;> omega

/-- The `A`-leaf point `(z₁−1, z₂+d)` is in the tile. -/
theorem memA_tile (d z1 z2 : ℤ) (hd : 4 ≤ d) (hk : TwosKey d z1 z2)
    (hA : 0 ≤ z1 ∧ z2 - z1 ≤ d ∧ z2 ≤ 2 * d - 1)
    (hnC : ¬((z1 = -1 ∧ z2 - z1 = d + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1))) :
    (z1 - 1, z2 + d) ∈ paperNearLadderTile d := by
  unfold TwosKey at hk
  simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
    Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Prod.mk.injEq, not_or]
  omega

/-- The `B`-leaf point `(z₁+1, z₂−d)` is in the tile. -/
theorem memB_tile (d z1 z2 : ℤ) (hd : 4 ≤ d) (hk : TwosKey d z1 z2)
    (hA : ¬(0 ≤ z1 ∧ z2 - z1 ≤ d ∧ z2 ≤ 2 * d - 1))
    (hC : ¬((z1 = -1 ∧ z2 - z1 = d + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1))) :
    (z1 + 1, z2 - d) ∈ paperNearLadderTile d := by
  unfold TwosKey at hk
  simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
    Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Prod.mk.injEq, not_or]
  omega

/-- The `C`-leaf point `(z₁+d, z₂+2d−1)` is in the tile. -/
theorem memC_tile (d z1 z2 : ℤ) (hd : 4 ≤ d) (hk : TwosKey d z1 z2)
    (hC : (z1 = -1 ∧ z2 - z1 = d + 1) ∨ (z1 = 0 ∧ z2 - z1 ≤ 1)) :
    (z1 + d, z2 + 2 * d - 1) ∈ paperNearLadderTile d := by
  unfold TwosKey at hk
  simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
    Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Prod.mk.injEq, not_or]
  omega


set_option maxHeartbeats 400000 in
/-- **The price range of `2^(k+1)` on its closed polygon**: `c₀ − 1 ≤ P ≤ c₀` with `c₀ = k²+5k+5`. -/
theorem twos_priceRange_E (k : ℕ) (z : Site)
    (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon) :
    (frameAt (List.replicate (k + 1) Digit.two)).cutPrice - 1 ≤
        (frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) z ∧
      (frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) z ≤
        (frameAt (List.replicate (k + 1) Digit.two)).cutPrice := by
  rw [twos_cutPrice, twos_price_unfold, standardField_twos_eq_paperNear k hz]
  have hk : TwosKey (2 * (k : ℤ) + 4) z.1 z.2 := twos_E_key k z hz
  have hd : (4 : ℤ) ≤ 2 * (k : ℤ) + 4 := by omega
  have hP := twos_standardField_hasPeriods k
  by_cases hC : (z.1 = -1 ∧ z.2 - z.1 = 2 * (k : ℤ) + 4 + 1) ∨ (z.1 = 0 ∧ z.2 - z.1 ≤ 1)
  · have hK := period_kernel_apply hP (z.1 - 1, z.2 + (2 * (k : ℤ) + 3))
    rw [twos_kernel_explicit, Prod.mk_add_mk] at hK
    have hF := standardField_twos_eq_tile k
      (w := (z.1 - 1 + (2 * (k : ℤ) + 5), z.2 + (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3)))
      (x := (z.1 + (2 * (k : ℤ) + 4), z.2 + 2 * (2 * (k : ℤ) + 4) - 1))
      (by ext <;> dsimp only <;> ring) (memC_tile (2 * (k : ℤ) + 4) z.1 z.2 hd hk hC)
    rw [← hK, hF]
    rcases hk with h | h | h | h | h
    · exact priceC_main k z.1 z.2 h hC
    · exact priceC_s1 k z.1 z.2 h hC
    · exact priceC_s2 k z.1 z.2 h hC
    · exact priceC_s3 k z.1 z.2 h hC
    · exact priceC_s4 k z.1 z.2 h hC
  · by_cases hA : 0 ≤ z.1 ∧ z.2 - z.1 ≤ 2 * (k : ℤ) + 4 ∧ z.2 ≤ 2 * (2 * (k : ℤ) + 4) - 1
    · have hF := standardField_twos_eq_tile k (w := (z.1 - 1, z.2 + (2 * (k : ℤ) + 3)))
        (x := (z.1 - 1, z.2 + (2 * (k : ℤ) + 4)))
        (by ext <;> (dsimp only; try ring)) (memA_tile (2 * (k : ℤ) + 4) z.1 z.2 hd hk hA hC)
      rw [hF]
      rcases hk with h | h | h | h | h
      · exact priceA_main k z.1 z.2 h hA
      · exact priceA_s1 k z.1 z.2 h hA
      · exact priceA_s2 k z.1 z.2 h hA
      · exact priceA_s3 k z.1 z.2 h hA
      · exact priceA_s4 k z.1 z.2 h hA
    · have hTr := period_transverse_apply hP (z.1 + 1, z.2 - (2 * (k : ℤ) + 5))
      rw [twos_transverse_explicit, twos_transverseGrade_explicit, ladderEvenConstantV_eq] at hTr
      have e : (z.1 + 1, z.2 - (2 * (k : ℤ) + 5)) + (-2, 4 * (k : ℤ) + 8) = (z.1 - 1, z.2 + (2 * (k : ℤ) + 3)) := by
        rw [Prod.mk_add_mk]
        congr 1 <;> ring
      rw [e] at hTr
      dsimp only at hTr
      have hF := standardField_twos_eq_tile k (w := (z.1 + 1, z.2 - (2 * (k : ℤ) + 5)))
        (x := (z.1 + 1, z.2 - (2 * (k : ℤ) + 4)))
        (by ext <;> (dsimp only; try ring)) (memB_tile (2 * (k : ℤ) + 4) z.1 z.2 hd hk hA hC)
      rw [hTr, hF]
      rcases hk with h | h | h | h | h
      · have h' := priceB_main k z.1 z.2 h hA hC
        exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
      · have h' := priceB_s1 k z.1 z.2 h hA hC
        exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
      · have h' := priceB_s2 k z.1 z.2 h hA hC
        exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
      · have h' := priceB_s3 k z.1 z.2 h hA hC
        exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
      · have h' := priceB_s4 k z.1 z.2 h hA hC
        exact ⟨by linarith [h'.1], by linarith [h'.2]⟩

end FLatticePaper.Induction
