import FLatticePaper.Plane.Induction.TwosPriceClosed

/-! Task 118, base inputs at `2^(k+1)` (the unit price): the exact price of the twos standard field on the closed polygon.

For a `TwosKey` point `z` (the closed polygon, `twos_E_key`), `P z = c₀ − δ(z)` with `c₀ = k²+5k+5` and `δ(z) = 1`
exactly on the three bands `TwosDelta` (checked numerically for `k = 0,…,6` on all of the polygon). The proof runs through the
three shift classes of `twos_price_closed{0,U,V}`; the bounded pieces (`min`, `max`, the indicator of `A ∪ B`) are split
into their linear pieces (`twos_minpieces`, `twos_minpieces4`, `twos_maxpieces`) and `omega` closes each piece. The special points
of `TwosKey` outside the main box are computed directly. -/

set_option maxHeartbeats 400000
namespace FLatticePaper.Induction
open Farey Construction

/-- The bands where the exact price of `2^(k+1)` on the closed polygon is `c₀ − 1` (the rest is `c₀`). -/
def TwosDelta (k : ℕ) (z1 z2 : ℤ) : Prop :=
  (2 ≤ z1 ∧ z2 - z1 ≤ -1) ∨
  ((2 * (k : ℤ) + 4 ≤ z2 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1) ∧
    (z2 - z1 ≤ 2 * (k : ℤ) + 4 - 2 ∨ (z1 = 2 * (k : ℤ) + 4 ∧ z2 = 2 * (2 * (k : ℤ) + 4) - 1))) ∨
  (2 * (2 * (k : ℤ) + 4) ≤ z2 ∧ 0 ≤ z1)

theorem twos_minpieces (d z2 : ℤ) (hz : 0 ≤ z2) :
    (min 0 (d - (z2 + 1)) + min 0 (2 * d - (z2 + 1)) - min 0 (-z2) - min 0 (d - z2) = z2 ∧ z2 ≤ d - 1) ∨
      (min 0 (d - (z2 + 1)) + min 0 (2 * d - (z2 + 1)) - min 0 (-z2) - min 0 (d - z2) = z2 - 1 ∧
        d ≤ z2 ∧ z2 ≤ 2 * d - 1) ∨
      (min 0 (d - (z2 + 1)) + min 0 (2 * d - (z2 + 1)) - min 0 (-z2) - min 0 (d - z2) = 2 * d - 2 ∧
        2 * d - 1 ≤ z2) := by
  simp only [min_def]
  split_ifs <;> omega

theorem twos_maxpiece1 (d b : ℤ) (_hd : 0 ≤ d) :
    (max (b - d) 0 = 0 ∧ b ≤ d) ∨ (max (b - d) 0 = b - d ∧ d ≤ b) := by
  simp only [max_def]
  split_ifs <;> omega

theorem twos_maxpieces (d b : ℤ) (hd : 0 ≤ d) :
    (max (b - d) 0 - max b 0 = 0 ∧ b ≤ 0) ∨ (max (b - d) 0 - max b 0 = -b ∧ 0 ≤ b ∧ b ≤ d) ∨
      (max (b - d) 0 - max b 0 = -d ∧ d ≤ b) := by
  simp only [max_def]
  split_ifs <;> omega

theorem twos_minpieces4 (d z2 : ℤ) (_hz : 0 ≤ z2) (hd : 4 ≤ d) (hz2 : z2 ≤ 3 * d - 2) :
    (min 0 (d - (z2 + 1)) + min 0 (2 * d - (z2 + 1)) - min 0 (2 * d - z2) - min 0 (3 * d - z2) = 0 ∧ z2 ≤ d - 1) ∨
      (min 0 (d - (z2 + 1)) + min 0 (2 * d - (z2 + 1)) - min 0 (2 * d - z2) - min 0 (3 * d - z2) = d - 1 - z2 ∧
        d ≤ z2 ∧ z2 ≤ 2 * d - 2) ∨
      (min 0 (d - (z2 + 1)) + min 0 (2 * d - (z2 + 1)) - min 0 (2 * d - z2) - min 0 (3 * d - z2) = 3 * d - 2 - 2 * z2 ∧
        2 * d - 1 ≤ z2 ∧ z2 ≤ 2 * d) ∨
      (min 0 (d - (z2 + 1)) + min 0 (2 * d - (z2 + 1)) - min 0 (2 * d - z2) - min 0 (3 * d - z2) = d - 2 - z2 ∧
        2 * d ≤ z2) := by
  simp only [min_def]
  split_ifs <;> omega

theorem twos_tile0_of (k : ℕ) {z1 z2 : ℤ}     (hz1 : -1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 5) (hu : -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * (2 * (k : ℤ) + 4))
    (hz2 : 0 ≤ z2 ∧ z2 ≤ 3 * (2 * (k : ℤ) + 4) - 2)
    (_hm1 : 0 ≤ z1 ∨ 2 * (k : ℤ) + 5 ≤ z2) (_hm2 : z1 ≤ 2 * (k : ℤ) + 4 ∨ z2 ≤ 4 * (k : ℤ) + 6)
    (hr0 : 0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1 ∧ (1 ≤ z1 ∨ 2 ≤ z2)) :
    (z1 - 1, z2 + (2 * (k : ℤ) + 3) + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
  simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
    Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Prod.mk.injEq, not_or]
  omega

theorem twos_tileV_of (k : ℕ) {z1 z2 : ℤ}     (hz1 : -1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 5) (hu : -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * (2 * (k : ℤ) + 4))
    (hz2 : 0 ≤ z2 ∧ z2 ≤ 3 * (2 * (k : ℤ) + 4) - 2)
    (_hm1 : 0 ≤ z1 ∨ 2 * (k : ℤ) + 5 ≤ z2) (hm2 : z1 ≤ 2 * (k : ℤ) + 4 ∨ z2 ≤ 4 * (k : ℤ) + 6)
    (hrV : (z1 = -1 ∧ 2 * (k : ℤ) + 5 ≤ z2) ∨ (0 ≤ z1 ∧ (2 * (k : ℤ) + 5 ≤ z2 - z1 ∨ 2 * (2 * (k : ℤ) + 4) ≤ z2))) :
    (z1 + 1, z2 - (2 * (k : ℤ) + 4)) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
  simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
    Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Prod.mk.injEq, not_or]
  omega

theorem twos_delta_class0_M1 (k : ℕ) {z1 z2 : ℤ}
    (hz1 : -1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 5) (hu : -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * (2 * (k : ℤ) + 4))
    (hz2 : 0 ≤ z2 ∧ z2 ≤ 3 * (2 * (k : ℤ) + 4) - 2)
    (hm1 : 0 ≤ z1 ∨ 2 * (k : ℤ) + 5 ≤ z2) (hm2 : z1 ≤ 2 * (k : ℤ) + 4 ∨ z2 ≤ 4 * (k : ℤ) + 6)
    (hr0 : 0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1 ∧ (1 ≤ z1 ∨ 2 ≤ z2))
    (hM : min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) - min 0 (-z2) - min 0 (2 * (k : ℤ) + 4 - z2) = z2) (hM' : z2 ≤ (2 * (k : ℤ) + 4) - 1) :
    ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k z1 z2) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k z1 z2) := by
  have h0 := twos_tile0_of k hz1 hu hz2 hm1 hm2 hr0
  rw [twos_price_closed0 k (by unfold TwosKey; omega) h0]
  have hX := twos_maxpieces (2 * (k : ℤ) + 4) (z2 + 1 - z1) (by omega)
  have hi1 := twosInd_spec (2 * (k : ℤ) + 4) z1 (z2 + 1)
  have hi2 := twosInd_spec (2 * (k : ℤ) + 4) (z1 - 1) (z2 + (2 * (k : ℤ) + 4))
  unfold TwosDelta
  generalize twosInd (2 * (k : ℤ) + 4) (z1, z2 + 1) = i1 at *
  generalize twosInd (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) = i2 at *
  generalize min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) - min 0 (-z2) - min 0 (2 * (k : ℤ) + 4 - z2) = M at *
  generalize max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 - max (z2 + 1 - z1) 0 = X at *
  clear h0
  rcases hX with ⟨hX1, hX2⟩ | ⟨hX1, hX2, hX3⟩ | ⟨hX1, hX2⟩ <;> omega

theorem twos_delta_class0_M2 (k : ℕ) {z1 z2 : ℤ}
    (hz1 : -1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 5) (hu : -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * (2 * (k : ℤ) + 4))
    (hz2 : 0 ≤ z2 ∧ z2 ≤ 3 * (2 * (k : ℤ) + 4) - 2)
    (hm1 : 0 ≤ z1 ∨ 2 * (k : ℤ) + 5 ≤ z2) (hm2 : z1 ≤ 2 * (k : ℤ) + 4 ∨ z2 ≤ 4 * (k : ℤ) + 6)
    (hr0 : 0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1 ∧ (1 ≤ z1 ∨ 2 ≤ z2))
    (hM : min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) - min 0 (-z2) - min 0 (2 * (k : ℤ) + 4 - z2) = z2 - 1) (hM' : (2 * (k : ℤ) + 4) ≤ z2 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1) :
    ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k z1 z2) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k z1 z2) := by
  have h0 := twos_tile0_of k hz1 hu hz2 hm1 hm2 hr0
  rw [twos_price_closed0 k (by unfold TwosKey; omega) h0]
  have hX := twos_maxpieces (2 * (k : ℤ) + 4) (z2 + 1 - z1) (by omega)
  have hi1 := twosInd_spec (2 * (k : ℤ) + 4) z1 (z2 + 1)
  have hi2 := twosInd_spec (2 * (k : ℤ) + 4) (z1 - 1) (z2 + (2 * (k : ℤ) + 4))
  unfold TwosDelta
  generalize twosInd (2 * (k : ℤ) + 4) (z1, z2 + 1) = i1 at *
  generalize twosInd (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) = i2 at *
  generalize min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) - min 0 (-z2) - min 0 (2 * (k : ℤ) + 4 - z2) = M at *
  generalize max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 - max (z2 + 1 - z1) 0 = X at *
  clear h0
  rcases hX with ⟨hX1, hX2⟩ | ⟨hX1, hX2, hX3⟩ | ⟨hX1, hX2⟩ <;> omega

theorem twos_delta_class0_M3 (k : ℕ) {z1 z2 : ℤ}
    (hz1 : -1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 5) (hu : -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * (2 * (k : ℤ) + 4))
    (hz2 : 0 ≤ z2 ∧ z2 ≤ 3 * (2 * (k : ℤ) + 4) - 2)
    (hm1 : 0 ≤ z1 ∨ 2 * (k : ℤ) + 5 ≤ z2) (hm2 : z1 ≤ 2 * (k : ℤ) + 4 ∨ z2 ≤ 4 * (k : ℤ) + 6)
    (hr0 : 0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1 ∧ (1 ≤ z1 ∨ 2 ≤ z2))
    (hM : min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) - min 0 (-z2) - min 0 (2 * (k : ℤ) + 4 - z2) = 2 * (2 * (k : ℤ) + 4) - 2) (hM' : 2 * (2 * (k : ℤ) + 4) - 1 ≤ z2) :
    ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k z1 z2) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k z1 z2) := by
  have h0 := twos_tile0_of k hz1 hu hz2 hm1 hm2 hr0
  rw [twos_price_closed0 k (by unfold TwosKey; omega) h0]
  have hX := twos_maxpieces (2 * (k : ℤ) + 4) (z2 + 1 - z1) (by omega)
  have hi1 := twosInd_spec (2 * (k : ℤ) + 4) z1 (z2 + 1)
  have hi2 := twosInd_spec (2 * (k : ℤ) + 4) (z1 - 1) (z2 + (2 * (k : ℤ) + 4))
  unfold TwosDelta
  generalize twosInd (2 * (k : ℤ) + 4) (z1, z2 + 1) = i1 at *
  generalize twosInd (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4)) = i2 at *
  generalize min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) - min 0 (-z2) - min 0 (2 * (k : ℤ) + 4 - z2) = M at *
  generalize max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 - max (z2 + 1 - z1) 0 = X at *
  clear h0
  rcases hX with ⟨hX1, hX2⟩ | ⟨hX1, hX2, hX3⟩ | ⟨hX1, hX2⟩ <;> omega

theorem twos_delta_classV_P2 (k : ℕ) {z1 z2 : ℤ}
    (hz1 : -1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 5) (hu : -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * (2 * (k : ℤ) + 4))
    (hz2 : 0 ≤ z2 ∧ z2 ≤ 3 * (2 * (k : ℤ) + 4) - 2)
    (hm1 : 0 ≤ z1 ∨ 2 * (k : ℤ) + 5 ≤ z2) (hm2 : z1 ≤ 2 * (k : ℤ) + 4 ∨ z2 ≤ 4 * (k : ℤ) + 6)
    (hrV : (z1 = -1 ∧ 2 * (k : ℤ) + 5 ≤ z2) ∨ (0 ≤ z1 ∧ (2 * (k : ℤ) + 5 ≤ z2 - z1 ∨ 2 * (2 * (k : ℤ) + 4) ≤ z2)))
    (hM : min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) - min 0 (2 * (2 * (k : ℤ) + 4) - z2) - min 0 (3 * (2 * (k : ℤ) + 4) - z2) = (2 * (k : ℤ) + 4) - 1 - z2) (hM' : (2 * (k : ℤ) + 4) ≤ z2 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 2) :
    ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k z1 z2) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k z1 z2) := by
  have hV := twos_tileV_of k hz1 hu hz2 hm1 hm2 hrV
  rw [twos_price_closedV k (by unfold TwosKey; omega) hV]
  have hX2 : max (z2 - z1 - 2 * (2 * (k : ℤ) + 4) - 1) 0 = 0 := max_eq_right (by omega)
  rw [hX2]
  have hX1 := twos_maxpiece1 (2 * (k : ℤ) + 4) (z2 + 1 - z1) (by omega)
  have hi1 := twosInd_spec (2 * (k : ℤ) + 4) z1 (z2 + 1)
  have hi2 := twosInd_spec (2 * (k : ℤ) + 4) (z1 + 1) (z2 - (2 * (k : ℤ) + 4))
  unfold TwosDelta
  generalize twosInd (2 * (k : ℤ) + 4) (z1, z2 + 1) = i1 at *
  generalize twosInd (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) = i2 at *
  generalize min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) - min 0 (2 * (2 * (k : ℤ) + 4) - z2) - min 0 (3 * (2 * (k : ℤ) + 4) - z2) = M at *
  generalize max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 = X at *
  clear hV
  rcases hX1 with ⟨hX11, hX12⟩ | ⟨hX11, hX12⟩ <;> omega

theorem twos_delta_classV_P3 (k : ℕ) {z1 z2 : ℤ}
    (hz1 : -1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 5) (hu : -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * (2 * (k : ℤ) + 4))
    (hz2 : 0 ≤ z2 ∧ z2 ≤ 3 * (2 * (k : ℤ) + 4) - 2)
    (hm1 : 0 ≤ z1 ∨ 2 * (k : ℤ) + 5 ≤ z2) (hm2 : z1 ≤ 2 * (k : ℤ) + 4 ∨ z2 ≤ 4 * (k : ℤ) + 6)
    (hrV : (z1 = -1 ∧ 2 * (k : ℤ) + 5 ≤ z2) ∨ (0 ≤ z1 ∧ (2 * (k : ℤ) + 5 ≤ z2 - z1 ∨ 2 * (2 * (k : ℤ) + 4) ≤ z2)))
    (hM : min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) - min 0 (2 * (2 * (k : ℤ) + 4) - z2) - min 0 (3 * (2 * (k : ℤ) + 4) - z2) = 3 * (2 * (k : ℤ) + 4) - 2 - 2 * z2) (hM' : 2 * (2 * (k : ℤ) + 4) - 1 ≤ z2 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4)) :
    ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k z1 z2) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k z1 z2) := by
  have hV := twos_tileV_of k hz1 hu hz2 hm1 hm2 hrV
  rw [twos_price_closedV k (by unfold TwosKey; omega) hV]
  have hX2 : max (z2 - z1 - 2 * (2 * (k : ℤ) + 4) - 1) 0 = 0 := max_eq_right (by omega)
  rw [hX2]
  have hX1 := twos_maxpiece1 (2 * (k : ℤ) + 4) (z2 + 1 - z1) (by omega)
  have hi1 := twosInd_spec (2 * (k : ℤ) + 4) z1 (z2 + 1)
  have hi2 := twosInd_spec (2 * (k : ℤ) + 4) (z1 + 1) (z2 - (2 * (k : ℤ) + 4))
  unfold TwosDelta
  generalize twosInd (2 * (k : ℤ) + 4) (z1, z2 + 1) = i1 at *
  generalize twosInd (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) = i2 at *
  generalize min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) - min 0 (2 * (2 * (k : ℤ) + 4) - z2) - min 0 (3 * (2 * (k : ℤ) + 4) - z2) = M at *
  generalize max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 = X at *
  clear hV
  rcases hX1 with ⟨hX11, hX12⟩ | ⟨hX11, hX12⟩ <;> omega

theorem twos_delta_classV_P4 (k : ℕ) {z1 z2 : ℤ}
    (hz1 : -1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 5) (hu : -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * (2 * (k : ℤ) + 4))
    (hz2 : 0 ≤ z2 ∧ z2 ≤ 3 * (2 * (k : ℤ) + 4) - 2)
    (hm1 : 0 ≤ z1 ∨ 2 * (k : ℤ) + 5 ≤ z2) (hm2 : z1 ≤ 2 * (k : ℤ) + 4 ∨ z2 ≤ 4 * (k : ℤ) + 6)
    (hrV : (z1 = -1 ∧ 2 * (k : ℤ) + 5 ≤ z2) ∨ (0 ≤ z1 ∧ (2 * (k : ℤ) + 5 ≤ z2 - z1 ∨ 2 * (2 * (k : ℤ) + 4) ≤ z2)))
    (hM : min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) - min 0 (2 * (2 * (k : ℤ) + 4) - z2) - min 0 (3 * (2 * (k : ℤ) + 4) - z2) = (2 * (k : ℤ) + 4) - 2 - z2) (hM' : 2 * (2 * (k : ℤ) + 4) ≤ z2) :
    ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k z1 z2) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k z1 z2) := by
  have hV := twos_tileV_of k hz1 hu hz2 hm1 hm2 hrV
  rw [twos_price_closedV k (by unfold TwosKey; omega) hV]
  have hX2 : max (z2 - z1 - 2 * (2 * (k : ℤ) + 4) - 1) 0 = 0 := max_eq_right (by omega)
  rw [hX2]
  have hX1 := twos_maxpiece1 (2 * (k : ℤ) + 4) (z2 + 1 - z1) (by omega)
  have hi1 := twosInd_spec (2 * (k : ℤ) + 4) z1 (z2 + 1)
  have hi2 := twosInd_spec (2 * (k : ℤ) + 4) (z1 + 1) (z2 - (2 * (k : ℤ) + 4))
  unfold TwosDelta
  generalize twosInd (2 * (k : ℤ) + 4) (z1, z2 + 1) = i1 at *
  generalize twosInd (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) = i2 at *
  generalize min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) - min 0 (2 * (2 * (k : ℤ) + 4) - z2) - min 0 (3 * (2 * (k : ℤ) + 4) - z2) = M at *
  generalize max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 = X at *
  clear hV
  rcases hX1 with ⟨hX11, hX12⟩ | ⟨hX11, hX12⟩ <;> omega

theorem twos_delta_special_U0 (k : ℕ) :     ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (0, 0) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k 0 0) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (0, 0) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k 0 0) := by
  have hU : ((0 : ℤ) + (2 * (k : ℤ) + 4), (0 : ℤ) + 2 * (2 * (k : ℤ) + 4) - 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.mk.injEq, not_or]
    omega
  have hk : TwosKey (2 * (k : ℤ) + 4) 0 0 := by unfold TwosKey; omega
  rw [twos_price_closedU k hk hU]
  have hi1 := twosInd_spec (2 * (k : ℤ) + 4) 0 (0 + 1)
  have hi2 := twosInd_spec (2 * (k : ℤ) + 4) (0 + (2 * (k : ℤ) + 4)) (0 + 2 * (2 * (k : ℤ) + 4) - 1)
  unfold TwosDelta
  simp only [min_def, max_def]
  split_ifs <;> omega

theorem twos_delta_special_U1 (k : ℕ) :     ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (0, 1) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k 0 1) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (0, 1) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k 0 1) := by
  have hU : ((0 : ℤ) + (2 * (k : ℤ) + 4), (1 : ℤ) + 2 * (2 * (k : ℤ) + 4) - 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.mk.injEq, not_or]
    omega
  have hk : TwosKey (2 * (k : ℤ) + 4) 0 1 := by unfold TwosKey; omega
  rw [twos_price_closedU k hk hU]
  have hi1 := twosInd_spec (2 * (k : ℤ) + 4) 0 (1 + 1)
  have hi2 := twosInd_spec (2 * (k : ℤ) + 4) (0 + (2 * (k : ℤ) + 4)) (1 + 2 * (2 * (k : ℤ) + 4) - 1)
  unfold TwosDelta
  simp only [min_def, max_def]
  split_ifs <;> omega

theorem twos_delta_special_s3 (k : ℕ) :     ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (-1, 2 * (k : ℤ) + 4) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k (-1) (2 * (k : ℤ) + 4)) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (-1, 2 * (k : ℤ) + 4) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k (-1) (2 * (k : ℤ) + 4)) := by
  have hU : ((-1 : ℤ) + (2 * (k : ℤ) + 4), (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.mk.injEq, not_or]
    omega
  have hk : TwosKey (2 * (k : ℤ) + 4) (-1) (2 * (k : ℤ) + 4) := by unfold TwosKey; omega
  rw [twos_price_closedU k hk hU]
  have hi1 := twosInd_spec (2 * (k : ℤ) + 4) (-1) (2 * (k : ℤ) + 4 + 1)
  have hi2 := twosInd_spec (2 * (k : ℤ) + 4) ((-1) + (2 * (k : ℤ) + 4)) (2 * (k : ℤ) + 4 + 2 * (2 * (k : ℤ) + 4) - 1)
  unfold TwosDelta
  simp only [min_def, max_def]
  split_ifs <;> omega

theorem twos_delta_special_s1 (k : ℕ) :     ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (-1, 2 * (2 * (k : ℤ) + 4)) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k (-1) (2 * (2 * (k : ℤ) + 4))) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (-1, 2 * (2 * (k : ℤ) + 4)) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k (-1) (2 * (2 * (k : ℤ) + 4))) := by
  have hV : ((-1 : ℤ) + 1, 2 * (2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4)) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.mk.injEq, not_or]
    omega
  have hk : TwosKey (2 * (k : ℤ) + 4) (-1) (2 * (2 * (k : ℤ) + 4)) := by unfold TwosKey; omega
  rw [twos_price_closedV k hk hV]
  have hX2 : max (2 * (2 * (k : ℤ) + 4) - (-1) - 2 * (2 * (k : ℤ) + 4) - 1) 0 = 0 := max_eq_right (by omega)
  rw [hX2]
  have hi1 := twosInd_spec (2 * (k : ℤ) + 4) (-1) (2 * (2 * (k : ℤ) + 4) + 1)
  have hi2 := twosInd_spec (2 * (k : ℤ) + 4) ((-1) + 1) (2 * (2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4))
  unfold TwosDelta
  simp only [min_def, max_def]
  split_ifs <;> omega

theorem twos_delta_special_s2 (k : ℕ) :     ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k (2 * (k : ℤ) + 5) (2 * (k : ℤ) + 2)) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k (2 * (k : ℤ) + 5) (2 * (k : ℤ) + 2)) := by
  have h0 : ((2 * (k : ℤ) + 5) - 1, (2 * (k : ℤ) + 2) + (2 * (k : ℤ) + 3) + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.mk.injEq, not_or]
    omega
  have hk : TwosKey (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 5) (2 * (k : ℤ) + 2) := by unfold TwosKey; omega
  rw [twos_price_closed0 k hk h0]
  have hi1 := twosInd_spec (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 5) ((2 * (k : ℤ) + 2) + 1)
  have hi2 := twosInd_spec (2 * (k : ℤ) + 4) ((2 * (k : ℤ) + 5) - 1) ((2 * (k : ℤ) + 2) + (2 * (k : ℤ) + 4))
  unfold TwosDelta
  simp only [min_def, max_def]
  split_ifs <;> omega

theorem twos_delta_special_s4 (k : ℕ) :     ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 6) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k (2 * (k : ℤ) + 5) (4 * (k : ℤ) + 6)) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 6) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k (2 * (k : ℤ) + 5) (4 * (k : ℤ) + 6)) := by
  have h0 : ((2 * (k : ℤ) + 5) - 1, (4 * (k : ℤ) + 6) + (2 * (k : ℤ) + 3) + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.mk.injEq, not_or]
    omega
  have hk : TwosKey (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 5) (4 * (k : ℤ) + 6) := by unfold TwosKey; omega
  rw [twos_price_closed0 k hk h0]
  have hi1 := twosInd_spec (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 5) ((4 * (k : ℤ) + 6) + 1)
  have hi2 := twosInd_spec (2 * (k : ℤ) + 4) ((2 * (k : ℤ) + 5) - 1) ((4 * (k : ℤ) + 6) + (2 * (k : ℤ) + 4))
  unfold TwosDelta
  simp only [min_def, max_def]
  split_ifs <;> omega

theorem twos_price_delta (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2) :
    ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 ∧ ¬ TwosDelta k z1 z2) ∨
      ((frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
        (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 ∧ TwosDelta k z1 z2) := by
  by_cases hsp : (z1 = -1 ∧ z2 = 2 * (2 * (k : ℤ) + 4)) ∨ (z1 = 2 * (k : ℤ) + 5 ∧ z2 = 2 * (k : ℤ) + 2) ∨
      (z1 = -1 ∧ z2 = 2 * (k : ℤ) + 4) ∨ (z1 = 2 * (k : ℤ) + 5 ∧ z2 = 4 * (k : ℤ) + 6)
  · rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2
      exact twos_delta_special_s1 k
    · subst h1 h2
      exact twos_delta_special_s2 k
    · subst h1 h2
      exact twos_delta_special_s3 k
    · subst h1 h2
      exact twos_delta_special_s4 k
  by_cases hu0 : z1 = 0 ∧ z2 ≤ 1
  · obtain ⟨h1, h2⟩ := hu0
    subst h1
    have hz : 0 ≤ z2 ∧ z2 ≤ 1 := by unfold TwosKey at hk; omega
    rcases (show z2 = 0 ∨ z2 = 1 by omega) with h | h
    · subst h
      exact twos_delta_special_U0 k
    · subst h
      exact twos_delta_special_U1 k
  have hbox : -1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 5 ∧ -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * (2 * (k : ℤ) + 4) ∧
      0 ≤ z2 ∧ z2 ≤ 3 * (2 * (k : ℤ) + 4) - 2 ∧ (0 ≤ z1 ∨ 2 * (k : ℤ) + 5 ≤ z2) ∧
      (z1 ≤ 2 * (k : ℤ) + 4 ∨ z2 ≤ 4 * (k : ℤ) + 6) := by
    unfold TwosKey at hk
    omega
  obtain ⟨hz1, hu, hz2, hm1, hm2⟩ : (-1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 5) ∧ (-2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * (2 * (k : ℤ) + 4)) ∧
      (0 ≤ z2 ∧ z2 ≤ 3 * (2 * (k : ℤ) + 4) - 2) ∧ (0 ≤ z1 ∨ 2 * (k : ℤ) + 5 ≤ z2) ∧
      (z1 ≤ 2 * (k : ℤ) + 4 ∨ z2 ≤ 4 * (k : ℤ) + 6) :=
    ⟨⟨hbox.1, hbox.2.1⟩, ⟨hbox.2.2.1, hbox.2.2.2.1⟩, ⟨hbox.2.2.2.2.1, hbox.2.2.2.2.2.1⟩,
      hbox.2.2.2.2.2.2.1, hbox.2.2.2.2.2.2.2⟩
  by_cases hr0 : 0 ≤ z1 ∧ z2 - z1 ≤ 2 * (k : ℤ) + 4 ∧ z2 ≤ 2 * (2 * (k : ℤ) + 4) - 1 ∧ (1 ≤ z1 ∨ 2 ≤ z2)
  · have hz0 : 0 ≤ z2 := hz2.1
    rcases twos_minpieces (2 * (k : ℤ) + 4) z2 hz0 with ⟨m1, m2⟩ | ⟨m1, m2, m3⟩ | ⟨m1, m2⟩
    · exact twos_delta_class0_M1 k hz1 hu hz2 hm1 hm2 hr0 m1 m2
    · exact twos_delta_class0_M2 k hz1 hu hz2 hm1 hm2 hr0 m1 ⟨m2, m3⟩
    · exact twos_delta_class0_M3 k hz1 hu hz2 hm1 hm2 hr0 m1 m2
  by_cases hrV : (z1 = -1 ∧ 2 * (k : ℤ) + 5 ≤ z2) ∨ (0 ≤ z1 ∧ (2 * (k : ℤ) + 5 ≤ z2 - z1 ∨ 2 * (2 * (k : ℤ) + 4) ≤ z2))
  · have hz0 : 0 ≤ z2 := hz2.1
    rcases twos_minpieces4 (2 * (k : ℤ) + 4) z2 hz0 (by omega) hz2.2 with
      ⟨p1, p1'⟩ | ⟨p2, p2'⟩ | ⟨p3, p3'⟩ | ⟨p4, p4'⟩
    · exfalso
      rcases hrV with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩ <;> omega
    · exact twos_delta_classV_P2 k hz1 hu hz2 hm1 hm2 hrV p2 p2'
    · exact twos_delta_classV_P3 k hz1 hu hz2 hm1 hm2 hrV p3 p3'
    · exact twos_delta_classV_P4 k hz1 hu hz2 hm1 hm2 hrV p4 p4'
  exfalso
  exact hrV (by omega)

end FLatticePaper.Induction
