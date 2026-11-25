import FLatticePaper.Plane.Induction.TwosPriceForm
import FLatticePaper.Plane.Induction.TwosSlipForm
import FLatticePaper.Plane.Induction.TwosChainMono

/-! The chain potential of sign `+1` on the tile, in the class-0 case: `Φ(x, y) = slip + (k+2)² + (k+2) − x + M`, with `M` the
difference of the two closed-form pieces (min, max and indicator terms) of the near-ladder value. The square `(q−p)²/4` cancels up
to the linear term `(k+2)(q−p)` because the shift `a = 2k+4` is even. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The closed form of the near-ladder value, with the indicator written as a conditional. -/
theorem pnv_eq (d p q : ℤ) : paperNearLadderValue d (p, q) =
    -((q - p) ^ 2 / 4) + min 0 (d - q) + min 0 (2 * d - q) + max ((q - p) - d) 0 +
      (if (p, q) ∈ paperNearLadderA d ∪ paperNearLadderB d then 1 else 0) := by
  unfold paperNearLadderValue
  rw [Set.indicator_apply]

/-- The membership in the near-ladder tile, as linear conditions. -/
theorem mem_pnTile_iff (d p q : ℤ) : (p, q) ∈ paperNearLadderTile d ↔
    (((p = -1 ∧ q = 2 * d + 1) ∨ (p = d + 1 ∧ q = d - 1) ∨ (q - p = d ∧ 0 < p ∧ p < d) ∨
      (-1 ≤ p ∧ p ≤ d + 1 ∧ 1 ≤ q ∧ q ≤ 3 * d - 1 ∧ -1 ≤ q - p ∧ q - p ≤ 2 * d + 1)) ∧
     ¬ ((p = -1 ∧ q ≤ d + 1) ∨ (p = d + 1 ∧ 2 * d - 1 ≤ q))) := by
  unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Prod.mk.injEq]
  tauto

/-- The square shift: `((h + 2(k+2))²)/4 = h²/4 + (k+2) h + (k+2)²`. -/
theorem sq_shift_even (k h : ℤ) : (h + (2 * k + 4)) ^ 2 / 4 = h ^ 2 / 4 + (k + 2) * h + (k + 2) ^ 2 := by
  have e : (h + (2 * k + 4)) ^ 2 = h ^ 2 + 4 * ((k + 2) * h + (k + 2) ^ 2) := by ring
  rw [e, mul_comm 4, Int.add_mul_ediv_right _ _ (by norm_num)]
  ring

/-- **The chain potential in class 0.** At a site `(x, y)` whose shifted point `(x+1, y+1)` is in the key set and whose class-0
tile membership holds, `Φ = slip + (k+2)² + (k+2) − x + (P − P')`, with `P, P'` the two near-ladder pieces. -/
theorem chain_class0 (k : ℕ) {x y : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) (x + 1) (y + 1))
    (h0 : (x + 1 - 1, y + 1 + (2 * (k : ℤ) + 3) + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential
        (standardField (List.replicate (k + 1) Digit.two)) 1 (x, y) =
      twosSlip k (x, y) + ((k : ℤ) + 2) ^ 2 + ((k : ℤ) + 2) - x +
        ((min 0 (2 * (k : ℤ) + 4 - (y + 1 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (y + 1 + 1)) +
            max ((y + 1 + 1 - (x + 1)) - (2 * (k : ℤ) + 4)) 0 +
            (if (x + 1, y + 1 + 1) ∈ paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4)
              then 1 else 0)) -
          (min 0 (2 * (k : ℤ) + 4 - (y + 1 + (2 * (k : ℤ) + 3) + 1)) +
            min 0 (2 * (2 * (k : ℤ) + 4) - (y + 1 + (2 * (k : ℤ) + 3) + 1)) +
            max ((y + 1 + (2 * (k : ℤ) + 3) + 1 - (x + 1 - 1)) - (2 * (k : ℤ) + 4)) 0 +
            (if (x + 1 - 1, y + 1 + (2 * (k : ℤ) + 3) + 1) ∈
                paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4) then 1 else 0))) := by
  rw [chainP_eq]
  have hP := twos_price_class0 k hk h0
  unfold twosP
  dsimp only
  rw [hP, pnv_eq, pnv_eq]
  have e : (y + 1 + (2 * (k : ℤ) + 3) + 1 - (x + 1 - 1)) = (y + 1 + 1 - (x + 1)) + (2 * (k : ℤ) + 4) := by ring
  rw [e, sq_shift_even]
  ring

/-- The square shift by `+2m`. -/
theorem sq_shift_pos (m h : ℤ) : (h + 2 * m) ^ 2 / 4 = h ^ 2 / 4 + m * h + m ^ 2 := by
  have e : (h + 2 * m) ^ 2 = h ^ 2 + 4 * (m * h + m ^ 2) := by ring
  rw [e, mul_comm 4, Int.add_mul_ediv_right _ _ (by norm_num)]
  ring

/-- The square shift by `−2m`. -/
theorem sq_shift_neg (m h : ℤ) : (h - 2 * m) ^ 2 / 4 = h ^ 2 / 4 - m * h + m ^ 2 := by
  have e : (h - 2 * m) ^ 2 = h ^ 2 + 4 * (-(m * h) + m ^ 2) := by ring
  rw [e, mul_comm 4, Int.add_mul_ediv_right _ _ (by norm_num)]
  ring

/-- **The chain potential in class `V`.** -/
theorem chain_classV (k : ℕ) {x y : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) (x + 1) (y + 1))
    (hV : (x + 1 + 1, y + 1 - (2 * (k : ℤ) + 4)) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential
        (standardField (List.replicate (k + 1) Digit.two)) 1 (x, y) =
      twosSlip k (x, y) + ((k : ℤ) + 2) ^ 2 + ((k : ℤ) + 2) + x + 1 +
        ((min 0 (2 * (k : ℤ) + 4 - (y + 1 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (y + 1 + 1)) +
            max ((y + 1 + 1 - (x + 1)) - (2 * (k : ℤ) + 4)) 0 +
            (if (x + 1, y + 1 + 1) ∈ paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4)
              then 1 else 0)) -
          (min 0 (2 * (k : ℤ) + 4 - (y + 1 - (2 * (k : ℤ) + 4))) +
            min 0 (2 * (2 * (k : ℤ) + 4) - (y + 1 - (2 * (k : ℤ) + 4))) +
            max ((y + 1 - (2 * (k : ℤ) + 4) - (x + 1 + 1)) - (2 * (k : ℤ) + 4)) 0 +
            (if (x + 1 + 1, y + 1 - (2 * (k : ℤ) + 4)) ∈
                paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4) then 1 else 0))) := by
  rw [chainP_eq]
  have hP := twos_price_classV k hk hV
  unfold twosP
  dsimp only
  rw [hP, pnv_eq, pnv_eq]
  have e : (y + 1 - (2 * (k : ℤ) + 4) - (x + 1 + 1)) = (y + 1 + 1 - (x + 1)) - 2 * ((k : ℤ) + 3) := by ring
  rw [e, sq_shift_neg]
  ring

/-- **The chain potential in class `U`.** -/
theorem chain_classU (k : ℕ) {x y : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) (x + 1) (y + 1))
    (hU : (x + 1 + (2 * (k : ℤ) + 4), y + 1 + 2 * (2 * (k : ℤ) + 4) - 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential
        (standardField (List.replicate (k + 1) Digit.two)) 1 (x, y) =
      twosSlip k (x, y) + ((k : ℤ) + 1) ^ 2 + ((k : ℤ) + 1) - y +
        ((min 0 (2 * (k : ℤ) + 4 - (y + 1 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (y + 1 + 1)) +
            max ((y + 1 + 1 - (x + 1)) - (2 * (k : ℤ) + 4)) 0 +
            (if (x + 1, y + 1 + 1) ∈ paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4)
              then 1 else 0)) -
          (min 0 (2 * (k : ℤ) + 4 - (y + 1 + 2 * (2 * (k : ℤ) + 4) - 1)) +
            min 0 (2 * (2 * (k : ℤ) + 4) - (y + 1 + 2 * (2 * (k : ℤ) + 4) - 1)) +
            max ((y + 1 + 2 * (2 * (k : ℤ) + 4) - 1 - (x + 1 + (2 * (k : ℤ) + 4))) - (2 * (k : ℤ) + 4)) 0 +
            (if (x + 1 + (2 * (k : ℤ) + 4), y + 1 + 2 * (2 * (k : ℤ) + 4) - 1) ∈
                paperNearLadderA (2 * (k : ℤ) + 4) ∪ paperNearLadderB (2 * (k : ℤ) + 4) then 1 else 0))) := by
  rw [chainP_eq]
  have hP := twos_price_classU k hk hU
  unfold twosP
  dsimp only
  rw [hP, pnv_eq, pnv_eq]
  have e : (y + 1 + 2 * (2 * (k : ℤ) + 4) - 1 - (x + 1 + (2 * (k : ℤ) + 4))) = (y + 1 + 1 - (x + 1)) + 2 * ((k : ℤ) + 1) := by ring
  rw [e, sq_shift_pos]
  ring

end FLatticePaper.TwosEPolicy
