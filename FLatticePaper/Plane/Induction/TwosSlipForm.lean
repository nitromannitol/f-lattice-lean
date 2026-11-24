import FLatticePaper.Plane.Induction.TwosPriceClosed
import FLatticePaper.Plane.Induction.TwosUnitPrice

/-! Task 118, base slip at `2^(k+1)`: the explicit slip `D(z) = F(z) − F(z + σ)` on the closed polygon.

Since `σ = (1,1) − U` (`twos_shortShift_explicit`, `twos_kernel_explicit`), the kernel period gives `F(z + σ) = F(z + (1,1))`
(`twos_shift_F`). On the closed polygon `F(z) = paperNearLadderValue (z + (0,1))` (`twos_F_E`), and `F(z + (1,1))` is the tile value
in class `0` (`(z₁+1, z₂+2)` in the tile) or in class `U` (`(z₁ − d, z₂ − d + 3)` in the tile), with two exceptional points in
class `V`. The result is `D ∈ {0, 1, 2}` with the threshold description `TwosSlipZ0`, `TwosSlipZ2`. In this part: the class-`0` band (`twos_slip_band0`, all six column
regions), the two exceptional values, the cover, and the `η = −1` translation (`twos_slip_neg`). The class-`U` band is not yet
proved in this module. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- The twos slip `D(z) = F(z) − F(z + σ)`. -/
noncomputable def twosSlip (k : ℕ) (z : Site) : ℤ :=
  standardField (List.replicate (k + 1) Digit.two) z -
    standardField (List.replicate (k + 1) Digit.two) (z + (frameAt (List.replicate (k + 1) Digit.two)).shortShift)

/-- The zero band of the slip: `D = 0` on the closed polygon. -/
def TwosSlipZ0 (d z1 z2 : ℤ) : Prop :=
  (-1 ≤ z1 ∧ z1 ≤ 0 ∧ z2 ≤ d - 1) ∨ (1 ≤ z1 ∧ z1 ≤ d ∧ z2 ≤ d - 2) ∨ z1 = d + 1

/-- The two band of the slip: `D = 2` on the closed polygon. -/
def TwosSlipZ2 (d z1 z2 : ℤ) : Prop :=
  (-1 ≤ z1 ∧ z1 ≤ d - 2 ∧ 2 * d - 1 ≤ z2) ∨ (z1 = d - 1 ∧ 2 * d - 2 ≤ z2) ∨ (z1 = d ∧ 3 * d - 2 ≤ z2)

/-- The shift `F(z + σ) = F(z + (1,1))`: `σ + U = (1,1)` and the kernel period is `0`. -/
theorem twos_shift_F (k : ℕ) (z : Site) :
    standardField (List.replicate (k + 1) Digit.two)
        (z + (frameAt (List.replicate (k + 1) Digit.two)).shortShift) =
      standardField (List.replicate (k + 1) Digit.two) (z.1 + 1, z.2 + 1) := by
  have hP := twos_standardField_hasPeriods k
  have hK := period_kernel_apply hP (z + (frameAt (List.replicate (k + 1) Digit.two)).shortShift)
  rw [twos_kernel_explicit] at hK
  have e : z + (frameAt (List.replicate (k + 1) Digit.two)).shortShift + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) =
      (z.1 + 1, z.2 + 1) := by
    rw [twos_shortShift_explicit]
    ext <;> simp <;> ring
  rw [e] at hK
  exact hK.symm

/-- **The slip in class `0`.** `F(z + (1,1))` is the tile value at `(z₁+1, z₂+1)`. -/
theorem twos_slip_class0 (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h0 : (z1 + 1, z2 + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    twosSlip k (z1, z2) = paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + 1, z2 + 2) := by
  have hF := standardField_twos_eq_tile k (w := (z1 + 1, z2 + 1)) (x := (z1 + 1, z2 + 2))
    (Prod.ext rfl (by dsimp only; ring)) h0
  unfold twosSlip
  rw [twos_shift_F k (z1, z2)]
  dsimp only
  rw [hF, twos_F_E k hk]

/-- **The slip in class `U`.** `F(z + (1,1)) = F(z + (1,1) − U)`, and `(z₁ − d, z₂ − d + 3)` is the tile point. -/
theorem twos_slip_classU (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (hU : (z1 - (2 * (k : ℤ) + 4), z2 - (2 * (k : ℤ) + 4) + 3) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    twosSlip k (z1, z2) = paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1 - (2 * (k : ℤ) + 4), z2 - (2 * (k : ℤ) + 4) + 3) := by
  have hP := twos_standardField_hasPeriods k
  have hK := period_kernel_apply hP (z1 - (2 * (k : ℤ) + 4), z2 - (2 * (k : ℤ) + 4) + 2)
  rw [twos_kernel_explicit] at hK
  have e : (z1 - (2 * (k : ℤ) + 4), z2 - (2 * (k : ℤ) + 4) + 2) + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) =
      (z1 + 1, z2 + 1) := by
    ext <;> simp <;> ring
  rw [e] at hK
  have hF := standardField_twos_eq_tile k (w := (z1 - (2 * (k : ℤ) + 4), z2 - (2 * (k : ℤ) + 4) + 2))
    (x := (z1 - (2 * (k : ℤ) + 4), z2 - (2 * (k : ℤ) + 4) + 3)) (Prod.ext rfl (by dsimp only; ring)) hU
  unfold twosSlip
  rw [twos_shift_F k (z1, z2)]
  dsimp only
  rw [hK, hF, twos_F_E k hk]

/-- The tile membership of `(0, 2d+1)`'s predecessor data, through the transverse period: `F(x + V)` for `x = (2,1)`. -/
theorem twos_F_transverse_21 (k : ℕ) :
    standardField (List.replicate (k + 1) Digit.two) (-1 + 1, 2 * (2 * (k : ℤ) + 4) + 1) =
      standardField (List.replicate (k + 1) Digit.two) (2, 1) +
        (1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4) - ((2 * (k : ℤ) + 5) * 1 - (2 * (k : ℤ) + 3) * 2)) := by
  have hT := period_transverse_apply (twos_standardField_hasPeriods k) (2, 1)
  rw [twos_transverse_explicit, twos_transverseGrade_explicit, ladderEvenConstantV_eq] at hT
  have e : ((2 : ℤ), (1 : ℤ)) + (-2, 4 * (k : ℤ) + 8) = (-1 + 1, 2 * (2 * (k : ℤ) + 4) + 1) := by
    ext <;> simp
    all_goals ring
  rw [e] at hT
  exact hT

/-- The exceptional point `(−1, 2d)` has slip `2`. -/
theorem twos_slip_special1 (k : ℕ) : twosSlip k ((-1 : ℤ), 2 * (2 * (k : ℤ) + 4)) = 2 := by
  have hT1 : ((-1 : ℤ), 2 * (2 * (k : ℤ) + 4) + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    refine ⟨Or.inl (Or.inl (Set.mem_insert _ _)), ?_⟩
    intro h
    simp only [paperNearLadderD, Set.mem_setOf_eq] at h
    omega
  have hF1 := standardField_twos_eq_tile k (w := ((-1 : ℤ), 2 * (2 * (k : ℤ) + 4))) (x := ((-1 : ℤ), 2 * (2 * (k : ℤ) + 4) + 1))
    rfl hT1
  have hT2 : ((2 : ℤ), (2 : ℤ)) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    refine ⟨Or.inr ?_, ?_⟩
    · simp only [paperNearLadderC, Set.mem_setOf_eq]
      omega
    · intro h
      simp only [paperNearLadderD, Set.mem_setOf_eq] at h
      omega
  have hF2 := standardField_twos_eq_tile k (w := ((2 : ℤ), (1 : ℤ))) (x := ((2 : ℤ), (2 : ℤ))) rfl hT2
  unfold twosSlip
  rw [twos_shift_F k ((-1 : ℤ), 2 * (2 * (k : ℤ) + 4)), twos_F_transverse_21 k, hF1, hF2]
  rw [twos_H_pieces, twos_H_pieces]
  have i1 : twosInd (2 * (k : ℤ) + 4) (-1, 2 * (2 * (k : ℤ) + 4) + 1) = 1 := by
    rcases twosInd_spec (2 * (k : ℤ) + 4) (-1) (2 * (2 * (k : ℤ) + 4) + 1) with ⟨h, -⟩ | ⟨-, hn⟩
    · exact h
    · exact absurd (Or.inl ⟨rfl, rfl⟩) hn
  have i2 : twosInd (2 * (k : ℤ) + 4) (2, 2) = 0 := by
    rcases twosInd_spec (2 * (k : ℤ) + 4) 2 2 with ⟨h, hc⟩ | ⟨h, -⟩
    · exfalso
      rcases hc with hc | hc | hc <;> omega
    · exact h
  have q1 : (2 * (2 * (k : ℤ) + 4) + 1 - -1) ^ 2 / 4 = (2 * (k : ℤ) + 5) ^ 2 := by
    rw [show 2 * (2 * (k : ℤ) + 4) + 1 - -1 = 2 * (2 * (k : ℤ) + 5) by ring,
      show (2 * (2 * (k : ℤ) + 5)) ^ 2 = 4 * (2 * (k : ℤ) + 5) ^ 2 by ring]
    omega
  have q2 : (2 - 2 : ℤ) ^ 2 / 4 = 0 := by norm_num
  dsimp only at i1 i2 q1 q2 ⊢
  rw [q1, q2, i1, i2]
  have ex : (2 * (k : ℤ) + 5) ^ 2 = (2 * (k : ℤ) + 4) ^ 2 + 4 * (k : ℤ) + 9 := by ring
  omega

/-- The exceptional point `(d−2, 3d−2)` has slip `2`. -/
theorem twos_slip_special2 (k : ℕ) :
    twosSlip k ((2 * (k : ℤ) + 4) - 2, 3 * (2 * (k : ℤ) + 4) - 2) = 2 := by
  have hT1 : ((2 * (k : ℤ) + 4) - 2, 3 * (2 * (k : ℤ) + 4) - 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    refine ⟨Or.inr ?_, ?_⟩
    · simp only [paperNearLadderC, Set.mem_setOf_eq]
      omega
    · intro h
      simp only [paperNearLadderD, Set.mem_setOf_eq] at h
      omega
  have hF1 := standardField_twos_eq_tile k (w := ((2 * (k : ℤ) + 4) - 2, 3 * (2 * (k : ℤ) + 4) - 2))
    (x := ((2 * (k : ℤ) + 4) - 2, 3 * (2 * (k : ℤ) + 4) - 1)) (Prod.ext rfl (by dsimp only; ring)) hT1
  have hT2 : (2 * (k : ℤ) + 4 + 1, 2 * (k : ℤ) + 4) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    refine ⟨Or.inr ?_, ?_⟩
    · simp only [paperNearLadderC, Set.mem_setOf_eq]
      omega
    · intro h
      simp only [paperNearLadderD, Set.mem_setOf_eq] at h
      omega
  have hF2 := standardField_twos_eq_tile k (w := (2 * (k : ℤ) + 4 + 1, 2 * (k : ℤ) + 4 - 1))
    (x := (2 * (k : ℤ) + 4 + 1, 2 * (k : ℤ) + 4)) (Prod.ext rfl (by dsimp only; ring)) hT2
  have hP := twos_standardField_hasPeriods k
  have hT := period_transverse_apply hP (2 * (k : ℤ) + 4 + 1, 2 * (k : ℤ) + 4 - 1)
  rw [twos_transverse_explicit, twos_transverseGrade_explicit, ladderEvenConstantV_eq] at hT
  have e : (2 * (k : ℤ) + 4 + 1, 2 * (k : ℤ) + 4 - 1) + (-2, 4 * (k : ℤ) + 8) =
      (2 * (k : ℤ) + 4 - 2 + 1, 3 * (2 * (k : ℤ) + 4) - 2 + 1) := by
    ext <;> simp <;> ring
  rw [e] at hT
  unfold twosSlip
  rw [hF1, twos_shift_F k ((2 * (k : ℤ) + 4) - 2, 3 * (2 * (k : ℤ) + 4) - 2), hT, hF2]
  rw [twos_H_pieces, twos_H_pieces]
  dsimp only
  have i1 : twosInd (2 * (k : ℤ) + 4) ((2 * (k : ℤ) + 4) - 2, 3 * (2 * (k : ℤ) + 4) - 1) = 0 := by
    rcases twosInd_spec (2 * (k : ℤ) + 4) ((2 * (k : ℤ) + 4) - 2) (3 * (2 * (k : ℤ) + 4) - 1) with ⟨h, hc⟩ | ⟨h, -⟩
    · exfalso
      rcases hc with hc | hc | hc <;> omega
    · exact h
  have i2 : twosInd (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + 1, 2 * (k : ℤ) + 4) = 0 := by
    rcases twosInd_spec (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + 1) (2 * (k : ℤ) + 4) with ⟨h, hc⟩ | ⟨h, -⟩
    · exfalso
      rcases hc with hc | hc | hc <;> omega
    · exact h
  have qa : (3 * (2 * (k : ℤ) + 4) - 1 - ((2 * (k : ℤ) + 4) - 2)) ^ 2 =
      4 * ((2 * (k : ℤ) + 4) ^ 2 + (2 * (k : ℤ) + 4)) + 1 := by ring
  have qb : ((2 * (k : ℤ) + 4) - (2 * (k : ℤ) + 4 + 1)) ^ 2 = 1 := by ring
  have ht : (2 * (k : ℤ) + 5) * (2 * (k : ℤ) + 4 - 1) - (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 4 + 1) = 0 := by ring
  omega

/-- Membership in the native tile as explicit linear conditions. -/
theorem twos_tile_iff (d x1 x2 : ℤ) :
    (x1, x2) ∈ paperNearLadderTile d ↔
      (((x1 = -1 ∧ x2 = 2 * d + 1) ∨ (x1 = d + 1 ∧ x2 = d - 1) ∨ (x2 - x1 = d ∧ 0 < x1 ∧ x1 < d) ∨
          (-1 ≤ x1 ∧ x1 ≤ d + 1 ∧ 1 ≤ x2 ∧ x2 ≤ 3 * d - 1 ∧ -1 ≤ x2 - x1 ∧ x2 - x1 ≤ 2 * d + 1)) ∧
        ¬ ((x1 = -1 ∧ x2 ≤ d + 1) ∨ (x1 = d + 1 ∧ 2 * d - 1 ≤ x2))) := by
  unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Prod.mk.injEq]
  constructor <;> intro h <;> omega

set_option maxHeartbeats 400000 in
/-- The two exceptional points and the two tile shifts cover the closed polygon. The class-`0` tile point fails exactly at
the two exceptional points, at `z₁ = d+1`, at `z₁ = d` with `z₂ ≥ 2d−3`, and at `(d−1, 3d−2)`; there the class-`U` point is in the
tile. -/
theorem twos_slip_cover (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2) :
    (z1 = -1 ∧ z2 = 2 * (2 * (k : ℤ) + 4)) ∨ (z1 = 2 * (k : ℤ) + 4 - 2 ∧ z2 = 3 * (2 * (k : ℤ) + 4) - 2) ∨
      (z1 + 1, z2 + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) ∨
      (z1 - (2 * (k : ℤ) + 4), z2 - (2 * (k : ℤ) + 4) + 3) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
  rw [twosKey_pos] at hk
  by_cases hs1 : z1 = -1 ∧ z2 = 2 * (2 * (k : ℤ) + 4)
  · exact Or.inl hs1
  by_cases hs2 : z1 = 2 * (k : ℤ) + 4 - 2 ∧ z2 = 3 * (2 * (k : ℤ) + 4) - 2
  · exact Or.inr (Or.inl hs2)
  by_cases hU : z1 = 2 * (k : ℤ) + 4 + 1 ∨ (z1 = 2 * (k : ℤ) + 4 ∧ 2 * (2 * (k : ℤ) + 4) - 3 ≤ z2) ∨
      (z1 = 2 * (k : ℤ) + 4 - 1 ∧ z2 = 3 * (2 * (k : ℤ) + 4) - 2)
  · exact Or.inr (Or.inr (Or.inr (by rw [twos_tile_iff]; omega)))
  · exact Or.inr (Or.inr (Or.inl (by rw [twos_tile_iff]; omega)))

/-- The `z₂`-part of the class-`0` closed form: two threshold steps. -/
theorem twos_minpart0 (d z2 : ℤ) :
    min 0 (d - (z2 + 1)) + min 0 (2 * d - (z2 + 1)) - (min 0 (d - (z2 + 2)) + min 0 (2 * d - (z2 + 2))) =
      (if d - 1 ≤ z2 then 1 else 0) + (if 2 * d - 1 ≤ z2 then 1 else 0) := by
  split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- The class-`0` slip band on the column region `z1 = -1`. -/
theorem twos_slip_band0_m1 (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h0 : (z1 + 1, z2 + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) (hz : z1 = -1) :
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
/-- The class-`0` slip band on the column region `z1 = 0`. -/
theorem twos_slip_band0_0 (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h0 : (z1 + 1, z2 + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) (hz : z1 = 0) :
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
/-- The class-`0` slip band on the column region `1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 4 - 2`. -/
theorem twos_slip_band0_mid (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h0 : (z1 + 1, z2 + 2) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) (hz : 1 ≤ z1 ∧ z1 ≤ 2 * (k : ℤ) + 4 - 2) :
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

end FLatticePaper.Induction
