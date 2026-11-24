import FLatticePaper.Plane.Induction.NoSaddle

/-! The base slip of the pure word `3^k`: `D z = F z − F(z + (−2,0))` (`slip 1` of `frameAt`).

`F` is invariant under the kernel `K = (d,1)`, and `F(z + T) = F z − (d z₂ − z₁) + cV` with `cV = −d(d+3)/2` on the transverse
period `T = (1−d, 1+d)`. Hence `D(z + K) = D z` and `D(z + T) = D z + 2`. On the raw tile `F` is the staircase value, so
`D` is an explicit staircase difference (`slipD_M`, `slipD_N`) on the two families of raw points, with two exceptional points. -/

namespace FLatticePaper.Induction

open Farey Construction

/-- The base slip `D z = F z − F(z + (−2,0))` of the pure word. -/
noncomputable def slipD (k : ℕ) (z : Site) : ℤ :=
  reciprocalField k z - reciprocalField k (z + (-2, 0))

theorem slip_threes_eq (k : ℕ) (z : Site) :
    (frameAt (List.replicate k Digit.three)).slip (standardField (List.replicate k Digit.three)) 1 z =
      slipD k z := by
  rw [standardField_threes]
  unfold ChildFrame.slip slipD
  rw [frameAt_threes_shortShift]
  simp

/-- `F` is invariant under the kernel `K = (d, 1)`. -/
theorem reciprocalField_K (k : ℕ) (z : Site) :
    reciprocalField k (z + (2 * (k : ℤ) + 3, 1)) = reciprocalField k z := by
  have h := (reciprocalField_spec k).2.1 z
  rw [kernel_threes] at h
  rw [h]
  simp

/-- `F(z + T) = F z − (d z₂ − z₁) + cV` on the transverse period `T = (1−d, 1+d)`. -/
theorem reciprocalField_T (k : ℕ) (z : Site) :
    reciprocalField k (z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) =
      reciprocalField k z - ((2 * (k : ℤ) + 3) * z.2 - z.1) + stairEvenConstantV (2 * (k : ℤ) + 3) := by
  have h := (reciprocalField_spec k).2.2 z
  rw [transverse_threes] at h
  unfold Fraction.transverseGrade at h
  rw [h]
  ring

theorem slipD_K (k : ℕ) (z : Site) :
    slipD k (z + (2 * (k : ℤ) + 3, 1)) = slipD k z := by
  unfold slipD
  have e : z + (2 * (k : ℤ) + 3, 1) + (-2, 0) = (z + (-2, 0)) + (2 * (k : ℤ) + 3, 1) := by
    ext <;> simp
    all_goals ring
  rw [e, reciprocalField_K, reciprocalField_K]

theorem slipD_T (k : ℕ) (z : Site) :
    slipD k (z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) = slipD k z + 2 := by
  unfold slipD
  have e : z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) + (-2, 0) =
      (z + (-2, 0)) + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) := by
    ext <;> simp
    all_goals ring
  rw [e, reciprocalField_T, reciprocalField_T]
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The point `(2 − d, d+1)`: `D = 2`, from the transverse period and `F(d−1, 1) = 0`. -/
theorem slipD_exc_top (k : ℕ) :
    slipD k (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) = 2 := by
  unfold slipD
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have e1 : (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) + (-2, 0) + (2 * (k : ℤ) + 3, 1) =
      (2 * (k : ℤ) + 3 - 1, 1) + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) := by
    ext <;> simp
    all_goals ring
  have hK : reciprocalField k ((2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) + (-2, 0)) =
      reciprocalField k ((2 * (k : ℤ) + 3 - 1, 1) + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) := by
    rw [← e1, reciprocalField_K]
  rw [reciprocalField_T] at hK
  dsimp only at hK
  have hraw1 : reciprocalField k (2 * (k : ℤ) + 3 - 1, 1) =
      BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3 - 1, 1) :=
    reciprocalField_raw_eq k _ ((raw_mem_site _ _).mpr (by simp only [RawMem]; omega))
  have hraw2 : reciprocalField k (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) =
      BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) :=
    reciprocalField_raw_eq k _ ((raw_mem_site _ _).mpr (by simp only [RawMem]; omega))
  have hS1 : BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3 - 1, 1) = 0 := by
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3 - 1, 1) := by
      unfold BaseMask.StairEvenCorner
      simp only
      omega
    unfold BaseMask.stairEvenValue
    rw [if_neg hc, min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 3 - 1 - 1)]
    norm_num
  have hS2 : BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) =
      -((2 * (k : ℤ) + 3 + 1) * (2 * (k : ℤ) + 3 + 1 - 1) / 2) + (2 - (2 * (k : ℤ) + 3) - 1) := by
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) := by
      unfold BaseMask.StairEvenCorner
      simp only
      omega
    unfold BaseMask.stairEvenValue
    rw [if_neg hc, min_eq_left (by omega : 2 - (2 * (k : ℤ) + 3) - 1 ≤ 0)]
    ring
  have hcV := stairEvenConstantV_eq (2 * (k : ℤ) + 3)
  have hdiv : (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3 + 3) / 2 =
      (2 * (k : ℤ) + 3 + 1) * (2 * (k : ℤ) + 3 + 1 - 1) / 2 + (2 * (k : ℤ) + 3) := by
    have h : (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3 + 3) =
        (2 * (k : ℤ) + 3 + 1) * (2 * (k : ℤ) + 3 + 1 - 1) + 2 * (2 * (k : ℤ) + 3) := by ring
    rw [h]
    omega
  rw [hraw1, hS1] at hK
  rw [hraw2, hS2, hK, hcV]
  omega

theorem slipD_M (k : ℕ) (y1 y2 : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) y1 y2)
    (hM : RawMem (2 * (k : ℤ) + 3) (y1 - 2) y2) :
    slipD k (y1, y2) = BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (y1, y2) -
      BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (y1 - 2, y2) := by
  unfold slipD
  have e : ((y1, y2) : Site) + (-2, 0) = (y1 - 2, y2) := by
    ext <;> simp
    all_goals ring
  rw [e, reciprocalField_raw_eq k (y1, y2) ((raw_mem_site _ _).mpr hy),
    reciprocalField_raw_eq k (y1 - 2, y2) ((raw_mem_site _ _).mpr hM)]

theorem slipD_N (k : ℕ) (y1 y2 : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) y1 y2)
    (hN : RawMem (2 * (k : ℤ) + 3) (y1 + (2 * (k : ℤ) + 3) - 2) (y2 + 1)) :
    slipD k (y1, y2) = BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (y1, y2) -
      BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (y1 + (2 * (k : ℤ) + 3) - 2, y2 + 1) := by
  unfold slipD
  have e : ((y1, y2) : Site) + (-2, 0) + (2 * (k : ℤ) + 3, 1) = (y1 + (2 * (k : ℤ) + 3) - 2, y2 + 1) := by
    ext <;> simp
    all_goals ring
  rw [← reciprocalField_K k ((y1, y2) + (-2, 0)), e, reciprocalField_raw_eq k (y1, y2) ((raw_mem_site _ _).mpr hy),
    reciprocalField_raw_eq k (y1 + (2 * (k : ℤ) + 3) - 2, y2 + 1) ((raw_mem_site _ _).mpr hN)]

/-- The raw tile is covered by the two families and the two exceptional points, on which `D = 2`. -/
theorem slipD_raw_cases (k : ℕ) (y1 y2 : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) y1 y2) :
    RawMem (2 * (k : ℤ) + 3) (y1 - 2) y2 ∨
      RawMem (2 * (k : ℤ) + 3) (y1 + (2 * (k : ℤ) + 3) - 2) (y2 + 1) ∨
      (y1 = 2 - (2 * (k : ℤ) + 3) ∧ y2 = 2 * (k : ℤ) + 3 + 1) ∨
      (y1 = 3 - (2 * (k : ℤ) + 3) ∧ y2 = 2 * (k : ℤ) + 3 + 1) := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hM, hN, hE1, hE2⟩ := hcon
  unfold RawMem at hy hM hN
  omega

theorem slipD_exc_bottom (k : ℕ) :
    slipD k (3 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) = 2 := by
  unfold slipD
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have e1 : (3 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) + (-2, 0) + (2 * (k : ℤ) + 3, 1) =
      (2 * (k : ℤ) + 3, 1) + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) := by
    ext <;> simp
    all_goals ring
  have hK : reciprocalField k ((3 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) + (-2, 0)) =
      reciprocalField k ((2 * (k : ℤ) + 3, 1) + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) := by
    rw [← e1, reciprocalField_K]
  rw [reciprocalField_T] at hK
  dsimp only at hK
  have hraw1 : reciprocalField k (2 * (k : ℤ) + 3, 1) =
      BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3, 1) :=
    reciprocalField_raw_eq k _ ((raw_mem_site _ _).mpr (by simp only [RawMem]; omega))
  have hS1 : BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3, 1) = 0 := by
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3, 1) := by
      unfold BaseMask.StairEvenCorner
      simp only
      omega
    unfold BaseMask.stairEvenValue
    rw [if_neg hc, min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 3 - 1)]
    norm_num
  have hraw2 : reciprocalField k (3 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) =
      BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) :=
    reciprocalField_raw_eq k _ ((raw_mem_site _ _).mpr (by simp only [RawMem]; omega))
  have hS2 : BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) =
      -((2 * (k : ℤ) + 3 + 1) * (2 * (k : ℤ) + 3 + 1 - 1) / 2) + (3 - (2 * (k : ℤ) + 3) - 1) := by
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 + 1) := by
      unfold BaseMask.StairEvenCorner
      simp only
      omega
    unfold BaseMask.stairEvenValue
    rw [if_neg hc, min_eq_left (by omega : 3 - (2 * (k : ℤ) + 3) - 1 ≤ 0)]
    ring
  have hcV := stairEvenConstantV_eq (2 * (k : ℤ) + 3)
  have hdiv : (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3 + 3) / 2 =
      (2 * (k : ℤ) + 3 + 1) * (2 * (k : ℤ) + 3 + 1 - 1) / 2 + (2 * (k : ℤ) + 3) := by
    have h : (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3 + 3) =
        (2 * (k : ℤ) + 3 + 1) * (2 * (k : ℤ) + 3 + 1 - 1) + 2 * (2 * (k : ℤ) + 3) := by ring
    rw [h]
    omega
  rw [hraw1, hS1] at hK
  rw [hraw2, hS2, hK, hcV]
  omega

set_option maxHeartbeats 400000 in
/-- **`slipRange` at `3^k`:** `0 ≤ D ≤ 2` on the raw tile, which is the closed polygon. -/
theorem slipD_raw_range (k : ℕ) (y : Site)
    (hy : y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    0 ≤ slipD k y ∧ slipD k y ≤ 2 := by
  obtain ⟨y1, y2⟩ := y
  have hy' : RawMem (2 * (k : ℤ) + 3) y1 y2 := (raw_mem_site _ _).mp hy
  rcases slipD_raw_cases k y1 y2 hy' with hM | hN | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [slipD_M k y1 y2 hy' hM]
    unfold RawMem at hy' hM
    unfold BaseMask.stairEvenValue BaseMask.StairEvenCorner
    simp only [min_def]
    constructor <;> split_ifs <;> omega
  · rw [slipD_N k y1 y2 hy' hN]
    have ht := tri_succ y2
    unfold RawMem at hy' hN
    unfold BaseMask.stairEvenValue BaseMask.StairEvenCorner
    simp only [min_def, add_sub_cancel_right]
    constructor <;> split_ifs <;> omega
  · rw [slipD_exc_top k]
    norm_num
  · rw [slipD_exc_bottom k]
    norm_num

/-- `D` is `K`-invariant. -/
theorem slipD_nK (k : ℕ) (w : Site) (n : ℤ) :
    slipD k (w + (n * (2 * (k : ℤ) + 3), n)) = slipD k w := by
  refine Int.induction_on n ?_ ?_ ?_
  · have e0 : w + ((0 : ℤ) * (2 * (k : ℤ) + 3), (0 : ℤ)) = w := by ext <;> simp
    rw [e0]
  · intro i ih
    have e : w + (((i : ℤ) + 1) * (2 * (k : ℤ) + 3), (i : ℤ) + 1) =
        (w + ((i : ℤ) * (2 * (k : ℤ) + 3), (i : ℤ))) + (2 * (k : ℤ) + 3, 1) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add]
      all_goals ring
    rw [e, slipD_K, ih]
  · intro i ih
    have e : w + ((-(i : ℤ) - 1) * (2 * (k : ℤ) + 3), -(i : ℤ) - 1) + (2 * (k : ℤ) + 3, 1) =
        w + (-(i : ℤ) * (2 * (k : ℤ) + 3), -(i : ℤ)) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add]
      all_goals ring
    have h := slipD_K k (w + ((-(i : ℤ) - 1) * (2 * (k : ℤ) + 3), -(i : ℤ) - 1))
    rw [e, ih] at h
    exact h.symm

/-- `D` shifts by `2m` under `mT`. -/
theorem slipD_mT (k : ℕ) (w : Site) (m : ℤ) :
    slipD k (w + (m * (1 - (2 * (k : ℤ) + 3)), m * (1 + (2 * (k : ℤ) + 3)))) = slipD k w + 2 * m := by
  refine Int.induction_on m ?_ ?_ ?_
  · have e0 : w + ((0 : ℤ) * (1 - (2 * (k : ℤ) + 3)), (0 : ℤ) * (1 + (2 * (k : ℤ) + 3))) = w := by
      ext <;> simp
    rw [e0]
    ring
  · intro i ih
    have e : w + (((i : ℤ) + 1) * (1 - (2 * (k : ℤ) + 3)), ((i : ℤ) + 1) * (1 + (2 * (k : ℤ) + 3))) =
        (w + ((i : ℤ) * (1 - (2 * (k : ℤ) + 3)), (i : ℤ) * (1 + (2 * (k : ℤ) + 3)))) +
          (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add]
      all_goals ring
    rw [e, slipD_T, ih]
    ring
  · intro i ih
    have e : w + ((-(i : ℤ) - 1) * (1 - (2 * (k : ℤ) + 3)), (-(i : ℤ) - 1) * (1 + (2 * (k : ℤ) + 3))) +
        (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) =
        w + (-(i : ℤ) * (1 - (2 * (k : ℤ) + 3)), -(i : ℤ) * (1 + (2 * (k : ℤ) + 3))) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add]
      all_goals ring
    have h := slipD_T k (w + ((-(i : ℤ) - 1) * (1 - (2 * (k : ℤ) + 3)), (-(i : ℤ) - 1) * (1 + (2 * (k : ℤ) + 3))))
    rw [e, ih] at h
    linarith

/-- The translation law: `D(w + combine i j) = D w + 2j`. -/
theorem slipD_combine (k : ℕ) (w : Site) (i j : ℤ) :
    slipD k (w + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j) = slipD k w + 2 * j := by
  rw [combine_eq _ (by omega : (2 * (k : ℤ) + 3) % 2 = 1)]
  have e : w + (i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3)), i + j * (1 + (2 * (k : ℤ) + 3))) =
      (w + (i * (2 * (k : ℤ) + 3), i)) + (j * (1 - (2 * (k : ℤ) + 3)), j * (1 + (2 * (k : ℤ) + 3))) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add]
    all_goals ring
  rw [e, slipD_mT, slipD_nK]

end FLatticePaper.Induction
