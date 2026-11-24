import FLatticePaper.Plane.Induction.NoSaddle

/-! The base slip of the pure word `3^k`: `D z = F z − F(z + (−2,0))` (`slip 1` of `frameAt`).

`F` is invariant under the kernel `K = (d,1)`, and `F(z + T) = F z − (d z₂ − z₁) + cV` with `cV = −d(d+3)/2` on the transverse
period `T = (1−d, 1+d)`. Hence `D(z + K) = D z` and `D(z + T) = D z + 2`. On the raw tile `F` is the staircase value, so
`D` is an explicit staircase difference (`slipD_M`, `slipD_N`) on the two families of raw points, with two exceptional points. -/

namespace FLatticePaper.Induction

open Farey Construction

open scoped Classical

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

/-- The closed form of the slip on the raw tile `(x, y)` (with `d = 2k+3`): `0` for `x ≥ 3`; `1` on `x = 2` except the
corners `(2,0) ↦ 0` and `(2,d+1) ↦ 2`; `clamp(x+y−1, 0, 2)` for `3−d ≤ x ≤ 1`; on `x = 2−d`, `y+2−d` and `2` at `y = d+1`. -/
def slipDcf (d x y : ℤ) : ℤ :=
  if 3 ≤ x then 0
  else if x = 2 then (if y = 0 then 0 else if y = d + 1 then 2 else 1)
  else if 3 - d ≤ x then (if x + y - 1 ≤ 0 then 0 else if x + y - 1 ≤ 2 then x + y - 1 else 2)
  else (if y = d + 1 then 2 else y + 2 - d)

/-- The `M`-family value in closed form. -/
theorem slipD_M_closed (k : ℕ) (y1 y2 : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) y1 y2)
    (hM : RawMem (2 * (k : ℤ) + 3) (y1 - 2) y2) :
    slipD k (y1, y2) = slipDcf (2 * (k : ℤ) + 3) y1 y2 := by
  rw [slipD_M k y1 y2 hy hM]
  unfold RawMem at hy hM
  unfold BaseMask.stairEvenValue BaseMask.StairEvenCorner slipDcf
  simp only [min_def]
  split_ifs <;> omega

/-- The `N`-family value in closed form. -/
theorem slipD_N_closed (k : ℕ) (y1 y2 : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) y1 y2)
    (hN : RawMem (2 * (k : ℤ) + 3) (y1 + (2 * (k : ℤ) + 3) - 2) (y2 + 1)) :
    slipD k (y1, y2) = slipDcf (2 * (k : ℤ) + 3) y1 y2 := by
  rw [slipD_N k y1 y2 hy hN]
  have ht := tri_succ y2
  unfold RawMem at hy hN
  unfold BaseMask.stairEvenValue BaseMask.StairEvenCorner slipDcf
  simp only [min_def, add_sub_cancel_right]
  split_ifs <;> omega

/-- The exceptional points. -/
theorem slipDcf_exc (k : ℕ) :
    slipDcf (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (2 * (k : ℤ) + 3 + 1) = 2 ∧
      slipDcf (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (2 * (k : ℤ) + 3 + 1) = 2 := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  unfold slipDcf
  constructor <;> split_ifs <;> omega

/-- The value of `D` on a raw point. -/
theorem slipD_raw_Dcf (k : ℕ) (y1 y2 : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) y1 y2) :
    slipD k (y1, y2) = slipDcf (2 * (k : ℤ) + 3) y1 y2 := by
  rcases slipD_raw_cases k y1 y2 hy with hM | hN | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact slipD_M_closed k y1 y2 hy hM
  · exact slipD_N_closed k y1 y2 hy hN
  · subst h1
    subst h2
    rw [slipD_exc_top, (slipDcf_exc k).1]
  · subst h1
    subst h2
    rw [slipD_exc_bottom, (slipDcf_exc k).2]

/-- The left neighbour of an even raw point: `D(x−1, w)` in closed form (by `K`-invariance when `(x−1, w)` is not raw). -/
theorem slip_val_even_minus (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w)
    (hpar : (x + w) % 2 = 0) :
    slipD k (x - 1, w) = if RawMem (2 * (k : ℤ) + 3) (x - 1) w then slipDcf (2 * (k : ℤ) + 3) (x - 1) w
      else slipDcf (2 * (k : ℤ) + 3) (x - 1 + (2 * (k : ℤ) + 3)) (w + 1) := by
  split_ifs with h
  · exact slipD_raw_Dcf k (x - 1) w h
  · have hK : RawMem (2 * (k : ℤ) + 3) (x - 1 + (2 * (k : ℤ) + 3)) (w + 1) := by
      unfold RawMem at hy h ⊢
      omega
    have e : slipD k (x - 1, w) = slipD k (x - 1 + (2 * (k : ℤ) + 3), w + 1) := by
      rw [← slipD_K k (x - 1, w)]
      congr 1
    rw [e]
    exact slipD_raw_Dcf k _ _ hK

/-- The right neighbour of an even raw point: `D(x+1, w)` in closed form (by `K`-invariance when `(x+1, w)` is not raw). -/
theorem slip_val_even_plus (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w)
    (hpar : (x + w) % 2 = 0) :
    slipD k (x + 1, w) = if RawMem (2 * (k : ℤ) + 3) (x + 1) w then slipDcf (2 * (k : ℤ) + 3) (x + 1) w
      else slipDcf (2 * (k : ℤ) + 3) (x + 1 - (2 * (k : ℤ) + 3)) (w - 1) := by
  split_ifs with h
  · exact slipD_raw_Dcf k (x + 1) w h
  · have hK : RawMem (2 * (k : ℤ) + 3) (x + 1 - (2 * (k : ℤ) + 3)) (w - 1) := by
      unfold RawMem at hy h ⊢
      omega
    have e : slipD k (x + 1, w) = slipD k (x + 1 - (2 * (k : ℤ) + 3), w - 1) := by
      rw [← slipD_K k (x + 1 - (2 * (k : ℤ) + 3), w - 1)]
      congr 1
      ext <;> simp
    rw [e]
    exact slipD_raw_Dcf k _ _ hK

/-- The left neighbour value of an even raw point (closed form). -/
noncomputable def slipLeft (d x w : ℤ) : ℤ :=
  if RawMem d (x - 1) w then slipDcf d (x - 1) w else slipDcf d (x - 1 + d) (w + 1)

/-- The right neighbour value of an even raw point (closed form). -/
noncomputable def slipRight (d x w : ℤ) : ℤ :=
  if RawMem d (x + 1) w then slipDcf d (x + 1) w else slipDcf d (x + 1 - d) (w - 1)

set_option maxHeartbeats 400000 in
/-- The left unit bound at an even raw centre. -/
theorem slipLeft_bounds (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hpar : (x + w) % 2 = 0) :
    -1 ≤ slipLeft (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w ∧
    slipLeft (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w ≤ 1 := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  unfold slipLeft
  unfold RawMem at hy
  by_cases hL : RawMem (2 * (k : ℤ) + 3) (x - 1) w
  · rw [if_pos hL]
    unfold RawMem at hL
    unfold slipDcf
    split_ifs <;> omega
  · rw [if_neg hL]
    unfold RawMem at hL
    unfold slipDcf
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- The right unit bound at an even raw centre. -/
theorem slipRight_bounds (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hpar : (x + w) % 2 = 0) :
    -1 ≤ slipRight (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w ∧
    slipRight (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w ≤ 1 := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  unfold slipRight
  unfold RawMem at hy
  by_cases hR : RawMem (2 * (k : ℤ) + 3) (x + 1) w
  · rw [if_pos hR]
    unfold RawMem at hR
    unfold slipDcf
    split_ifs <;> omega
  · rw [if_neg hR]
    unfold RawMem at hR
    unfold slipDcf
    split_ifs <;> omega
set_option maxHeartbeats 400000 in
/-- The slip on a raw point lies in `[0, 2]` (closed form). -/
theorem slipDcf_range (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) :
    0 ≤ slipDcf (2 * (k : ℤ) + 3) x w ∧ slipDcf (2 * (k : ℤ) + 3) x w ≤ 2 := by
  have h := slipD_raw_range k (x, w) ((raw_mem_site _ _).mpr hy)
  rw [slipD_raw_Dcf k x w hy] at h
  exact h

set_option maxHeartbeats 400000 in
/-- The left neighbour of an even raw point has its slip in `[0, 2]`. -/
theorem slipLeft_range (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hpar : (x + w) % 2 = 0) :
    0 ≤ slipLeft (2 * (k : ℤ) + 3) x w ∧ slipLeft (2 * (k : ℤ) + 3) x w ≤ 2 := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  unfold slipLeft
  unfold RawMem at hy
  by_cases hL : RawMem (2 * (k : ℤ) + 3) (x - 1) w
  · rw [if_pos hL]
    unfold RawMem at hL
    unfold slipDcf
    split_ifs <;> omega
  · rw [if_neg hL]
    unfold RawMem at hL
    unfold slipDcf
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- The right neighbour of an even raw point has its slip in `[0, 2]`. -/
theorem slipRight_range (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hpar : (x + w) % 2 = 0) :
    0 ≤ slipRight (2 * (k : ℤ) + 3) x w ∧ slipRight (2 * (k : ℤ) + 3) x w ≤ 2 := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  unfold slipRight
  unfold RawMem at hy
  by_cases hR : RawMem (2 * (k : ℤ) + 3) (x + 1) w
  · rw [if_pos hR]
    unfold RawMem at hR
    unfold slipDcf
    split_ifs <;> omega
  · rw [if_neg hR]
    unfold RawMem at hR
    unfold slipDcf
    split_ifs <;> omega

/-- No saddle at an even raw centre: the centre and both neighbours lie in `[0, 2]`, and an even centre value
excludes the opposite unit steps. -/
theorem even_no_saddle (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hpar : (x + w) % 2 = 0) :
    slipDcf (2 * (k : ℤ) + 3) x w % 2 = 0 →
      ¬ ((slipLeft (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w = -1 ∧
          slipRight (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w = 1) ∨
        (slipLeft (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w = 1 ∧
          slipRight (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w = -1)) := by
  intro hev
  obtain ⟨hA0, hA2⟩ := slipDcf_range k x w hy
  obtain ⟨hL0, hL2⟩ := slipLeft_range k x w hy hpar
  obtain ⟨hR0, hR2⟩ := slipRight_range k x w hy hpar
  omega

/-- The value of `D` at the lower vertical neighbour of an odd raw point (closed form). -/
noncomputable def slipDown (d x w : ℤ) : ℤ :=
  if RawMem d x (w - 1) then slipDcf d x (w - 1)
  else if w = 0 then slipDcf d (x + 1 - d) (w + d) - 2 else slipDcf d (x + d) w

/-- The value of `D` at the upper vertical neighbour of an odd raw point (closed form). -/
noncomputable def slipUp (d x w : ℤ) : ℤ :=
  if RawMem d x (w + 1) then slipDcf d x (w + 1)
  else if w = d + 1 then slipDcf d (x - 1 + d) (w - d) + 2 else slipDcf d (x - d) w

theorem slip_val_odd_down (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hpar : (x + w) % 2 = 1) :
    slipD k (x, w - 1) = slipDown (2 * (k : ℤ) + 3) x w := by
  unfold slipDown
  by_cases h1 : RawMem (2 * (k : ℤ) + 3) x (w - 1)
  · rw [if_pos h1]
    exact slipD_raw_Dcf k x (w - 1) h1
  · rw [if_neg h1]
    by_cases h2 : w = 0
    · rw [if_pos h2]
      have hu : RawMem (2 * (k : ℤ) + 3) (x + 1 - (2 * (k : ℤ) + 3)) (w + (2 * (k : ℤ) + 3)) := by
        unfold RawMem at hy h1 ⊢
        omega
      have e2 : ((x, w - 1) : Site) + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) =
          (x + 1 - (2 * (k : ℤ) + 3), w + (2 * (k : ℤ) + 3)) := by
        ext <;> simp only [Prod.fst_add, Prod.snd_add]
        all_goals ring
      have h := slipD_T k (x, w - 1)
      rw [e2] at h
      have e : slipD k (x, w - 1) = slipD k (x + 1 - (2 * (k : ℤ) + 3), w + (2 * (k : ℤ) + 3)) - 2 := by
        linarith
      rw [e, slipD_raw_Dcf k _ _ hu]
    · rw [if_neg h2]
      have hu : RawMem (2 * (k : ℤ) + 3) (x + (2 * (k : ℤ) + 3)) w := by
        unfold RawMem at hy h1 ⊢
        omega
      have e2 : ((x, w - 1) : Site) + (2 * (k : ℤ) + 3, 1) = (x + (2 * (k : ℤ) + 3), w) := by
        ext <;> simp only [Prod.fst_add, Prod.snd_add]
        all_goals ring
      have h := slipD_K k (x, w - 1)
      rw [e2] at h
      rw [← h, slipD_raw_Dcf k _ _ hu]

theorem slip_val_odd_up (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hpar : (x + w) % 2 = 1) :
    slipD k (x, w + 1) = slipUp (2 * (k : ℤ) + 3) x w := by
  unfold slipUp
  by_cases h1 : RawMem (2 * (k : ℤ) + 3) x (w + 1)
  · rw [if_pos h1]
    exact slipD_raw_Dcf k x (w + 1) h1
  · rw [if_neg h1]
    by_cases h2 : w = 2 * (k : ℤ) + 3 + 1
    · rw [if_pos h2]
      have hu : RawMem (2 * (k : ℤ) + 3) (x - 1 + (2 * (k : ℤ) + 3)) (w - (2 * (k : ℤ) + 3)) := by
        unfold RawMem at hy h1 ⊢
        omega
      have e2 : ((x - 1 + (2 * (k : ℤ) + 3), w - (2 * (k : ℤ) + 3)) : Site) + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) =
          (x, w + 1) := by
        ext <;> simp only [Prod.fst_add, Prod.snd_add]
        all_goals ring
      have h := slipD_T k (x - 1 + (2 * (k : ℤ) + 3), w - (2 * (k : ℤ) + 3))
      rw [e2] at h
      have e : slipD k (x, w + 1) = slipD k (x - 1 + (2 * (k : ℤ) + 3), w - (2 * (k : ℤ) + 3)) + 2 := by
        linarith
      rw [e, slipD_raw_Dcf k _ _ hu]
    · rw [if_neg h2]
      have hu : RawMem (2 * (k : ℤ) + 3) (x - (2 * (k : ℤ) + 3)) w := by
        unfold RawMem at hy h1 h2 ⊢
        omega
      have e2 : ((x - (2 * (k : ℤ) + 3), w) : Site) + (2 * (k : ℤ) + 3, 1) = (x, w + 1) := by
        ext <;> simp only [Prod.fst_add, Prod.snd_add]
        all_goals ring
      have h := slipD_K k (x - (2 * (k : ℤ) + 3), w)
      rw [e2] at h
      rw [h, slipD_raw_Dcf k _ _ hu]

set_option maxHeartbeats 400000 in
/-- The lower vertical neighbour of an odd raw point is within one unit of its centre. -/
theorem slipDown_bounds (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hpar : (x + w) % 2 = 1) :
    -1 ≤ slipDown (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w ∧
    slipDown (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w ≤ 1 := by
  unfold slipDown
  unfold RawMem at hy
  by_cases h1 : RawMem (2 * (k : ℤ) + 3) x (w - 1)
  · rw [if_pos h1]
    unfold RawMem at h1
    unfold slipDcf
    split_ifs <;> omega
  · rw [if_neg h1]
    unfold RawMem at h1
    by_cases h2 : w = 0
    · rw [if_pos h2]
      unfold slipDcf
      split_ifs <;> omega
    · rw [if_neg h2]
      unfold slipDcf
      split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- The upper vertical neighbour of an odd raw point is within one unit of its centre. -/
theorem slipUp_bounds (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hpar : (x + w) % 2 = 1) :
    -1 ≤ slipUp (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w ∧
    slipUp (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w ≤ 1 := by
  unfold slipUp
  unfold RawMem at hy
  by_cases h1 : RawMem (2 * (k : ℤ) + 3) x (w + 1)
  · rw [if_pos h1]
    unfold RawMem at h1
    unfold slipDcf
    split_ifs <;> omega
  · rw [if_neg h1]
    unfold RawMem at h1
    by_cases h2 : w = 2 * (k : ℤ) + 3 + 1
    · rw [if_pos h2]
      unfold slipDcf
      split_ifs <;> omega
    · rw [if_neg h2]
      unfold slipDcf
      split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- The lower neighbour value of an odd raw point lies in `[0, 2]`. -/
theorem slipDown_range (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hpar : (x + w) % 2 = 1) :
    0 ≤ slipDown (2 * (k : ℤ) + 3) x w ∧ slipDown (2 * (k : ℤ) + 3) x w ≤ 2 := by
  unfold slipDown
  unfold RawMem at hy
  by_cases h1 : RawMem (2 * (k : ℤ) + 3) x (w - 1)
  · rw [if_pos h1]
    exact slipDcf_range k x (w - 1) h1
  · rw [if_neg h1]
    unfold RawMem at h1
    by_cases h2 : w = 0
    · rw [if_pos h2]
      have hv : slipDcf (2 * (k : ℤ) + 3) (x + 1 - (2 * (k : ℤ) + 3)) (w + (2 * (k : ℤ) + 3)) = 2 := by
        unfold slipDcf
        split_ifs <;> omega
      rw [hv]
      norm_num
    · rw [if_neg h2]
      have hu : RawMem (2 * (k : ℤ) + 3) (x + (2 * (k : ℤ) + 3)) w := by
        unfold RawMem
        omega
      exact slipDcf_range k _ _ hu

set_option maxHeartbeats 400000 in
/-- The upper neighbour value of an odd raw point lies in `[0, 3]`, and reaches `3` only on the top row. -/
theorem slipUp_range (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hpar : (x + w) % 2 = 1) :
    0 ≤ slipUp (2 * (k : ℤ) + 3) x w ∧ slipUp (2 * (k : ℤ) + 3) x w ≤ 3 ∧
      (slipUp (2 * (k : ℤ) + 3) x w = 3 → w = 2 * (k : ℤ) + 3 + 1) := by
  unfold slipUp
  unfold RawMem at hy
  by_cases h1 : RawMem (2 * (k : ℤ) + 3) x (w + 1)
  · rw [if_pos h1]
    obtain ⟨a, b⟩ := slipDcf_range k x (w + 1) h1
    exact ⟨a, by omega, fun h => by omega⟩
  · rw [if_neg h1]
    unfold RawMem at h1
    by_cases h2 : w = 2 * (k : ℤ) + 3 + 1
    · rw [if_pos h2]
      have hv : slipDcf (2 * (k : ℤ) + 3) (x - 1 + (2 * (k : ℤ) + 3)) (w - (2 * (k : ℤ) + 3)) ≤ 1 ∧
          0 ≤ slipDcf (2 * (k : ℤ) + 3) (x - 1 + (2 * (k : ℤ) + 3)) (w - (2 * (k : ℤ) + 3)) := by
        unfold slipDcf
        split_ifs <;> omega
      exact ⟨by omega, by omega, fun _ => h2⟩
    · rw [if_neg h2]
      have hu : RawMem (2 * (k : ℤ) + 3) (x - (2 * (k : ℤ) + 3)) w := by
        unfold RawMem
        omega
      obtain ⟨a, b⟩ := slipDcf_range k _ _ hu
      exact ⟨a, by omega, fun h => by omega⟩

set_option maxHeartbeats 400000 in
/-- On the top row the lower neighbour has slip `2`. -/
theorem slipDown_top (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hw : w = 2 * (k : ℤ) + 3 + 1)
    (hpar : (x + w) % 2 = 1) : slipDown (2 * (k : ℤ) + 3) x w = 2 := by
  unfold slipDown
  unfold RawMem at hy
  have hv : slipDcf (2 * (k : ℤ) + 3) x (w - 1) = 2 := by
    unfold slipDcf
    split_ifs <;> omega
  have hu : RawMem (2 * (k : ℤ) + 3) x (w - 1) := by
    unfold RawMem
    omega
  rw [if_pos hu, hv]

set_option maxHeartbeats 400000 in
/-- No saddle at an odd raw centre with even value. -/
theorem odd_no_saddle (k : ℕ) (x w : ℤ) (hy : RawMem (2 * (k : ℤ) + 3) x w) (hpar : (x + w) % 2 = 1) :
    slipDcf (2 * (k : ℤ) + 3) x w % 2 = 0 →
      ¬ ((slipDown (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w = -1 ∧
          slipUp (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w = 1) ∨
        (slipDown (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w = 1 ∧
          slipUp (2 * (k : ℤ) + 3) x w - slipDcf (2 * (k : ℤ) + 3) x w = -1)) := by
  intro hev
  obtain ⟨hA0, hA2⟩ := slipDcf_range k x w (by unfold RawMem at hy ⊢; exact hy)
  obtain ⟨hD0, hD2⟩ := slipDown_range k x w hy hpar
  obtain ⟨hU0, hU3, hUtop⟩ := slipUp_range k x w hy hpar
  have htop : slipUp (2 * (k : ℤ) + 3) x w = 3 → slipDown (2 * (k : ℤ) + 3) x w = 2 :=
    fun h => slipDown_top k x w hy (hUtop h) hpar
  omega

end FLatticePaper.Induction
