import FLatticePaper.Plane.Induction.PolygonRaw
import FLatticePaper.Plane.Induction.PureBaseUnitPrice

/-! The price range `0 ≤ P ≤ 1` on the closed polygon of the pure word `3^k` (`priceRange` of `StrongResidual`).

The closed polygon of the pure frame is contained in the native raw tile `RawMem` (`PolygonRaw`), so the range is a statement about
the raw tile. On the raw tile, `F` is the staircase value (`stairEven_raw_height`). The price `P = threesP` is computed on the set
`N = {y raw : y − (1,−1) raw}` (where `P y = [y₁ ≤ 1]`), and on the remaining raw points (the top row `y₂ = d+1`, the two points
with `y₁ = 2−d` near the top, and the two corners) from the period shifts `K = (d,1)`, `T = (1−d,1+d)` and one explicit unit step. -/

namespace FLatticePaper.Induction

open Farey Construction

/-- The price of the pure word in explicit form (`price_threes`). -/
noncomputable def threesP (k : ℕ) (z : Site) : ℤ :=
  reciprocalField k z - reciprocalField k (z - (1, -1)) - z.2

theorem reciprocalField_raw_eq (k : ℕ) (y : Site)
    (hy : y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    reciprocalField k y = BaseMask.stairEvenValue (2 * (k : ℤ) + 3) y := by
  have h := (reciprocalField_spec k).1 ⟨y, hy⟩
  rw [BaseMask.stairEven_raw_height] at h
  simpa using h.symm

theorem threesP_K (k : ℕ) (z : Site) :
    threesP k (z + (2 * (k : ℤ) + 3, 1)) = threesP k z - 1 := by
  have h := (priceDrift_threes k z).1
  rw [frameAt_threes_child, kernel_threes] at h
  simp only [price_threes] at h
  unfold threesP
  linarith

theorem threesP_T (k : ℕ) (z : Site) :
    threesP k (z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) = threesP k z := by
  have h := (priceDrift_threes k z).2
  rw [frameAt_threes_child, transverse_threes] at h
  simp only [price_threes] at h
  unfold threesP
  linarith

/-- The corner `(2, d+1)` is raw. -/
theorem raw_corner_top (d : ℤ) (hd : 3 ≤ d) : RawMem d 2 (d + 1) := by
  unfold RawMem
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

/-- The price on `N`: for raw `y` with `y − (1,−1)` raw, `P y = [y₁ ≤ 1]`. -/
theorem threesP_of_N (k : ℕ) (y1 y2 : ℤ)
    (hy : RawMem (2 * (k : ℤ) + 3) y1 y2) (hv : RawMem (2 * (k : ℤ) + 3) (y1 - 1) (y2 + 1)) :
    threesP k (y1, y2) = if y1 ≤ 1 then 1 else 0 := by
  have hyS : (y1, y2) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
    (raw_mem_site _ _).mpr hy
  have hvS : (y1 - 1, y2 + 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
    (raw_mem_site _ _).mpr hv
  have hc1 : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (y1, y2) := by
    unfold RawMem at hv hy
    unfold BaseMask.StairEvenCorner
    simp only
    omega
  have hc2 : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (y1 - 1, y2 + 1) := by
    unfold RawMem at hv hy
    unfold BaseMask.StairEvenCorner
    simp only
    omega
  unfold threesP
  have e2 : (y1, y2) - ((1 : ℤ), (-1 : ℤ)) = (y1 - 1, y2 + 1) := by
    ext <;> simp
  rw [e2, reciprocalField_raw_eq k (y1, y2) hyS, reciprocalField_raw_eq k (y1 - 1, y2 + 1) hvS]
  unfold BaseMask.stairEvenValue
  rw [if_neg hc1, if_neg hc2]
  have ht := tri_succ y2
  have hm : min (y1 - 1) 0 - min (y1 - 1 - 1) 0 = if y1 ≤ 1 then 1 else 0 := by
    by_cases h : y1 ≤ 1
    · rw [if_pos h, min_eq_left (by omega : y1 - 1 ≤ 0), min_eq_left (by omega : y1 - 1 - 1 ≤ 0)]
      ring
    · rw [if_neg h, min_eq_right (by omega : 0 ≤ y1 - 1), min_eq_right (by omega : 0 ≤ y1 - 1 - 1)]
      ring
  simp only [add_sub_cancel_right] at ht ⊢
  linarith

/-- The top row `y₂ = d+1` (with `2 − d ≤ x ≤ 1`): `P` is the price of the point `(x+d−1, 0)` (by the `T`-period). -/
theorem threesP_E1 (k : ℕ) (x : ℤ) (hx1 : 2 - (2 * (k : ℤ) + 3) ≤ x) (hx2 : x ≤ 1) :
    threesP k (x, 2 * (k : ℤ) + 3 + 1) = if x ≤ 2 - (2 * (k : ℤ) + 3) then 1 else 0 := by
  have hT : (x + (2 * (k : ℤ) + 3) - 1, (0 : ℤ)) + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) =
      (x, 2 * (k : ℤ) + 3 + 1) := by
    ext <;> simp
    all_goals ring
  rw [← hT, threesP_T, threesP_of_N k (x + (2 * (k : ℤ) + 3) - 1) 0]
  · split_ifs <;> omega
  · unfold RawMem
    omega
  · unfold RawMem
    omega

/-- `P(2−d, d−1) = 1`, via `K`-shift to `(2, d)`, where `P = 0`. -/
theorem threesP_E2a (k : ℕ) : threesP k (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 - 1) = 1 := by
  have h := threesP_K k (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 - 1)
  have hz : (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 - 1) + (2 * (k : ℤ) + 3, 1) = (2, 2 * (k : ℤ) + 3) := by
    ext <;> simp
  rw [hz, threesP_of_N k 2 (2 * (k : ℤ) + 3) (by unfold RawMem; omega) (by unfold RawMem; omega)] at h
  norm_num at h
  linarith

/-- `P(2−d, d) = P(2, d+1) + 1`, via `K`-shift. -/
theorem threesP_E2b (k : ℕ) : threesP k (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) =
    threesP k (2, 2 * (k : ℤ) + 3 + 1) + 1 := by
  have h := threesP_K k (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3)
  have hz : (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3, 1) = (2, 2 * (k : ℤ) + 3 + 1) := by
    ext <;> simp
  rw [hz] at h
  linarith

/-- `P(0,0) = 1`, via `K`-shift to `(d,1)`, where `P = 0`. -/
theorem threesP_E3a (k : ℕ) : threesP k (0, 0) = 1 := by
  have h := threesP_K k (0, 0)
  have hz : ((0 : ℤ), (0 : ℤ)) + (2 * (k : ℤ) + 3, 1) = (2 * (k : ℤ) + 3, 1) := by
    ext <;> simp
  rw [hz, threesP_of_N k (2 * (k : ℤ) + 3) 1 (by unfold RawMem; omega) (by unfold RawMem; omega)] at h
  have hne : ¬ (2 * (k : ℤ) + 3 ≤ 1) := by omega
  rw [if_neg hne] at h
  linarith

set_option maxHeartbeats 400000 in
/-- `P(2, d+1) = 0`: the unit step from `(1, d+1)` to `(1, d+2)`, with the representative `(d, 0)` of `(1, d+1)`. -/
theorem threesP_E3b (k : ℕ) : threesP k (2, 2 * (k : ℤ) + 3 + 1) = 0 := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hyS : ((2 * (k : ℤ) + 3, 0) : Site) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
    (raw_mem_site _ _).mpr (by simp only [RawMem]; omega)
  have hyeS : ((2 * (k : ℤ) + 3, 0) : Site) + (0, 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
    (raw_mem_site _ _).mpr (by simp only [RawMem, Prod.fst_add, Prod.snd_add]; omega)
  have hz : ((1 : ℤ), 2 * (k : ℤ) + 3 + 1) =
      ((2 * (k : ℤ) + 3, 0) : Site) + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine 0 1 := by
    rw [combine_eq _ hodd]
    ext <;> simp
    all_goals ring
  have hstep := reciprocal_native_step k hyS hyeS hz
  have e4 : ((2 * (k : ℤ) + 3, 0) : Site) + (0, 1) = (2 * (k : ℤ) + 3, 1) := by
    ext <;> simp
  rw [e4] at hstep
  dsimp only at hstep
  have hF1 : reciprocalField k (1, 2 * (k : ℤ) + 3 + 1) =
      BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (1, 2 * (k : ℤ) + 3 + 1) :=
    reciprocalField_raw_eq k (1, 2 * (k : ℤ) + 3 + 1)
      ((raw_mem_site (2 * (k : ℤ) + 3) (1, 2 * (k : ℤ) + 3 + 1)).mpr (by simp only [RawMem]; omega))
  have hF2 : reciprocalField k (2, 2 * (k : ℤ) + 3 + 1) =
      BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (2, 2 * (k : ℤ) + 3 + 1) :=
    reciprocalField_raw_eq k (2, 2 * (k : ℤ) + 3 + 1)
      ((raw_mem_site (2 * (k : ℤ) + 3) (2, 2 * (k : ℤ) + 3 + 1)).mpr (raw_corner_top _ hd3))
  have hS21 : BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (2, 2 * (k : ℤ) + 3 + 1) =
      -((2 * (k : ℤ) + 3 + 1) * (2 * (k : ℤ) + 3 + 1 - 1) / 2) + 1 := by
    have hc : BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2, 2 * (k : ℤ) + 3 + 1) :=
      Or.inr ⟨rfl, rfl⟩
    unfold BaseMask.stairEvenValue
    rw [if_pos hc]
    norm_num
  have hS11 : BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (1, 2 * (k : ℤ) + 3 + 1) =
      -((2 * (k : ℤ) + 3 + 1) * (2 * (k : ℤ) + 3 + 1 - 1) / 2) := by
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (1, 2 * (k : ℤ) + 3 + 1) := by
      unfold BaseMask.StairEvenCorner
      simp only
      omega
    unfold BaseMask.stairEvenValue
    rw [if_neg hc]
    norm_num
  have hSd1 : BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3, 1) = 0 := by
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3, 1) := by
      unfold BaseMask.StairEvenCorner
      simp only
      omega
    unfold BaseMask.stairEvenValue
    rw [if_neg hc, min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 3 - 1)]
    norm_num
  have hSd0 : BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3, 0) = 0 := by
    have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3, 0) := by
      unfold BaseMask.StairEvenCorner
      simp only
      omega
    unfold BaseMask.stairEvenValue
    rw [if_neg hc, min_eq_right (by omega : (0 : ℤ) ≤ 2 * (k : ℤ) + 3 - 1)]
    norm_num
  have e3 : ((2 : ℤ), 2 * (k : ℤ) + 3 + 1) - ((1 : ℤ), (-1 : ℤ)) =
      (1, 2 * (k : ℤ) + 3 + 1) + ((0 : ℤ), (1 : ℤ)) := by
    ext <;> simp
  unfold threesP
  rw [e3, hF2]
  dsimp only
  linarith [hstep, hF1, hS21, hS11, hSd1, hSd0]

/-- The price on every raw point lies in `[0, 1]`: the case split of the raw tile into `N` and the exceptional points. -/
theorem threesP_raw_range (k : ℕ) (y : Site)
    (hy : y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    0 ≤ threesP k y ∧ threesP k y ≤ 1 := by
  obtain ⟨y1, y2⟩ := y
  have hy' : RawMem (2 * (k : ℤ) + 3) y1 y2 := (raw_mem_site (2 * (k : ℤ) + 3) (y1, y2)).mp hy
  by_cases hv : RawMem (2 * (k : ℤ) + 3) (y1 - 1) (y2 + 1)
  · rw [threesP_of_N k y1 y2 hy' hv]
    split_ifs <;> norm_num
  · have hcases : (y1 = 0 ∧ y2 = 0) ∨ (y1 = 2 ∧ y2 = 2 * (k : ℤ) + 3 + 1) ∨
        (y2 = 2 * (k : ℤ) + 3 + 1 ∧ 2 - (2 * (k : ℤ) + 3) ≤ y1 ∧ y1 ≤ 1) ∨
        (y1 = 2 - (2 * (k : ℤ) + 3) ∧ y2 = 2 * (k : ℤ) + 3 - 1) ∨
        (y1 = 2 - (2 * (k : ℤ) + 3) ∧ y2 = 2 * (k : ℤ) + 3) := by
      unfold RawMem at hy' hv
      omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, h3, h4⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [threesP_E3a]
      norm_num
    · rw [threesP_E3b]
      norm_num
    · rw [threesP_E1 k y1 h3 h4]
      split_ifs <;> norm_num
    · rw [threesP_E2a]
      norm_num
    · rw [threesP_E2b, threesP_E3b]
      norm_num

/-- The closed polygon of the pure frame lies in the raw tile. -/
theorem closedPolygon_threes_raw (k : ℕ) (z : Site)
    (hz : z ∈ (frameAt (List.replicate k Digit.three)).closedPolygon) :
    RawMem (2 * (k : ℤ) + 3) z.1 z.2 := by
  have hc := frameAt_threes_child k
  unfold ChildFrame.closedPolygon at hz
  simp only [Set.mem_setOf_eq, ChildFrame.tGrade, ChildFrame.sGrade, hc, Fraction.periodDenominator] at hz
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  by_cases he : EvenSite z
  · rw [if_pos he] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    exact polygon_even_raw (2 * (k : ℤ) + 3) z.1 z.2 hd3 hodd he (by linarith) (by linarith)
      (by linarith) (by linarith)
  · rw [if_neg he] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have hpar : (z.1 + z.2) % 2 = 1 := by
      unfold EvenSite at he
      omega
    exact polygon_odd_raw (2 * (k : ℤ) + 3) z.1 z.2 hd3 hodd hpar (by linarith) (by linarith)
      (by linarith) (by linarith)

theorem frame_price_threes (k : ℕ) (z : Site) :
    (frameAt (List.replicate k Digit.three)).price (standardField (List.replicate k Digit.three)) z =
      threesP k z := by
  rw [standardField_threes, price_threes]
  rfl

theorem cutPrice_threes (k : ℕ) : (frameAt (List.replicate k Digit.three)).cutPrice = 1 := by
  unfold ChildFrame.cutPrice
  rw [frameAt_threes_eps]
  simp [frameAt, parentsAt_replicate_three, Fraction.periodDenominator]

/-- **The price range at `3^k`**: `cutPrice − 1 ≤ P ≤ cutPrice` on the closed polygon (`priceRange` of `StrongResidual`). -/
theorem priceRange_threes (k : ℕ) : ∀ z ∈ (frameAt (List.replicate k Digit.three)).closedPolygon,
    (frameAt (List.replicate k Digit.three)).cutPrice - 1 ≤
        (frameAt (List.replicate k Digit.three)).price (standardField (List.replicate k Digit.three)) z ∧
      (frameAt (List.replicate k Digit.three)).price (standardField (List.replicate k Digit.three)) z ≤
        (frameAt (List.replicate k Digit.three)).cutPrice := by
  intro z hz
  rw [cutPrice_threes, frame_price_threes]
  obtain ⟨h0, h1⟩ := threesP_raw_range k z ((raw_mem_site _ z).mpr (closedPolygon_threes_raw k z hz))
  constructor <;> linarith

end FLatticePaper.Induction
