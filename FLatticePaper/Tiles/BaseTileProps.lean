import FLatticePaper.Tiles.TileTranslation
import FLatticePaper.Tiles.SurgicalAltOdometers
import FLatticePaper.Construction.BaseCaseRecurrence
import FLatticePaper.Construction.NearOneBaseCases

/-! # The base cases of the tile step (task (A) of the joint induction)

For the paper base odometers (`SurgicalWeak.PaperBaseCond`, `SurgicalAlt.PaperAltBaseCond`), the tile properties
`JointFamily.TileProps` hold at the base words. For each family of base odometers this file proves the normalisation
`FirstTileNormal`, the translations (a) through `TileTranslation.tileTranslation_of_corners` (the lattice compatibilities
of `WeakProps` are hypotheses), and the 180-degree symmetries (b).

This part covers the even standard stair `stairF d` (`d = 2k+3`: the even child of `[]` and of `3^k`), read by
`paperStairValue d`. -/

namespace FLatticePaper.Tiles.BaseTileProps

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.TileTranslation
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.SurgicalAlt

/-! ### Helpers -/

/-- `2 * (y (y+1) / 2) = y (y+1)`: the triangular values `x_2 (x_2 + 1) / 2` of the base heights are exact. -/
theorem two_mul_T2 (y : ℤ) : 2 * (y * (y + 1) / 2) = y * (y + 1) := by
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self y
  rw [hm]
  omega

/-- Membership in the base stair `stairF d`, with the coordinates written out. -/
theorem mem_stairF_ab (d : ℤ) (hd : 3 ≤ d) (a b : ℤ) : (a, b) ∈ stairF d ↔
    (2 - d ≤ a ∧ a ≤ d ∧ 0 ≤ b ∧ b ≤ d + 1 ∧ 1 ≤ a + b ∧ a + b ≤ d + 2) ∨ (a = 0 ∧ b = 0) ∨ (a = 2 ∧ b = d + 1) := by
  simp only [stairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, h⟩ <;> omega

/-- The normalised odometer `E - 0 - 0` is `E` itself. -/
theorem normed_zero (o : PartialOdometer) (p : Site) : normed o 0 0 p = o.val p := by
  simp [normed, dotS]

/-- The normalisation: with `α = 0` and `β = 0`, the four values on `T_{1/1}` are `0, -1, 0, 0`. -/
theorem firstNormal_of (o : PartialOdometer)
    (h00 : (0, 0) ∈ o.dom ∧ o.val (0, 0) = 0) (h01 : (0, 1) ∈ o.dom ∧ o.val (0, 1) = -1)
    (h10 : (1, 0) ∈ o.dom ∧ o.val (1, 0) = 0) (h11 : (1, 1) ∈ o.dom ∧ o.val (1, 1) = 0) :
    FirstTileNormal o 0 0 := by
  intro x hx
  simp only [tileShape, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨h00.1, by simp [normed, dotS, zTileOdo, oneOdometer, h00.2]⟩
  · exact ⟨h01.1, by simp [normed, dotS, zTileOdo, oneOdometer, h01.2]⟩
  · exact ⟨h10.1, by simp [normed, dotS, zTileOdo, oneOdometer, h10.2]⟩
  · exact ⟨h11.1, by simp [normed, dotS, zTileOdo, oneOdometer, h11.2]⟩

/-! ### The even stair `stairF d` (`d = 2k+3`) -/

theorem stairV_00 (d : ℤ) : paperStairValue d (0, 0) = 0 := by
  unfold paperStairValue
  norm_num

theorem stairV_10 (d : ℤ) : paperStairValue d (1, 0) = 0 := by
  unfold paperStairValue
  norm_num

theorem stairV_01 (d : ℤ) : paperStairValue d (0, 1) = -1 := by
  unfold paperStairValue
  norm_num

theorem stairV_11 (d : ℤ) : paperStairValue d (1, 1) = 0 := by
  unfold paperStairValue
  norm_num

/-- The values of the stair at the corner points of `stairE_corners`. -/
theorem stairV_d0 (d : ℤ) (hd : 3 ≤ d) : paperStairValue d (d, 0) = 0 := by
  unfold paperStairValue
  dsimp only
  split_ifs with h1
  · exfalso
    simp only [Prod.mk.injEq] at h1
    omega
  · rw [min_eq_right (by omega : (0 : ℤ) ≤ d - 1)]
    norm_num

theorem stairV_d1 (d : ℤ) (hd : 3 ≤ d) : paperStairValue d (d, 1) = 0 := by
  unfold paperStairValue
  dsimp only
  split_ifs with h1
  · exfalso
    simp only [Prod.mk.injEq] at h1
    omega
  · rw [min_eq_right (by omega : (0 : ℤ) ≤ d - 1)]
    ring

theorem stairV_2d (d : ℤ) (hd : 3 ≤ d) :
    paperStairValue d (2 - d, 1 + d) = -((1 + d) * (1 + d + 1) / 2) + 2 := by
  unfold paperStairValue
  dsimp only
  split_ifs with h1
  · exfalso
    simp only [Prod.mk.injEq] at h1
    omega
  · rw [min_eq_left (by omega : 2 - d - 1 ≤ 0)]
    ring

theorem stairV_2d' (d : ℤ) (hd : 3 ≤ d) :
    paperStairValue d (2 - d, d) = -(d * (d + 1) / 2) + 1 := by
  unfold paperStairValue
  dsimp only
  split_ifs with h1
  · exfalso
    simp only [Prod.mk.injEq] at h1
    omega
  · rw [min_eq_left (by omega : 2 - d - 1 ≤ 0)]
    ring

theorem stairV_2d1 (d : ℤ) (hd : 3 ≤ d) :
    paperStairValue d (2, d + 1) = -((d + 1) * (d + 1 + 1) / 2) + (d + 2) := by
  unfold paperStairValue
  dsimp only
  split_ifs with h1
  · rw [min_eq_right (by norm_num : (0 : ℤ) ≤ 2 - 1)]
    ring
  · exact absurd (Or.inr rfl) h1

theorem stairV_1d1 (d : ℤ) (hd : 3 ≤ d) :
    paperStairValue d (1, d + 1) = -((d + 1) * (d + 1 + 1) / 2) + (d + 1) := by
  unfold paperStairValue
  dsimp only
  split_ifs with h1
  · exfalso
    simp only [Prod.mk.injEq] at h1
    omega
  · rw [min_eq_right (by norm_num : (0 : ℤ) ≤ 1 - 1)]
    ring

/-- The normalisation of the even stair. -/
theorem stairE_firstNormal (d : ℤ) (hd : 3 ≤ d) (E : PartialOdometer) (hdom : E.dom = stairF d)
    (hval : ∀ x ∈ E.dom, E.val x = paperStairValue d x) : FirstTileNormal E 0 0 := by
  have at_ : ∀ a b : ℤ, (a, b) ∈ stairF d → (a, b) ∈ E.dom ∧ E.val (a, b) = paperStairValue d (a, b) :=
    fun a b h => ⟨by rw [hdom]; exact h, hval _ (by rw [hdom]; exact h)⟩
  apply firstNormal_of E
  · obtain ⟨m, v⟩ := at_ 0 0 ((mem_stairF_ab d hd 0 0).2 (by omega))
    exact ⟨m, by rw [v, stairV_00]⟩
  · obtain ⟨m, v⟩ := at_ 0 1 ((mem_stairF_ab d hd 0 1).2 (by omega))
    exact ⟨m, by rw [v, stairV_01]⟩
  · obtain ⟨m, v⟩ := at_ 1 0 ((mem_stairF_ab d hd 1 0).2 (by omega))
    exact ⟨m, by rw [v, stairV_10]⟩
  · obtain ⟨m, v⟩ := at_ 1 1 ((mem_stairF_ab d hd 1 1).2 (by omega))
    exact ⟨m, by rw [v, stairV_11]⟩

/-- The 180-degree symmetry of the even stair (b) of `lemma:tile-odometer-existence`: the centre is `(2, d+1)`. -/
theorem stairE_halfturn (d : ℤ) (hd : 3 ≤ d) (E : PartialOdometer) (hdom : E.dom = stairF d)
    (hval : ∀ x ∈ E.dom, E.val x = paperStairValue d x) :
    TileHalfTurn E (d, 1) (1 - d, 1 + d) (1, -d) := by
  refine ⟨0, 0, stairE_firstNormal d hd E hdom hval, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxS : (a, b) ∈ stairF d := by rw [← hdom]; exact hx
  have hD : ((d, 1) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ))) = ((2 : ℤ), d + 1) := by
    ext <;> simp <;> ring
  have hy : ((2 : ℤ), d + 1) - (a, b) = (2 - a, d + 1 - b) := by
    rw [Prod.mk_sub_mk]
  rw [hD, hy]
  have hyS : (2 - a, d + 1 - b) ∈ stairF d :=
    (mem_stairF_ab d hd _ _).2 (by have h := (mem_stairF_ab d hd a b).1 hxS; omega)
  have hyE : (2 - a, d + 1 - b) ∈ E.dom := by rw [hdom]; exact hyS
  refine ⟨hyE, ?_⟩
  simp only [normed_zero, dotS]
  rw [hval _ hyE, hval _ hx]
  simp only [paperStairValue]
  have hind : (if (2 - a, d + 1 - b) = ((0 : ℤ), (0 : ℤ)) ∨ (2 - a, d + 1 - b) = ((2 : ℤ), d + 1) then (1 : ℤ) else 0) =
      (if (a, b) = ((0 : ℤ), (0 : ℤ)) ∨ (a, b) = ((2 : ℤ), d + 1) then (1 : ℤ) else 0) := by
    simp only [Prod.mk.injEq]
    split_ifs <;> omega
  have hmin : min (2 - a - 1) 0 - min (a - 1) 0 = 1 - a := by
    omega
  linarith [two_mul_T2 (d + 1 - b), two_mul_T2 b, hmin, hind]

/-- The corner identities (`StdCornerValues`) of the even stair, with `c(T) = 0`, `X = (d, 1)`, `Y = (1-d, 1+d)`,
`e = (1, -d)`. The centre `D = (2, d+1)`. The value `-h0 Y = chooseTwo (1-d) - (d^2 + d)`. -/
theorem stairE_corners (d : ℤ) (hd : 3 ≤ d) (E : PartialOdometer) (hdom : E.dom = stairF d)
    (hval : ∀ x ∈ E.dom, E.val x = paperStairValue d x) :
    StdCornerValues E 0 0 (d, 1) (1 - d, 1 + d) (1, -d) := by
  have at_ : ∀ a b : ℤ, (a, b) ∈ stairF d → (a, b) ∈ E.dom ∧ E.val (a, b) = paperStairValue d (a, b) :=
    fun a b h => ⟨by rw [hdom]; exact h, hval _ (by rw [hdom]; exact h)⟩
  have hsq : (1 - d - (1 + d) - 1) ^ 2 / 4 = d ^ 2 + d := by
    have h : (1 - d - (1 + d) - 1) ^ 2 = 4 * (d ^ 2 + d) + 1 := by ring
    rw [h]
    generalize d ^ 2 + d = q
    omega
  have hG : -h0 (1 - d, 1 + d) = chooseTwo (1 - d) - (d ^ 2 + d) := by
    unfold h0 centeredQuarterTurnCorrection
    dsimp only
    rw [hsq]
    ring
  have hC := two_mul_chooseTwo (1 - d)
  have hT1 := two_mul_T2 (d + 1)
  have hT0 := two_mul_T2 d
  have k0 : (0 : Site) ∈ E.dom ∧ E.val 0 = 0 := by
    obtain ⟨m, v⟩ := at_ 0 0 ((mem_stairF_ab d hd 0 0).2 (by omega))
    exact ⟨m, by show E.val (0, 0) = 0; rw [v, stairV_00]⟩
  have k1 : ((1 : ℤ), (0 : ℤ)) ∈ E.dom ∧ E.val (1, 0) = 0 := by
    obtain ⟨m, v⟩ := at_ 1 0 ((mem_stairF_ab d hd 1 0).2 (by omega))
    exact ⟨m, by rw [v, stairV_10]⟩
  have k2 : (d, 1) - ((0 : ℤ), (1 : ℤ)) ∈ E.dom ∧ E.val ((d, 1) - (0, 1)) = 0 := by
    have e : ((d, 1) : Site) - (0, 1) = (d, 0) := by ext <;> simp
    rw [e]
    obtain ⟨m, v⟩ := at_ d 0 ((mem_stairF_ab d hd d 0).2 (by omega))
    exact ⟨m, by rw [v, stairV_d0 d hd]⟩
  have k3 : ((d, 1) : Site) ∈ E.dom ∧ E.val (d, 1) = 0 := by
    obtain ⟨m, v⟩ := at_ d 1 ((mem_stairF_ab d hd d 1).2 (by omega))
    exact ⟨m, by rw [v, stairV_d1 d hd]⟩
  have k4 : (1 - d, 1 + d) + ((1 : ℤ), (0 : ℤ)) ∈ E.dom ∧
      E.val ((1 - d, 1 + d) + (1, 0)) = -((1 + d) * (1 + d + 1) / 2) + 2 := by
    have e : ((1 - d, 1 + d) : Site) + (1, 0) = (2 - d, 1 + d) := by ext <;> simp <;> ring
    rw [e]
    obtain ⟨m, v⟩ := at_ (2 - d) (1 + d) ((mem_stairF_ab d hd _ _).2 (by omega))
    exact ⟨m, by rw [v, stairV_2d d hd]⟩
  have k5 : (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) ∈ E.dom ∧
      E.val ((1 - d, 1 + d) + (1, -1)) = -(d * (d + 1) / 2) + 1 := by
    have e : ((1 - d, 1 + d) : Site) + (1, -1) = (2 - d, d) := by ext <;> simp <;> ring
    rw [e]
    obtain ⟨m, v⟩ := at_ (2 - d) d ((mem_stairF_ab d hd _ _).2 (by omega))
    exact ⟨m, by rw [v, stairV_2d' d hd]⟩
  have k6 : (d, 1) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) ∈ E.dom ∧
      E.val ((d, 1) + (1 - d, 1 + d) + (1, -1)) = -((d + 1) * (d + 1 + 1) / 2) + (d + 2) := by
    have e : ((d, 1) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) : Site) = (2, d + 1) := by
      ext <;> simp <;> ring
    rw [e]
    obtain ⟨m, v⟩ := at_ 2 (d + 1) ((mem_stairF_ab d hd _ _).2 (by omega))
    exact ⟨m, by rw [v, stairV_2d1 d hd]⟩
  have k7 : (d, 1) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈ E.dom ∧
      E.val ((d, 1) + (1 - d, 1 + d) + (1, -1) - (1, 0)) = -((d + 1) * (d + 1 + 1) / 2) + (d + 1) := by
    have e : ((d, 1) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) : Site) = (1, d + 1) := by
      ext <;> simp <;> ring
    rw [e]
    obtain ⟨m, v⟩ := at_ 1 (d + 1) ((mem_stairF_ab d hd _ _).2 (by omega))
    exact ⟨m, by rw [v, stairV_1d1 d hd]⟩
  unfold StdCornerValues
  dsimp only
  refine ⟨⟨k0.1, by rw [normed_zero]; exact k0.2⟩, ⟨k1.1, by rw [normed_zero]; exact k1.2⟩,
    ⟨k2.1, by rw [normed_zero]; exact k2.2⟩, ⟨k3.1, by rw [normed_zero]; exact k3.2⟩,
    ⟨k4.1, by rw [normed_zero, k4.2, hG]; linarith [two_mul_T2 (1 + d)]⟩,
    ⟨k5.1, by rw [normed_zero, k5.2, hG]; linarith⟩,
    ⟨k6.1, by rw [normed_zero, k6.2, hG]; linarith⟩, ⟨k7.1, by rw [normed_zero, k7.2, hG]; linarith⟩⟩

/-- (a) of `lemma:tile-odometer-existence` for the even stair: the translations by `X = (d,1)` and `Y = (1-d, 1+d)`,
given the lattice compatibilities of `WeakProps`. -/
theorem stairE_translation (d : ℤ) (hd : 3 ≤ d) (E : PartialOdometer) (hdom : E.dom = stairF d)
    (hval : ∀ x ∈ E.dom, E.val x = paperStairValue d x)
    (hcX : LatticeSelfCompatible E (d, 1) 0) (hcY : LatticeSelfCompatible E (1 - d, 1 + d) (1, -d)) :
    TileTranslation E (d, 1) (1 - d, 1 + d) (1, -d) :=
  tileTranslation_of_corners E (d, 1) (1 - d, 1 + d) (1, -d) 0 0
    (stairE_firstNormal d hd E hdom hval) (stairE_corners d hd E hdom hval) hcX hcY

end FLatticePaper.Tiles.BaseTileProps
