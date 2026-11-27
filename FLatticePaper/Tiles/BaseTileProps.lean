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

theorem stairV_2d1 (d : ℤ) (_hd : 3 ≤ d) :
    paperStairValue d (2, d + 1) = -((d + 1) * (d + 1 + 1) / 2) + (d + 2) := by
  unfold paperStairValue
  dsimp only
  split_ifs with h1
  · rw [min_eq_right (by norm_num : (0 : ℤ) ≤ 2 - 1)]
    ring
  · exact absurd (Or.inr rfl) h1

theorem stairV_1d1 (d : ℤ) (_hd : 3 ≤ d) :
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
    ext <;> simp; ring
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
    have e : ((1 - d, 1 + d) : Site) + (1, 0) = (2 - d, 1 + d) := by ext <;> simp; ring
    rw [e]
    obtain ⟨m, v⟩ := at_ (2 - d) (1 + d) ((mem_stairF_ab d hd _ _).2 (by omega))
    exact ⟨m, by rw [v, stairV_2d d hd]⟩
  have k5 : (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) ∈ E.dom ∧
      E.val ((1 - d, 1 + d) + (1, -1)) = -(d * (d + 1) / 2) + 1 := by
    have e : ((1 - d, 1 + d) : Site) + (1, -1) = (2 - d, d) := by ext <;> simp; ring
    rw [e]
    obtain ⟨m, v⟩ := at_ (2 - d) d ((mem_stairF_ab d hd _ _).2 (by omega))
    exact ⟨m, by rw [v, stairV_2d' d hd]⟩
  have k6 : (d, 1) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) ∈ E.dom ∧
      E.val ((d, 1) + (1 - d, 1 + d) + (1, -1)) = -((d + 1) * (d + 1 + 1) / 2) + (d + 2) := by
    have e : ((d, 1) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) : Site) = (2, d + 1) := by
      ext <;> simp; ring
    rw [e]
    obtain ⟨m, v⟩ := at_ 2 (d + 1) ((mem_stairF_ab d hd _ _).2 (by omega))
    exact ⟨m, by rw [v, stairV_2d1 d hd]⟩
  have k7 : (d, 1) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈ E.dom ∧
      E.val ((d, 1) + (1 - d, 1 + d) + (1, -1) - (1, 0)) = -((d + 1) * (d + 1 + 1) / 2) + (d + 1) := by
    have e : ((d, 1) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) : Site) = (1, d + 1) := by
      ext <;> simp; ring
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

/-! ### The odd near-one stair `nstairN (2k+3)` (words `[]` with `k = 0`, and `2^k`)

The domain is `nstairN d = shift (nstairF d) (0,-1)`, read at `x + (0,1)` by `paperNearStairValue d`. -/

theorem mem_nstairF_ab (d : ℤ) (hd : 3 ≤ d) (a b : ℤ) : (a, b) ∈ nstairF d ↔
    (0 ≤ a ∧ a ≤ d + 1 ∧ 1 ≤ b ∧ b ≤ 2 * d - 1 ∧ -1 ≤ b - a ∧ b - a ≤ d) ∨ (a = 0 ∧ b = d + 1) ∨
      (a = d + 1 ∧ b = d - 1) := by
  simp only [nstairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, h⟩ <;> omega

theorem mem_nstairN_ab (d : ℤ) (a b : ℤ) : (a, b) ∈ nstairN d ↔ (a, b + 1) ∈ nstairF d := by
  unfold nstairN
  rw [mem_shift, show ((a, b) : Site) - (0, -1) = (a, b + 1) by ext <;> simp]

theorem pnsV (d a b : ℤ) : paperNearStairValue d (a, b) = -((b - a) ^ 2 / 4) + min (d - b) 0 +
    (if (a, b) = (0, d + 1) ∨ (a, b) = (d + 1, d - 1) then 1 else 0) := rfl

theorem sq4_even (s m : ℤ) (h : s = 2 * m) : s ^ 2 / 4 = m ^ 2 := by
  subst h
  rw [show (2 * m) ^ 2 = 4 * m ^ 2 by ring]
  generalize m ^ 2 = X
  omega

theorem sq4_odd (s m : ℤ) (h : s = 2 * m + 1) : s ^ 2 / 4 = m ^ 2 + m := by
  subst h
  rw [show (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 by ring]
  generalize m ^ 2 + m = X
  omega

/-- The floor identity of the near-one stair: `-(u^2/4) + ((2c-u)^2/4) = c^2 - uc` for every `u`. -/
theorem sq4_sym (c u : ℤ) : -(u ^ 2 / 4) + ((2 * c - u) ^ 2 / 4) = c ^ 2 - u * c := by
  obtain ⟨m, hm | hm⟩ : ∃ m, u = 2 * m ∨ u = 2 * m + 1 := ⟨u / 2, by omega⟩
  · subst hm
    rw [sq4_even (2 * m) m rfl, sq4_even (2 * c - 2 * m) (c - m) (by ring)]
    ring
  · subst hm
    rw [sq4_odd (2 * m + 1) m rfl, sq4_odd (2 * c - (2 * m + 1)) (c - m - 1) (by ring)]
    ring

/-- The odd near-one stair at `x`: the domain and the value, read at `x + (0,1)`. -/
theorem nO_at (k : ℤ) (O : PartialOdometer) (hdom : O.dom = nstairN (2 * k + 3))
    (hval : ∀ x ∈ O.dom, O.val x = paperNearStairValue (2 * k + 3) (x + (0, 1)))
    (a b : ℤ) (h : (a, b + 1) ∈ nstairF (2 * k + 3)) :
    (a, b) ∈ O.dom ∧ O.val (a, b) = paperNearStairValue (2 * k + 3) (a, b + 1) := by
  have hm : (a, b) ∈ O.dom := by rw [hdom, mem_nstairN_ab]; exact h
  refine ⟨hm, ?_⟩
  rw [hval _ hm, show ((a, b) : Site) + (0, 1) = (a, b + 1) by ext <;> simp]

theorem nstairO_firstNormal (k : ℤ) (hk : 0 ≤ k) (O : PartialOdometer) (hdom : O.dom = nstairN (2 * k + 3))
    (hval : ∀ x ∈ O.dom, O.val x = paperNearStairValue (2 * k + 3) (x + (0, 1))) :
    FirstTileNormal O 0 0 := by
  apply firstNormal_of O
  · obtain ⟨m, v⟩ := nO_at k O hdom hval 0 0 ((mem_nstairF_ab _ (by omega) 0 (0 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsV]
    split_ifs with h1 <;> simp only [Prod.mk.injEq] at h1 <;> norm_num <;> omega
  · obtain ⟨m, v⟩ := nO_at k O hdom hval 0 1 ((mem_nstairF_ab _ (by omega) 0 (1 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsV]
    split_ifs with h1 <;> simp only [Prod.mk.injEq] at h1 <;> norm_num <;> omega
  · obtain ⟨m, v⟩ := nO_at k O hdom hval 1 0 ((mem_nstairF_ab _ (by omega) 1 (0 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsV]
    split_ifs with h1 <;> simp only [Prod.mk.injEq] at h1 <;> norm_num <;> omega
  · obtain ⟨m, v⟩ := nO_at k O hdom hval 1 1 ((mem_nstairF_ab _ (by omega) 1 (1 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsV]
    split_ifs with h1 <;> simp only [Prod.mk.injEq] at h1 <;> norm_num <;> omega

/-- The 180-degree symmetry of the odd near-one stair: the centre is `D = (2k+4, 4k+4)`. -/
theorem nstairO_halfturn (k : ℤ) (hk : 0 ≤ k) (O : PartialOdometer) (hdom : O.dom = nstairN (2 * k + 3))
    (hval : ∀ x ∈ O.dom, O.val x = paperNearStairValue (2 * k + 3) (x + (0, 1))) :
    TileHalfTurn O (2 * k + 4, 2 * k + 2) (-1, 2 * k + 3) (k + 1, -(k + 2)) := by
  refine ⟨0, 0, nstairO_firstNormal k hk O hdom hval, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxS : (a, b + 1) ∈ nstairF (2 * k + 3) := by
    rw [← mem_nstairN_ab, ← hdom]
    exact hx
  have hD : ((2 * k + 4, 2 * k + 2) + (-1, 2 * k + 3) + ((1 : ℤ), (-1 : ℤ))) = ((2 * k + 4 : ℤ), 4 * k + 4) := by
    ext <;> simp; ring
  have hy : ((2 * k + 4 : ℤ), 4 * k + 4) - (a, b) = (2 * k + 4 - a, 4 * k + 4 - b) := by
    rw [Prod.mk_sub_mk]
  rw [hD, hy]
  have hyS : (2 * k + 4 - a, 4 * k + 4 - b + 1) ∈ nstairF (2 * k + 3) :=
    (mem_nstairF_ab _ (by omega) _ _).2 (by
      have h := (mem_nstairF_ab _ (by omega) a (b + 1)).1 hxS
      omega)
  have hyO : (2 * k + 4 - a, 4 * k + 4 - b) ∈ O.dom := by
    rw [hdom, mem_nstairN_ab]
    exact hyS
  refine ⟨hyO, ?_⟩
  simp only [normed_zero, dotS]
  rw [hval _ hyO, hval _ hx, show ((2 * k + 4 - a, 4 * k + 4 - b) : Site) + (0, 1) = (2 * k + 4 - a, 4 * k + 4 - b + 1) by ext <;> simp, show ((a, b) : Site) + (0, 1) = (a, b + 1) by ext <;> simp]
  rw [pnsV, pnsV]
  rw [show 4 * k + 4 - b + 1 - (2 * k + 4 - a) = 2 * (k + 1) - (b + 1 - a) by ring]
  have hS := sq4_sym (k + 1) (b + 1 - a)
  have hm : min (2 * k + 3 - (4 * k + 4 - b + 1)) 0 - min (2 * k + 3 - (b + 1)) 0 = b - 2 * k - 2 := by
    omega
  have hind : (if (2 * k + 4 - a, 4 * k + 4 - b + 1) = (0, 2 * k + 3 + 1) ∨
        (2 * k + 4 - a, 4 * k + 4 - b + 1) = (2 * k + 3 + 1, 2 * k + 3 - 1) then (1 : ℤ) else 0) =
      (if (a, b + 1) = (0, 2 * k + 3 + 1) ∨ (a, b + 1) = (2 * k + 3 + 1, 2 * k + 3 - 1) then (1 : ℤ) else 0) := by
    simp only [Prod.mk.injEq]
    split_ifs <;> omega
  linarith [hS, hm, hind]

/-- The value `-h0 (-1, 2k+3) = -(k^2 + 5k + 5)` at the odd near-one stair's `Y`. -/
theorem nstairO_G (k : ℤ) : -h0 (-1, 2 * k + 3) = -(k ^ 2 + 5 * k + 5) := by
  have hc1 : chooseTwo (-1) = 1 := by unfold chooseTwo; norm_num
  have hsq : (-1 - (2 * k + 3) - 1) ^ 2 / 4 = k ^ 2 + 5 * k + 6 := by
    rw [show (-1 - (2 * k + 3) - 1) ^ 2 = 4 * (k ^ 2 + 5 * k + 6) + 1 by ring]
    generalize k ^ 2 + 5 * k + 6 = X
    omega
  unfold h0 centeredQuarterTurnCorrection
  dsimp only
  rw [hc1, hsq]
  ring

/-- The corner identities of the odd near-one stair (`StdCornerValues`), `X = (2k+4, 2k+2)`, `Y = (-1, 2k+3)`,
`e = (k+1, -(k+2))`, `D = (2k+4, 4k+4)`. -/
theorem nstairO_corners (k : ℤ) (hk : 0 ≤ k) (O : PartialOdometer) (hdom : O.dom = nstairN (2 * k + 3))
    (hval : ∀ x ∈ O.dom, O.val x = paperNearStairValue (2 * k + 3) (x + (0, 1))) :
    StdCornerValues O 0 0 (2 * k + 4, 2 * k + 2) (-1, 2 * k + 3) (k + 1, -(k + 2)) := by
  have hd : (3 : ℤ) ≤ 2 * k + 3 := by omega
  have hG := nstairO_G k
  have k0 : (0 : Site) ∈ O.dom ∧ O.val 0 = 0 := by
    obtain ⟨m, v⟩ := nO_at k O hdom hval 0 0 ((mem_nstairF_ab _ hd 0 (0 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    show O.val (0, 0) = 0
    rw [v, pnsV]
    split_ifs with h1 <;> simp only [Prod.mk.injEq] at h1 <;> norm_num <;> omega
  have k1 : ((1 : ℤ), (0 : ℤ)) ∈ O.dom ∧ O.val (1, 0) = 0 := by
    obtain ⟨m, v⟩ := nO_at k O hdom hval 1 0 ((mem_nstairF_ab _ hd 1 (0 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsV]
    split_ifs with h1 <;> simp only [Prod.mk.injEq] at h1 <;> norm_num <;> omega
  have k2 : (2 * k + 4, 2 * k + 2) - ((0 : ℤ), (1 : ℤ)) ∈ O.dom ∧
      O.val ((2 * k + 4, 2 * k + 2) - (0, 1)) = 0 := by
    have e : ((2 * k + 4, 2 * k + 2) : Site) - (0, 1) = (2 * k + 4, 2 * k + 1) := by ext <;> simp; ring
    rw [e]
    obtain ⟨m, v⟩ := nO_at k O hdom hval (2 * k + 4) (2 * k + 1)
      ((mem_nstairF_ab _ hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsV]
    rw [show 2 * k + 1 + 1 - (2 * k + 4) = -2 by ring]
    split_ifs with h1 <;> simp only [Prod.mk.injEq] at h1 <;> norm_num <;> omega
  have k3 : (2 * k + 4, 2 * k + 2) ∈ O.dom ∧ O.val (2 * k + 4, 2 * k + 2) = 0 := by
    obtain ⟨m, v⟩ := nO_at k O hdom hval (2 * k + 4) (2 * k + 2)
      ((mem_nstairF_ab _ hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsV]
    rw [show 2 * k + 2 + 1 - (2 * k + 4) = -1 by ring]
    split_ifs with h1 <;> simp only [Prod.mk.injEq] at h1 <;> norm_num <;> omega
  have k4 : (-1, 2 * k + 3) + ((1 : ℤ), (0 : ℤ)) ∈ O.dom ∧
      O.val ((-1, 2 * k + 3) + (1, 0)) = -((k + 2) ^ 2) := by
    have e : ((-1, 2 * k + 3) : Site) + (1, 0) = (0, 2 * k + 3) := by ext <;> simp
    rw [e]
    obtain ⟨m, v⟩ := nO_at k O hdom hval 0 (2 * k + 3) ((mem_nstairF_ab _ hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    have hc : ((0 : ℤ), 2 * k + 3 + 1) = (0, 2 * k + 3 + 1) ∨ ((0 : ℤ), 2 * k + 3 + 1) = (2 * k + 3 + 1, 2 * k + 3 - 1) :=
      Or.inl rfl
    have hm' : min (2 * k + 3 - (2 * k + 3 + 1)) 0 = -1 := by omega
    rw [v, pnsV, sq4_even (2 * k + 3 + 1 - 0) (k + 2) (by ring), if_pos hc, hm']
    ring
  have k5 : (-1, 2 * k + 3) + ((1 : ℤ), (-1 : ℤ)) ∈ O.dom ∧
      O.val ((-1, 2 * k + 3) + (1, -1)) = -((k + 1) ^ 2 + (k + 1)) := by
    have e : ((-1, 2 * k + 3) : Site) + (1, -1) = (0, 2 * k + 2) := by ext <;> simp; ring
    rw [e]
    obtain ⟨m, v⟩ := nO_at k O hdom hval 0 (2 * k + 2) ((mem_nstairF_ab _ hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsV, sq4_odd (2 * k + 2 + 1 - 0) (k + 1) (by ring)]
    split_ifs with h1 <;> simp only [Prod.mk.injEq] at h1 <;> omega
  have k6 : (2 * k + 4, 2 * k + 2) + (-1, 2 * k + 3) + ((1 : ℤ), (-1 : ℤ)) ∈ O.dom ∧
      O.val ((2 * k + 4, 2 * k + 2) + (-1, 2 * k + 3) + (1, -1)) = -(k ^ 2 + 3 * k + 2) := by
    have e : ((2 * k + 4, 2 * k + 2) + (-1, 2 * k + 3) + ((1 : ℤ), (-1 : ℤ)) : Site) = (2 * k + 4, 4 * k + 4) := by
      ext <;> simp; ring
    rw [e]
    obtain ⟨m, v⟩ := nO_at k O hdom hval (2 * k + 4) (4 * k + 4) ((mem_nstairF_ab _ hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsV, sq4_odd (4 * k + 4 + 1 - (2 * k + 4)) (k) (by ring)]
    split_ifs with h1 <;> simp only [Prod.mk.injEq] at h1 <;> omega
  have k7 : (2 * k + 4, 2 * k + 2) + (-1, 2 * k + 3) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈ O.dom ∧
      O.val ((2 * k + 4, 2 * k + 2) + (-1, 2 * k + 3) + (1, -1) - (1, 0)) = -((k + 1) ^ 2) - (2 * k + 2) := by
    have e : ((2 * k + 4, 2 * k + 2) + (-1, 2 * k + 3) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) : Site) =
        (2 * k + 3, 4 * k + 4) := by
      ext <;> simp <;> ring
    rw [e]
    obtain ⟨m, v⟩ := nO_at k O hdom hval (2 * k + 3) (4 * k + 4) ((mem_nstairF_ab _ hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsV, sq4_even (4 * k + 4 + 1 - (2 * k + 3)) (k + 1) (by ring)]
    split_ifs with h1 <;> simp only [Prod.mk.injEq] at h1 <;> omega
  unfold StdCornerValues
  dsimp only
  refine ⟨⟨k0.1, by rw [normed_zero]; exact k0.2⟩, ⟨k1.1, by rw [normed_zero]; exact k1.2⟩,
    ⟨k2.1, by rw [normed_zero]; exact k2.2⟩, ⟨k3.1, by rw [normed_zero]; exact k3.2⟩,
    ⟨k4.1, by rw [normed_zero, k4.2, hG]; ring⟩,
    ⟨k5.1, by rw [normed_zero, k5.2, hG]; ring⟩,
    ⟨k6.1, by rw [normed_zero, k6.2, hG]; ring⟩,
    ⟨k7.1, by rw [normed_zero, k7.2, hG]; ring⟩⟩

/-- (a) of `lemma:tile-odometer-existence` for the odd near-one stair. -/
theorem nstairO_translation (k : ℤ) (hk : 0 ≤ k) (O : PartialOdometer) (hdom : O.dom = nstairN (2 * k + 3))
    (hval : ∀ x ∈ O.dom, O.val x = paperNearStairValue (2 * k + 3) (x + (0, 1)))
    (hcX : LatticeSelfCompatible O (2 * k + 4, 2 * k + 2) 0)
    (hcY : LatticeSelfCompatible O (-1, 2 * k + 3) (k + 1, -(k + 2))) :
    TileTranslation O (2 * k + 4, 2 * k + 2) (-1, 2 * k + 3) (k + 1, -(k + 2)) :=
  tileTranslation_of_corners O _ _ _ 0 0 (nstairO_firstNormal k hk O hdom hval)
    (nstairO_corners k hk O hdom hval) hcX hcY

/-! ### The odd doubled stair `ladderF d` (words `3^k`, `d = 2k+2`)

The domain is `ladderF d`, read unshifted by `paperLadderValue d`. The lemmas are stated for every `d ≥ 4`. -/

theorem mem_ladderF_ab (d : ℤ) (hd : 4 ≤ d) (a b : ℤ) : (a, b) ∈ ladderF d ↔
    (2 - d ≤ a ∧ a ≤ 2 * d ∧ 0 ≤ b ∧ b ≤ d + 2) ∧
      ((a = 0 ∧ b = 0) ∨ (a = d + 2 ∧ b = d + 2) ∨ (a + b = d + 2 ∧ 1 < b ∧ b < d + 1) ∨
        (2 - d ≤ a ∧ a ≤ 2 * d ∧ 0 ≤ b ∧ b ≤ d + 2 ∧ 1 ≤ a + b ∧ a + b ≤ 2 * d + 3)) ∧
      ¬((d ≤ a ∧ b = 0) ∨ (a ≤ 2 ∧ b = d + 2)) := by
  simp only [ladderF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- The value of the doubled stair, with the indicator of `A ∪ B` written as an `if`. -/
theorem plV (d a b : ℤ) : paperLadderValue d (a, b) = -(b * (b + 1) / 2) + (b + min (a - 1) 0) +
    min 0 (d + 1 - a) + max (a + b - d - 2) 0 +
    (if (a, b) = (0, 0) ∨ (a, b) = (d + 2, d + 2) ∨ (a + b = d + 2 ∧ 1 < b ∧ b < d + 1) then 1 else 0) := by
  have hI : (paperLadderA d ∪ paperLadderB d).indicator (fun _ => (1 : ℤ)) (a, b) =
      (if (a, b) = (0, 0) ∨ (a, b) = (d + 2, d + 2) ∨ (a + b = d + 2 ∧ 1 < b ∧ b < d + 1) then 1 else 0) := by
    unfold Set.indicator
    simp only [Set.mem_union, paperLadderA, paperLadderB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, or_assoc]
  unfold paperLadderValue
  rw [hI]

theorem negh0_Y (d : ℤ) : -h0 (1 - d, 1 + d) = chooseTwo (1 - d) - (d ^ 2 + d) := by
  have hsq : (1 - d - (1 + d) - 1) ^ 2 / 4 = d ^ 2 + d := by
    have h : (1 - d - (1 + d) - 1) ^ 2 = 4 * (d ^ 2 + d) + 1 := by ring
    rw [h]
    generalize d ^ 2 + d = q
    omega
  unfold h0 centeredQuarterTurnCorrection
  dsimp only
  rw [hsq]
  ring

theorem ladO_at (d : ℤ) (O : PartialOdometer) (hdom : O.dom = ladderF d)
    (hval : ∀ x ∈ O.dom, O.val x = paperLadderValue d x) (a b : ℤ) (h : (a, b) ∈ ladderF d) :
    (a, b) ∈ O.dom ∧ O.val (a, b) = paperLadderValue d (a, b) :=
  ⟨by rw [hdom]; exact h, hval _ (by rw [hdom]; exact h)⟩

theorem ladO_firstNormal (d : ℤ) (hd : 4 ≤ d) (O : PartialOdometer) (hdom : O.dom = ladderF d)
    (hval : ∀ x ∈ O.dom, O.val x = paperLadderValue d x) : FirstTileNormal O 0 0 := by
  apply firstNormal_of O
  · obtain ⟨m, v⟩ := ladO_at d O hdom hval 0 0 ((mem_ladderF_ab d hd 0 0).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, plV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := ladO_at d O hdom hval 0 1 ((mem_ladderF_ab d hd 0 1).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, plV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := ladO_at d O hdom hval 1 0 ((mem_ladderF_ab d hd 1 0).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, plV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := ladO_at d O hdom hval 1 1 ((mem_ladderF_ab d hd 1 1).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, plV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega

/-- The 180-degree symmetry of the odd doubled stair: the centre is `(d+2, d+2)`. -/
theorem ladO_halfturn (d : ℤ) (hd : 4 ≤ d) (O : PartialOdometer) (hdom : O.dom = ladderF d)
    (hval : ∀ x ∈ O.dom, O.val x = paperLadderValue d x) :
    TileHalfTurn O (2 * d, 2) (1 - d, 1 + d) (1, -d) := by
  refine ⟨0, 0, ladO_firstNormal d hd O hdom hval, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxS : (a, b) ∈ ladderF d := by rw [← hdom]; exact hx
  have hD : ((2 * d, 2) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ))) = ((d + 2 : ℤ), d + 2) := by
    ext <;> simp <;> ring
  have hy : ((d + 2 : ℤ), d + 2) - (a, b) = (d + 2 - a, d + 2 - b) := by
    rw [Prod.mk_sub_mk]
  rw [hD, hy]
  have hyS : (d + 2 - a, d + 2 - b) ∈ ladderF d :=
    (mem_ladderF_ab d hd _ _).2 (by have h := (mem_ladderF_ab d hd a b).1 hxS; omega)
  have hyO : (d + 2 - a, d + 2 - b) ∈ O.dom := by
    rw [hdom]
    exact hyS
  refine ⟨hyO, ?_⟩
  simp only [normed_zero, dotS]
  rw [hval _ hyO, hval _ hx, plV, plV]
  have hmm : min (d + 2 - a - 1) 0 - min (a - 1) 0 + (min 0 (d + 1 - (d + 2 - a)) - min 0 (d + 1 - a)) +
      (max (d + 2 - a + (d + 2 - b) - d - 2) 0 - max (a + b - d - 2) 0) = d + 2 - a - b := by
    omega
  have hind : (if (d + 2 - a, d + 2 - b) = (0, 0) ∨ (d + 2 - a, d + 2 - b) = (d + 2, d + 2) ∨
        (d + 2 - a + (d + 2 - b) = d + 2 ∧ 1 < d + 2 - b ∧ d + 2 - b < d + 1) then (1 : ℤ) else 0) =
      (if (a, b) = (0, 0) ∨ (a, b) = (d + 2, d + 2) ∨ (a + b = d + 2 ∧ 1 < b ∧ b < d + 1) then (1 : ℤ) else 0) := by
    simp only [Prod.mk.injEq]
    split_ifs <;> omega
  linarith [two_mul_T2 (d + 2 - b), two_mul_T2 b, hmm, hind]

/-- The corner identities of the odd doubled stair (`StdCornerValues`), with `X = (2d, 2)`, `Y = (1-d, 1+d)`,
`e = (1, -d)`, `D = (d+2, d+2)`. -/
theorem ladO_corners (d : ℤ) (hd : 4 ≤ d) (O : PartialOdometer) (hdom : O.dom = ladderF d)
    (hval : ∀ x ∈ O.dom, O.val x = paperLadderValue d x) :
    StdCornerValues O 0 0 (2 * d, 2) (1 - d, 1 + d) (1, -d) := by
  have k0 : (0 : Site) ∈ O.dom ∧ O.val 0 = 0 := by
    obtain ⟨m, v⟩ := ladO_at d O hdom hval 0 0 ((mem_ladderF_ab d hd 0 0).2 (by omega))
    refine ⟨m, ?_⟩
    show O.val (0, 0) = 0
    rw [v, plV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k1 : ((1 : ℤ), (0 : ℤ)) ∈ O.dom ∧ O.val (1, 0) = 0 := by
    obtain ⟨m, v⟩ := ladO_at d O hdom hval 1 0 ((mem_ladderF_ab d hd 1 0).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, plV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k2 : (2 * d, 2) - ((0 : ℤ), (1 : ℤ)) ∈ O.dom ∧ O.val ((2 * d, 2) - (0, 1)) = 0 := by
    have e : ((2 * d, 2) : Site) - (0, 1) = (2 * d, 1) := by ext <;> simp
    rw [e]
    obtain ⟨m, v⟩ := ladO_at d O hdom hval (2 * d) 1 ((mem_ladderF_ab d hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, plV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k3 : (2 * d, 2) ∈ O.dom ∧ O.val (2 * d, 2) = 0 := by
    obtain ⟨m, v⟩ := ladO_at d O hdom hval (2 * d) 2 ((mem_ladderF_ab d hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, plV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k4 : (1 - d, 1 + d) + ((1 : ℤ), (0 : ℤ)) ∈ O.dom ∧
      O.val ((1 - d, 1 + d) + (1, 0)) = -((1 + d) * (1 + d + 1) / 2) + 2 := by
    have e : ((1 - d, 1 + d) : Site) + (1, 0) = (2 - d, 1 + d) := by ext <;> simp; ring
    rw [e]
    obtain ⟨m, v⟩ := ladO_at d O hdom hval (2 - d) (1 + d) ((mem_ladderF_ab d hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, plV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k5 : (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) ∈ O.dom ∧
      O.val ((1 - d, 1 + d) + (1, -1)) = -(d * (d + 1) / 2) + 1 := by
    have e : ((1 - d, 1 + d) : Site) + (1, -1) = (2 - d, d) := by ext <;> simp; ring
    rw [e]
    obtain ⟨m, v⟩ := ladO_at d O hdom hval (2 - d) d ((mem_ladderF_ab d hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, plV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k6 : (2 * d, 2) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) ∈ O.dom ∧
      O.val ((2 * d, 2) + (1 - d, 1 + d) + (1, -1)) = -((d + 2) * (d + 2 + 1) / 2) + (2 * d + 4) := by
    have e : ((2 * d, 2) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) : Site) = (d + 2, d + 2) := by
      ext <;> simp <;> ring
    rw [e]
    obtain ⟨m, v⟩ := ladO_at d O hdom hval (d + 2) (d + 2) ((mem_ladderF_ab d hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, plV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k7 : (2 * d, 2) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈ O.dom ∧
      O.val ((2 * d, 2) + (1 - d, 1 + d) + (1, -1) - (1, 0)) = -((d + 2) * (d + 2 + 1) / 2) + (2 * d + 3) := by
    have e : ((2 * d, 2) + (1 - d, 1 + d) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) : Site) = (d + 1, d + 2) := by
      ext <;> simp <;> ring
    rw [e]
    obtain ⟨m, v⟩ := ladO_at d O hdom hval (d + 1) (d + 2) ((mem_ladderF_ab d hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, plV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  unfold StdCornerValues
  dsimp only
  refine ⟨⟨k0.1, by rw [normed_zero]; exact k0.2⟩, ⟨k1.1, by rw [normed_zero]; exact k1.2⟩,
    ⟨k2.1, by rw [normed_zero]; exact k2.2⟩, ⟨k3.1, by rw [normed_zero]; exact k3.2⟩,
    ⟨k4.1, by rw [normed_zero, k4.2, negh0_Y]; linarith [two_mul_T2 (1 + d), two_mul_chooseTwo (1 - d)]⟩,
    ⟨k5.1, by rw [normed_zero, k5.2, negh0_Y]; linarith [two_mul_T2 d, two_mul_chooseTwo (1 - d)]⟩,
    ⟨k6.1, by rw [normed_zero, k6.2, negh0_Y]; linarith [two_mul_T2 (d + 2), two_mul_chooseTwo (1 - d)]⟩,
    ⟨k7.1, by rw [normed_zero, k7.2, negh0_Y]; linarith [two_mul_T2 (d + 2), two_mul_chooseTwo (1 - d)]⟩⟩

/-- (a) of `lemma:tile-odometer-existence` for the odd doubled stair. -/
theorem ladO_translation (d : ℤ) (hd : 4 ≤ d) (O : PartialOdometer) (hdom : O.dom = ladderF d)
    (hval : ∀ x ∈ O.dom, O.val x = paperLadderValue d x)
    (hcX : LatticeSelfCompatible O (2 * d, 2) 0) (hcY : LatticeSelfCompatible O (1 - d, 1 + d) (1, -d)) :
    TileTranslation O (2 * d, 2) (1 - d, 1 + d) (1, -d) :=
  tileTranslation_of_corners O _ _ _ 0 0 (ladO_firstNormal d hd O hdom hval)
    (ladO_corners d hd O hdom hval) hcX hcY

/-! ### The even near-one doubled stair `nladderN d` (words `2^k`, `d = 2k+2`)

The domain is `nladderN d = shift (nladderF d) (0,-1)`, read at `x + (0,1)` by `paperNearLadderValue d`. -/

theorem mem_nladderF_ab (d : ℤ) (hd : 4 ≤ d) (a b : ℤ) : (a, b) ∈ nladderF d ↔
    ((-1 ≤ a ∧ a ≤ d + 1 ∧ 1 ≤ b ∧ b ≤ 3 * d - 1) ∧
      ((a = -1 ∧ b = 2 * d + 1) ∨ (a = d + 1 ∧ b = d - 1) ∨ (b - a = d ∧ 0 < a ∧ a < d) ∨
        (-1 ≤ a ∧ a ≤ d + 1 ∧ 1 ≤ b ∧ b ≤ 3 * d - 1 ∧ -1 ≤ b - a ∧ b - a ≤ 2 * d + 1)) ∧
      ¬((a = -1 ∧ b ≤ d + 1) ∨ (a = d + 1 ∧ 2 * d - 1 ≤ b))) := by
  simp only [nladderF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro h
    omega
  · intro h
    omega

theorem mem_nladderN_ab (d : ℤ) (a b : ℤ) : (a, b) ∈ nladderN d ↔ (a, b + 1) ∈ nladderF d := by
  unfold nladderN
  rw [mem_shift, show ((a, b) : Site) - (0, -1) = (a, b + 1) by ext <;> simp]

/-- The value of the near-one doubled stair, with the indicator of `A ∪ B` written as an `if`. -/
theorem pnlV (d a b : ℤ) : paperNearLadderValue d (a, b) = -((b - a) ^ 2 / 4) + min 0 (d - b) +
    min 0 (2 * d - b) + max ((b - a) - d) 0 +
    (if (a, b) = (-1, 2 * d + 1) ∨ (a, b) = (d + 1, d - 1) ∨ (b - a = d ∧ 0 < a ∧ a < d) then 1 else 0) := by
  have hI : (paperNearLadderA d ∪ paperNearLadderB d).indicator (fun _ => (1 : ℤ)) (a, b) =
      (if (a, b) = (-1, 2 * d + 1) ∨ (a, b) = (d + 1, d - 1) ∨ (b - a = d ∧ 0 < a ∧ a < d) then 1 else 0) := by
    unfold Set.indicator
    simp only [Set.mem_union, paperNearLadderA, paperNearLadderB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, or_assoc]
  unfold paperNearLadderValue
  rw [hI]

theorem nlE_at (d : ℤ) (E : PartialOdometer) (hdom : E.dom = nladderN d)
    (hval : ∀ x ∈ E.dom, E.val x = paperNearLadderValue d (x + (0, 1))) (a b : ℤ) (h : (a, b + 1) ∈ nladderF d) :
    (a, b) ∈ E.dom ∧ E.val (a, b) = paperNearLadderValue d (a, b + 1) := by
  have hm : (a, b) ∈ E.dom := by
    rw [hdom, mem_nladderN_ab]
    exact h
  refine ⟨hm, ?_⟩
  rw [hval _ hm, show ((a, b) : Site) + (0, 1) = (a, b + 1) by ext <;> simp]

theorem nlE_firstNormal (d : ℤ) (hd : 4 ≤ d) (E : PartialOdometer) (hdom : E.dom = nladderN d)
    (hval : ∀ x ∈ E.dom, E.val x = paperNearLadderValue d (x + (0, 1))) : FirstTileNormal E 0 0 := by
  apply firstNormal_of E
  · obtain ⟨m, v⟩ := nlE_at d E hdom hval 0 0 ((mem_nladderF_ab d hd 0 (0 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := nlE_at d E hdom hval 0 1 ((mem_nladderF_ab d hd 0 (1 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := nlE_at d E hdom hval 1 0 ((mem_nladderF_ab d hd 1 (0 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := nlE_at d E hdom hval 1 1 ((mem_nladderF_ab d hd 1 (1 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega

/-- The 180-degree symmetry of the even near-one doubled stair: the centre is `D = (d, 3d-2)`. -/
theorem nlE_halfturn (d : ℤ) (hd : 4 ≤ d) (E : PartialOdometer) (hdom : E.dom = nladderN d)
    (hval : ∀ x ∈ E.dom, E.val x = paperNearLadderValue d (x + (0, 1))) :
    TileHalfTurn E (d + 1, d - 1) (-2, 2 * d) (d - 1, -(d + 1)) := by
  refine ⟨0, 0, nlE_firstNormal d hd E hdom hval, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxS : (a, b + 1) ∈ nladderF d := by
    rw [← mem_nladderN_ab, ← hdom]
    exact hx
  have hD : ((d + 1, d - 1) + (-2, 2 * d) + ((1 : ℤ), (-1 : ℤ))) = ((d : ℤ), 3 * d - 2) := by
    ext <;> simp <;> ring
  have hy : ((d : ℤ), 3 * d - 2) - (a, b) = (d - a, 3 * d - 2 - b) := by
    rw [Prod.mk_sub_mk]
  rw [hD, hy]
  have hyS : (d - a, 3 * d - 2 - b + 1) ∈ nladderF d :=
    (mem_nladderF_ab d hd _ _).2 (by have h := (mem_nladderF_ab d hd a (b + 1)).1 hxS; omega)
  have hyE : (d - a, 3 * d - 2 - b) ∈ E.dom := by
    rw [hdom, mem_nladderN_ab]
    exact hyS
  refine ⟨hyE, ?_⟩
  simp only [normed_zero, dotS]
  rw [hval _ hyE, hval _ hx, show ((d - a, 3 * d - 2 - b) : Site) + (0, 1) = (d - a, 3 * d - 2 - b + 1) by ext <;> simp,
    show ((a, b) : Site) + (0, 1) = (a, b + 1) by ext <;> simp, pnlV, pnlV]
  have hS : -((b + 1 - a) ^ 2 / 4) + (3 * d - 2 - b + 1 - (d - a)) ^ 2 / 4 = d ^ 2 - (b + 1 - a) * d := by
    rw [show 3 * d - 2 - b + 1 - (d - a) = 2 * d - (b + 1 - a) by ring]
    exact sq4_sym d (b + 1 - a)
  have hmm : min 0 (d - (3 * d - 2 - b + 1)) + min 0 (2 * d - (3 * d - 2 - b + 1)) +
      max ((3 * d - 2 - b + 1 - (d - a)) - d) 0 - (min 0 (d - (b + 1)) + min 0 (2 * d - (b + 1)) +
      max ((b + 1 - a) - d) 0) = -2 * d + b + a + 1 := by
    omega
  have hind : (if (d - a, 3 * d - 2 - b + 1) = (-1, 2 * d + 1) ∨ (d - a, 3 * d - 2 - b + 1) = (d + 1, d - 1) ∨
        (3 * d - 2 - b + 1 - (d - a) = d ∧ 0 < d - a ∧ d - a < d) then (1 : ℤ) else 0) =
      (if (a, b + 1) = (-1, 2 * d + 1) ∨ (a, b + 1) = (d + 1, d - 1) ∨ (b + 1 - a = d ∧ 0 < a ∧ a < d) then
        (1 : ℤ) else 0) := by
    simp only [Prod.mk.injEq]
    split_ifs <;> omega
  linarith [hS, hmm, hind]

theorem nlE_G (d : ℤ) : -h0 (-2, 2 * d) = -(d ^ 2 + 3 * d - 1) := by
  have hc : chooseTwo (-2) = 3 := by unfold chooseTwo; norm_num
  have hsq : (-2 - 2 * d - 1) ^ 2 / 4 = d ^ 2 + 3 * d + 2 := by
    rw [show (-2 - 2 * d - 1) ^ 2 = 4 * (d ^ 2 + 3 * d + 2) + 1 by ring]
    generalize d ^ 2 + 3 * d + 2 = X
    omega
  unfold h0 centeredQuarterTurnCorrection
  dsimp only
  rw [hc, hsq]
  ring

/-- The corner identities of the even near-one doubled stair (`StdCornerValues`), with `X = (d+1, d-1)`,
`Y = (-2, 2d)`, `e = (d-1, -(d+1))`, `D = (d, 3d-2)`. -/
theorem nlE_corners (d : ℤ) (hd : 4 ≤ d) (E : PartialOdometer) (hdom : E.dom = nladderN d)
    (hval : ∀ x ∈ E.dom, E.val x = paperNearLadderValue d (x + (0, 1))) :
    StdCornerValues E 0 0 (d + 1, d - 1) (-2, 2 * d) (d - 1, -(d + 1)) := by
  have hG := nlE_G d
  have k0 : (0 : Site) ∈ E.dom ∧ E.val 0 = 0 := by
    obtain ⟨m, v⟩ := nlE_at d E hdom hval 0 0 ((mem_nladderF_ab d hd 0 (0 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    show E.val (0, 0) = 0
    rw [v, pnlV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k1 : ((1 : ℤ), (0 : ℤ)) ∈ E.dom ∧ E.val (1, 0) = 0 := by
    obtain ⟨m, v⟩ := nlE_at d E hdom hval 1 0 ((mem_nladderF_ab d hd 1 (0 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlV]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k2 : (d + 1, d - 1) - ((0 : ℤ), (1 : ℤ)) ∈ E.dom ∧ E.val ((d + 1, d - 1) - (0, 1)) = 0 := by
    have e : ((d + 1, d - 1) : Site) - (0, 1) = (d + 1, d - 2) := by ext <;> simp; ring
    rw [e]
    obtain ⟨m, v⟩ := nlE_at d E hdom hval (d + 1) (d - 2) ((mem_nladderF_ab d hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlV, show d - 2 + 1 - (d + 1) = -2 by ring]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k3 : (d + 1, d - 1) ∈ E.dom ∧ E.val (d + 1, d - 1) = 0 := by
    obtain ⟨m, v⟩ := nlE_at d E hdom hval (d + 1) (d - 1) ((mem_nladderF_ab d hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlV, show d - 1 + 1 - (d + 1) = -1 by ring]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k4 : (-2, 2 * d) + ((1 : ℤ), (0 : ℤ)) ∈ E.dom ∧ E.val ((-2, 2 * d) + (1, 0)) = -((d + 1) ^ 2) + 1 := by
    have e : ((-2, 2 * d) : Site) + (1, 0) = (-1, 2 * d) := by ext <;> simp
    rw [e]
    obtain ⟨m, v⟩ := nlE_at d E hdom hval (-1) (2 * d) ((mem_nladderF_ab d hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlV, sq4_even (2 * d + 1 - -1) (d + 1) (by ring)]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k5 : (-2, 2 * d) + ((1 : ℤ), (-1 : ℤ)) ∈ E.dom ∧ E.val ((-2, 2 * d) + (1, -1)) = -(d ^ 2 + d) + 1 := by
    have e : ((-2, 2 * d) : Site) + (1, -1) = (-1, 2 * d - 1) := by ext <;> simp; ring
    rw [e]
    obtain ⟨m, v⟩ := nlE_at d E hdom hval (-1) (2 * d - 1) ((mem_nladderF_ab d hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlV, sq4_odd (2 * d - 1 + 1 - -1) d (by ring)]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k6 : (d + 1, d - 1) + (-2, 2 * d) + ((1 : ℤ), (-1 : ℤ)) ∈ E.dom ∧
      E.val ((d + 1, d - 1) + (-2, 2 * d) + (1, -1)) = -((d - 1) ^ 2 + (d - 1)) + (1 - 2 * d) + (1 - d) + (d - 1) := by
    have e : ((d + 1, d - 1) + (-2, 2 * d) + ((1 : ℤ), (-1 : ℤ)) : Site) = (d, 3 * d - 2) := by
      ext <;> simp <;> ring
    rw [e]
    obtain ⟨m, v⟩ := nlE_at d E hdom hval d (3 * d - 2) ((mem_nladderF_ab d hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlV, show 3 * d - 2 + 1 - d = 2 * (d - 1) + 1 by ring, sq4_odd (2 * (d - 1) + 1) (d - 1) rfl]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  have k7 : (d + 1, d - 1) + (-2, 2 * d) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈ E.dom ∧
      E.val ((d + 1, d - 1) + (-2, 2 * d) + (1, -1) - (1, 0)) = -(d ^ 2) + 1 - 2 * d + (1 - d) + d := by
    have e : ((d + 1, d - 1) + (-2, 2 * d) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) : Site) =
        (d - 1, 3 * d - 2) := by
      ext <;> simp <;> ring
    rw [e]
    obtain ⟨m, v⟩ := nlE_at d E hdom hval (d - 1) (3 * d - 2) ((mem_nladderF_ab d hd _ _).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlV, show 3 * d - 2 + 1 - (d - 1) = 2 * d by ring, sq4_even (2 * d) d rfl]
    split_ifs with h1
    all_goals (try simp only [Prod.mk.injEq] at h1)
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  unfold StdCornerValues
  dsimp only
  refine ⟨⟨k0.1, by rw [normed_zero]; exact k0.2⟩, ⟨k1.1, by rw [normed_zero]; exact k1.2⟩,
    ⟨k2.1, by rw [normed_zero]; exact k2.2⟩, ⟨k3.1, by rw [normed_zero]; exact k3.2⟩,
    ⟨k4.1, by rw [normed_zero, k4.2, hG]; ring⟩, ⟨k5.1, by rw [normed_zero, k5.2, hG]; ring⟩,
    ⟨k6.1, by rw [normed_zero, k6.2, hG]; ring⟩, ⟨k7.1, by rw [normed_zero, k7.2, hG]; ring⟩⟩

/-- (a) of `lemma:tile-odometer-existence` for the even near-one doubled stair. -/
theorem nlE_translation (d : ℤ) (hd : 4 ≤ d) (E : PartialOdometer) (hdom : E.dom = nladderN d)
    (hval : ∀ x ∈ E.dom, E.val x = paperNearLadderValue d (x + (0, 1)))
    (hcX : LatticeSelfCompatible E (d + 1, d - 1) 0) (hcY : LatticeSelfCompatible E (-2, 2 * d) (d - 1, -(d + 1))) :
    TileTranslation E (d + 1, d - 1) (-2, 2 * d) (d - 1, -(d + 1)) :=
  tileTranslation_of_corners E _ _ _ 0 0 (nlE_firstNormal d hd E hdom hval)
    (nlE_corners d hd E hdom hval) hcX hcY

/-! ### The alternate families of the base cases

`AltHalfTurn o Dh E`: the alternate tile `o` is normalised and symmetric about `Dh` with affine factor `E`.
Four parametric families: the stair-alternate even tile (words `[]` and `3^k`), the ladder-alternate odd tile (`3^k`),
the near-one-stair-alternate odd tile (`[]` and `2^k`) and the near-one-ladder-alternate even tile (`2^k`). -/

theorem mem_stAlt (d a b : ℤ) : (a, b) ∈ paperStairAltTile d ↔
    (((a = 1 - d ∧ -1 ≤ b ∧ b ≤ 0) ∨ (a = 3 ∧ d ≤ b ∧ b ≤ d + 1)) ∨ (a + b = 2 ∧ 0 < b ∧ b < d)) ∨
      ((1 - d ≤ a ∧ a ≤ 0 ∧ b = -1) ∨ (4 - d ≤ a ∧ a ≤ 3 ∧ b = d + 1)) ∨
      (4 - 2 * d ≤ a ∧ a ≤ d ∧ 0 ≤ b ∧ b ≤ d ∧ -d + 2 ≤ a + b ∧ a + b ≤ d + 2) := by
  simp only [paperStairAltTile, paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD, Set.mem_union,
    Set.mem_setOf_eq, or_assoc]

theorem pstA (d a b : ℤ) : paperStairAltValue d (a, b) = -(b * (b + 1) / 2) + min 0 (2 - a) + min 0 (d - 2 + a) +
    max (a + b - 2) 0 +
    (if ((a = 1 - d ∧ -1 ≤ b ∧ b ≤ 0) ∨ (a = 3 ∧ d ≤ b ∧ b ≤ d + 1)) ∨ (a + b = 2 ∧ 0 < b ∧ b < d) then 1 else 0) := by
  unfold paperStairAltValue
  unfold Set.indicator
  simp only [Set.mem_union, paperStairAltA, paperStairAltB, Set.mem_setOf_eq, or_assoc]

theorem stA_normal (d : ℤ) (hd : 3 ≤ d) (E : PartialOdometer) (hdom : ∀ x : Site, x ∈ E.dom ↔ x ∈ paperStairAltTile d)
    (hval : ∀ x ∈ E.dom, E.val x = paperStairAltValue d x) : FirstTileNormal E 0 0 := by
  have at_ : ∀ a b : ℤ, (a, b) ∈ paperStairAltTile d → (a, b) ∈ E.dom ∧ E.val (a, b) = paperStairAltValue d (a, b) :=
    fun a b h => ⟨(hdom _).2 h, hval _ ((hdom _).2 h)⟩
  apply firstNormal_of E
  · obtain ⟨m, v⟩ := at_ 0 0 ((mem_stAlt d 0 0).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pstA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := at_ 0 1 ((mem_stAlt d 0 1).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pstA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := at_ 1 0 ((mem_stAlt d 1 0).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pstA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := at_ 1 1 ((mem_stAlt d 1 1).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pstA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega

/-- The alternate stair (even child of `[]` and `3^k`): symmetric about `(4-d, d)` with affine factor `(1, -d)`. -/
theorem stA_halfturn (d : ℤ) (hd : 3 ≤ d) (E : PartialOdometer) (hdom : ∀ x : Site, x ∈ E.dom ↔ x ∈ paperStairAltTile d)
    (hval : ∀ x ∈ E.dom, E.val x = paperStairAltValue d x) : AltHalfTurn E (4 - d, d) (1, -d) := by
  refine ⟨0, 0, stA_normal d hd E hdom hval, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxS : (a, b) ∈ paperStairAltTile d := (hdom _).1 hx
  have hyS : (4 - d - a, d - b) ∈ paperStairAltTile d :=
    (mem_stAlt d _ _).2 (by have h := (mem_stAlt d a b).1 hxS; omega)
  have hyE : (4 - d - a, d - b) ∈ E.dom := (hdom _).2 hyS
  have hy : ((4 - d, d) : Site) - (a, b) = (4 - d - a, d - b) := by
    rw [Prod.mk_sub_mk]
  rw [hy]
  refine ⟨hyE, ?_⟩
  simp only [normed_zero, dotS]
  rw [hval _ hyE, hval _ hx, pstA, pstA]
  have hm : min 0 (2 - (4 - d - a)) + min 0 (d - 2 + (4 - d - a)) + max (4 - d - a + (d - b) - 2) 0 -
      (min 0 (2 - a) + min 0 (d - 2 + a) + max (a + b - 2) 0) = 2 - a - b := by
    omega
  have hind : (if ((4 - d - a = 1 - d ∧ -1 ≤ d - b ∧ d - b ≤ 0) ∨ (4 - d - a = 3 ∧ d ≤ d - b ∧ d - b ≤ d + 1)) ∨
        (4 - d - a + (d - b) = 2 ∧ 0 < d - b ∧ d - b < d) then (1 : ℤ) else 0) =
      (if ((a = 1 - d ∧ -1 ≤ b ∧ b ≤ 0) ∨ (a = 3 ∧ d ≤ b ∧ b ≤ d + 1)) ∨ (a + b = 2 ∧ 0 < b ∧ b < d) then
        (1 : ℤ) else 0) := by
    split_ifs <;> omega
  linarith [two_mul_T2 (d - b), two_mul_T2 b, hm, hind]

/-! #### The ladder-alternate odd tile (words `3^k`, `d = 2k+2`), read at `x - (1,1)` -/

theorem mem_ladAlt (d a b : ℤ) : (a, b) ∈ paperLadderAltTile d ↔
    ((((a = -1 ∧ b = -1) ∨ (a = d ∧ b = d + 2)) ∨ (a + b = d ∧ 0 < a ∧ a < d - 1)) ∨
      (1 - d ≤ a ∧ a ≤ 2 * d - 2 ∧ -1 ≤ b ∧ b ≤ d + 2 ∧ -1 ≤ a + b ∧ a + b ≤ 2 * d + 1)) ∧
    ¬((d ≤ a ∧ -1 ≤ b ∧ b ≤ 0) ∨ (a ≤ -1 ∧ d + 1 ≤ b ∧ b ≤ d + 2)) := by
  simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, or_assoc]

theorem pladA (d a b : ℤ) : paperLadderAltValue d (a, b) = -(b * (b + 1) / 2) + min 0 a + min 0 (d - a - 1) +
    max (a + b - d) 0 + (if (a = -1 ∧ b = -1) ∨ (a = d ∧ b = d + 2) ∨ (a + b = d ∧ 0 < a ∧ a < d - 1) then 1 else 0) := by
  unfold paperLadderAltValue
  unfold Set.indicator
  simp only [Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_setOf_eq, Prod.mk.injEq, or_assoc]

/-- The ladder-alternate odd tile: the read point `x - (1,1)` and the domain `x ∈ dom ↔ x - (1,1) ∈ tile`. -/
theorem ladA_at (d : ℤ) (O : PartialOdometer) (hdom : ∀ x : Site, x ∈ O.dom ↔ x - (1, 1) ∈ paperLadderAltTile d)
    (hval : ∀ x ∈ O.dom, O.val x = paperLadderAltValue d (x - (1, 1))) (a b : ℤ)
    (h : (a - 1, b - 1) ∈ paperLadderAltTile d) :
    (a, b) ∈ O.dom ∧ O.val (a, b) = paperLadderAltValue d (a - 1, b - 1) := by
  have e : ((a, b) : Site) - (1, 1) = (a - 1, b - 1) := by ext <;> simp
  have hm : (a, b) ∈ O.dom := (hdom _).2 (by rw [e]; exact h)
  exact ⟨hm, by rw [hval _ hm, e]⟩

theorem ladA_normal (d : ℤ) (hd : 4 ≤ d) (O : PartialOdometer)
    (hdom : ∀ x : Site, x ∈ O.dom ↔ x - (1, 1) ∈ paperLadderAltTile d)
    (hval : ∀ x ∈ O.dom, O.val x = paperLadderAltValue d (x - (1, 1))) : FirstTileNormal O 0 0 := by
  apply firstNormal_of O
  · obtain ⟨m, v⟩ := ladA_at d O hdom hval 0 0 ((mem_ladAlt d (0 - 1) (0 - 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pladA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := ladA_at d O hdom hval 0 1 ((mem_ladAlt d (0 - 1) (1 - 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pladA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := ladA_at d O hdom hval 1 0 ((mem_ladAlt d (1 - 1) (0 - 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pladA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := ladA_at d O hdom hval 1 1 ((mem_ladAlt d (1 - 1) (1 - 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pladA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega

set_option maxHeartbeats 400000 in
/-- The alternate ladder (odd child of `3^k`): symmetric about `(d+1, d+3)` with affine factor `(1, -(d+1))`. -/
theorem ladA_halfturn (d : ℤ) (hd : 4 ≤ d) (O : PartialOdometer)
    (hdom : ∀ x : Site, x ∈ O.dom ↔ x - (1, 1) ∈ paperLadderAltTile d)
    (hval : ∀ x ∈ O.dom, O.val x = paperLadderAltValue d (x - (1, 1))) :
    AltHalfTurn O (d + 1, d + 3) (1, -(d + 1)) := by
  refine ⟨0, 0, ladA_normal d hd O hdom hval, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxS : (a - 1, b - 1) ∈ paperLadderAltTile d := by
    have e : ((a, b) : Site) - (1, 1) = (a - 1, b - 1) := by ext <;> simp
    rw [← e]
    exact (hdom _).1 hx
  have hyS : (d - a, d + 2 - b) ∈ paperLadderAltTile d :=
    (mem_ladAlt d _ _).2 (by have h := (mem_ladAlt d (a - 1) (b - 1)).1 hxS; omega)
  have e2 : ((d + 1 - a, d + 3 - b) : Site) - (1, 1) = (d - a, d + 2 - b) := by ext <;> simp <;> ring
  have hyO : (d + 1 - a, d + 3 - b) ∈ O.dom := (hdom _).2 (by rw [e2]; exact hyS)
  have hy : ((d + 1, d + 3) : Site) - (a, b) = (d + 1 - a, d + 3 - b) := by
    rw [Prod.mk_sub_mk]
  rw [hy]
  refine ⟨hyO, ?_⟩
  simp only [normed_zero, dotS]
  have e1 : ((a, b) : Site) - (1, 1) = (a - 1, b - 1) := by ext <;> simp
  have hxv : O.val (a, b) = paperLadderAltValue d (a - 1, b - 1) := by rw [hval _ hx, e1]
  have hyv : O.val (d + 1 - a, d + 3 - b) = paperLadderAltValue d (d - a, d + 2 - b) := by
    rw [hval _ hyO, e2]
  rw [hxv, hyv, pladA, pladA]
  have hm : min 0 (d - a) + min 0 (d - (d - a) - 1) + max (d - a + (d + 2 - b) - d) 0 -
      (min 0 (a - 1) + min 0 (d - (a - 1) - 1) + max (a - 1 + (b - 1) - d) 0) = d + 2 - a - b := by
    omega
  have hind : (if (d - a = -1 ∧ d + 2 - b = -1) ∨ (d - a = d ∧ d + 2 - b = d + 2) ∨
        (d - a + (d + 2 - b) = d ∧ 0 < d - a ∧ d - a < d - 1) then (1 : ℤ) else 0) =
      (if (a - 1 = -1 ∧ b - 1 = -1) ∨ (a - 1 = d ∧ b - 1 = d + 2) ∨ (a - 1 + (b - 1) = d ∧ 0 < a - 1 ∧ a - 1 < d - 1)
        then (1 : ℤ) else 0) := by
    split_ifs <;> omega
  linarith [two_mul_T2 (d + 2 - b), two_mul_T2 (b - 1), hm, hind]

/-! #### The near-one-stair-alternate odd tile (words `[]` and `2^k`, `d = 2k+3`), read at `x + (0,1)` -/

theorem mem_nsAlt (d a b : ℤ) : (a, b) ∈ paperNearStairAltTile d ↔
    ((((-1 ≤ a ∧ a ≤ 0 ∧ b = 2 * d) ∨ (d ≤ a ∧ a ≤ d + 1 ∧ b = d - 2)) ∨ (b - a = d - 1 ∧ 0 < a ∧ a < d)) ∨
      ((a = -1 ∧ d + 1 ≤ b ∧ b ≤ 2 * d) ∨ (a = d + 1 ∧ d - 2 ≤ b ∧ b ≤ 2 * d - 3))) ∨
    (0 ≤ a ∧ a ≤ d ∧ 1 ≤ b ∧ b ≤ 3 * d - 3 ∧ -1 ≤ b - a ∧ b - a ≤ 2 * d - 1) := by
  simp only [paperNearStairAltTile, paperNearStairAltA, paperNearStairAltB, paperNearStairAltC,
    paperNearStairAltD, Set.mem_union, Set.mem_setOf_eq, or_assoc]

theorem pnsA (d a b : ℤ) : paperNearStairAltValue d (a, b) = -((b - a) ^ 2 / 4) + min (d - b - 1) 0 +
    min (2 * d - 1 - b) 0 + max (b - a - d + 1) 0 +
    (if (-1 ≤ a ∧ a ≤ 0 ∧ b = 2 * d) ∨ (d ≤ a ∧ a ≤ d + 1 ∧ b = d - 2) ∨ (b - a = d - 1 ∧ 0 < a ∧ a < d) then 1
      else 0) := by
  unfold paperNearStairAltValue
  unfold Set.indicator
  simp only [Set.mem_union, paperNearStairAltA, paperNearStairAltB, Set.mem_setOf_eq, or_assoc]

theorem nsA_at (d : ℤ) (O : PartialOdometer) (hdom : ∀ x : Site, x ∈ O.dom ↔ x + (0, 1) ∈ paperNearStairAltTile d)
    (hval : ∀ x ∈ O.dom, O.val x = paperNearStairAltValue d (x + (0, 1))) (a b : ℤ)
    (h : (a, b + 1) ∈ paperNearStairAltTile d) :
    (a, b) ∈ O.dom ∧ O.val (a, b) = paperNearStairAltValue d (a, b + 1) := by
  have e : ((a, b) : Site) + (0, 1) = (a, b + 1) := by ext <;> simp
  have hm : (a, b) ∈ O.dom := (hdom _).2 (by rw [e]; exact h)
  exact ⟨hm, by rw [hval _ hm, e]⟩

theorem nsA_normal (d : ℤ) (hd : 3 ≤ d) (O : PartialOdometer)
    (hdom : ∀ x : Site, x ∈ O.dom ↔ x + (0, 1) ∈ paperNearStairAltTile d)
    (hval : ∀ x ∈ O.dom, O.val x = paperNearStairAltValue d (x + (0, 1))) : FirstTileNormal O 0 0 := by
  apply firstNormal_of O
  · obtain ⟨m, v⟩ := nsA_at d O hdom hval 0 0 ((mem_nsAlt d 0 (0 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := nsA_at d O hdom hval 0 1 ((mem_nsAlt d 0 (1 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := nsA_at d O hdom hval 1 0 ((mem_nsAlt d 1 (0 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := nsA_at d O hdom hval 1 1 ((mem_nsAlt d 1 (1 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnsA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega

set_option maxHeartbeats 400000 in
/-- The alternate near-one stair (odd child of `[]` and `2^k`): symmetric about `(d, 3d-4)` with affine factor
`(d-2, -d)`. -/
theorem nsA_halfturn (d : ℤ) (hd : 3 ≤ d) (O : PartialOdometer)
    (hdom : ∀ x : Site, x ∈ O.dom ↔ x + (0, 1) ∈ paperNearStairAltTile d)
    (hval : ∀ x ∈ O.dom, O.val x = paperNearStairAltValue d (x + (0, 1))) :
    AltHalfTurn O (d, 3 * d - 4) (d - 2, -d) := by
  refine ⟨0, 0, nsA_normal d hd O hdom hval, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxS : (a, b + 1) ∈ paperNearStairAltTile d := by
    have e : ((a, b) : Site) + (0, 1) = (a, b + 1) := by ext <;> simp
    rw [← e]
    exact (hdom _).1 hx
  have hyS : (d - a, 3 * d - 3 - b) ∈ paperNearStairAltTile d :=
    (mem_nsAlt d _ _).2 (by have h := (mem_nsAlt d a (b + 1)).1 hxS; omega)
  have e2 : ((d - a, 3 * d - 4 - b) : Site) + (0, 1) = (d - a, 3 * d - 3 - b) := by ext <;> simp; ring
  have hyO : (d - a, 3 * d - 4 - b) ∈ O.dom := (hdom _).2 (by rw [e2]; exact hyS)
  have hy : ((d, 3 * d - 4) : Site) - (a, b) = (d - a, 3 * d - 4 - b) := by
    rw [Prod.mk_sub_mk]
  rw [hy]
  refine ⟨hyO, ?_⟩
  simp only [normed_zero, dotS]
  have e1 : ((a, b) : Site) + (0, 1) = (a, b + 1) := by ext <;> simp
  rw [hval _ hyO, hval _ hx, e2, e1, pnsA, pnsA]
  have hS : -((b + 1 - a) ^ 2 / 4) + (3 * d - 3 - b - (d - a)) ^ 2 / 4 = (d - 1) ^ 2 - (b + 1 - a) * (d - 1) := by
    rw [show 3 * d - 3 - b - (d - a) = 2 * (d - 1) - (b + 1 - a) by ring]
    exact sq4_sym (d - 1) (b + 1 - a)
  have hm : min (d - (3 * d - 3 - b) - 1) 0 + min (2 * d - 1 - (3 * d - 3 - b)) 0 +
      max (3 * d - 3 - b - (d - a) - d + 1) 0 - (min (d - (b + 1) - 1) 0 + min (2 * d - 1 - (b + 1)) 0 +
      max (b + 1 - a - d + 1) 0) = b + 2 - 2 * d + a := by
    omega
  have hind : (if (-1 ≤ d - a ∧ d - a ≤ 0 ∧ 3 * d - 3 - b = 2 * d) ∨ (d ≤ d - a ∧ d - a ≤ d + 1 ∧ 3 * d - 3 - b = d - 2) ∨
        (3 * d - 3 - b - (d - a) = d - 1 ∧ 0 < d - a ∧ d - a < d) then (1 : ℤ) else 0) =
      (if (-1 ≤ a ∧ a ≤ 0 ∧ b + 1 = 2 * d) ∨ (d ≤ a ∧ a ≤ d + 1 ∧ b + 1 = d - 2) ∨ (b + 1 - a = d - 1 ∧ 0 < a ∧ a < d)
        then (1 : ℤ) else 0) := by
    split_ifs <;> omega
  linarith [hS, hm, hind]

/-! #### The near-one-ladder-alternate even tile (words `2^k`, `d = 2k+2`), read at `x + (0,1)` -/

theorem mem_nlAlt (d a b : ℤ) : (a, b) ∈ paperNearLadderAltTile d ↔
    ((((a = -2 ∧ b = 2 * d) ∨ (a = d + 1 ∧ b = d - 1)) ∨ (b - a = d ∧ 0 < a ∧ a < d - 1)) ∨
      (-2 ≤ a ∧ a ≤ d + 1 ∧ 1 ≤ b ∧ b ≤ 3 * d - 2 ∧ -1 ≤ b - a ∧ b - a ≤ 2 * d + 1)) ∧
    ¬((a ≤ -1 ∧ b ≤ d - 1) ∨ (d ≤ a ∧ 2 * d ≤ b)) := by
  simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC,
    paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_setOf_eq, Prod.mk.injEq, or_assoc]

theorem pnlA (d a b : ℤ) : paperNearLadderAltValue d (a, b) = -((b - a) ^ 2 / 4) + min 0 (d - b) +
    min 0 (2 * d - 1 - b) + max 0 (b - a - d) +
    (if (a = -2 ∧ b = 2 * d) ∨ (a = d + 1 ∧ b = d - 1) ∨ (b - a = d ∧ 0 < a ∧ a < d - 1) then 1 else 0) := by
  unfold paperNearLadderAltValue
  unfold Set.indicator
  simp only [Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_setOf_eq, Prod.mk.injEq, or_assoc]

theorem nlA_at (d : ℤ) (E : PartialOdometer) (hdom : ∀ x : Site, x ∈ E.dom ↔ x + (0, 1) ∈ paperNearLadderAltTile d)
    (hval : ∀ x ∈ E.dom, E.val x = paperNearLadderAltValue d (x + (0, 1))) (a b : ℤ)
    (h : (a, b + 1) ∈ paperNearLadderAltTile d) :
    (a, b) ∈ E.dom ∧ E.val (a, b) = paperNearLadderAltValue d (a, b + 1) := by
  have e : ((a, b) : Site) + (0, 1) = (a, b + 1) := by ext <;> simp
  have hm : (a, b) ∈ E.dom := (hdom _).2 (by rw [e]; exact h)
  exact ⟨hm, by rw [hval _ hm, e]⟩

theorem nlA_normal (d : ℤ) (hd : 4 ≤ d) (E : PartialOdometer)
    (hdom : ∀ x : Site, x ∈ E.dom ↔ x + (0, 1) ∈ paperNearLadderAltTile d)
    (hval : ∀ x ∈ E.dom, E.val x = paperNearLadderAltValue d (x + (0, 1))) : FirstTileNormal E 0 0 := by
  apply firstNormal_of E
  · obtain ⟨m, v⟩ := nlA_at d E hdom hval 0 0 ((mem_nlAlt d 0 (0 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := nlA_at d E hdom hval 0 1 ((mem_nlAlt d 0 (1 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := nlA_at d E hdom hval 1 0 ((mem_nlAlt d 1 (0 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega
  · obtain ⟨m, v⟩ := nlA_at d E hdom hval 1 1 ((mem_nlAlt d 1 (1 + 1)).2 (by omega))
    refine ⟨m, ?_⟩
    rw [v, pnlA]
    split_ifs with h1
    all_goals (try norm_num at h1)
    all_goals (try norm_num)
    all_goals omega

set_option maxHeartbeats 400000 in
/-- The alternate near-one ladder (even child of `2^k`): symmetric about `(d-1, 3d-3)` with affine factor
`(d-1, -(d+1))`. -/
theorem nlA_halfturn (d : ℤ) (hd : 4 ≤ d) (E : PartialOdometer)
    (hdom : ∀ x : Site, x ∈ E.dom ↔ x + (0, 1) ∈ paperNearLadderAltTile d)
    (hval : ∀ x ∈ E.dom, E.val x = paperNearLadderAltValue d (x + (0, 1))) :
    AltHalfTurn E (d - 1, 3 * d - 3) (d - 1, -(d + 1)) := by
  refine ⟨0, 0, nlA_normal d hd E hdom hval, ?_⟩
  rintro ⟨a, b⟩ hx
  have e1 : ((a, b) : Site) + (0, 1) = (a, b + 1) := by ext <;> simp
  have hxS : (a, b + 1) ∈ paperNearLadderAltTile d := by
    rw [← e1]
    exact (hdom _).1 hx
  have hyS : (d - 1 - a, 3 * d - 3 - b + 1) ∈ paperNearLadderAltTile d :=
    (mem_nlAlt d _ _).2 (by have h := (mem_nlAlt d a (b + 1)).1 hxS; omega)
  have e2 : ((d - 1 - a, 3 * d - 3 - b) : Site) + (0, 1) = (d - 1 - a, 3 * d - 3 - b + 1) := by
    ext <;> simp
  have hyE : (d - 1 - a, 3 * d - 3 - b) ∈ E.dom := (hdom _).2 (by rw [e2]; exact hyS)
  have hy : ((d - 1, 3 * d - 3) : Site) - (a, b) = (d - 1 - a, 3 * d - 3 - b) := by
    rw [Prod.mk_sub_mk]
  rw [hy]
  refine ⟨hyE, ?_⟩
  simp only [normed_zero, dotS]
  rw [hval _ hyE, hval _ hx, e2, e1, pnlA, pnlA]
  have hS : -((b + 1 - a) ^ 2 / 4) + (3 * d - 3 - b + 1 - (d - 1 - a)) ^ 2 / 4 = d ^ 2 - (b + 1 - a) * d := by
    rw [show 3 * d - 3 - b + 1 - (d - 1 - a) = 2 * d - (b + 1 - a) by ring]
    exact sq4_sym d (b + 1 - a)
  have hm : min 0 (d - (3 * d - 3 - b + 1)) + min 0 (2 * d - 1 - (3 * d - 3 - b + 1)) +
      max 0 (3 * d - 3 - b + 1 - (d - 1 - a) - d) - (min 0 (d - (b + 1)) + min 0 (2 * d - 1 - (b + 1)) +
      max 0 (b + 1 - a - d)) = -2 * d + b + a + 2 := by
    omega
  have hind : (if (d - 1 - a = -2 ∧ 3 * d - 3 - b + 1 = 2 * d) ∨ (d - 1 - a = d + 1 ∧ 3 * d - 3 - b + 1 = d - 1) ∨
        (3 * d - 3 - b + 1 - (d - 1 - a) = d ∧ 0 < d - 1 - a ∧ d - 1 - a < d - 1) then (1 : ℤ) else 0) =
      (if (a = -2 ∧ b + 1 = 2 * d) ∨ (a = d + 1 ∧ b + 1 = d - 1) ∨ (b + 1 - a = d ∧ 0 < a ∧ a < d - 1) then
        (1 : ℤ) else 0) := by
    split_ifs <;> omega
  linarith [hS, hm, hind]

/-! ### The parents of the base words and the vectors of their tile properties -/

theorem parents_three (k : ℕ) : parentsAt (List.replicate k Digit.three) = ⟨⟨0, 1⟩, ⟨1, 2 * (k : ℤ) + 1⟩⟩ := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', parentsAt_append_singleton, ih]
    simp only [Parents.step, Parents.current, Parents.combine]
    congr 1
    congr 1
    all_goals push_cast
    all_goals ring

theorem parents_two (k : ℕ) : parentsAt (List.replicate k Digit.two) = ⟨⟨(k : ℤ), (k : ℤ) + 1⟩, ⟨1, 1⟩⟩ := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', parentsAt_append_singleton, ih]
    simp only [Parents.step, Parents.current, Parents.combine]
    congr 1
    congr 1
    all_goals push_cast
    all_goals ring

theorem phase_three (k : ℕ) : phase (List.replicate k Digit.three) = 0 := by
  simp [phase, List.count_replicate]

theorem phase_two (k : ℕ) : phase (List.replicate k Digit.two) = 0 := by
  simp [phase, List.count_replicate]

theorem altD_three_true (k : ℕ) : altD (List.replicate k Digit.three) true =
    (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 5) := by
  ext <;> simp [altD, vP1, vP2, vQ1, vQ2, parents_three, W1Odd, phase_three, texV1Odd, texV1Even, texV2] <;> ring

theorem altD_three_false (k : ℕ) : altD (List.replicate k Digit.three) false =
    (1 - 2 * (k : ℤ), 2 * (k : ℤ) + 3) := by
  ext <;> simp [altD, vP1, vP2, vQ2, parents_three, W1Odd, phase_three, texV1Odd, texV2] <;> ring

theorem altE_three (k : ℕ) : altE (List.replicate k Digit.three) = (1, -(2 * (k : ℤ) + 3)) := by
  ext <;> simp [altE, aP2, aQ2, parents_three, offsetA]; ring

theorem altD_two_true (k : ℕ) : altD (List.replicate k Digit.two) true =
    (2 * (k : ℤ) + 3, 6 * (k : ℤ) + 5) := by
  ext <;> simp [altD, vP1, vP2, vQ1, vQ2, parents_two, W1Odd, phase_two, texV1Odd, texV1Even, texV2] <;> ring

theorem altD_two_false (k : ℕ) : altD (List.replicate k Digit.two) false =
    (2 * (k : ℤ) + 1, 6 * (k : ℤ) + 3) := by
  ext <;> simp [altD, vP1, vP2, vQ2, parents_two, W1Odd, phase_two, texV1Odd, texV2] <;> ring

theorem altE_two (k : ℕ) : altE (List.replicate k Digit.two) = (2 * (k : ℤ) + 1, -(2 * (k : ℤ) + 3)) := by
  ext <;> simp [altE, aP2, aQ2, parents_two, offsetA]; ring

/-! ### The tile properties at the base words (`TileProps`, from the families above) -/

theorem prod_eq' (a b c d : ℤ) (h1 : a = c) (h2 : b = d) : ((a, b) : ℤ × ℤ) = (c, d) := by
  rw [h1, h2]

theorem cur_odd_three (k : ℕ) : (parentsAt (List.replicate k Digit.three)).current .odd =
    ⟨1, 2 * (k : ℤ) + 2⟩ := by
  rw [parents_three]
  simp only [Parents.current, Parents.combine]
  congr 1
  all_goals ring

theorem cur_even_three (k : ℕ) : (parentsAt (List.replicate k Digit.three)).current .even =
    ⟨1, 2 * (k : ℤ) + 3⟩ := by
  rw [parents_three]
  simp only [Parents.current, Parents.combine]
  congr 1
  all_goals ring

theorem cur_odd_two (k : ℕ) : (parentsAt (List.replicate k Digit.two)).current .odd =
    ⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ := by
  rw [parents_two]
  simp only [Parents.current, Parents.combine]
  congr 1
  all_goals ring

theorem cur_even_two (k : ℕ) : (parentsAt (List.replicate k Digit.two)).current .even =
    ⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩ := by
  rw [parents_two]
  simp only [Parents.current, Parents.combine]
  congr 1
  

theorem tileTranslation_congr {o : PartialOdometer} {v1 v2 a2 v1' v2' a2' : ℤ × ℤ}
    (h : TileTranslation o v1 v2 a2) (h1 : v1 = v1') (h2 : v2 = v2') (h3 : a2 = a2') :
    TileTranslation o v1' v2' a2' := by
  subst h1 h2 h3
  exact h

theorem tileHalfTurn_congr {o : PartialOdometer} {v1 v2 a2 v1' v2' a2' : ℤ × ℤ}
    (h : TileHalfTurn o v1 v2 a2) (h1 : v1 = v1') (h2 : v2 = v2') (h3 : a2 = a2') :
    TileHalfTurn o v1' v2' a2' := by
  subst h1 h2 h3
  exact h

theorem altHalfTurn_congr {o : PartialOdometer} {D E D' E' : ℤ × ℤ} (h : AltHalfTurn o D E) (hD : D = D')
    (hE : E = E') : AltHalfTurn o D' E' := by
  subst hD hE
  exact h

/-- The base case of the tile properties, the empty word (`[]`: the odd child is `nstairN 3`, the even child
`stairF 3`; the alternate odd `paperNearStairAltTile 3`, the alternate even `paperStairAltTile 3`). -/
theorem tileProps_empty (O E aO aE : PartialOdometer) (hS : PaperBaseCond [] O E)
    (hA : PaperAltBaseCond [] aO aE) (hW : WeakProps [] O E) : TileProps [] O E aO aE := by
  obtain ⟨hOd, hOv, hEd, hEv⟩ := hS.1 rfl
  obtain ⟨haOd, haOv, haEd, haEv⟩ := hA.1 rfl
  have cO : (parentsAt []).current .odd = ⟨1, 2⟩ := by decide
  have cE : (parentsAt []).current .even = ⟨1, 3⟩ := by decide
  unfold WeakProps at hW
  dsimp only at hW
  rw [cO, cE] at hW
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hW
  unfold TileProps
  dsimp only
  rw [cO, cE]
  have aT : altD ([] : Word) true = (3, 5) := by
    have h := altD_three_true 0
    simpa using h
  have aF : altD ([] : Word) false = (1, 3) := by
    have h := altD_three_false 0
    simpa using h
  have aE' : altE ([] : Word) = (1, -3) := by
    have h := altE_three 0
    simpa using h
  rw [aT, aF, aE']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact nstairO_translation 0 le_rfl O hOd hOv hc1 hc2
  · exact stairE_translation 3 (by norm_num) E hEd hEv hc3 hc4
  · exact nstairO_halfturn 0 le_rfl O hOd hOv
  · exact stairE_halfturn 3 (by norm_num) E hEd hEv
  · exact altHalfTurn_congr (nsA_halfturn 3 (by norm_num) aO haOd haOv) (by decide) (by decide)
  · exact altHalfTurn_congr (stA_halfturn 3 (by norm_num) aE haEd haEv) (by decide) (by decide)


theorem lsc_congr {o : PartialOdometer} {v a v' a' : ℤ × ℤ} (h : LatticeSelfCompatible o v a) (hv : v = v')
    (ha : a = a') : LatticeSelfCompatible o v' a' := by
  subst hv ha
  exact h

/-- The base case of the tile properties, the words `3^k` (`k ≥ 1`): the odd child `ladderF (2k+2)`, the even child
`stairF (2k+3)`; the alternate odd `paperLadderAltTile (2k+2)`, the alternate even `paperStairAltTile (2k+3)`. -/
theorem tileProps_three (k : ℕ) (hk : 1 ≤ k) (O E aO aE : PartialOdometer)
    (hS : PaperBaseCond (List.replicate k Digit.three) O E)
    (hA : PaperAltBaseCond (List.replicate k Digit.three) aO aE)
    (hW : WeakProps (List.replicate k Digit.three) O E) :
    TileProps (List.replicate k Digit.three) O E aO aE := by
  obtain ⟨hOd, hOv, hEd, hEv⟩ := hS.2.1 k hk rfl
  obtain ⟨haOd, haOv, haEd, haEv⟩ := hA.2.1 k hk rfl
  unfold WeakProps at hW
  dsimp only at hW
  rw [cur_odd_three k, cur_even_three k] at hW
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hW
  unfold TileProps
  dsimp only
  rw [cur_odd_three k, cur_even_three k, altD_three_true k, altD_three_false k, altE_three k]
  have hk2 : (2 : ℤ) * (k : ℤ) + 2 ≥ 4 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ladO_translation (2 * (k : ℤ) + 2) (by omega) O hOd hOv hc1 hc2
  · exact stairE_translation (2 * (k : ℤ) + 3) (by omega) E hEd hEv hc3 hc4
  · exact ladO_halfturn (2 * (k : ℤ) + 2) (by omega) O hOd hOv
  · exact stairE_halfturn (2 * (k : ℤ) + 3) (by omega) E hEd hEv
  · exact altHalfTurn_congr (ladA_halfturn (2 * (k : ℤ) + 2) (by omega) aO haOd haOv)
      (prod_eq' _ _ _ _ (by ring) (by ring)) (prod_eq' _ _ _ _ (by ring) (by ring))
  · exact altHalfTurn_congr (stA_halfturn (2 * (k : ℤ) + 3) (by omega) aE haEd haEv)
      (prod_eq' _ _ _ _ (by ring) (by ring)) (prod_eq' _ _ _ _ (by ring) (by ring))

/-- The base case of the tile properties, the words `2^k` (`k ≥ 1`): the odd child `nstairN (2k+3)`, the even child
`nladderN (2k+2)`; the alternate odd `paperNearStairAltTile (2k+3)`, the alternate even `paperNearLadderAltTile (2k+2)`. -/
theorem tileProps_two (k : ℕ) (hk : 1 ≤ k) (O E aO aE : PartialOdometer)
    (hS : PaperBaseCond (List.replicate k Digit.two) O E)
    (hA : PaperAltBaseCond (List.replicate k Digit.two) aO aE)
    (hW : WeakProps (List.replicate k Digit.two) O E) :
    TileProps (List.replicate k Digit.two) O E aO aE := by
  obtain ⟨hOd, hOv, hEd, hEv⟩ := hS.2.2 k hk rfl
  obtain ⟨haOd, haOv, haEd, haEv⟩ := hA.2.2 k hk rfl
  unfold WeakProps at hW
  dsimp only at hW
  rw [cur_odd_two k, cur_even_two k] at hW
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hW
  unfold TileProps
  dsimp only
  rw [cur_odd_two k, cur_even_two k, altD_two_true k, altD_two_false k, altE_two k]
  have vO1 : texV1Odd (⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ : Fraction) = (2 * (k : ℤ) + 4, 2 * (k : ℤ) + 2) := by
    ext <;> simp [texV1Odd] <;> ring
  have vO2 : texV2 (⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ : Fraction) = (-1, 2 * (k : ℤ) + 3) := by
    ext <;> simp [texV2] ; ring
  have aO2 : offsetA ((k : ℤ) + 1) ((k : ℤ) + 2) true = ((k : ℤ) + 1, -((k : ℤ) + 2)) := rfl
  have vE1 : texV1Even (⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩ : Fraction) = (2 * (k : ℤ) + 2 + 1, 2 * (k : ℤ) + 2 - 1) := by
    ext <;> simp [texV1Even] <;> ring
  have vE2 : texV2 (⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩ : Fraction) = (-2, 2 * (2 * (k : ℤ) + 2)) := by
    ext <;> simp [texV2] ; ring
  have aE2 : offsetA (2 * (k : ℤ) + 1) (2 * (k : ℤ) + 3) true = (2 * (k : ℤ) + 2 - 1, -(2 * (k : ℤ) + 2 + 1)) := by
    ext <;> simp [offsetA] <;> ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tileTranslation_congr (nstairO_translation (k : ℤ) (by positivity) O hOd hOv
      (lsc_congr hc1 vO1 rfl) (lsc_congr hc2 vO2 aO2)) vO1.symm vO2.symm aO2.symm
  · exact tileTranslation_congr (nlE_translation (2 * (k : ℤ) + 2) (by omega) E hEd hEv
      (lsc_congr hc3 vE1 rfl) (lsc_congr hc4 vE2 aE2)) vE1.symm vE2.symm aE2.symm
  · exact tileHalfTurn_congr (nstairO_halfturn (k : ℤ) (by positivity) O hOd hOv) vO1.symm vO2.symm aO2.symm
  · exact tileHalfTurn_congr (nlE_halfturn (2 * (k : ℤ) + 2) (by omega) E hEd hEv) vE1.symm vE2.symm aE2.symm
  · exact altHalfTurn_congr (nsA_halfturn (2 * (k : ℤ) + 3) (by omega) aO haOd haOv)
      (prod_eq' _ _ _ _ (by ring) (by ring)) (prod_eq' _ _ _ _ (by ring) (by ring))
  · exact altHalfTurn_congr (nlA_halfturn (2 * (k : ℤ) + 2) (by omega) aE haEd haEv)
      (prod_eq' _ _ _ _ (by ring) (by ring)) (prod_eq' _ _ _ _ (by ring) (by ring))



/-- The base case of the tile properties (`lemma:tile-odometer-existence` (a), (b) at the base words, with the
paper base conditions and the lattice compatibilities of `WeakProps` as hypotheses). -/
theorem base_tileProps (w : Word) (hw : IsBase w) (O E aO aE : PartialOdometer) (hS : PaperBaseCond w O E)
    (hA : PaperAltBaseCond w aO aE) (hW : WeakProps w O E) : TileProps w O E aO aE := by
  rcases hw with rfl | h3 | h2
  · exact tileProps_empty O E aO aE hS hA hW
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.three := ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h3⟩⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact tileProps_empty O E aO aE hS hA hW
    · exact tileProps_three k hk O E aO aE hS hA hW
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.two := ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h2⟩⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact tileProps_empty O E aO aE hS hA hW
    · exact tileProps_two k hk O E aO aE hS hA hW

/-- The base odometers are normalised with slope `0` (`α = 0` on the tiles of the base families): the four odometers of a
base word, the standard odd and even and the alternate odd and even, each with `FirstTileNormal _ 0 b` for some `b`. -/
theorem base_slopes (w : Word) (hw : IsBase w) (O E aO aE : PartialOdometer) (hS : PaperBaseCond w O E)
    (hA : PaperAltBaseCond w aO aE) :
    (∃ b : ℤ, FirstTileNormal O 0 b) ∧ (∃ b : ℤ, FirstTileNormal E 0 b) ∧
      (∃ b : ℤ, FirstTileNormal aO 0 b) ∧ (∃ b : ℤ, FirstTileNormal aE 0 b) := by
  rcases hw with rfl | h3 | h2
  · obtain ⟨hOd, hOv, hEd, hEv⟩ := hS.1 rfl
    obtain ⟨haOd, haOv, haEd, haEv⟩ := hA.1 rfl
    exact ⟨⟨0, nstairO_firstNormal 0 le_rfl O hOd hOv⟩, ⟨0, stairE_firstNormal 3 (by norm_num) E hEd hEv⟩,
      ⟨0, nsA_normal 3 (by norm_num) aO haOd haOv⟩, ⟨0, stA_normal 3 (by norm_num) aE haEd haEv⟩⟩
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.three := ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h3⟩⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain ⟨hOd, hOv, hEd, hEv⟩ := hS.1 rfl
      obtain ⟨haOd, haOv, haEd, haEv⟩ := hA.1 rfl
      exact ⟨⟨0, nstairO_firstNormal 0 le_rfl O hOd hOv⟩, ⟨0, stairE_firstNormal 3 (by norm_num) E hEd hEv⟩,
        ⟨0, nsA_normal 3 (by norm_num) aO haOd haOv⟩, ⟨0, stA_normal 3 (by norm_num) aE haEd haEv⟩⟩
    · obtain ⟨hOd, hOv, hEd, hEv⟩ := hS.2.1 k hk rfl
      obtain ⟨haOd, haOv, haEd, haEv⟩ := hA.2.1 k hk rfl
      exact ⟨⟨0, ladO_firstNormal (2 * (k : ℤ) + 2) (by omega) O hOd hOv⟩,
        ⟨0, stairE_firstNormal (2 * (k : ℤ) + 3) (by omega) E hEd hEv⟩,
        ⟨0, ladA_normal (2 * (k : ℤ) + 2) (by omega) aO haOd haOv⟩,
        ⟨0, stA_normal (2 * (k : ℤ) + 3) (by omega) aE haEd haEv⟩⟩
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.two := ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h2⟩⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain ⟨hOd, hOv, hEd, hEv⟩ := hS.1 rfl
      obtain ⟨haOd, haOv, haEd, haEv⟩ := hA.1 rfl
      exact ⟨⟨0, nstairO_firstNormal 0 le_rfl O hOd hOv⟩, ⟨0, stairE_firstNormal 3 (by norm_num) E hEd hEv⟩,
        ⟨0, nsA_normal 3 (by norm_num) aO haOd haOv⟩, ⟨0, stA_normal 3 (by norm_num) aE haEd haEv⟩⟩
    · obtain ⟨hOd, hOv, hEd, hEv⟩ := hS.2.2 k hk rfl
      obtain ⟨haOd, haOv, haEd, haEv⟩ := hA.2.2 k hk rfl
      exact ⟨⟨0, nstairO_firstNormal (k : ℤ) (by positivity) O hOd hOv⟩,
        ⟨0, nlE_firstNormal (2 * (k : ℤ) + 2) (by omega) E hEd hEv⟩,
        ⟨0, nsA_normal (2 * (k : ℤ) + 3) (by omega) aO haOd haOv⟩,
        ⟨0, nlA_normal (2 * (k : ℤ) + 2) (by omega) aE haEd haEv⟩⟩

/-! ### The rotation identities at the base words (`RotProps`)

`h0 x = -(chooseTwo x_1 - (x_1 - x_2 - 1)^2/4)`; the identities are the value identities of `TileRotation` and
`AltRotation`, with all normalisations `α = β = 0`. -/

/-- The two floor squares of identity A have opposite parity, so their floors sum exactly. -/
theorem floor_pair_A (a b : ℤ) : 2 * ((a + b - 2) ^ 2 / 4 + (a - b - 1) ^ 2 / 4) = a ^ 2 + b ^ 2 - 3 * a - b + 2 := by
  rcases Int.emod_two_eq_zero_or_one (a + b) with h | h
  · obtain ⟨m, hm⟩ : ∃ m, a + b - 2 = 2 * m := ⟨(a + b - 2) / 2, by omega⟩
    obtain ⟨n, hn⟩ : ∃ n, a - b - 1 = 2 * n + 1 := ⟨(a - b - 2) / 2, by omega⟩
    rw [sq4_even _ m hm, sq4_odd _ n hn]
    obtain rfl : a = m + n + 2 := by omega
    obtain rfl : b = m - n := by omega
    ring
  · obtain ⟨m, hm⟩ : ∃ m, a + b - 2 = 2 * m + 1 := ⟨(a + b - 3) / 2, by omega⟩
    obtain ⟨n, hn⟩ : ∃ n, a - b - 1 = 2 * n := ⟨(a - b - 1) / 2, by omega⟩
    rw [sq4_odd _ m hm, sq4_even _ n hn]
    obtain rfl : a = m + n + 2 := by omega
    obtain rfl : b = m - n + 1 := by omega
    ring

/-- The value identity A: the stair `stairF d` at `(a, b)` against the near-one stair `nstairN d` at the rotated point
`(d + 1 - b, a + d - 1)` (read at `+(0,1)`), with the correction `-h0 (a, b)`. -/
theorem rotA_val (d a b : ℤ) :
    paperStairValue d (a, b) = paperNearStairValue d (d + 1 - b, a + d - 1) - h0 (a, b) := by
  have e1 : a + d - 1 - (d + 1 - b) = a + b - 2 := by ring
  have e2 : d - (a + d - 1) = 1 - a := by ring
  have hI : (if (d + 1 - b, a + d - 1) = ((0 : ℤ), d + 1) ∨ (d + 1 - b, a + d - 1) = (d + 1, d - 1) then (1 : ℤ) else 0) =
      (if (a, b) = ((0 : ℤ), (0 : ℤ)) ∨ (a, b) = ((2 : ℤ), d + 1) then (1 : ℤ) else 0) := by
    simp only [Prod.mk.injEq]
    split_ifs <;> omega
  have hmin : min (1 - a) 0 - min (a - 1) 0 = 1 - a := by omega
  have hF := floor_pair_A a b
  have hC := two_mul_chooseTwo a
  have hT := two_mul_T2 b
  unfold paperStairValue paperNearStairValue h0 centeredQuarterTurnCorrection
  dsimp only
  rw [e1, e2, hI]
  linarith

/-- The value identity B: the near-one stair `nstairN d` at `(a, b)` (read at `+(0,1)`) against the stair `stairF d` at
the rotated point `(d - b, a)`, with the correction `-h0 (a, b)`. -/
theorem rotB_val (d a b : ℤ) :
    paperNearStairValue d (a, b + 1) = paperStairValue d (d - b, a) - h0 (a, b) := by
  have hI : (if (a, b + 1) = ((0 : ℤ), d + 1) ∨ (a, b + 1) = (d + 1, d - 1) then (1 : ℤ) else 0) =
      (if (d - b, a) = ((0 : ℤ), (0 : ℤ)) ∨ (d - b, a) = ((2 : ℤ), d + 1) then (1 : ℤ) else 0) := by
    simp only [Prod.mk.injEq]
    split_ifs <;> omega
  have hsq : (b + 1 - a) ^ 2 = (a - b - 1) ^ 2 := by ring
  have hmin : min (d - (b + 1)) 0 = min (d - b - 1) 0 := by
    rw [show d - (b + 1) = d - b - 1 by ring]
  have hT := two_mul_T2 a
  have hC := two_mul_chooseTwo a
  unfold paperNearStairValue paperStairValue h0 centeredQuarterTurnCorrection
  dsimp only
  rw [hI, hsq, hmin]
  linarith

/-- The value identity C: the near-one ladder `nladderN d` at `(a, b)` (read at `+(0,1)`) against the ladder `ladderF d`
at the rotated point `(2d - b, a + 1)`, with `-h0 (a, b)`. -/
theorem rotC_val (d a b : ℤ) :
    paperNearLadderValue d (a, b + 1) = paperLadderValue d (2 * d - b, a + 1) - h0 (a, b) := by
  have hI : (if (a, b + 1) = ((-1 : ℤ), 2 * d + 1) ∨ (a, b + 1) = (d + 1, d - 1) ∨
        (b + 1 - a = d ∧ 0 < a ∧ a < d) then (1 : ℤ) else 0) =
      (if (2 * d - b, a + 1) = ((0 : ℤ), (0 : ℤ)) ∨ (2 * d - b, a + 1) = (d + 2, d + 2) ∨
        (2 * d - b + (a + 1) = d + 2 ∧ 1 < a + 1 ∧ a + 1 < d + 1) then (1 : ℤ) else 0) := by
    simp only [Prod.mk.injEq]
    split_ifs <;> omega
  have hM : min 0 (d - (b + 1)) + min 0 (2 * d - (b + 1)) + max ((b + 1 - a) - d) 0 -
      (min (2 * d - b - 1) 0 + min 0 (d + 1 - (2 * d - b)) + max (2 * d - b + (a + 1) - d - 2) 0) = -a := by
    omega
  have hsq : (b + 1 - a) ^ 2 = (a - b - 1) ^ 2 := by ring
  have hT := two_mul_T2 (a + 1)
  have hC := two_mul_chooseTwo a
  rw [pnlV, plV]
  unfold h0 centeredQuarterTurnCorrection
  dsimp only
  rw [hI, hsq]
  linarith

/-- The value identity D: the ladder `ladderF d` at `(a, b)` against the near-one ladder `nladderN d` at the rotated point
`(d + 1 - b, a + d - 1)` (read at `+(0,1)`), with `-h0 (a, b)`. -/
theorem rotD_val (d a b : ℤ) :
    paperLadderValue d (a, b) = paperNearLadderValue d (d + 1 - b, a + d - 1) - h0 (a, b) := by
  have hI : (if (a, b) = ((0 : ℤ), (0 : ℤ)) ∨ (a, b) = (d + 2, d + 2) ∨ (a + b = d + 2 ∧ 1 < b ∧ b < d + 1) then
        (1 : ℤ) else 0) =
      (if (d + 1 - b, a + d - 1) = ((-1 : ℤ), 2 * d + 1) ∨ (d + 1 - b, a + d - 1) = (d + 1, d - 1) ∨
        (a + d - 1 - (d + 1 - b) = d ∧ 0 < d + 1 - b ∧ d + 1 - b < d) then (1 : ℤ) else 0) := by
    simp only [Prod.mk.injEq]
    split_ifs <;> omega
  have hM : min (a - 1) 0 + min 0 (d + 1 - a) + max (a + b - d - 2) 0 -
      (min 0 (1 - a) + min 0 (2 * d - (a + d - 1)) + max (a + b - 2 - d) 0) = a - 1 := by
    omega
  have hF := floor_pair_A a b
  have hC := two_mul_chooseTwo a
  have hT := two_mul_T2 b
  have e1 : a + d - 1 - (d + 1 - b) = a + b - 2 := by ring
  have e2 : d - (a + d - 1) = 1 - a := by ring
  rw [plV, pnlV]
  unfold h0 centeredQuarterTurnCorrection
  dsimp only
  rw [hI, e1, e2]
  linarith

/-- The floor squares of two integers whose sum is odd: `4 (u^2/4 + v^2/4) = u^2 + v^2 - 1`. -/
theorem floor_pair (u v : ℤ) (h : (u + v) % 2 = 1) : 4 * (u ^ 2 / 4 + v ^ 2 / 4) = u ^ 2 + v ^ 2 - 1 := by
  rcases Int.emod_two_eq_zero_or_one u with hu | hu
  · obtain ⟨m, hm⟩ : ∃ m, u = 2 * m := ⟨u / 2, by omega⟩
    obtain ⟨n, hn⟩ : ∃ n, v = 2 * n + 1 := ⟨(v - 1) / 2, by omega⟩
    subst hm hn
    rw [sq4_even _ m rfl, sq4_odd _ n rfl]
    ring
  · obtain ⟨m, hm⟩ : ∃ m, u = 2 * m + 1 := ⟨(u - 1) / 2, by omega⟩
    obtain ⟨n, hn⟩ : ∃ n, v = 2 * n := ⟨v / 2, by omega⟩
    subst hm hn
    rw [sq4_odd _ m rfl, sq4_even _ n rfl]
    ring

/-- The value identity A1 (the odd alternate `[]`/`2^k` against the even alternate `3^k` family): the stair alternate
`stAlt (2k+3)` at `(a, b)` against the near-one stair alternate at the rotated point, with `γ = (k+1, k)`, `c0 = (k+1)^2`. -/
theorem rotA1_val (k a b : ℤ) :
    paperStairAltValue (2 * k + 3) (a, b) =
      paperNearStairAltValue (2 * k + 3) (2 * k + 3 - b, a + 2 * (2 * k + 3) - 3) - h0 (a, b) +
        ((k + 1) * a + k * b) + (k + 1) ^ 2 := by
  have hF := floor_pair (a + b + 2 * k) (a - b - 1) (by omega)
  have hT := two_mul_T2 b
  have hC := two_mul_chooseTwo a
  rw [pstA, pnsA]
  unfold h0 centeredQuarterTurnCorrection
  dsimp only
  have e1 : a + 2 * (2 * k + 3) - 3 - (2 * k + 3 - b) = a + b + 2 * k := by ring
  rw [e1]
  have hm23 : min 0 (2 * k + 3 - 2 + a) - min (2 * k + 3 - (a + 2 * (2 * k + 3) - 3) - 1) 0 = 2 * k + 3 - 2 + a := by
    omega
  have hc1 : min 0 (2 - a) = min (2 * (2 * k + 3) - 1 - (a + 2 * (2 * k + 3) - 3)) 0 := by omega
  have hc2 : max (a + b - 2) 0 = max (a + b + 2 * k - (2 * k + 3) + 1) 0 := by omega
  split_ifs <;> first | omega | linarith

/-- The value identity A2 (`x.aEven = stAlt`, `r.aOdd = nsAlt`, `cf = (d, 0)`, `γ = 0`, `c0 = 0`). -/
theorem rotA2_val (k a b : ℤ) :
    paperNearStairAltValue (2 * k + 3) (a, b + 1) = paperStairAltValue (2 * k + 3) (2 * k + 3 - b, a) - h0 (a, b) := by
  have hsq : (b + 1 - a) ^ 2 = (a - b - 1) ^ 2 := by ring
  have hT := two_mul_T2 a
  have hC := two_mul_chooseTwo a
  rw [pnsA, pstA]
  unfold h0 centeredQuarterTurnCorrection
  dsimp only
  rw [hsq]
  have hm : min (2 * k + 3 - (b + 1) - 1) 0 + min (2 * (2 * k + 3) - 1 - (b + 1)) 0 +
      max (b + 1 - a - (2 * k + 3) + 1) 0 -
      (min 0 (2 - (2 * k + 3 - b)) + min 0 (2 * k + 3 - 2 + (2 * k + 3 - b)) + max (2 * k + 3 - b + a - 2) 0) =
      -a := by
    omega
  split_ifs <;> first | omega | linarith

/-- The value identity A3 (`x.aOdd = ladAlt`, `r.aEven = nlAlt`, `cf = (2d-1, 2)`, `γ = (1, 0)`, `c0 = 1`), `d = 2k+2`. -/
theorem rotA3_val (k a b : ℤ) :
    paperNearLadderAltValue (2 * k + 2) (a, b + 1) =
      paperLadderAltValue (2 * k + 2) (2 * (2 * k + 2) - 2 - b, a + 1) - h0 (a, b) + a + 1 := by
  have hsq : (b + 1 - a) ^ 2 = (a - b - 1) ^ 2 := by ring
  have hT := two_mul_T2 (a + 1)
  have hC := two_mul_chooseTwo a
  rw [pnlA, pladA]
  unfold h0 centeredQuarterTurnCorrection
  dsimp only
  rw [hsq]
  have hm : min 0 (2 * k + 2 - (b + 1)) + min 0 (2 * (2 * k + 2) - 1 - (b + 1)) +
      max 0 (b + 1 - a - (2 * k + 2)) -
      (min 0 (2 * (2 * k + 2) - 2 - b) + min 0 (2 * k + 2 - (2 * (2 * k + 2) - 2 - b) - 1) +
        max (2 * (2 * k + 2) - 2 - b + (a + 1) - (2 * k + 2)) 0) = -a := by
    omega
  split_ifs <;> first | omega | linarith

/-- The value identity A4 (`x.aEven = nlAlt`, `r.aOdd = ladAlt`, `cf = (d+1, d-2)`, `γ = 0`, `c0 = 0`), `d = 2k+2`. -/
theorem rotA4_val (k a b : ℤ) :
    paperLadderAltValue (2 * k + 2) (a - 1, b - 1) =
      paperNearLadderAltValue (2 * k + 2) (2 * k + 2 + 1 - b, a + (2 * k + 2) - 1) - h0 (a, b) := by
  have e1 : a + (2 * k + 2) - 1 - (2 * k + 2 + 1 - b) = a + b - 2 := by ring
  have hF := floor_pair_A a b
  have hT := two_mul_T2 (b - 1)
  have hC := two_mul_chooseTwo a
  rw [pladA, pnlA]
  unfold h0 centeredQuarterTurnCorrection
  dsimp only
  rw [e1]
  have hm : min 0 (a - 1) + min 0 (2 * k + 2 - (a - 1) - 1) + max (a - 1 + (b - 1) - (2 * k + 2)) 0 -
      (min 0 (2 * k + 2 - (a + (2 * k + 2) - 1)) + min 0 (2 * (2 * k + 2) - 1 - (a + (2 * k + 2) - 1)) +
        max 0 (a + b - 2 - (2 * k + 2))) = a - 1 := by
    omega
  split_ifs <;> first | omega | linarith

/-! #### The rotation predicates of the base families -/

theorem tileRotation_congr {o oR : PartialOdometer} {v v' : ℤ × ℤ} (h : TileRotation o oR v) (hv : v = v') :
    TileRotation o oR v' := by
  subst hv
  exact h

theorem altRotation_congr {o oR : PartialOdometer} {cf cf' γ γ' : ℤ × ℤ} (h : AltRotation o oR cf γ) (hc : cf = cf')
    (hg : γ = γ') : AltRotation o oR cf' γ' := by
  subst hc hg
  exact h

/-- `TileRotation` at the stair (`o = nstairN`, `oR = stairF`, `v1 = (2k+4, 2k+2)`): the odd child of `2^k` and `[]`
against the even child of the swapped word. -/
theorem rotStd_A (k : ℤ) (hk : 0 ≤ k) (O E : PartialOdometer) (hOd : O.dom = nstairN (2 * k + 3))
    (hOv : ∀ x ∈ O.dom, O.val x = paperNearStairValue (2 * k + 3) (x + (0, 1)))
    (hEd : E.dom = stairF (2 * k + 3)) (hEv : ∀ x ∈ E.dom, E.val x = paperStairValue (2 * k + 3) x) :
    TileRotation O E (2 * k + 4, 2 * k + 2) := by
  refine ⟨0, 0, 0, 0, nstairO_firstNormal k hk O hOd hOv, stairE_firstNormal (2 * k + 3) (by omega) E hEd hEv, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxS : (a, b) ∈ stairF (2 * k + 3) := by
    rw [← hEd]
    exact hx
  have hmS : (2 * k + 4 - b, a + (2 * k + 2)) ∈ nstairF (2 * k + 3) :=
    (mem_nstairF_ab _ (by omega) _ _).2 (by
      have h := (mem_stairF_ab (2 * k + 3) (by omega) a b).1 hxS
      omega)
  have hyO : (2 * k + 4 - b, a + (2 * k + 2) - 1) ∈ O.dom := by
    rw [hOd, mem_nstairN_ab, show a + (2 * k + 2) - 1 + 1 = a + (2 * k + 2) by ring]
    exact hmS
  have ey : mulI ((a, b) : Site) + (2 * k + 4, 2 * k + 2) - ((0 : ℤ), (1 : ℤ)) =
      (2 * k + 4 - b, a + (2 * k + 2) - 1) := by
    ext <;> simp [mulI]; ring
  rw [ey]
  refine ⟨hyO, ?_⟩
  rw [normed_zero, normed_zero, hEv _ hx, hOv _ hyO,
    show (2 * k + 4 - b, a + (2 * k + 2) - 1) + ((0 : ℤ), (1 : ℤ)) = (2 * k + 3 + 1 - b, a + (2 * k + 3) - 1) by
      ext <;> simp <;> ring]
  exact rotA_val (2 * k + 3) a b

/-- `TileRotation` at the even stair (`o = stairF`, `oR = nstairN`, `v1 = (2k+3, 1)`). -/
theorem rotStd_B (k : ℤ) (hk : 0 ≤ k) (St NS : PartialOdometer) (hSd : St.dom = stairF (2 * k + 3))
    (hSv : ∀ x ∈ St.dom, St.val x = paperStairValue (2 * k + 3) x)
    (hNd : NS.dom = nstairN (2 * k + 3))
    (hNv : ∀ x ∈ NS.dom, NS.val x = paperNearStairValue (2 * k + 3) (x + (0, 1))) :
    TileRotation St NS (2 * k + 3, 1) := by
  refine ⟨0, 0, 0, 0, stairE_firstNormal (2 * k + 3) (by omega) St hSd hSv, nstairO_firstNormal k hk NS hNd hNv, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxN : (a, b + 1) ∈ nstairF (2 * k + 3) := by
    rw [← mem_nstairN_ab, ← hNd]
    exact hx
  have hyS : (2 * k + 3 - b, a) ∈ stairF (2 * k + 3) :=
    (mem_stairF_ab _ (by omega) _ _).2 (by
      have h := (mem_nstairF_ab _ (by omega) a (b + 1)).1 hxN
      omega)
  have hyO : (2 * k + 3 - b, a) ∈ St.dom := by
    rw [hSd]
    exact hyS
  have ey : mulI ((a, b) : Site) + (2 * k + 3, 1) - ((0 : ℤ), (1 : ℤ)) = (2 * k + 3 - b, a) := by
    ext <;> simp [mulI]; ring
  rw [ey]
  refine ⟨hyO, ?_⟩
  rw [normed_zero, normed_zero, hNv _ hx, hSv _ hyO,
    show (a, b) + ((0 : ℤ), (1 : ℤ)) = (a, b + 1) by ext <;> simp]
  exact rotB_val (2 * k + 3) a b

/-- `TileRotation` at the ladder (`o = ladderF`, `oR = nladderN`, `v1 = (4k+4, 2)`), `k ≥ 1`. -/
theorem rotStd_C (k : ℤ) (hk : 1 ≤ k) (L NL : PartialOdometer) (hLd : L.dom = ladderF (2 * k + 2))
    (hLv : ∀ x ∈ L.dom, L.val x = paperLadderValue (2 * k + 2) x)
    (hNd : NL.dom = nladderN (2 * k + 2))
    (hNv : ∀ x ∈ NL.dom, NL.val x = paperNearLadderValue (2 * k + 2) (x + (0, 1))) :
    TileRotation L NL (2 * (2 * k + 2), 2) := by
  refine ⟨0, 0, 0, 0, ladO_firstNormal (2 * k + 2) (by omega) L hLd hLv,
    nlE_firstNormal (2 * k + 2) (by omega) NL hNd hNv, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxN : (a, b + 1) ∈ nladderF (2 * k + 2) := by
    rw [← mem_nladderN_ab, ← hNd]
    exact hx
  have hyL : (2 * (2 * k + 2) - b, a + 1) ∈ ladderF (2 * k + 2) :=
    (mem_ladderF_ab _ (by omega) _ _).2 (by
      have h := (mem_nladderF_ab _ (by omega) a (b + 1)).1 hxN
      omega)
  have hyO : (2 * (2 * k + 2) - b, a + 1) ∈ L.dom := by
    rw [hLd]
    exact hyL
  have ey : mulI ((a, b) : Site) + (2 * (2 * k + 2), 2) - ((0 : ℤ), (1 : ℤ)) = (2 * (2 * k + 2) - b, a + 1) := by
    ext <;> simp [mulI] <;> ring
  rw [ey]
  refine ⟨hyO, ?_⟩
  rw [normed_zero, normed_zero, hNv _ hx, hLv _ hyO, show (a, b) + ((0 : ℤ), (1 : ℤ)) = (a, b + 1) by
    ext <;> simp]
  exact rotC_val (2 * k + 2) a b

/-- `TileRotation` at the near-one ladder (`o = nladderN`, `oR = ladderF`, `v1 = (d+1, d-1)`), `k ≥ 1`. -/
theorem rotStd_D (k : ℤ) (hk : 1 ≤ k) (NL L : PartialOdometer) (hNd : NL.dom = nladderN (2 * k + 2))
    (hNv : ∀ x ∈ NL.dom, NL.val x = paperNearLadderValue (2 * k + 2) (x + (0, 1)))
    (hLd : L.dom = ladderF (2 * k + 2)) (hLv : ∀ x ∈ L.dom, L.val x = paperLadderValue (2 * k + 2) x) :
    TileRotation NL L (2 * k + 2 + 1, 2 * k + 2 - 1) := by
  refine ⟨0, 0, 0, 0, nlE_firstNormal (2 * k + 2) (by omega) NL hNd hNv,
    ladO_firstNormal (2 * k + 2) (by omega) L hLd hLv, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxL : (a, b) ∈ ladderF (2 * k + 2) := by
    rw [← hLd]
    exact hx
  have hyN : (2 * k + 2 + 1 - b, a + (2 * k + 2) - 2) ∈ NL.dom := by
    rw [hNd, mem_nladderN_ab, show a + (2 * k + 2) - 2 + 1 = a + (2 * k + 2) - 1 by ring]
    exact (mem_nladderF_ab _ (by omega) _ _).2 (by
      have h := (mem_ladderF_ab _ (by omega) a b).1 hxL
      omega)
  have ey : mulI ((a, b) : Site) + (2 * k + 2 + 1, 2 * k + 2 - 1) - ((0 : ℤ), (1 : ℤ)) =
      (2 * k + 2 + 1 - b, a + (2 * k + 2) - 2) := by
    ext <;> simp [mulI] <;> ring
  rw [ey]
  refine ⟨hyN, ?_⟩
  rw [normed_zero, normed_zero, hLv _ hx, hNv _ hyN,
    show (2 * k + 2 + 1 - b, a + (2 * k + 2) - 2) + ((0 : ℤ), (1 : ℤ)) = (2 * k + 2 + 1 - b, a + (2 * k + 2) - 1) by
      ext <;> simp; ring]
  exact rotD_val (2 * k + 2) a b

set_option maxHeartbeats 400000 in
/-- `AltRotation` of the near-one stair alternate (`o = nsAlt (2k+3)`) against the stair alternate (`oR = stAlt`),
`cf = (2k+3, 4k+2)`, `γ = (k+1, k)`, `c0 = (k+1)^2` (the domain transport uses the disjunctive tile membership). -/
theorem rotAlt_A1 (k : ℤ) (hk : 0 ≤ k) (NS ST : PartialOdometer)
    (hNd : ∀ x : Site, x ∈ NS.dom ↔ x + (0, 1) ∈ paperNearStairAltTile (2 * k + 3))
    (hNv : ∀ x ∈ NS.dom, NS.val x = paperNearStairAltValue (2 * k + 3) (x + (0, 1)))
    (hSd : ∀ x : Site, x ∈ ST.dom ↔ x ∈ paperStairAltTile (2 * k + 3))
    (hSv : ∀ x ∈ ST.dom, ST.val x = paperStairAltValue (2 * k + 3) x) :
    AltRotation NS ST (2 * k + 3, 2 * (2 * k + 3) - 4) (k + 1, k) := by
  refine ⟨0, 0, 0, 0, (k + 1) ^ 2, nsA_normal (2 * k + 3) (by omega) NS hNd hNv,
    stA_normal (2 * k + 3) (by omega) ST hSd hSv, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxT : (a, b) ∈ paperStairAltTile (2 * k + 3) := (hSd _).1 hx
  have hyT : (2 * k + 3 - b, a + 2 * (2 * k + 3) - 3) ∈ paperNearStairAltTile (2 * k + 3) :=
    (mem_nsAlt _ _ _).2 (by
      have h := (mem_stAlt _ a b).1 hxT
      omega)
  have hyN : (2 * k + 3 - b, a + 2 * (2 * k + 3) - 4) ∈ NS.dom := by
    apply (hNd _).2
    rw [show ((2 * k + 3 - b, a + 2 * (2 * k + 3) - 4) : Site) + (0, 1) =
      (2 * k + 3 - b, a + 2 * (2 * k + 3) - 3) by ext <;> simp; ring]
    exact hyT
  have ey : mulI ((a, b) : Site) + (2 * k + 3, 2 * (2 * k + 3) - 4) = (2 * k + 3 - b, a + 2 * (2 * k + 3) - 4) := by
    ext <;> simp [mulI] <;> ring
  rw [ey]
  refine ⟨hyN, ?_⟩
  rw [normed_zero, normed_zero, hSv _ hx, hNv _ hyN, show (2 * k + 3 - b, a + 2 * (2 * k + 3) - 4) + ((0 : ℤ), (1 : ℤ)) =
    (2 * k + 3 - b, a + 2 * (2 * k + 3) - 3) by ext <;> simp; ring]
  have h := rotA1_val k a b
  simp only [dotS]
  linarith

set_option maxHeartbeats 400000 in
/-- `AltRotation` of the stair alternate (`o = stAlt`) against the near-one stair alternate (`oR = nsAlt`), `cf = (2k+3, 0)`,
`γ = 0`, `c0 = 0`. -/
theorem rotAlt_A2 (k : ℤ) (hk : 0 ≤ k) (ST NS : PartialOdometer)
    (hSd : ∀ x : Site, x ∈ ST.dom ↔ x ∈ paperStairAltTile (2 * k + 3))
    (hSv : ∀ x ∈ ST.dom, ST.val x = paperStairAltValue (2 * k + 3) x)
    (hNd : ∀ x : Site, x ∈ NS.dom ↔ x + (0, 1) ∈ paperNearStairAltTile (2 * k + 3))
    (hNv : ∀ x ∈ NS.dom, NS.val x = paperNearStairAltValue (2 * k + 3) (x + (0, 1))) :
    AltRotation ST NS (2 * k + 3, 0) (0, 0) := by
  refine ⟨0, 0, 0, 0, 0, stA_normal (2 * k + 3) (by omega) ST hSd hSv,
    nsA_normal (2 * k + 3) (by omega) NS hNd hNv, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxN : (a, b + 1) ∈ paperNearStairAltTile (2 * k + 3) := by
    have h := (hNd _).1 hx
    rwa [show ((a, b) : Site) + (0, 1) = (a, b + 1) by ext <;> simp] at h
  have hyS : (2 * k + 3 - b, a) ∈ paperStairAltTile (2 * k + 3) :=
    (mem_stAlt _ _ _).2 (by
      have h := (mem_nsAlt _ a (b + 1)).1 hxN
      omega)
  have hyO : (2 * k + 3 - b, a) ∈ ST.dom := (hSd _).2 hyS
  have ey : mulI ((a, b) : Site) + (2 * k + 3, 0) = (2 * k + 3 - b, a) := by
    ext <;> simp [mulI]; ring
  rw [ey]
  refine ⟨hyO, ?_⟩
  rw [normed_zero, normed_zero, hNv _ hx, hSv _ hyO, show ((a, b) : Site) + ((0 : ℤ), (1 : ℤ)) = (a, b + 1) by
    ext <;> simp]
  have h := rotA2_val k a b
  simp only [dotS, zero_mul, add_zero]
  linarith

set_option maxHeartbeats 400000 in
/-- `AltRotation` of the ladder alternate (`o = ladAlt`, read at `x - (1,1)`) against the near-one ladder alternate
(`oR = nlAlt`), `cf = (2d-1, 2)`, `γ = (1, 0)`, `c0 = 1`, `d = 2k+2`. -/
theorem rotAlt_A3 (k : ℤ) (hk : 1 ≤ k) (LA NLA : PartialOdometer)
    (hLd : ∀ x : Site, x ∈ LA.dom ↔ x - (1, 1) ∈ paperLadderAltTile (2 * k + 2))
    (hLv : ∀ x ∈ LA.dom, LA.val x = paperLadderAltValue (2 * k + 2) (x - (1, 1)))
    (hNd : ∀ x : Site, x ∈ NLA.dom ↔ x + (0, 1) ∈ paperNearLadderAltTile (2 * k + 2))
    (hNv : ∀ x ∈ NLA.dom, NLA.val x = paperNearLadderAltValue (2 * k + 2) (x + (0, 1))) :
    AltRotation LA NLA (2 * (2 * k + 2) - 1, 2) (1, 0) := by
  refine ⟨0, 0, 0, 0, 1, ladA_normal (2 * k + 2) (by omega) LA hLd hLv,
    nlA_normal (2 * k + 2) (by omega) NLA hNd hNv, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxN : (a, b + 1) ∈ paperNearLadderAltTile (2 * k + 2) := by
    have h := (hNd _).1 hx
    rwa [show ((a, b) : Site) + (0, 1) = (a, b + 1) by ext <;> simp] at h
  have hyL : (2 * (2 * k + 2) - 2 - b, a + 1) ∈ paperLadderAltTile (2 * k + 2) :=
    (mem_ladAlt _ _ _).2 (by
      have h := (mem_nlAlt _ a (b + 1)).1 hxN
      omega)
  have hyO : (2 * (2 * k + 2) - 1 - b, a + 2) ∈ LA.dom := by
    apply (hLd _).2
    rw [show ((2 * (2 * k + 2) - 1 - b, a + 2) : Site) - (1, 1) = (2 * (2 * k + 2) - 2 - b, a + 1) by
      ext <;> simp <;> ring]
    exact hyL
  have ey : mulI ((a, b) : Site) + (2 * (2 * k + 2) - 1, 2) = (2 * (2 * k + 2) - 1 - b, a + 2) := by
    ext <;> simp [mulI]; ring
  rw [ey]
  refine ⟨hyO, ?_⟩
  rw [normed_zero, normed_zero, hNv _ hx, show ((a, b) : Site) + ((0 : ℤ), (1 : ℤ)) = (a, b + 1) by
    ext <;> simp, hLv _ hyO, show ((2 * (2 * k + 2) - 1 - b, a + 2) : Site) - (1, 1) =
    (2 * (2 * k + 2) - 2 - b, a + 1) by ext <;> simp <;> ring]
  have h := rotA3_val k a b
  simp only [dotS, one_mul, zero_mul, add_zero]
  linarith

set_option maxHeartbeats 400000 in
/-- `AltRotation` of the near-one ladder alternate (`o = nlAlt`) against the ladder alternate (`oR = ladAlt`),
`cf = (d+1, d-2)`, `γ = 0`, `c0 = 0`, `d = 2k+2`. -/
theorem rotAlt_A4 (k : ℤ) (hk : 1 ≤ k) (NLA LA : PartialOdometer)
    (hNd : ∀ x : Site, x ∈ NLA.dom ↔ x + (0, 1) ∈ paperNearLadderAltTile (2 * k + 2))
    (hNv : ∀ x ∈ NLA.dom, NLA.val x = paperNearLadderAltValue (2 * k + 2) (x + (0, 1)))
    (hLd : ∀ x : Site, x ∈ LA.dom ↔ x - (1, 1) ∈ paperLadderAltTile (2 * k + 2))
    (hLv : ∀ x ∈ LA.dom, LA.val x = paperLadderAltValue (2 * k + 2) (x - (1, 1))) :
    AltRotation NLA LA (2 * k + 3, 2 * k) (0, 0) := by
  refine ⟨0, 0, 0, 0, 0, nlA_normal (2 * k + 2) (by omega) NLA hNd hNv,
    ladA_normal (2 * k + 2) (by omega) LA hLd hLv, ?_⟩
  rintro ⟨a, b⟩ hx
  have hxL : (a - 1, b - 1) ∈ paperLadderAltTile (2 * k + 2) := by
    have h := (hLd _).1 hx
    rwa [show ((a, b) : Site) - (1, 1) = (a - 1, b - 1) by ext <;> simp] at h
  have hyO : (2 * k + 3 - b, a + 2 * k) ∈ NLA.dom := by
    apply (hNd _).2
    rw [show ((2 * k + 3 - b, a + 2 * k) : Site) + ((0 : ℤ), (1 : ℤ)) = (2 * k + 3 - b, a + 2 * k + 1) by
      ext <;> simp]
    exact (mem_nlAlt _ _ _).2 (by
      have h := (mem_ladAlt _ _ _).1 hxL
      omega)
  have ey : mulI ((a, b) : Site) + (2 * k + 3, 2 * k) = (2 * k + 3 - b, a + 2 * k) := by
    ext <;> simp [mulI]; ring
  rw [ey]
  refine ⟨hyO, ?_⟩
  rw [normed_zero, normed_zero, hLv _ hx, show ((a, b) : Site) - (1, 1) = (a - 1, b - 1) by ext <;> simp,
    hNv _ hyO, show ((2 * k + 3 - b, a + 2 * k) : Site) + ((0 : ℤ), (1 : ℤ)) =
    (2 * k + 2 + 1 - b, a + (2 * k + 2) - 1) by ext <;> simp <;> ring]
  have h := rotA4_val k a b
  simp only [dotS, zero_mul, add_zero]
  linarith

/-! #### `RotProps` at the base words -/

theorem swapW_three_eq (k : ℕ) : swapW (List.replicate k Digit.three) = List.replicate k Digit.two := by
  unfold swapW
  rw [List.map_replicate]
  rfl

theorem swapW_two_eq (k : ℕ) : swapW (List.replicate k Digit.two) = List.replicate k Digit.three := by
  unfold swapW
  rw [List.map_replicate]
  rfl

theorem altCf_three_true_fst (k : ℕ) : (altCf (List.replicate k Digit.three) true).1 = (4 * (k : ℤ) + 3, 2) := by
  ext <;> simp [altCf, Parents.current, Parents.combine, vP2, W1Odd, phase_three, parents_three, texV1Odd, texV2] ; ring

theorem altCf_three_true_snd (k : ℕ) : (altCf (List.replicate k Digit.three) true).2 = (1, 0) := by
  ext <;> simp [altCf, Parents.current, Parents.combine, aP2, W1Odd, phase_three, parents_three, offsetA, mulI]

theorem altCf_three_false_fst (k : ℕ) : (altCf (List.replicate k Digit.three) false).1 = (2 * (k : ℤ) + 3, 0) := by
  ext <;> simp [altCf, vP1, vQ1, W1Odd, phase_three, parents_three, texV1Odd, texV1Even] ; ring

theorem altCf_three_false_snd (k : ℕ) : (altCf (List.replicate k Digit.three) false).2 = (0, 0) := by
  ext <;> simp [altCf, W1Odd, phase_three]

theorem altCf_two_true_fst (k : ℕ) : (altCf (List.replicate k Digit.two) true).1 = (2 * (k : ℤ) + 3, 4 * (k : ℤ) + 2) := by
  ext <;> simp [altCf, Parents.current, Parents.combine, vP2, W1Odd, phase_two, parents_two, texV1Odd, texV2] <;> ring

theorem altCf_two_true_snd (k : ℕ) : (altCf (List.replicate k Digit.two) true).2 = ((k : ℤ) + 1, (k : ℤ)) := by
  ext <;> simp [altCf, Parents.current, Parents.combine, aP2, W1Odd, phase_two, parents_two, offsetA, mulI]

theorem altCf_two_false_fst (k : ℕ) : (altCf (List.replicate k Digit.two) false).1 = (2 * (k : ℤ) + 3, 2 * (k : ℤ)) := by
  ext <;> simp [altCf, vP1, vQ1, W1Odd, phase_two, parents_two, texV1Odd, texV1Even] ; ring

theorem altCf_two_false_snd (k : ℕ) : (altCf (List.replicate k Digit.two) false).2 = (0, 0) := by
  ext <;> simp [altCf, W1Odd, phase_two]

/-- `RotProps` at the empty word: the families of `[]` (`nstairN 3`, `stairF 3`, `nsAlt 3`, `stAlt 3`). -/
theorem rotProps_empty (x r : JSlice) (hx : PaperBaseCond [] x.tOdd x.tEven ∧ PaperAltBaseCond [] x.aOdd x.aEven)
    (hr : PaperBaseCond [] r.tOdd r.tEven ∧ PaperAltBaseCond [] r.aOdd r.aEven) : RotProps [] x r := by
  obtain ⟨hOd, hOv, hEd, hEv⟩ := hx.1.1 rfl
  obtain ⟨haOd, haOv, haEd, haEv⟩ := hx.2.1 rfl
  obtain ⟨rOd, rOv, rEd, rEv⟩ := hr.1.1 rfl
  obtain ⟨raOd, raOv, raEd, raEv⟩ := hr.2.1 rfl
  have c1 : (parentsAt ([] : Word)).current .odd = ⟨1, 2⟩ := by decide
  have c2 : (parentsAt ([] : Word)).current .even = ⟨1, 3⟩ := by decide
  have a1 : (altCf ([] : Word) true).1 = (3, 2) := by simpa using altCf_three_true_fst 0
  have a2 : (altCf ([] : Word) true).2 = (1, 0) := by simpa using altCf_three_true_snd 0
  have a3 : (altCf ([] : Word) false).1 = (3, 0) := by simpa using altCf_three_false_fst 0
  have a4 : (altCf ([] : Word) false).2 = (0, 0) := by simpa using altCf_three_false_snd 0
  unfold RotProps
  rw [c1, c2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tileRotation_congr (rotStd_A 0 le_rfl x.tOdd r.tEven hOd hOv rEd rEv) (by decide)
  · exact tileRotation_congr (rotStd_B 0 le_rfl x.tEven r.tOdd hEd hEv rOd rOv) (by decide)
  · exact altRotation_congr (rotAlt_A1 0 le_rfl x.aOdd r.aEven haOd haOv raEd raEv)
      (by rw [a1]; decide) (by rw [a2]; decide)
  · exact altRotation_congr (rotAlt_A2 0 le_rfl x.aEven r.aOdd haEd haEv raOd raOv)
      (by simp [a3]) (by simp [a4])

/-- `RotProps` at the words `3^k`, `k ≥ 1`: `x` on `3^k` against `r` on `2^k`. -/
theorem rotProps_three (k : ℕ) (hk : 1 ≤ k) (x r : JSlice)
    (hx : PaperBaseCond (List.replicate k Digit.three) x.tOdd x.tEven ∧
      PaperAltBaseCond (List.replicate k Digit.three) x.aOdd x.aEven)
    (hr : PaperBaseCond (List.replicate k Digit.two) r.tOdd r.tEven ∧
      PaperAltBaseCond (List.replicate k Digit.two) r.aOdd r.aEven) :
    RotProps (List.replicate k Digit.three) x r := by
  obtain ⟨hOd, hOv, hEd, hEv⟩ := hx.1.2.1 k hk rfl
  obtain ⟨haOd, haOv, haEd, haEv⟩ := hx.2.2.1 k hk rfl
  obtain ⟨rOd, rOv, rEd, rEv⟩ := hr.1.2.2 k hk rfl
  obtain ⟨raOd, raOv, raEd, raEv⟩ := hr.2.2.2 k hk rfl
  have a1 := altCf_three_true_fst k
  have a2 := altCf_three_true_snd k
  have a3 := altCf_three_false_fst k
  have a4 := altCf_three_false_snd k
  unfold RotProps
  rw [cur_odd_three k, cur_even_three k]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tileRotation_congr (rotStd_C (k : ℤ) (by exact_mod_cast hk) x.tOdd r.tEven hOd hOv rEd rEv)
      (by ext <;> simp [texV1Odd])
  · exact tileRotation_congr (rotStd_B (k : ℤ) (by positivity) x.tEven r.tOdd hEd hEv rOd rOv)
      (by ext <;> simp [texV1Even])
  · exact altRotation_congr (rotAlt_A3 (k : ℤ) (by exact_mod_cast hk) x.aOdd r.aEven haOd haOv raEd raEv)
      (by rw [a1]; ext <;> simp ; ring) (by rw [a2])
  · exact altRotation_congr (rotAlt_A2 (k : ℤ) (by positivity) x.aEven r.aOdd haEd haEv raOd raOv)
      (by rw [a3]) (by rw [a4])

/-- `RotProps` at the words `2^k`, `k ≥ 1`: `x` on `2^k` against `r` on `3^k`. -/
theorem rotProps_two (k : ℕ) (hk : 1 ≤ k) (x r : JSlice)
    (hx : PaperBaseCond (List.replicate k Digit.two) x.tOdd x.tEven ∧
      PaperAltBaseCond (List.replicate k Digit.two) x.aOdd x.aEven)
    (hr : PaperBaseCond (List.replicate k Digit.three) r.tOdd r.tEven ∧
      PaperAltBaseCond (List.replicate k Digit.three) r.aOdd r.aEven) :
    RotProps (List.replicate k Digit.two) x r := by
  obtain ⟨hOd, hOv, hEd, hEv⟩ := hx.1.2.2 k hk rfl
  obtain ⟨haOd, haOv, haEd, haEv⟩ := hx.2.2.2 k hk rfl
  obtain ⟨rOd, rOv, rEd, rEv⟩ := hr.1.2.1 k hk rfl
  obtain ⟨raOd, raOv, raEd, raEv⟩ := hr.2.2.1 k hk rfl
  unfold RotProps
  rw [cur_odd_two k, cur_even_two k]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tileRotation_congr (rotStd_A (k : ℤ) (by positivity) x.tOdd r.tEven hOd hOv rEd rEv)
      (by ext <;> simp [texV1Odd] <;> ring)
  · exact tileRotation_congr (rotStd_D (k : ℤ) (by exact_mod_cast hk) x.tEven r.tOdd hEd hEv rOd rOv)
      (by ext <;> simp [texV1Even] <;> ring)
  · exact altRotation_congr (rotAlt_A1 (k : ℤ) (by positivity) x.aOdd r.aEven haOd haOv raEd raEv)
      (by rw [altCf_two_true_fst k]; ext <;> simp ; ring) (by rw [altCf_two_true_snd k])
  · exact altRotation_congr (rotAlt_A4 (k : ℤ) (by exact_mod_cast hk) x.aEven r.aOdd haEd haEv raOd raOv)
      (by simp [altCf_two_false_fst k]) (by simp [altCf_two_false_snd k])

/-- The rotation of the base words (`RotProps` at `w`, with the paper base conditions of the two slices). -/
theorem base_rotProps (w : Word) (hw : IsBase w) (x r : JSlice)
    (hx : PaperBaseCond w x.tOdd x.tEven ∧ PaperAltBaseCond w x.aOdd x.aEven)
    (hr : PaperBaseCond (swapW w) r.tOdd r.tEven ∧ PaperAltBaseCond (swapW w) r.aOdd r.aEven) :
    RotProps w x r := by
  rcases hw with rfl | h3 | h2
  · exact rotProps_empty x r hx hr
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.three := ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h3⟩⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact rotProps_empty x r hx hr
    · rw [swapW_three_eq k] at hr
      exact rotProps_three k hk x r hx hr
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.two := ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h2⟩⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact rotProps_empty x r hx hr
    · rw [swapW_two_eq k] at hr
      exact rotProps_two k hk x r hx hr

end FLatticePaper.Tiles.BaseTileProps
