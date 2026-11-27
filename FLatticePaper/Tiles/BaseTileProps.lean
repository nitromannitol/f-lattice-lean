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

end FLatticePaper.Tiles.BaseTileProps
