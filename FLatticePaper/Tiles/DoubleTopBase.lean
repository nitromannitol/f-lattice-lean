import FLatticePaper.Tiles.BaseHmTwoEven
import FLatticePaper.Tiles.DoubleBottomBase
import FLatticePaper.Tiles.BaseHmTwoOddOdo

/-! # The base fact of the double case for the top side (`DoubleTopBaseInput`)

The top string of the even base tile of `2^j` is the reversed horizontal string of the even child, anchored at `posE j 0`
(`anchor_hm_even`). Its tiles are `zero` at `(-1, 4j+2)`, `one` at `(1, 4j+3)` and `oneD` at `(t, t+4j+2)`, `2 ≤ t ≤ 2j+1`
(`BaseHmTwoEven`). The base odometer `E` of `2^j` equals, on this string, the last stem `O'` (the odd piece of `2^{j-1}`)
shifted by `(-1, 2j+3)` with affine factor `(j+1, -(j+2))`, and the enlarged piece at `(2j+1, 6j+3)` with affine factor
`(2j, -(2j+2))`. -/

namespace FLatticePaper.Tiles.DoubleTopBase

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.BaseHmTwoEven FLatticePaper.Tiles.BaseHpNearEven FLatticePaper.Tiles.BaseHmTwoOdd
open FLatticePaper.Tiles.Standard (nstairN nstairF nladderN nladderF oneTile)
open FLatticePaper.Tiles.DoubleBottomBase (mem_nstairN_iff mem_nladderN_iff pbc_odd)
open FLatticePaper.Tiles.JointFamily (enlOdo)
open FLatticePaper.Tiles.BaseTileProps
open FLatticePaper.Tiles.BaseHmTwoOddOdo (sq_div4 pv_gen)

/-- The top string of the even base tile of `2^k` as a union of its enlarged tiles. -/
theorem top_mem (k : ℕ) (x : GInt) :
    x ∈ placedSites (sideString (hWordOf (List.replicate k Digit.two) true)
        (vWordOf (List.replicate k Digit.two) true) 0 .hMinus) ↔
      ∃ t : ℕ, t < 2 * k + 2 ∧ ∃ u ∈ tileShape (hTileAt (lettersOf (wEv k) true) t), u + posE k t = x := by
  have h0 : (0 : GInt) = (0, 0) := rfl
  rw [hWordOf_two_true, h0]
  unfold sideString
  rw [anchor_hm_even k]
  have hl : lettersOf (wEv k).reverse false = lettersOf (wEv k) true := rfl
  rw [hRevStringAt_eq_map (wEv k).reverse (posE k 0) (posE k) rfl (fun j hj => by
    rw [List.length_reverse, wEv_length] at hj
    exact posE_succ k j (by omega))]
  rw [hl, List.length_reverse, wEv_length]
  unfold placedSites
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨t, ⟨i, hi, rfl⟩, hx⟩
    refine ⟨i, hi, ?_⟩
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨u, hu, rfl⟩
  · rintro ⟨i, hi, u, hu, rfl⟩
    refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
    exact ⟨u, hu, rfl⟩

theorem posE_sE (j : ℕ) (hj : 1 ≤ j) :
    posE j (2 * j + 1) = (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3) := by
  rw [posE_pos j (2 * j + 1) (by omega)]
  ext <;> ((try simp); (try ring))

theorem top_sE_mem (j : ℕ) (hj : 1 ≤ j) :
    ((2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3) : GInt) ∈
      placedSites (sideString (hWordOf (List.replicate j Digit.two) true)
        (vWordOf (List.replicate j Digit.two) true) 0 .hMinus) := by
  rw [top_mem]
  refine ⟨2 * j + 1, by omega, (0, 0), ?_, ?_⟩
  · rw [tileE_D j (2 * j + 1) (by omega) le_rfl]
    simp [tileShape]
  · rw [posE_sE j hj]
    simp

theorem top_cov (j : ℕ) (hj : 1 ≤ j) (x : GInt)
    (hx : x ∈ placedSites (sideString (hWordOf (List.replicate j Digit.two) true)
        (vWordOf (List.replicate j Digit.two) true) 0 .hMinus)) :
    x - ((-1 : ℤ), 2 * (j : ℤ) + 3) ∈ nstairN (2 * (j : ℤ) + 1) ∨
      x - (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3) ∈ tileShape ZTile.oneD := by
  obtain ⟨t, ht, u, hu, rfl⟩ := (top_mem j _).1 hx
  obtain ⟨u1, u2⟩ := u
  rcases (show t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t ≤ 2 * j) ∨ t = 2 * j + 1 by omega) with rfl | rfl | ⟨h1, h2⟩ | rfl
  · left
    rw [tileE_zero] at hu
    rw [posE_zero, mem_nstairN_iff]
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    simp only [nstairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk_add_mk, Prod.mk_sub_mk]
    omega
  · left
    rw [tileE_one] at hu
    rw [posE_pos j 1 le_rfl, mem_nstairN_iff]
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    simp only [nstairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk_add_mk, Prod.mk_sub_mk]
    omega
  · left
    rw [tileE_D j t h1 (by omega)] at hu
    rw [posE_pos j t (by omega), mem_nstairN_iff]
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    simp only [nstairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk_add_mk, Prod.mk_sub_mk]
    omega
  · right
    rw [tileE_D j (2 * j + 1) (by omega) le_rfl] at hu
    rw [posE_sE j hj, show ((u1, u2) + (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3) - (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3) : GInt) =
      (u1, u2) by simp]
    exact hu

theorem top_Edom (j : ℕ) (hj : 1 ≤ j) (x : GInt)
    (hx : x ∈ placedSites (sideString (hWordOf (List.replicate j Digit.two) true)
        (vWordOf (List.replicate j Digit.two) true) 0 .hMinus)) :
    x ∈ nladderN (2 * (j : ℤ) + 2) := by
  obtain ⟨t, ht, u, hu, rfl⟩ := (top_mem j _).1 hx
  obtain ⟨u1, u2⟩ := u
  rw [mem_nladderN_iff]
  rcases (show t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t ≤ 2 * j + 1) by omega) with rfl | rfl | ⟨h1, h2⟩
  · rw [tileE_zero] at hu
    rw [posE_zero]
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    simp only [nladderF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk_add_mk, add_zero]
    omega
  · rw [tileE_one] at hu
    rw [posE_pos j 1 le_rfl]
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    simp only [nladderF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk_add_mk, add_zero]
    omega
  · rw [tileE_D j t h1 (by omega)] at hu
    rw [posE_pos j t (by omega)]
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    simp only [nladderF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk_add_mk, add_zero]
    omega

theorem top_J_mem (j : ℕ) (hj : 1 ≤ j) :
    ((-1 : ℤ), 4 * (j : ℤ) + 1) ∈ nladderN (2 * (j : ℤ) + 2) := by
  rw [mem_nladderN_iff]
  simp only [nladderF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk_add_mk, add_zero]
  omega

theorem top_c3 (j : ℕ) (hj : 1 ≤ j) (u : GInt) (hu : u ∈ tileShape ZTile.oneD) :
    paperNearLadderValue (2 * (j : ℤ) + 2) (u + posE j (2 * j + 1) + (0, 1)) =
      zTileOdo ZTile.oneD u + ptDot (2 * (j : ℤ), -(2 * (j : ℤ) + 2)) u + (-(4 * (j : ℤ) ^ 2 + 6 * (j : ℤ) + 1) - 2 * (2 * (j : ℤ) + 1)) := by
  rw [evenE_D j (2 * j + 1) (by omega) (by omega) le_rfl u hu, aE_pos j (2 * j + 1) (by omega) le_rfl, cE,
    if_neg (show ¬ (2 * j + 1 = 0) by omega)]
  push_cast
  ring

theorem sq_shift (B c : ℤ) : (B + 2 * c) ^ 2 / 4 = B ^ 2 / 4 + c * B + c ^ 2 := by
  rw [show (B + 2 * c) ^ 2 = B ^ 2 + (c * B + c ^ 2) * 4 by ring, Int.add_mul_ediv_right _ _ (by norm_num)]
  ring

theorem pnl_shift (d x1 x2 B c m I : ℤ) (hn : x2 - x1 = B + 2 * c)
    (hm : min 0 (d - x2) + min 0 (2 * d - x2) + max (x2 - x1 - d) 0 = m)
    (hI : (if (x1, x2) = (-1, 2 * d + 1) ∨ (x1, x2) = (d + 1, d - 1) ∨ (x2 - x1 = d ∧ 0 < x1 ∧ x1 < d) then
      (1 : ℤ) else 0) = I) :
    paperNearLadderValue d (x1, x2) = -(B ^ 2 / 4 + c * B + c ^ 2) + m + I := by
  have hsq : (x2 - x1) ^ 2 / 4 = B ^ 2 / 4 + c * B + c ^ 2 := by
    rw [hn]; exact sq_shift B c
  rw [pnlV, hsq, hI, ← hm]
  ring

theorem pv_shift (d x1 x2 B m I : ℤ) (hn : x2 - x1 = B) (hm : min (d - x2) 0 = m)
    (hI : (if (x1, x2) = (0, d + 1) ∨ (x1, x2) = (d + 1, d - 1) then (1 : ℤ) else 0) = I) :
    paperNearStairValue d (x1, x2) = -(B ^ 2 / 4) + m + I := by
  unfold paperNearStairValue
  dsimp only
  rw [hn, hI, ← hm]

theorem pnl_gen (d x1 x2 q e m I : ℤ) (he : e = 0 ∨ e = 1) (hn : x2 - x1 = 2 * q + e)
    (hm : min 0 (d - x2) + min 0 (2 * d - x2) + max (x2 - x1 - d) 0 = m)
    (hI : (if (x1, x2) = (-1, 2 * d + 1) ∨ (x1, x2) = (d + 1, d - 1) ∨ (x2 - x1 = d ∧ 0 < x1 ∧ x1 < d) then
      (1 : ℤ) else 0) = I) :
    paperNearLadderValue d (x1, x2) = -(q * q + e * q) + m + I := by
  rw [pnlV, sq_div4 (x2 - x1) q e he hn, hI, ← hm]
  ring

/-- The stem identity on the zero tile of the top string. -/
theorem c1_zero (j : ℕ) (hj : 1 ≤ j) (u1 u2 : ℤ) (hb1 : 0 ≤ u1) (hb1' : u1 ≤ 1) (hb2 : 0 ≤ u2) (hb2' : u2 ≤ 2) :
    paperNearLadderValue (2 * (j : ℤ) + 2) (u1 - 1, u2 + 4 * (j : ℤ) + 3) =
      paperNearStairValue (2 * (j : ℤ) + 1) (u1, u2 + 2 * (j : ℤ)) +
        dotS ((j : ℤ) + 1, -((j : ℤ) + 2)) (u1 - 1, u2 + 4 * (j : ℤ) + 2) + ((j : ℤ) + 1) * ((j : ℤ) + 2) := by
  have hj' : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  have hm : min 0 (2 * (j : ℤ) + 2 - (u2 + 4 * (j : ℤ) + 3)) +
      min 0 (2 * (2 * (j : ℤ) + 2) - (u2 + 4 * (j : ℤ) + 3)) +
      max (u2 + 4 * (j : ℤ) + 3 - (u1 - 1) - (2 * (j : ℤ) + 2)) 0 = 1 - u1 + min 0 (1 - u2) := by
    rw [min_eq_right (show 2 * (j : ℤ) + 2 - (u2 + 4 * (j : ℤ) + 3) ≤ 0 by omega),
      max_eq_left (show 0 ≤ u2 + 4 * (j : ℤ) + 3 - (u1 - 1) - (2 * (j : ℤ) + 2) by omega),
      show 2 * (2 * (j : ℤ) + 2) - (u2 + 4 * (j : ℤ) + 3) = 1 - u2 by ring]
    ring
  have hI : (if (u1 - 1, u2 + 4 * (j : ℤ) + 3) = (-1, 2 * (2 * (j : ℤ) + 2) + 1) ∨
      (u1 - 1, u2 + 4 * (j : ℤ) + 3) = (2 * (j : ℤ) + 2 + 1, 2 * (j : ℤ) + 2 - 1) ∨
      (u2 + 4 * (j : ℤ) + 3 - (u1 - 1) = 2 * (j : ℤ) + 2 ∧ 0 < u1 - 1 ∧ u1 - 1 < 2 * (j : ℤ) + 2) then
      (1 : ℤ) else 0) = (if u1 = 0 ∧ u2 = 2 then 1 else 0) := by
    split_ifs <;> first | omega | (simp only [Prod.mk.injEq] at *; try omega)
  have hE := pnl_shift (2 * (j : ℤ) + 2) (u1 - 1) (u2 + 4 * (j : ℤ) + 3) (u2 + 2 * (j : ℤ) - u1)
    ((j : ℤ) + 2) _ _ (by ring) hm hI
  have hm' : min (2 * (j : ℤ) + 1 - (u2 + 2 * (j : ℤ))) 0 = min 0 (1 - u2) := by
    rw [show 2 * (j : ℤ) + 1 - (u2 + 2 * (j : ℤ)) = 1 - u2 by ring, min_comm]
  have hI' : (if (u1, u2 + 2 * (j : ℤ)) = (0, 2 * (j : ℤ) + 1 + 1) ∨
      (u1, u2 + 2 * (j : ℤ)) = (2 * (j : ℤ) + 1 + 1, 2 * (j : ℤ) + 1 - 1) then (1 : ℤ) else 0) =
      (if u1 = 0 ∧ u2 = 2 then 1 else 0) := by
    split_ifs <;> first | omega | (simp only [Prod.mk.injEq] at *; try omega)
  have hS := pv_shift (2 * (j : ℤ) + 1) u1 (u2 + 2 * (j : ℤ)) (u2 + 2 * (j : ℤ) - u1) _ _ (by ring) hm' hI'
  rw [hE, hS]
  unfold dotS
  ring

/-- The stem identity on the one tile of the top string. -/
theorem c1_one (j : ℕ) (hj : 1 ≤ j) (u1 u2 : ℤ) (hb1 : 0 ≤ u1) (hb1' : u1 ≤ 1) (hb2 : 0 ≤ u2) (hb2' : u2 ≤ 1) :
    paperNearLadderValue (2 * (j : ℤ) + 2) (u1 + 1, u2 + 4 * (j : ℤ) + 4) =
      paperNearStairValue (2 * (j : ℤ) + 1) (u1 + 2, u2 + 2 * (j : ℤ) + 1) +
        dotS ((j : ℤ) + 1, -((j : ℤ) + 2)) (u1 + 1, u2 + 4 * (j : ℤ) + 3) + ((j : ℤ) + 1) * ((j : ℤ) + 2) := by
  have hj' : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  have hm : min 0 (2 * (j : ℤ) + 2 - (u2 + 4 * (j : ℤ) + 4)) +
      min 0 (2 * (2 * (j : ℤ) + 2) - (u2 + 4 * (j : ℤ) + 4)) +
      max (u2 + 4 * (j : ℤ) + 4 - (u1 + 1) - (2 * (j : ℤ) + 2)) 0 = -1 - u1 + min 0 (-u2) := by
    rw [min_eq_right (show 2 * (j : ℤ) + 2 - (u2 + 4 * (j : ℤ) + 4) ≤ 0 by omega),
      max_eq_left (show 0 ≤ u2 + 4 * (j : ℤ) + 4 - (u1 + 1) - (2 * (j : ℤ) + 2) by omega),
      show 2 * (2 * (j : ℤ) + 2) - (u2 + 4 * (j : ℤ) + 4) = -u2 by ring]
    ring
  have hI : (if (u1 + 1, u2 + 4 * (j : ℤ) + 4) = (-1, 2 * (2 * (j : ℤ) + 2) + 1) ∨
      (u1 + 1, u2 + 4 * (j : ℤ) + 4) = (2 * (j : ℤ) + 2 + 1, 2 * (j : ℤ) + 2 - 1) ∨
      (u2 + 4 * (j : ℤ) + 4 - (u1 + 1) = 2 * (j : ℤ) + 2 ∧ 0 < u1 + 1 ∧ u1 + 1 < 2 * (j : ℤ) + 2) then
      (1 : ℤ) else 0) = 0 := by
    split_ifs <;> first | omega | (simp only [Prod.mk.injEq] at *; try omega)
  have hE := pnl_shift (2 * (j : ℤ) + 2) (u1 + 1) (u2 + 4 * (j : ℤ) + 4) (u2 + 2 * (j : ℤ) - u1 - 1)
    ((j : ℤ) + 2) _ 0 (by ring) hm hI
  have hm' : min (2 * (j : ℤ) + 1 - (u2 + 2 * (j : ℤ) + 1)) 0 = min 0 (-u2) := by
    rw [show 2 * (j : ℤ) + 1 - (u2 + 2 * (j : ℤ) + 1) = -u2 by ring, min_comm]
  have hI' : (if (u1 + 2, u2 + 2 * (j : ℤ) + 1) = (0, 2 * (j : ℤ) + 1 + 1) ∨
      (u1 + 2, u2 + 2 * (j : ℤ) + 1) = (2 * (j : ℤ) + 1 + 1, 2 * (j : ℤ) + 1 - 1) then (1 : ℤ) else 0) = 0 := by
    split_ifs <;> first | omega | (simp only [Prod.mk.injEq] at *; try omega)
  have hS := pv_shift (2 * (j : ℤ) + 1) (u1 + 2) (u2 + 2 * (j : ℤ) + 1) (u2 + 2 * (j : ℤ) - u1 - 1) _ 0
    (by ring) hm' hI'
  rw [hE, hS]
  unfold dotS
  ring

/-- The stem identity on the middle tiles `2 ≤ t ≤ 2j+1` of the top string. -/
theorem c1_mid (j : ℕ) (hj : 1 ≤ j) (t u1 u2 : ℤ) (ht2 : 2 ≤ t) (ht : t ≤ 2 * (j : ℤ) + 1)
    (hb1 : -1 ≤ u1) (hb1' : u1 ≤ 1) (hb2 : -1 ≤ u2) (hb2' : u2 ≤ 1) :
    paperNearLadderValue (2 * (j : ℤ) + 2) (u1 + t, u2 + t + 4 * (j : ℤ) + 3) =
      paperNearStairValue (2 * (j : ℤ) + 1) (u1 + t + 1, u2 + t + 2 * (j : ℤ)) +
        dotS ((j : ℤ) + 1, -((j : ℤ) + 2)) (u1 + t, u2 + t + 4 * (j : ℤ) + 2) + ((j : ℤ) + 1) * ((j : ℤ) + 2) := by
  have hj' : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  have hm : min 0 (2 * (j : ℤ) + 2 - (u2 + t + 4 * (j : ℤ) + 3)) +
      min 0 (2 * (2 * (j : ℤ) + 2) - (u2 + t + 4 * (j : ℤ) + 3)) +
      max (u2 + t + 4 * (j : ℤ) + 3 - (u1 + t) - (2 * (j : ℤ) + 2)) 0 = 1 - u1 - u2 - 2 * t := by
    rw [min_eq_right (show 2 * (j : ℤ) + 2 - (u2 + t + 4 * (j : ℤ) + 3) ≤ 0 by omega),
      min_eq_right (show 2 * (2 * (j : ℤ) + 2) - (u2 + t + 4 * (j : ℤ) + 3) ≤ 0 by omega),
      max_eq_left (show 0 ≤ u2 + t + 4 * (j : ℤ) + 3 - (u1 + t) - (2 * (j : ℤ) + 2) by omega)]
    ring
  have hI : (if (u1 + t, u2 + t + 4 * (j : ℤ) + 3) = (-1, 2 * (2 * (j : ℤ) + 2) + 1) ∨
      (u1 + t, u2 + t + 4 * (j : ℤ) + 3) = (2 * (j : ℤ) + 2 + 1, 2 * (j : ℤ) + 2 - 1) ∨
      (u2 + t + 4 * (j : ℤ) + 3 - (u1 + t) = 2 * (j : ℤ) + 2 ∧ 0 < u1 + t ∧ u1 + t < 2 * (j : ℤ) + 2) then
      (1 : ℤ) else 0) = 0 := by
    split_ifs <;> first | omega | (simp only [Prod.mk.injEq] at *; try omega)
  have hE := pnl_shift (2 * (j : ℤ) + 2) (u1 + t) (u2 + t + 4 * (j : ℤ) + 3) (u2 + 2 * (j : ℤ) - u1 - 1)
    ((j : ℤ) + 2) _ 0 (by ring) hm hI
  have hm' : min (2 * (j : ℤ) + 1 - (u2 + t + 2 * (j : ℤ))) 0 = 1 - u2 - t := by
    rw [show 2 * (j : ℤ) + 1 - (u2 + t + 2 * (j : ℤ)) = 1 - u2 - t by ring]
    exact min_eq_left (by omega)
  have hI' : (if (u1 + t + 1, u2 + t + 2 * (j : ℤ)) = (0, 2 * (j : ℤ) + 1 + 1) ∨
      (u1 + t + 1, u2 + t + 2 * (j : ℤ)) = (2 * (j : ℤ) + 1 + 1, 2 * (j : ℤ) + 1 - 1) then (1 : ℤ) else 0) = 0 := by
    split_ifs <;> first | omega | (simp only [Prod.mk.injEq] at *; try omega)
  have hS := pv_shift (2 * (j : ℤ) + 1) (u1 + t + 1) (u2 + t + 2 * (j : ℤ)) (u2 + 2 * (j : ℤ) - u1 - 1) _ 0
    (by ring) hm' hI'
  rw [hE, hS]
  unfold dotS
  ring

/-- The `J` clause of the top string: the value of `E` at `J = (-1, 4j+1)`, which lies on the stem copy but not on `T`. -/
theorem top_J_val (j : ℕ) (hj : 1 ≤ j) :
    paperNearLadderValue (2 * (j : ℤ) + 2) (-1, 4 * (j : ℤ) + 2) =
      paperNearStairValue (2 * (j : ℤ) + 1) ((0 : ℤ), 2 * (j : ℤ) - 1) +
        dotS ((j : ℤ) + 1, -((j : ℤ) + 2)) (-1, 4 * (j : ℤ) + 1) + ((j : ℤ) + 1) * ((j : ℤ) + 2) := by
  have hj' : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  have hm : min 0 (2 * (j : ℤ) + 2 - (4 * (j : ℤ) + 2)) + min 0 (2 * (2 * (j : ℤ) + 2) - (4 * (j : ℤ) + 2)) +
      max (4 * (j : ℤ) + 2 - (-1) - (2 * (j : ℤ) + 2)) 0 = 1 := by
    rw [min_eq_right (show 2 * (j : ℤ) + 2 - (4 * (j : ℤ) + 2) ≤ 0 by omega),
      min_eq_left (show (0 : ℤ) ≤ 2 * (2 * (j : ℤ) + 2) - (4 * (j : ℤ) + 2) by omega),
      max_eq_left (show (0 : ℤ) ≤ 4 * (j : ℤ) + 2 - (-1) - (2 * (j : ℤ) + 2) by omega)]
    ring
  have hI : (if (-1, 4 * (j : ℤ) + 2) = (-1, 2 * (2 * (j : ℤ) + 2) + 1) ∨
      (-1, 4 * (j : ℤ) + 2) = (2 * (j : ℤ) + 2 + 1, 2 * (j : ℤ) + 2 - 1) ∨
      (4 * (j : ℤ) + 2 - (-1) = 2 * (j : ℤ) + 2 ∧ 0 < (-1 : ℤ) ∧ (-1 : ℤ) < 2 * (j : ℤ) + 2) then
      (1 : ℤ) else 0) = 0 := by
    split_ifs <;> first | omega | (simp only [Prod.mk.injEq] at *; try omega)
  have hE := pnl_gen (2 * (j : ℤ) + 2) (-1) (4 * (j : ℤ) + 2) (2 * (j : ℤ) + 1) 1 1 0 (Or.inr rfl)
    (by ring) hm hI
  have hm' : min (2 * (j : ℤ) + 1 - (2 * (j : ℤ) - 1)) 0 = 0 := by
    rw [min_eq_right (by omega)]
  have hI' : (if ((0 : ℤ), 2 * (j : ℤ) - 1) = (0, 2 * (j : ℤ) + 1 + 1) ∨
      ((0 : ℤ), 2 * (j : ℤ) - 1) = (2 * (j : ℤ) + 1 + 1, 2 * (j : ℤ) + 1 - 1) then (1 : ℤ) else 0) = 0 := by
    split_ifs <;> first | omega | (simp only [Prod.mk.injEq] at *; try omega)
  have hS := pv_gen (2 * (j : ℤ) + 1) 0 (2 * (j : ℤ) - 1) ((j : ℤ) - 1) 1 0 0 (Or.inr rfl) (by ring) hm' hI'
  rw [hE, hS]
  unfold dotS
  ring

/-- The stem identity at every site of the top string (no membership needed). -/
theorem top_c1_pure (j : ℕ) (hj : 1 ≤ j) (x : GInt)
    (hx : x ∈ placedSites (sideString (hWordOf (List.replicate j Digit.two) true)
        (vWordOf (List.replicate j Digit.two) true) 0 .hMinus)) :
    paperNearLadderValue (2 * (j : ℤ) + 2) (x + (0, 1)) =
      paperNearStairValue (2 * (j : ℤ) + 1) ((x - ((-1 : ℤ), 2 * (j : ℤ) + 3)) + (0, 1)) +
        dotS ((j : ℤ) + 1, -((j : ℤ) + 2)) x + ((j : ℤ) + 1) * ((j : ℤ) + 2) := by
  obtain ⟨t, ht, u, hu, rfl⟩ := (top_mem j _).1 hx
  obtain ⟨u1, u2⟩ := u
  rcases (show t = 0 ∨ t = 1 ∨ 2 ≤ t by omega) with rfl | rfl | h2
  · rw [tileE_zero] at hu
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    rw [posE_zero,
      show ((u1, u2) + (-1, 4 * (j : ℤ) + 2) + (0, 1) : GInt) = (u1 - 1, u2 + 4 * (j : ℤ) + 3) by
        ext <;> ((try simp); (try ring)),
      show ((u1, u2) + (-1, 4 * (j : ℤ) + 2) - ((-1 : ℤ), 2 * (j : ℤ) + 3) + (0, 1) : GInt) =
        (u1, u2 + 2 * (j : ℤ)) by ext <;> ((try simp); (try ring)),
      show ((u1, u2) + (-1, 4 * (j : ℤ) + 2) : GInt) = (u1 - 1, u2 + 4 * (j : ℤ) + 2) by
        ext <;> ((try simp); (try ring))]
    exact c1_zero j hj u1 u2 (by omega) (by omega) (by omega) (by omega)
  · rw [tileE_one] at hu
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    have hp : posE j 1 = ((1 : ℤ), 4 * (j : ℤ) + 3) := by
      rw [posE_pos j 1 le_rfl]
      ext <;> ((try simp); (try ring))
    rw [hp,
      show ((u1, u2) + (1, 4 * (j : ℤ) + 3) + (0, 1) : GInt) = (u1 + 1, u2 + 4 * (j : ℤ) + 4) by
        ext <;> ((try simp); (try ring)),
      show ((u1, u2) + (1, 4 * (j : ℤ) + 3) - ((-1 : ℤ), 2 * (j : ℤ) + 3) + (0, 1) : GInt) =
        (u1 + 2, u2 + 2 * (j : ℤ) + 1) by ext <;> ((try simp); (try ring)),
      show ((u1, u2) + (1, 4 * (j : ℤ) + 3) : GInt) = (u1 + 1, u2 + 4 * (j : ℤ) + 3) by
        ext <;> ((try simp); (try ring))]
    exact c1_one j hj u1 u2 (by omega) (by omega) (by omega) (by omega)
  · rw [tileE_D j t h2 (by omega)] at hu
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    rw [posE_pos j t (by omega),
      show ((u1, u2) + ((t : ℤ), (t : ℤ) + 4 * (j : ℤ) + 2) + (0, 1) : GInt) =
        (u1 + t, u2 + t + 4 * (j : ℤ) + 3) by ext <;> ((try simp); (try ring)),
      show ((u1, u2) + ((t : ℤ), (t : ℤ) + 4 * (j : ℤ) + 2) - ((-1 : ℤ), 2 * (j : ℤ) + 3) + (0, 1) : GInt) =
        (u1 + t + 1, u2 + t + 2 * (j : ℤ)) by ext <;> ((try simp); (try ring)),
      show ((u1, u2) + ((t : ℤ), (t : ℤ) + 4 * (j : ℤ) + 2) : GInt) =
        (u1 + t, u2 + t + 4 * (j : ℤ) + 2) by ext <;> ((try simp); (try ring))]
    exact c1_mid j hj (t : ℤ) u1 u2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The enlarged clause at every site of the enlarged piece. -/
theorem top_c3_pt (j : ℕ) (hj : 1 ≤ j) (x : GInt)
    (hx : x ∈ placedSites (sideString (hWordOf (List.replicate j Digit.two) true)
        (vWordOf (List.replicate j Digit.two) true) 0 .hMinus))
    (hz : x - (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3) ∈ enlOdo.dom) :
    paperNearLadderValue (2 * (j : ℤ) + 2) (x + (0, 1)) =
      enlOdo.val (x - (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3)) +
        dotS (2 * (j : ℤ), -(2 * (j : ℤ) + 2)) x + (4 * (j : ℤ) ^ 2 + 6 * (j : ℤ) + 3) := by
  have hz' : x - (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3) ∈ tileShape ZTile.oneD := List.mem_toFinset.1 hz
  obtain ⟨u, hu, hxu⟩ : ∃ u, u ∈ tileShape ZTile.oneD ∧ u + posE j (2 * j + 1) = x :=
    ⟨x - (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3), hz', by rw [posE_sE j hj, sub_add_cancel]⟩
  subst hxu
  rw [top_c3 j hj u hu, posE_sE j hj]
  unfold enlOdo
  dsimp only
  rw [add_sub_cancel_right]
  unfold dotS ptDot
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- **The base fact of the double case for the top side** (`LSidesEvenK.DoubleTopBaseInput`), proved. -/
theorem double_top_base : ∀ (j : ℕ), 1 ≤ j → ∀ (O E O' E' : PartialOdometer),
    SurgicalWeak.PaperBaseCond (List.replicate j Digit.two) O E →
    SurgicalWeak.PaperBaseCond (List.replicate (j - 1) Digit.two) O' E' →
    (∀ x ∈ placedSites (sideString (hWordOf (List.replicate j Digit.two) true)
        (vWordOf (List.replicate j Digit.two) true) 0 .hMinus),
      x - ((-1 : ℤ), 2 * (j : ℤ) + 3) ∈ O'.dom ∨ x - (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3) ∈ enlOdo.dom) ∧
    (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3) ∈ placedSites (sideString (hWordOf (List.replicate j Digit.two) true)
        (vWordOf (List.replicate j Digit.two) true) 0 .hMinus) ∧
    ∃ c1 c3 : ℤ,
      (∀ x ∈ placedSites (sideString (hWordOf (List.replicate j Digit.two) true)
        (vWordOf (List.replicate j Digit.two) true) 0 .hMinus),
        x ∈ E.dom ∧
        (x - ((-1 : ℤ), 2 * (j : ℤ) + 3) ∈ O'.dom →
          E.val x = O'.val (x - ((-1 : ℤ), 2 * (j : ℤ) + 3)) + dotS ((j : ℤ) + 1, -((j : ℤ) + 2)) x + c1) ∧
        (x - (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3) ∈ enlOdo.dom →
          E.val x = enlOdo.val (x - (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3)) + dotS (2 * (j : ℤ), -(2 * (j : ℤ) + 2)) x + c3)) ∧
      ((-1 : ℤ), 4 * (j : ℤ) + 1) ∈ E.dom ∧
      E.val ((-1 : ℤ), 4 * (j : ℤ) + 1) =
        O'.val (((-1 : ℤ), 4 * (j : ℤ) + 1) - ((-1 : ℤ), 2 * (j : ℤ) + 3)) +
          dotS ((j : ℤ) + 1, -((j : ℤ) + 2)) ((-1 : ℤ), 4 * (j : ℤ) + 1) + c1 := by
  intro j hj O E O' E' hO hO'
  obtain ⟨-, -, hC⟩ := hO
  obtain ⟨-, -, hEdom, hEval⟩ := hC j hj rfl
  obtain ⟨hOdom, hOval⟩ := pbc_odd j hj O' E' hO'
  have hcov : ∀ x ∈ placedSites (sideString (hWordOf (List.replicate j Digit.two) true)
        (vWordOf (List.replicate j Digit.two) true) 0 .hMinus),
      x - ((-1 : ℤ), 2 * (j : ℤ) + 3) ∈ O'.dom ∨ x - (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3) ∈ enlOdo.dom := by
    intro x hx
    rcases top_cov j hj x hx with h | h
    · left; rw [hOdom]; exact h
    · right; exact List.mem_toFinset.2 h
  have hA : ∀ x ∈ placedSites (sideString (hWordOf (List.replicate j Digit.two) true)
        (vWordOf (List.replicate j Digit.two) true) 0 .hMinus),
      x ∈ E.dom ∧
      (x - ((-1 : ℤ), 2 * (j : ℤ) + 3) ∈ O'.dom →
        E.val x = O'.val (x - ((-1 : ℤ), 2 * (j : ℤ) + 3)) + dotS ((j : ℤ) + 1, -((j : ℤ) + 2)) x +
          ((j : ℤ) + 1) * ((j : ℤ) + 2)) ∧
      (x - (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3) ∈ enlOdo.dom →
        E.val x = enlOdo.val (x - (2 * (j : ℤ) + 1, 6 * (j : ℤ) + 3)) + dotS (2 * (j : ℤ), -(2 * (j : ℤ) + 2)) x +
          (4 * (j : ℤ) ^ 2 + 6 * (j : ℤ) + 3)) := by
    intro x hx
    have hE : x ∈ E.dom := by rw [hEdom]; exact top_Edom j hj x hx
    refine ⟨hE, fun hd => ?_, fun hz => ?_⟩
    · rw [hEval x hE, hOval _ hd]
      exact top_c1_pure j hj x hx
    · rw [hEval x hE]
      exact top_c3_pt j hj x hx hz
  have hJmem : ((-1 : ℤ), 4 * (j : ℤ) + 1) ∈ E.dom := by
    rw [hEdom]; exact top_J_mem j hj
  have hJs : ((-1 : ℤ), 4 * (j : ℤ) + 1) - ((-1 : ℤ), 2 * (j : ℤ) + 3) ∈ O'.dom := by
    rw [hOdom, mem_nstairN_iff]
    simp only [nstairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk_add_mk, Prod.mk_sub_mk]
    omega
  have hJv : E.val ((-1 : ℤ), 4 * (j : ℤ) + 1) =
      O'.val (((-1 : ℤ), 4 * (j : ℤ) + 1) - ((-1 : ℤ), 2 * (j : ℤ) + 3)) +
        dotS ((j : ℤ) + 1, -((j : ℤ) + 2)) ((-1 : ℤ), 4 * (j : ℤ) + 1) + ((j : ℤ) + 1) * ((j : ℤ) + 2) := by
    rw [hEval _ hJmem, hOval _ hJs,
      show ((-1 : ℤ), 4 * (j : ℤ) + 1) + (0, 1) = ((-1 : ℤ), 4 * (j : ℤ) + 2) by
        ext <;> ((try simp); (try ring)),
      show (((-1 : ℤ), 4 * (j : ℤ) + 1) - ((-1 : ℤ), 2 * (j : ℤ) + 3) + (0, 1) : GInt) =
        ((0 : ℤ), 2 * (j : ℤ) - 1) by ext <;> ((try simp); (try ring))]
    exact top_J_val j hj
  exact ⟨hcov, top_sE_mem j hj, ((j : ℤ) + 1) * ((j : ℤ) + 2), 4 * (j : ℤ) ^ 2 + 6 * (j : ℤ) + 3, hA, hJmem, hJv⟩

end FLatticePaper.Tiles.DoubleTopBase
