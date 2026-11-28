import FLatticePaper.Tiles.BaseHmTwoOdd
import FLatticePaper.Tiles.BaseHpStair
import FLatticePaper.Tiles.BaseThreeEven
import FLatticePaper.Tiles.BaseHmAnchor

/-! # The reversed horizontal base piece of the even `3^k` word (`k ≥ 0`, so also the empty word's even child)

The forward word of the even child of `3^k` is `wE k = q p^{k+1}` (`BaseHpStair`); its reversed word is `p^{k+1} q`. The
reversed horizontal string is anchored at `(-(2k+1), 2k+2)`, the last point of the reversed vertical string
(`BaseThreeEven.wv_three_even`). The family has `zero` tiles at `(2j-2k-1, 2k+2)` for `0 ≤ j ≤ k` and a `one` tile at
`(1, 2k+3)`. Its affine factors are `(1, -(2k+2))` on the `zero` tiles and `(0, -(2k+2))` on the `one` tile, and its centred
constants are `-(k+1)(2k+3) + 2j` and `-(k+1)(2k+3)`. The odometer is `paperStairValue (2k+3)`. -/

namespace FLatticePaper.Tiles.BaseHmThreeEven

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.BaseHpStair FLatticePaper.Tiles.BaseHmTwoOdd
open FLatticePaper.Tiles.BaseTileProps FLatticePaper.Tiles.VerticalRevBridge
open FLatticePaper.Tiles.BaseHmAnchor
open FLatticePaper.Tiles.BaseHpLadder (getD_rep getD_append_eq)

theorem wE_rev (k : ℕ) : (wE k).reverse = List.replicate (k + 1) Letter.p ++ [Letter.q] := by
  simp [wE]

theorem lettersOf_wE (k j : ℕ) :
    lettersOf (wE k) true j = if j ≤ k then Letter.p else if j = k + 1 then Letter.q else Letter.p := by
  unfold lettersOf
  simp only [if_true]
  rw [wE_rev, getD_append_eq, List.length_replicate, getD_rep]
  rcases Nat.lt_or_ge j (k + 1) with h | h
  · rw [if_pos h, if_pos h, if_pos (show j ≤ k by omega)]
  · rw [if_neg (show ¬ j < k + 1 by omega)]
    rcases Nat.eq_or_lt_of_le h with h2 | h2
    · rw [← h2, if_neg (show ¬ (k + 1 ≤ k) by omega), if_pos rfl]
      simp
    · rw [if_neg (show ¬ j ≤ k by omega), if_neg (show ¬ j = k + 1 by omega)]
      obtain ⟨m, hm⟩ : ∃ m, j - (k + 1) = m + 1 := ⟨j - (k + 2), by omega⟩
      rw [hm, List.getD_cons_succ, List.getD_nil]

/-- The positions of the reversed tiles of the even `3^k` piece. -/
def posH3 (k j : ℕ) : GInt :=
  if j ≤ k then ((2 * (j : ℤ) - 2 * (k : ℤ) - 1), 2 * (k : ℤ) + 2) else (1, 2 * (k : ℤ) + 3)

/-- The affine factor of the reversed even `3^k` piece: the letter factor plus the shift `(1, -(2k+3))`. -/
def aH3 (k j : ℕ) : GInt :=
  alphaH (lettersOf (wE k) true j) + (1, -(2 * (k : ℤ) + 3))

/-- The centred constant of the reversed even `3^k` piece. -/
def cH3 (k j : ℕ) : ℤ :=
  if j ≤ k then -((k : ℤ) + 1) * (2 * (k : ℤ) + 3) + 2 * (j : ℤ) else -((k : ℤ) + 1) * (2 * (k : ℤ) + 3)

theorem posH3_le (k j : ℕ) (hj : j ≤ k) :
    posH3 k j = ((2 * (j : ℤ) - 2 * (k : ℤ) - 1), 2 * (k : ℤ) + 2) := by
  unfold posH3; rw [if_pos hj]

theorem posH3_one (k : ℕ) : posH3 k (k + 1) = (1, 2 * (k : ℤ) + 3) := by
  unfold posH3; rw [if_neg (by omega)]

theorem aH3_le (k j : ℕ) (hj : j ≤ k) : aH3 k j = (1, -(2 * (k : ℤ) + 2)) := by
  unfold aH3; rw [lettersOf_wE, if_pos hj]
  refine Prod.ext ?_ ?_
  all_goals simp [alphaH]
  all_goals ring

theorem aH3_one (k : ℕ) : aH3 k (k + 1) = (0, -(2 * (k : ℤ) + 2)) := by
  unfold aH3; rw [lettersOf_wE, if_neg (by omega), if_pos rfl]
  refine Prod.ext ?_ ?_
  all_goals simp [alphaH]
  all_goals ring

theorem cH3_le (k j : ℕ) (hj : j ≤ k) :
    cH3 k j = -((k : ℤ) + 1) * (2 * (k : ℤ) + 3) + 2 * (j : ℤ) := by
  unfold cH3; rw [if_pos hj]

theorem cH3_one (k : ℕ) : cH3 k (k + 1) = -((k : ℤ) + 1) * (2 * (k : ℤ) + 3) := by
  unfold cH3; rw [if_neg (by omega)]

theorem posH3_succ (k j : ℕ) (hj : j + 1 < k + 2) :
    posH3 k (j + 1) = posH3 k j +
      zeroOneHorizontalReversedStep (lettersOf (wE k) true j) (lettersOf (wE k) true (j + 1)) := by
  by_cases h1 : j + 1 ≤ k
  · rw [posH3_le k (j + 1) h1, posH3_le k j (by omega), lettersOf_wE, lettersOf_wE,
      if_pos (show j ≤ k by omega), if_pos h1]
    unfold zeroOneHorizontalReversedStep
    ext
    all_goals simp
    all_goals ring
  · have hjk : j = k := by omega
    rw [show j + 1 = k + 1 by omega, posH3_one, posH3_le k j (by omega), lettersOf_wE, lettersOf_wE,
      if_pos (show j ≤ k by omega), if_neg (show ¬ (k + 1 ≤ k) by omega), if_pos rfl]
    unfold zeroOneHorizontalReversedStep
    ext
    all_goals simp
    all_goals omega

theorem cH3_succ (k j : ℕ) (hj : j + 1 < k + 2) :
    cH3 k (j + 1) = cH3 k j +
      ptDot (aH3 k j) (zeroOneHorizontalReversedStep (lettersOf (wE k) true j) (lettersOf (wE k) true (j + 1))) := by
  by_cases h1 : j + 1 ≤ k
  · rw [cH3_le k (j + 1) h1, cH3_le k j (by omega), aH3_le k j (by omega), lettersOf_wE, lettersOf_wE,
      if_pos (show j ≤ k by omega), if_pos h1]
    unfold zeroOneHorizontalReversedStep ptDot
    push_cast
    ring
  · have hjk : j = k := by omega
    rw [show j + 1 = k + 1 by omega, cH3_one, cH3_le k j (by omega), aH3_le k j (by omega), lettersOf_wE,
      lettersOf_wE, if_pos (show j ≤ k by omega), if_neg (show ¬ (k + 1 ≤ k) by omega), if_pos rfl]
    unfold zeroOneHorizontalReversedStep ptDot
    dsimp only
    rw [hjk]
    push_cast
    ring

/-- The tile types of the reversed even `3^k` piece: `zero` up to `k`, then `one`. -/
theorem tileE3_zero (k j : ℕ) (hj : j ≤ k) : hTileAt (lettersOf (wE k) true) j = ZTile.zero := by
  unfold hTileAt hPrev
  simp only [lettersOf_wE]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
    rfl
  · rw [if_neg (show ¬ j = 0 by omega), if_pos hj, if_pos (show j - 1 ≤ k by omega)]
    rfl

theorem tileE3_one (k : ℕ) : hTileAt (lettersOf (wE k) true) (k + 1) = ZTile.one := by
  unfold hTileAt hPrev
  rw [if_neg (show ¬ (k + 1 = 0) by omega), lettersOf_wE, lettersOf_wE,
    if_pos (show k + 1 - 1 ≤ k by omega), if_neg (show ¬ (k + 1 ≤ k) by omega), if_pos rfl]
  all_goals rfl

/-- The even `3^k` reversed horizontal family. -/
def HmThreeF (k : ℕ) : PTFamily :=
  { ts := (List.range (k + 2)).map (fun j => (hTileAt (lettersOf (wE k) true) j, posH3 k j)),
    a := fun j => aH3 k j,
    b := fun j => cH3 k j - ptDot (aH3 k j) (posH3 k j) }

theorem HmThreeF_n (k : ℕ) : (HmThreeF k).n = k + 2 := by
  simp [HmThreeF, PTFamily.n]

theorem HmThreeF_tile (k j : ℕ) (hj : j < k + 2) :
    (HmThreeF k).tile j = (hTileAt (lettersOf (wE k) true) j, posH3 k j) := by
  unfold PTFamily.tile HmThreeF
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem HmThreeF_respects (k : ℕ) :
    (HmThreeF k).Respects .horizontal true :=
  PTFamily.respects_of_triples (HmThreeF k) .horizontal true (lettersOf (wE k) true)
    (hPrev (lettersOf (wE k) true))
    (fun j => posH3 k j) hTt
    (fun y z => zeroOneHorizontalReversedStep y z) (fun _ y z => alphaH z - alphaH y)
    (fun j => cH3 k j) (fun _ _ _ => (0 : ℤ)) (fun _ _ _ => True)
    (fun j hj => by
      rw [HmThreeF_n] at hj
      rw [HmThreeF_tile k j hj]
      rfl)
    (fun j _ => hPrev_succ _ j)
    (fun j hj => by
      rw [HmThreeF_n] at hj
      exact posH3_succ k j (by omega))
    (fun j hj => by
      rw [HmThreeF_n] at hj
      show aH3 k (j + 1) = aH3 k j + (alphaH (lettersOf (wE k) true (j + 1)) - alphaH (lettersOf (wE k) true j))
      unfold aH3
      abel)
    (fun j _ => rfl)
    (fun j hj => by
      rw [HmThreeF_n] at hj
      show cH3 k (j + 1) = cH3 k j + (0 : ℤ) +
        ptDot (aH3 k j) (zeroOneHorizontalReversedStep (lettersOf (wE k) true j) (lettersOf (wE k) true (j + 1)))
      rw [cH3_succ k j (by omega)]
      ring)
    (fun _ _ => trivial)
    (fun x y => hTt_letter x y)
    (fun x y z _ => by
      cases y <;> cases z <;> simp [hTt_base_p, hTt_base_q, surgicalSlopeDiff, alphaH, Prod.ext_iff] <;> norm_num)
    (fun _ x y z _ u hu v hv hno hunit => hE_rev x y z u hu v hv hno hunit)
    (fun h => by cases h)

theorem tri_half (k m : ℤ) :
    (2 * k + m) * (2 * k + m + 1) / 2 = 2 * k ^ 2 + (2 * m + 1) * k + m * (m + 1) / 2 := by
  rw [show (2 * k + m) * (2 * k + m + 1) = m * (m + 1) + (2 * k ^ 2 + (2 * m + 1) * k) * 2 by ring,
    Int.add_mul_ediv_right _ _ (by norm_num)]
  ring

theorem stair3_zero (k j : ℕ) (hj : j ≤ k) (u : GInt) (hu : u ∈ tileShape ZTile.zero) :
    paperStairValue (2 * (k : ℤ) + 3) (u + posH3 k j) =
      zTileOdo ZTile.zero u + ptDot (aH3 k j) u + cH3 k j := by
  obtain ⟨u1, u2⟩ := u
  rw [posH3_le k j hj, aH3_le k j hj, cH3_le k j hj]
  rw [show ((u1, u2) + ((2 * (j : ℤ) - 2 * (k : ℤ) - 1), 2 * (k : ℤ) + 2) : GInt) =
      (u1 + (2 * (j : ℤ) - 2 * (k : ℤ) - 1), u2 + 2 * (k : ℤ) + 2) by simp only [Prod.mk_add_mk, add_assoc]]
  unfold paperStairValue
  dsimp only
  rw [show u2 + 2 * (k : ℤ) + 2 = 2 * (k : ℤ) + (u2 + 2) by ring, tri_half]
  have hb : 0 ≤ u1 ∧ u1 ≤ 1 ∧ 0 ≤ u2 ∧ u2 ≤ 2 := by
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    omega
  obtain ⟨hu1a, hu1b, hu2a, hu2b⟩ := hb
  rw [min_eq_left (show u1 + (2 * (j : ℤ) - 2 * (k : ℤ) - 1) - 1 ≤ 0 by omega)]
  split_ifs with hind
  · exfalso
    simp only [Prod.mk.injEq] at hind
    omega
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (norm_num [zTileOdo, zeroOdometer, ptDot]) <;> ring

theorem stair3_one (k : ℕ) (u : GInt) (hu : u ∈ tileShape ZTile.one) :
    paperStairValue (2 * (k : ℤ) + 3) (u + posH3 k (k + 1)) =
      zTileOdo ZTile.one u + ptDot (aH3 k (k + 1)) u + cH3 k (k + 1) := by
  obtain ⟨u1, u2⟩ := u
  rw [posH3_one, aH3_one, cH3_one]
  rw [show ((u1, u2) + (1, 2 * (k : ℤ) + 3) : GInt) = (u1 + 1, u2 + 2 * (k : ℤ) + 3) by simp only [Prod.mk_add_mk, add_assoc]]
  unfold paperStairValue
  dsimp only
  rw [show u2 + 2 * (k : ℤ) + 3 = 2 * (k : ℤ) + (u2 + 3) by ring, tri_half]
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (norm_num [zTileOdo, oneOdometer, ptDot]) <;> (try split_ifs) <;> (try omega) <;> ring

/-- The odometer of the reversed even `3^k` family is `paperStairValue (2k+3)` on each of its tiles. -/
theorem stair3_odo_eq (k j : ℕ) (hj : j < k + 2) (x : GInt) (hx : x ∈ (HmThreeF k).dom j) :
    paperStairValue (2 * (k : ℤ) + 3) x = (HmThreeF k).odo j x := by
  have hdom := hx
  unfold PTFamily.dom at hdom
  rw [HmThreeF_tile k j hj] at hdom
  simp only [List.mem_map] at hdom
  obtain ⟨u, hu, rfl⟩ := hdom
  have key : paperStairValue (2 * (k : ℤ) + 3) (u + posH3 k j) =
      zTileOdo (hTileAt (lettersOf (wE k) true) j) u + ptDot (aH3 k j) u + cH3 k j := by
    rcases Nat.lt_or_ge j (k + 1) with hj1 | hj1
    · rw [tileE3_zero k j (by omega)] at hu ⊢
      exact stair3_zero k j (by omega) u hu
    · obtain rfl : j = k + 1 := by omega
      rw [tileE3_one k] at hu ⊢
      exact stair3_one k u hu
  unfold PTFamily.odo
  rw [HmThreeF_tile k j hj]
  show paperStairValue _ (u + posH3 k j) =
    zTileOdo (hTileAt (lettersOf (wE k) true) j) (u + posH3 k j - posH3 k j) + (aH3 k j).1 * (u + posH3 k j).1 +
      (aH3 k j).2 * (u + posH3 k j).2 + (cH3 k j - ptDot (aH3 k j) (posH3 k j))
  rw [key, add_sub_cancel_right]
  unfold ptDot
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem anchor_hm_three (k : ℕ) :
    lastPosOf (vRevStringAt (vWordOf (List.replicate k Digit.three) true).reverse (0, 0)) = posH3 k 0 := by
  rw [BaseThreeEven.wv_three_even k]
  have hrev : (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]).reverse =
      Letter.q :: List.replicate (2 * k + 2) Letter.p := by
    simp [List.reverse_append]
  rw [hrev, lastPos_vRev_q_rep (2 * k + 2) (by omega), posH3_le k 0 (by omega)]
  ext
  all_goals simp
  all_goals ring

/-- The reversed horizontal string of the even `3^k` word (`k ≥ 0`), anchored at `posH3 k 0`, is respected by
`paperStairValue (2k+3)`. -/
theorem respects_hm_three (k : ℕ) :
    RespectsTiles .horizontal true (hRevStringAt (wE k).reverse (posH3 k 0))
      (fun x => paperStairValue (2 * (k : ℤ) + 3) x) := by
  have hl : lettersOf (wE k) true = lettersOf (wE k).reverse false := rfl
  have hts : (HmThreeF k).ts = hRevStringAt (wE k).reverse (posH3 k 0) := by
    rw [hRevStringAt_eq_map (wE k).reverse (posH3 k 0) (posH3 k) rfl (fun j hj => by
      rw [List.length_reverse, wE_length] at hj
      exact posH3_succ k j (by omega))]
    unfold HmThreeF
    rw [hl, List.length_reverse, wE_length]
  exact ⟨HmThreeF k, hts, fun j hj x hx => stair3_odo_eq k j (by rw [HmThreeF_n] at hj; exact hj) x hx,
    HmThreeF_respects k⟩

end FLatticePaper.Tiles.BaseHmThreeEven
