import FLatticePaper.Tiles.BaseHmTwoOdd

/-! # The odometer identities of the reversed horizontal piece of the odd `2^k` word

On each tile of `HmTwoOddF k` the paper odometer `paperOdd2 k` equals the family's odometer (`odo2_eq`), and the reversed
horizontal string of the odd `2^k` word is respected by `paperOdd2 k` (`odo2_respects`). Each tile identity is a finite case
analysis on the tile shape, with the half-square term evaluated by `sq_div4`. -/

namespace FLatticePaper.Tiles.BaseHmTwoOddOdo

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.BaseTwoOdd FLatticePaper.Tiles.BaseHpNear FLatticePaper.Tiles.BaseHmTwoOdd

/-- The paper odometer of the odd `2^k` piece, `paperNearStairValue (2k+3)` read at the shift `(0,1)`. -/
def paperOdd2 (k : ℕ) (x : GInt) : ℤ := paperNearStairValue (2 * (k : ℤ) + 3) (x + (0, 1))

theorem sq_div4 (n q e : ℤ) (he : e = 0 ∨ e = 1) (hn : n = 2 * q + e) :
    n ^ 2 / 4 = q * q + e * q := by
  rcases he with rfl | rfl
  · subst hn
    rw [BaseTwoOdd.sq_half, show (2 * q + 0) / 2 = q by omega, show (2 * q + 0 + 1) / 2 = q by omega]
    ring
  · subst hn
    rw [BaseTwoOdd.sq_half, show (2 * q + 1) / 2 = q by omega, show (2 * q + 1 + 1) / 2 = q + 1 by omega]
    ring

/-- The paper value at `(x1, x2)` once the half-square, the minimum and the indicator are known. -/
theorem pv_gen (d x1 x2 q e m I : ℤ) (he : e = 0 ∨ e = 1) (hn : x2 - x1 = 2 * q + e)
    (hm : min (d - x2) 0 = m)
    (hI : (if (x1, x2) = (0, d + 1) ∨ (x1, x2) = (d + 1, d - 1) then (1 : ℤ) else 0) = I) :
    paperNearStairValue d (x1, x2) = -(q * q + e * q) + m + I := by
  rw [BaseTwoOdd.paper_eval, hm, hI, sq_div4 (x2 - x1) q e he hn]

theorem paperOdd2_add (k : ℕ) (u1 u2 p1 p2 : ℤ) :
    paperOdd2 k ((u1, u2) + (p1, p2)) = paperNearStairValue (2 * (k : ℤ) + 3) (u1 + p1, u2 + p2 + 1) := by
  unfold paperOdd2
  congr 1
  ext <;> simp

theorem posH2_zero (k : ℕ) : posH2 k 0 = (0, 2 * (k : ℤ) + 1) := by
  simp [posH2]

theorem posH2_pos (k j : ℕ) (hj : 1 ≤ j) :
    posH2 k j = ((j : ℤ) + 1, (j : ℤ) + 2 * (k : ℤ) + 1) := by
  unfold posH2
  rw [if_neg (show ¬ j = 0 by omega)]

theorem cH2_zero (k : ℕ) : cH2 k 0 = -((k : ℤ) + 1) * ((k : ℤ) + 1) := by
  simp [cH2]

theorem cH2_pos (k j : ℕ) (hj : 1 ≤ j) :
    cH2 k j = -((k : ℤ) * (k : ℤ)) - (k : ℤ) - ((j : ℤ) - 1) := by
  unfold cH2
  rw [if_neg (show ¬ j = 0 by omega)]

theorem hTileAt_zero (k : ℕ) : hTileAt (lettersOf (wD k) true) 0 = ZTile.zero := by
  unfold hTileAt hPrev
  rw [if_pos rfl, lettersOf_wD0]
  rfl

theorem hTileAt_one (k : ℕ) : hTileAt (lettersOf (wD k) true) 1 = ZTile.one := by
  unfold hTileAt hPrev
  rw [if_neg (show ¬ (1 : ℕ) = 0 by omega), show (1 : ℕ) - 1 = 0 from rfl, lettersOf_wD0,
    lettersOf_wDq k 1 le_rfl (by omega)]
  rfl

theorem hTileAt_big (k j : ℕ) (hj : 2 ≤ j) (hjk : j ≤ 2 * k + 2) :
    hTileAt (lettersOf (wD k) true) j = ZTile.oneD := by
  unfold hTileAt hPrev
  rw [if_neg (show ¬ j = 0 by omega), lettersOf_wDq k (j - 1) (by omega) (by omega),
    lettersOf_wDq k j (by omega) hjk]
  rfl

/-- The zero tile at `(0, 2k+1)`: the paper odometer equals `zTileOdo zero` plus the affine part and constant. -/
theorem odo2_zero (k : ℕ) (u : GInt) (hu : u ∈ tileShape ZTile.zero) :
    paperOdd2 k (u + posH2 k 0) = zTileOdo ZTile.zero u + ptDot (aH2 k 0) u + cH2 k 0 := by
  rw [posH2_zero, aH2_zero, cH2_zero]
  obtain ⟨u1, u2⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rw [paperOdd2_add]
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [pv_gen (2 * (k : ℤ) + 3) (0 + 0) (0 + (2 * (k : ℤ) + 1) + 1) ((k : ℤ) + 1) 0 0 0 (by norm_num)
      (by ring) (min_eq_right (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, zeroOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (0 + 0) (1 + (2 * (k : ℤ) + 1) + 1) ((k : ℤ) + 1) 1 0 0 (by norm_num)
      (by ring) (min_eq_right (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, zeroOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (0 + 0) (2 + (2 * (k : ℤ) + 1) + 1) ((k : ℤ) + 2) 0
      ((2 * (k : ℤ) + 3) - (2 + (2 * (k : ℤ) + 1) + 1)) 1 (by norm_num)
      (by ring) (min_eq_left (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, zeroOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (1 + 0) (0 + (2 * (k : ℤ) + 1) + 1) (k : ℤ) 1 0 0 (by norm_num)
      (by ring) (min_eq_right (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, zeroOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (1 + 0) (1 + (2 * (k : ℤ) + 1) + 1) ((k : ℤ) + 1) 0 0 0 (by norm_num)
      (by ring) (min_eq_right (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, zeroOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (1 + 0) (2 + (2 * (k : ℤ) + 1) + 1) ((k : ℤ) + 1) 1
      ((2 * (k : ℤ) + 3) - (2 + (2 * (k : ℤ) + 1) + 1)) 0 (by norm_num)
      (by ring) (min_eq_left (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, zeroOdometer, ptDot]
    ring

/-- The one tile at `(j+1, j+2k+1)`, `j ≥ 1`. -/
theorem odo2_one (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ 2 * k + 2) (u : GInt) (hu : u ∈ tileShape ZTile.one) :
    paperOdd2 k (u + posH2 k j) = zTileOdo ZTile.one u + ptDot (aH2 k j) u + cH2 k j := by
  rw [posH2_pos k j hj, aH2_pos k j hj hjk, cH2_pos k j hj]
  obtain ⟨u1, u2⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rw [paperOdd2_add]
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [pv_gen (2 * (k : ℤ) + 3) (0 + ((j : ℤ) + 1)) (0 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1) (k : ℤ) 1
      ((2 * (k : ℤ) + 3) - (0 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1)) 0 (by norm_num)
      (by ring) (min_eq_left (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, oneOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (0 + ((j : ℤ) + 1)) (1 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1) ((k : ℤ) + 1) 0
      ((2 * (k : ℤ) + 3) - (1 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1)) 0 (by norm_num)
      (by ring) (min_eq_left (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, oneOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (1 + ((j : ℤ) + 1)) (0 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1) (k : ℤ) 0
      ((2 * (k : ℤ) + 3) - (0 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1)) 0 (by norm_num)
      (by ring) (min_eq_left (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, oneOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (1 + ((j : ℤ) + 1)) (1 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1) (k : ℤ) 1
      ((2 * (k : ℤ) + 3) - (1 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1)) 0 (by norm_num)
      (by ring) (min_eq_left (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, oneOdometer, ptDot]
    ring

/-- The enlarged tiles `oneD` at `(j+1, j+2k+1)`, `2 ≤ j ≤ 2k+2`. -/
theorem odo2_big (k j : ℕ) (hj : 2 ≤ j) (hjk : j ≤ 2 * k + 2) (u : GInt) (hu : u ∈ tileShape ZTile.oneD) :
    paperOdd2 k (u + posH2 k j) = zTileOdo ZTile.oneD u + ptDot (aH2 k j) u + cH2 k j := by
  rw [posH2_pos k j (by omega), aH2_pos k j (by omega) hjk, cH2_pos k j (by omega)]
  obtain ⟨u1, u2⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rw [paperOdd2_add]
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [pv_gen (2 * (k : ℤ) + 3) (0 + ((j : ℤ) + 1)) (0 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1) (k : ℤ) 1
      ((2 * (k : ℤ) + 3) - (0 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1)) 0 (by norm_num)
      (by ring) (min_eq_left (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, oneOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (0 + ((j : ℤ) + 1)) (1 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1) ((k : ℤ) + 1) 0
      ((2 * (k : ℤ) + 3) - (1 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1)) 0 (by norm_num)
      (by ring) (min_eq_left (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, oneOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (1 + ((j : ℤ) + 1)) (0 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1) (k : ℤ) 0
      ((2 * (k : ℤ) + 3) - (0 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1)) 0 (by norm_num)
      (by ring) (min_eq_left (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, oneOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (1 + ((j : ℤ) + 1)) (1 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1) (k : ℤ) 1
      ((2 * (k : ℤ) + 3) - (1 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1)) 0 (by norm_num)
      (by ring) (min_eq_left (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, oneOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (-1 + ((j : ℤ) + 1)) (1 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1) ((k : ℤ) + 1) 1
      ((2 * (k : ℤ) + 3) - (1 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1)) 0 (by norm_num)
      (by ring) (min_eq_left (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, oneOdometer, ptDot]
    ring
  · rw [pv_gen (2 * (k : ℤ) + 3) (1 + ((j : ℤ) + 1)) (-1 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1) ((k : ℤ) - 1) 1
      ((2 * (k : ℤ) + 3) - (-1 + ((j : ℤ) + 2 * (k : ℤ) + 1) + 1)) 0 (by norm_num)
      (by ring) (min_eq_left (by omega)) (by simp only [Prod.mk.injEq]; split_ifs <;> omega)]
    norm_num [zTileOdo, oneOdometer, ptDot]
    ring

/-- On each tile of `HmTwoOddF k` the paper odometer equals the family's odometer. -/
theorem odo2_eq (k : ℕ) (j : ℕ) (hj : j < 2 * k + 3) (x : GInt) (hx : x ∈ (HmTwoOddF k).dom j) :
    paperOdd2 k x = (HmTwoOddF k).odo j x := by
  have hdom := hx
  unfold PTFamily.dom at hdom
  rw [HmTwoOddF_tile k j hj] at hdom
  simp only [List.mem_map] at hdom
  obtain ⟨u, hu, rfl⟩ := hdom
  have key : paperOdd2 k (u + posH2 k j)
      = zTileOdo (hTileAt (lettersOf (wD k) true) j) u + ptDot (aH2 k j) u + cH2 k j := by
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · rcases Nat.lt_or_ge j 1 with hj1 | hj1
      · obtain rfl : j = 0 := by omega
        rw [hTileAt_zero] at hu ⊢
        exact odo2_zero k u hu
      · obtain rfl : j = 1 := by omega
        rw [hTileAt_one] at hu ⊢
        exact odo2_one k 1 (by norm_num) (by omega) u hu
    · rw [hTileAt_big k j hj2 (by omega)] at hu ⊢
      exact odo2_big k j hj2 (by omega) u hu
  unfold PTFamily.odo
  rw [HmTwoOddF_tile k j hj]
  show paperOdd2 k (u + posH2 k j) = zTileOdo (hTileAt (lettersOf (wD k) true) j) (u + posH2 k j - posH2 k j)
    + (aH2 k j).1 * (u + posH2 k j).1 + (aH2 k j).2 * (u + posH2 k j).2
    + (cH2 k j - ptDot (aH2 k j) (posH2 k j))
  rw [key, add_sub_cancel_right]
  unfold ptDot
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The reversed horizontal string of the odd `2^k` word, anchored at `posH2 k 0`, is respected by `paperOdd2 k`. -/
theorem odo2_respects (k : ℕ) :
    RespectsTiles .horizontal true (hRevStringAt (wD k).reverse (posH2 k 0)) (fun x => paperOdd2 k x) := by
  have hl : lettersOf (wD k) true = lettersOf (wD k).reverse false := rfl
  have hts : (HmTwoOddF k).ts = hRevStringAt (wD k).reverse (posH2 k 0) := by
    rw [hRevStringAt_eq_map (wD k).reverse (posH2 k 0) (posH2 k) rfl (fun j hj => by
      rw [List.length_reverse, wD_length] at hj
      exact posH2_succ k j (by omega))]
    unfold HmTwoOddF
    rw [hl, List.length_reverse, wD_length]
  exact ⟨HmTwoOddF k, hts, fun j hj x hx => odo2_eq k j (by rw [HmTwoOddF_n] at hj; exact hj) x hx,
    HmTwoOddF_respects k⟩

end FLatticePaper.Tiles.BaseHmTwoOddOdo
