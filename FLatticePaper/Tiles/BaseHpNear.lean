import FLatticePaper.Tiles.BaseRespectsHorizontal
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.BaseHpLadder

/-! # The forward horizontal clause of the odd odometer of `2^k` (`k ≥ 0`, the case `k = 0` is the empty word)

The forward word of the odd tile of `2^k` is `q^{2k+2} p` (`RegisterLink.quad_twos`). Its enlarged tiles: `one` at `(0,0)`,
`oneD` at `(j,j)` for `1 ≤ j ≤ 2k+1`, and `zero` at `(2k+3, 2k+1)`. The odd odometer is `paperNearStairValue (2k+3)` shifted by `(0,1)`,
and on each of these tiles it is the zero-one tile odometer (no affine part). -/

namespace FLatticePaper.Tiles.BaseHpNear

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Construction
open FLatticePaper.Tiles.BaseHpLadder (getD_rep getD_append_eq)
open FLatticePaper.Tiles.BaseTileProps

/-- The forward word of the odd tile of `2^k`: `q^{2k+2} p`. -/
def wD (k : ℕ) : BinaryWord := List.replicate (2 * k + 2) Letter.q ++ [Letter.p]

theorem wD_length (k : ℕ) : (wD k).length = 2 * k + 3 := by
  simp [wD]

theorem hWordOf_two_false (k : ℕ) : hWordOf (List.replicate k Digit.two) false = wD k := by
  have h := (RegisterLink.quad_twos k).1
  simp only [hWordOf, Bool.false_eq_true, if_false]
  rw [h]
  rfl

theorem hTt_qq : hTt Letter.q Letter.q = ZTile.oneD := rfl

theorem letter_wD (k j : ℕ) (hj : j < 2 * k + 3) :
    lettersOf (wD k) false j = if j ≤ 2 * k + 1 then Letter.q else Letter.p := by
  unfold lettersOf
  simp only [Bool.false_eq_true, if_false]
  unfold wD
  rw [getD_append_eq]
  simp only [List.length_replicate]
  by_cases h1 : j ≤ 2 * k + 1
  · rw [getD_rep]
    simp [show j < 2 * k + 2 by omega, h1]
  · rw [if_neg (show ¬ j < 2 * k + 2 by omega), if_neg h1, show j - (2 * k + 2) = 0 by omega]
    rfl

/-- The enlarged tile types of `q^{2k+2} p`. -/
def tyD (k j : ℕ) : ZTile :=
  if j = 0 then ZTile.one else if j ≤ 2 * k + 1 then ZTile.oneD else ZTile.zero

/-- The positions of the enlarged tiles of `q^{2k+2} p`. -/
def posD (k j : ℕ) : GInt := if j ≤ 2 * k + 1 then ((j : ℤ), (j : ℤ)) else (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1)

theorem posF_wD (k j : ℕ) (hj : j < 2 * k + 3) :
    posF .horizontal false (lettersOf (wD k) false) j = posD k j := by
  induction j with
  | zero => simp [posF, posD, Prod.ext_iff]
  | succ j ih =>
    rw [posF_fwd_succ, ih (by omega), letter_wD k (j + 1) hj]
    unfold posD zeroOneHorizontalStep
    split_ifs <;> simp [Prod.ext_iff] <;> omega

theorem tile_type_wD (k j : ℕ) (hj : j < 2 * k + 3) :
    hTileAt (lettersOf (wD k) false) j = tyD k j := by
  unfold hTileAt hPrev tyD
  rw [letter_wD k j hj]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [BaseHpLadder.hTt_pq]
  · rw [if_neg (show j ≠ 0 by omega), letter_wD k (j - 1) (by omega)]
    split_ifs <;> simp_all [BaseHpLadder.hTt_xp, hTt_qq]
    all_goals try omega

theorem tile_wD (k j : ℕ) (hj : j < 2 * k + 3) :
    (HPE (wD k)).tile j = (tyD k j, posD k j) := by
  rw [HPE_tile (wD k) j (by rw [wD_length]; exact hj), tile_type_wD k j hj, posF_wD k j hj]

/-- The value of `paperNearStairValue` at a point of a diagonal translate, with the difference of coordinates. -/
theorem pnsv_diag (d j a b : ℤ) :
    paperNearStairValue d ((a, b) + (j, j) + (0, 1)) =
      -((b + 1 - a) ^ 2 / 4) + min (d - (b + j + 1)) 0 +
        (if (a + j, b + j + 1) = (0, d + 1) ∨ (a + j, b + j + 1) = (d + 1, d - 1) then 1 else 0) := by
  unfold paperNearStairValue
  simp only [Prod.mk_add_mk, add_zero]
  have e : b + j + 1 - (a + j) = b + 1 - a := by ring
  rw [e]

/-- The general point of the last zero tile: its difference is `b - a - 1`. -/
theorem pnsv_last (k a b : ℤ) :
    paperNearStairValue (2 * k + 3) ((a, b) + (2 * k + 3, 2 * k + 1) + (0, 1)) =
      -((b - a - 1) ^ 2 / 4) + min (1 - b) 0 +
        (if (a + (2 * k + 3), b + (2 * k + 1) + 1) = (0, 2 * k + 3 + 1) ∨
            (a + (2 * k + 3), b + (2 * k + 1) + 1) = (2 * k + 3 + 1, 2 * k + 3 - 1) then 1 else 0) := by
  unfold paperNearStairValue
  simp only [Prod.mk_add_mk, add_zero]
  have e : b + (2 * k + 1) + 1 - (a + (2 * k + 3)) = b - a - 1 := by ring
  rw [e]
  have e2 : 2 * k + 3 - (b + (2 * k + 1) + 1) = 1 - b := by ring
  rw [e2]

theorem val_one0 (k : ℕ) (u : GInt) (hu : u ∈ tileShape ZTile.one) :
    paperNearStairValue (2 * (k : ℤ) + 3) (u + (0, 0) + (0, 1)) = zTileOdo ZTile.one u := by
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rw [pnsv_diag] <;> norm_num [zTileOdo, oneOdometer] <;> (try split_ifs) <;> omega

theorem val_oneD (k j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ 2 * k + 1) (u : GInt) (hu : u ∈ tileShape ZTile.oneD) :
    paperNearStairValue (2 * (k : ℤ) + 3) (u + ((j : ℤ), (j : ℤ)) + (0, 1)) = zTileOdo ZTile.oneD u := by
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rw [pnsv_diag] <;> norm_num [zTileOdo, oneOdometer] <;> (try split_ifs) <;> omega

theorem val_zero_last (k : ℕ) (u : GInt) (hu : u ∈ tileShape ZTile.zero) :
    paperNearStairValue (2 * (k : ℤ) + 3) (u + (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1) + (0, 1)) =
      zTileOdo ZTile.zero u := by
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rw [pnsv_last] <;> norm_num [zTileOdo, zeroOdometer] <;> (try split_ifs) <;> omega

theorem near_tile_value (k j : ℕ) (hj : j < 2 * k + 3) (u : GInt) (hu : u ∈ tileShape (tyD k j)) :
    paperNearStairValue (2 * (k : ℤ) + 3) (u + posD k j + (0, 1)) = zTileOdo (tyD k j) u := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have h1 : tyD k 0 = ZTile.one := by simp [tyD]
    have h2 : posD k 0 = (0, 0) := by simp [posD]
    rw [h1] at hu ⊢
    rw [h2]
    exact val_one0 k u hu
  · by_cases hjk : j ≤ 2 * k + 1
    · have h1 : tyD k j = ZTile.oneD := by unfold tyD; simp [show j ≠ 0 by omega, hjk]
      have h2 : posD k j = ((j : ℤ), (j : ℤ)) := by unfold posD; simp [hjk]
      rw [h1] at hu ⊢
      rw [h2]
      exact val_oneD k j hj0 hjk u hu
    · have h1 : tyD k j = ZTile.zero := by unfold tyD; simp [show j ≠ 0 by omega, hjk]
      have h2 : posD k j = (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1) := by
        unfold posD; simp [hjk]
      rw [h1] at hu ⊢
      rw [h2]
      exact val_zero_last k u hu

/-- The forward horizontal clause of the odd odometer of `2^k`: the paper near-one stair `paperNearStairValue (2k+3)` at the
shift `(0,1)` respects the forward string `hStringAt (q^{2k+2} p) (0,0)`. -/
theorem respects_hp_odd_two (k : ℕ) :
    RespectsTiles .horizontal false (hStringAt (wD k) (0, 0))
      (fun x => paperNearStairValue (2 * (k : ℤ) + 3) (x + (0, 1))) := by
  apply respectsTiles_hp_of_tiles
  intro j hj x hx
  have hj' : j < 2 * k + 3 := by
    rw [HPE_n, wD_length] at hj
    exact hj
  have hdom : x ∈ (HPE (wD k)).dom j := hx
  unfold PTFamily.dom at hdom
  rw [tile_wD k j hj'] at hdom ⊢
  simp only [List.mem_map] at hdom
  obtain ⟨u, hu, rfl⟩ := hdom
  simp only [add_sub_cancel_right]
  exact near_tile_value k j hj' u hu

end FLatticePaper.Tiles.BaseHpNear
