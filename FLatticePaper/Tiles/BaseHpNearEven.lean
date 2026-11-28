import FLatticePaper.Tiles.BaseRespectsHorizontal
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.BaseHpLadder
import FLatticePaper.Tiles.BaseTileProps

/-! # The forward horizontal clause of the even odometer of `2^k` (`k ≥ 1`)

The forward word of the even tile of `2^k` is `q^{2k+1} p` (`RegisterLink.quad_twos`, `childQ`). Its enlarged tiles: `one` at
`(0,0)`, `oneD` at `(j,j)` for `1 ≤ j ≤ 2k`, and `zero` at `(2k+2, 2k)`. The even odometer is `paperNearLadderValue (2k+2)` shifted by
`(0,1)`, and on each of these tiles it is the zero-one tile odometer (no affine part). -/

namespace FLatticePaper.Tiles.BaseHpNearEven

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Construction
open FLatticePaper.Tiles.BaseHpLadder (getD_rep getD_append_eq)
open FLatticePaper.Tiles.BaseTileProps

/-- The forward word of the even tile of `2^k`: `q^{2k+1} p`. -/
def wEv (k : ℕ) : BinaryWord := List.replicate (2 * k + 1) Letter.q ++ [Letter.p]

theorem wEv_length (k : ℕ) : (wEv k).length = 2 * k + 2 := by
  simp [wEv]

theorem hWordOf_two_true (k : ℕ) : hWordOf (List.replicate k Digit.two) true = wEv k := by
  have h := (RegisterLink.quad_twos k).2.1
  simp only [hWordOf, if_true]
  rw [h]
  rfl

theorem hTt_qq : hTt Letter.q Letter.q = ZTile.oneD := rfl

theorem letter_wEv (k j : ℕ) (hj : j < 2 * k + 2) :
    lettersOf (wEv k) false j = if j ≤ 2 * k then Letter.q else Letter.p := by
  unfold lettersOf
  simp only [Bool.false_eq_true, if_false]
  unfold wEv
  rw [getD_append_eq]
  simp only [List.length_replicate]
  by_cases h1 : j ≤ 2 * k
  · rw [getD_rep]
    simp [show j < 2 * k + 1 by omega, h1]
  · rw [if_neg (show ¬ j < 2 * k + 1 by omega), if_neg h1, show j - (2 * k + 1) = 0 by omega]
    rfl

/-- The enlarged tile types of `q^{2k+1} p`. -/
def tyEv (k j : ℕ) : ZTile :=
  if j = 0 then ZTile.one else if j ≤ 2 * k then ZTile.oneD else ZTile.zero

/-- The positions of the enlarged tiles of `q^{2k+1} p`. -/
def posEv (k j : ℕ) : GInt := if j ≤ 2 * k then ((j : ℤ), (j : ℤ)) else (2 * (k : ℤ) + 2, 2 * (k : ℤ))

theorem posF_wEv (k j : ℕ) (hj : j < 2 * k + 2) :
    posF .horizontal false (lettersOf (wEv k) false) j = posEv k j := by
  induction j with
  | zero => simp [posF, posEv, Prod.ext_iff]
  | succ j ih =>
    rw [posF_fwd_succ, ih (by omega), letter_wEv k (j + 1) hj]
    unfold posEv zeroOneHorizontalStep
    split_ifs <;> simp [Prod.ext_iff] <;> omega

theorem tile_type_wEv (k j : ℕ) (hj : j < 2 * k + 2) :
    hTileAt (lettersOf (wEv k) false) j = tyEv k j := by
  unfold hTileAt hPrev tyEv
  rw [letter_wEv k j hj]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [BaseHpLadder.hTt_pq]
  · rw [if_neg (show j ≠ 0 by omega), letter_wEv k (j - 1) (by omega)]
    split_ifs <;> simp_all [BaseHpLadder.hTt_xp, hTt_qq]
    all_goals try omega

theorem tile_wEv (k j : ℕ) (hj : j < 2 * k + 2) :
    (HPE (wEv k)).tile j = (tyEv k j, posEv k j) := by
  rw [HPE_tile (wEv k) j (by rw [wEv_length]; exact hj), tile_type_wEv k j hj, posF_wEv k j hj]

/-- The diagonal translate of the near-ladder value: the difference of coordinates is `b + 1 - a`. -/
theorem pnl_diag (d j a b : ℤ) :
    paperNearLadderValue d ((a, b) + (j, j) + (0, 1)) =
      -((b + 1 - a) ^ 2 / 4) + min 0 (d - (b + j + 1)) + min 0 (2 * d - (b + j + 1)) +
        max ((b + 1 - a) - d) 0 +
        (if (a + j, b + j + 1) = (-1, 2 * d + 1) ∨ (a + j, b + j + 1) = (d + 1, d - 1) ∨
            (b + 1 - a = d ∧ 0 < a + j ∧ a + j < d) then 1 else 0) := by
  simp only [Prod.mk_add_mk, add_zero]
  rw [pnlV]
  rw [show b + j + 1 - (a + j) = b + 1 - a by ring]

/-- The last zero tile at `(2k+2, 2k)`: the difference of coordinates is `b - a - 1`. -/
theorem pnl_last (k a b : ℤ) :
    paperNearLadderValue (2 * k + 2) ((a, b) + (2 * k + 2, 2 * k) + (0, 1)) =
      -((b - a - 1) ^ 2 / 4) + min 0 (1 - b) + min 0 (2 * k + 3 - b) + max ((b - a - 1) - (2 * k + 2)) 0 +
        (if (a + (2 * k + 2), b + 2 * k + 1) = (-1, 2 * (2 * k + 2) + 1) ∨
            (a + (2 * k + 2), b + 2 * k + 1) = (2 * k + 2 + 1, 2 * k + 2 - 1) ∨
            (b - a - 1 = 2 * k + 2 ∧ 0 < a + (2 * k + 2) ∧ a + (2 * k + 2) < 2 * k + 2) then 1 else 0) := by
  simp only [Prod.mk_add_mk, add_zero]
  rw [pnlV]
  rw [show b + 2 * k + 1 - (a + (2 * k + 2)) = b - a - 1 by ring]
  rw [show 2 * k + 2 - (b + 2 * k + 1) = 1 - b by ring]
  rw [show 2 * (2 * k + 2) - (b + 2 * k + 1) = 2 * k + 3 - b by ring]

theorem val_one0 (k : ℕ) (u : GInt) (hu : u ∈ tileShape ZTile.one) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (u + (0, 0) + (0, 1)) = zTileOdo ZTile.one u := by
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rw [pnl_diag] <;> norm_num [zTileOdo, oneOdometer] <;> (try split_ifs) <;> omega

theorem val_oneD (k j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ 2 * k) (hk : 1 ≤ k) (u : GInt) (hu : u ∈ tileShape ZTile.oneD) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (u + ((j : ℤ), (j : ℤ)) + (0, 1)) = zTileOdo ZTile.oneD u := by
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rw [pnl_diag] <;> norm_num [zTileOdo, oneOdometer] <;> (try split_ifs) <;> omega

theorem val_zero_last (k : ℕ) (u : GInt) (hu : u ∈ tileShape ZTile.zero) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (u + (2 * (k : ℤ) + 2, 2 * (k : ℤ)) + (0, 1)) =
      zTileOdo ZTile.zero u := by
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rw [pnl_last] <;> norm_num [zTileOdo, zeroOdometer] <;> (try split_ifs) <;> omega

theorem near_even_tile_value (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 * k + 2) (u : GInt)
    (hu : u ∈ tileShape (tyEv k j)) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (u + posEv k j + (0, 1)) = zTileOdo (tyEv k j) u := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have h1 : tyEv k 0 = ZTile.one := by simp [tyEv]
    have h2 : posEv k 0 = (0, 0) := by simp [posEv]
    rw [h1] at hu ⊢
    rw [h2]
    exact val_one0 k u hu
  · by_cases hjk : j ≤ 2 * k
    · have h1 : tyEv k j = ZTile.oneD := by unfold tyEv; simp [show j ≠ 0 by omega, hjk]
      have h2 : posEv k j = ((j : ℤ), (j : ℤ)) := by unfold posEv; simp [hjk]
      rw [h1] at hu ⊢
      rw [h2]
      exact val_oneD k j hj0 hjk hk u hu
    · have h1 : tyEv k j = ZTile.zero := by unfold tyEv; simp [show j ≠ 0 by omega, hjk]
      have h2 : posEv k j = (2 * (k : ℤ) + 2, 2 * (k : ℤ)) := by
        unfold posEv; simp [hjk]
      rw [h1] at hu ⊢
      rw [h2]
      exact val_zero_last k u hu

/-- The forward horizontal clause of the even odometer of `2^k` (`k ≥ 1`): the paper near-one ladder
`paperNearLadderValue (2k+2)` at the shift `(0,1)` respects the forward string `hStringAt (q^{2k+1} p) (0,0)`. -/
theorem respects_hp_even_two (k : ℕ) (hk : 1 ≤ k) :
    RespectsTiles .horizontal false (hStringAt (wEv k) (0, 0))
      (fun x => paperNearLadderValue (2 * (k : ℤ) + 2) (x + (0, 1))) := by
  apply respectsTiles_hp_of_tiles
  intro j hj x hx
  have hj' : j < 2 * k + 2 := by
    rw [HPE_n, wEv_length] at hj
    exact hj
  have hdom : x ∈ (HPE (wEv k)).dom j := hx
  unfold PTFamily.dom at hdom
  rw [tile_wEv k j hj'] at hdom ⊢
  simp only [List.mem_map] at hdom
  obtain ⟨u, hu, rfl⟩ := hdom
  simp only [add_sub_cancel_right]
  exact near_even_tile_value k j hk hj' u hu

end FLatticePaper.Tiles.BaseHpNearEven
