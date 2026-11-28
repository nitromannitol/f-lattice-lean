import FLatticePaper.Tiles.BaseRespectsHorizontal
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.BaseHpLadder

/-! # The forward horizontal clause of the even odometer of `3^k` (`k ≥ 0`, the case `k = 0` is the empty word)

The forward word of the even tile of `3^k` is `q p^{k+1}` (`RegisterLink.quad_threes`, second component). Its enlarged tiles: `one`
at `(0,0)` and `zero` at `(2j,0)` for `1 ≤ j ≤ k+1`. The even odometer is `paperStairValue (2k+3)`, and on each of these tiles it is
the zero-one tile odometer (no affine part). -/

namespace FLatticePaper.Tiles.BaseHpStair

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Construction
open FLatticePaper.Tiles.BaseHpLadder (getD_rep getD_append_eq)

/-- The forward word of the even tile of `3^k`: `q p^{k+1}`. -/
def wE (k : ℕ) : BinaryWord := [Letter.q] ++ List.replicate (k + 1) Letter.p

theorem wE_length (k : ℕ) : (wE k).length = k + 2 := by
  simp [wE]

theorem hWordOf_three_true (k : ℕ) : hWordOf (List.replicate k Digit.three) true = wE k := by
  have h := (RegisterLink.quad_threes k).2.1
  simp only [hWordOf, if_true]
  rw [h]
  simp [wE]

theorem letter_wE (k j : ℕ) (hj : j < k + 2) :
    lettersOf (wE k) false j = if j = 0 then Letter.q else Letter.p := by
  unfold lettersOf
  simp only [Bool.false_eq_true, if_false]
  unfold wE
  rw [getD_append_eq]
  simp only [List.length_singleton]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · rw [if_neg (by omega), getD_rep]
    split_ifs <;> first | rfl | omega

/-- The enlarged tile types of `q p^{k+1}`: `one` at the first position, `zero` elsewhere. -/
def tyE (j : ℕ) : ZTile := if j = 0 then ZTile.one else ZTile.zero

/-- The positions of the enlarged tiles of `q p^{k+1}`. -/
def posE (j : ℕ) : GInt := if j = 0 then (0, 0) else (2 * (j : ℤ), 0)

theorem posF_wE (k j : ℕ) (hj : j < k + 2) :
    posF .horizontal false (lettersOf (wE k) false) j = posE j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [posF_fwd_succ, ih (by omega), letter_wE k (j + 1) hj]
    unfold posE zeroOneHorizontalStep
    split_ifs <;> simp [Prod.ext_iff] <;> omega

theorem tile_type_wE (k j : ℕ) (hj : j < k + 2) :
    hTileAt (lettersOf (wE k) false) j = tyE j := by
  unfold hTileAt hPrev tyE
  rw [letter_wE k j hj]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [BaseHpLadder.hTt_pq]
  · rw [if_neg (show j ≠ 0 by omega), letter_wE k (j - 1) (by omega)]
    split_ifs <;> simp_all [BaseHpLadder.hTt_xp]

theorem tile_wE (k j : ℕ) (hj : j < k + 2) :
    (HPE (wE k)).tile j = (tyE j, posE j) := by
  rw [HPE_tile (wE k) j (by rw [wE_length]; exact hj), tile_type_wE k j hj, posF_wE k j hj]

theorem stair_val_j0 (k : ℕ) (u : GInt) (hu : u ∈ tileShape ZTile.one) :
    paperStairValue (2 * (k : ℤ) + 3) (u + (0, 0)) = zTileOdo ZTile.one u := by
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [paperStairValue, zTileOdo, oneOdometer]

theorem stair_val_zero (k j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) (u : GInt) (hu : u ∈ tileShape ZTile.zero) :
    paperStairValue (2 * (k : ℤ) + 3) (u + (2 * (j : ℤ), 0)) = zTileOdo ZTile.zero u := by
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [paperStairValue, zTileOdo, zeroOdometer] <;> (try split_ifs) <;> omega

theorem stair_tile_value (k j : ℕ) (hj : j < k + 2) (u : GInt) (hu : u ∈ tileShape (tyE j)) :
    paperStairValue (2 * (k : ℤ) + 3) (u + posE j) = zTileOdo (tyE j) u := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have h1 : tyE 0 = ZTile.one := by simp [tyE]
    have h2 : posE 0 = (0, 0) := by simp [posE]
    rw [h1] at hu ⊢
    rw [h2]
    exact stair_val_j0 k u hu
  · have h1 : tyE j = ZTile.zero := by unfold tyE; simp [show j ≠ 0 by omega]
    have h2 : posE j = (2 * (j : ℤ), 0) := by unfold posE; simp [show j ≠ 0 by omega]
    rw [h1] at hu ⊢
    rw [h2]
    exact stair_val_zero k j hj0 (by omega) u hu

/-- The forward horizontal clause of the even odometer of `3^k` (with `k = 0`, the empty word): the paper stair value
`paperStairValue (2k+3)` respects the forward string `hStringAt (q p^{k+1}) (0,0)`. -/
theorem respects_hp_even_three (k : ℕ) :
    RespectsTiles .horizontal false (hStringAt (wE k) (0, 0)) (fun x => paperStairValue (2 * (k : ℤ) + 3) x) := by
  apply respectsTiles_hp_of_tiles
  intro j hj x hx
  have hj' : j < k + 2 := by
    rw [HPE_n, wE_length] at hj
    exact hj
  have hdom : x ∈ (HPE (wE k)).dom j := hx
  unfold PTFamily.dom at hdom
  rw [tile_wE k j hj'] at hdom ⊢
  simp only [List.mem_map] at hdom
  obtain ⟨u, hu, rfl⟩ := hdom
  simp only [add_sub_cancel_right]
  exact stair_tile_value k j hj' u hu

end FLatticePaper.Tiles.BaseHpStair
