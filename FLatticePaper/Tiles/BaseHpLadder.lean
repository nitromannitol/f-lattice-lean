import FLatticePaper.Tiles.BaseRespectsHorizontal
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.SiteStrings

/-! # The forward horizontal clause of the odd odometer of `3^k` (`k ≥ 1`)

The forward word of the odd tile of `3^k` is `q p^k q p^{k+1}` (`RegisterLink.quad_threes`). Its enlarged tiles: `one` at `(0,0)`,
`zero` at `(2j,0)` for `1 ≤ j ≤ k`, `one` at `(2k+1,1)`, and `zero` at `(2j-1,1)` for `k+2 ≤ j ≤ 2k+2`. The odd odometer is
`paperLadderValue (2k+2)`, and on each of these tiles it is the zero-one tile odometer (no affine part). -/

namespace FLatticePaper.Tiles.BaseHpLadder

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Construction
open FLatticePaper.Tiles.BaseTileProps

/-- The forward word of the odd tile of `3^k`. -/
def wL (k : ℕ) : BinaryWord :=
  [Letter.q] ++ (List.replicate k Letter.p ++ ([Letter.q] ++ List.replicate (k + 1) Letter.p))

theorem wL_length (k : ℕ) : (wL k).length = 2 * k + 3 := by
  simp [wL]
  omega

theorem hWordOf_three_false (k : ℕ) : hWordOf (List.replicate k Digit.three) false = wL k := by
  have h := (RegisterLink.quad_threes k).1
  simp only [hWordOf, Bool.false_eq_true, if_false]
  rw [h]
  simp [wL, List.append_assoc]

theorem getD_rep (n : ℕ) (a d : Letter) (i : ℕ) :
    (List.replicate n a).getD i d = if i < n then a else d := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.replicate_succ, List.getD_cons_succ, ih]
      by_cases h : i < n
      · simp [h, show i + 1 < n + 1 by omega]
      · simp [h, show ¬ i + 1 < n + 1 by omega]

theorem getD_append_eq (l r : List Letter) (j : ℕ) :
    (l ++ r).getD j Letter.p = if j < l.length then l.getD j Letter.p else r.getD (j - l.length) Letter.p := by
  by_cases h : j < l.length
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega)]

theorem letter_wL (k j : ℕ) (hj : j < 2 * k + 3) :
    lettersOf (wL k) false j =
      if j = 0 then Letter.q else if j ≤ k then Letter.p else if j = k + 1 then Letter.q else Letter.p := by
  unfold lettersOf
  simp only [Bool.false_eq_true, if_false]
  unfold wL
  rw [getD_append_eq]
  simp only [List.length_singleton]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · rw [if_neg (by omega), getD_append_eq, getD_rep, getD_append_eq]
    simp only [List.length_replicate, List.length_singleton, getD_rep]
    split_ifs <;> first | rfl | omega | simp_all

/-- The enlarged tile types of `q p^k q p^{k+1}`: `one` at the first and at the `q` position, `zero` elsewhere. -/
def tyL (k j : ℕ) : ZTile := if j = 0 ∨ j = k + 1 then ZTile.one else ZTile.zero

/-- The positions of the enlarged tiles of `q p^k q p^{k+1}`. -/
def posL (k j : ℕ) : GInt := if j = 0 then (0, 0) else if j ≤ k then (2 * (j : ℤ), 0) else (2 * (j : ℤ) - 1, 1)

theorem posF_wL (k j : ℕ) (hj : j < 2 * k + 3) :
    posF .horizontal false (lettersOf (wL k) false) j = posL k j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [posF_fwd_succ, ih (by omega), letter_wL k (j + 1) hj]
    unfold posL zeroOneHorizontalStep
    split_ifs <;> simp [Prod.ext_iff] <;> omega

theorem hTt_xp (x : Letter) : hTt x Letter.p = ZTile.zero := by
  cases x <;> rfl

theorem hTt_pq : hTt Letter.p Letter.q = ZTile.one := rfl

theorem tile_type_wL (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 * k + 3) :
    hTileAt (lettersOf (wL k) false) j = tyL k j := by
  unfold hTileAt hPrev tyL
  rw [letter_wL k j hj]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [hTt_pq]
  · rw [if_neg (show j ≠ 0 by omega), letter_wL k (j - 1) (by omega)]
    split_ifs <;> simp_all [hTt_xp, hTt_pq]

theorem tile_wL (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 * k + 3) :
    (HPE (wL k)).tile j = (tyL k j, posL k j) := by
  rw [HPE_tile (wL k) j (by rw [wL_length]; exact hj), tile_type_wL k j hk hj, posF_wL k j hj]

theorem hp_val_j0 (k : ℕ) (u : GInt) (hu : u ∈ tileShape ZTile.one) :
    paperLadderValue (2 * (k : ℤ) + 2) (u + (0, 0)) = zTileOdo ZTile.one u := by
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [plV, zTileOdo, oneOdometer] <;> (try split_ifs) <;> omega

theorem hp_val_zero_mid (k j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) (u : GInt) (hu : u ∈ tileShape ZTile.zero) :
    paperLadderValue (2 * (k : ℤ) + 2) (u + (2 * (j : ℤ), 0)) = zTileOdo ZTile.zero u := by
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [plV, zTileOdo, zeroOdometer] <;> (try split_ifs) <;> omega

theorem hp_val_one_mid (k : ℕ) (u : GInt) (hu : u ∈ tileShape ZTile.one) :
    paperLadderValue (2 * (k : ℤ) + 2) (u + (2 * (k : ℤ) + 1, 1)) = zTileOdo ZTile.one u := by
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [plV, zTileOdo, oneOdometer] <;> (try split_ifs) <;> omega

theorem hp_val_zero_tail (k j : ℕ) (hj1 : k + 2 ≤ j) (hjk : j < 2 * k + 3) (u : GInt)
    (hu : u ∈ tileShape ZTile.zero) :
    paperLadderValue (2 * (k : ℤ) + 2) (u + (2 * (j : ℤ) - 1, 1)) = zTileOdo ZTile.zero u := by
  obtain ⟨a, b⟩ := u
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [plV, zTileOdo, zeroOdometer] <;> (try split_ifs) <;> omega

theorem hp_tile_value (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 * k + 3) (u : GInt)
    (hu : u ∈ tileShape (tyL k j)) :
    paperLadderValue (2 * (k : ℤ) + 2) (u + posL k j) = zTileOdo (tyL k j) u := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have h1 : tyL k 0 = ZTile.one := by simp [tyL]
    have h2 : posL k 0 = (0, 0) := by simp [posL]
    rw [h1] at hu ⊢
    rw [h2]
    exact hp_val_j0 k u hu
  · by_cases hjk : j ≤ k
    · have h1 : tyL k j = ZTile.zero := by
        unfold tyL; simp [show j ≠ 0 by omega, show j ≠ k + 1 by omega]
      have h2 : posL k j = (2 * (j : ℤ), 0) := by
        unfold posL; simp [show j ≠ 0 by omega, hjk]
      rw [h1] at hu ⊢
      rw [h2]
      exact hp_val_zero_mid k j hj0 hjk u hu
    · by_cases hj1 : j = k + 1
      · have h1 : tyL k j = ZTile.one := by unfold tyL; simp [hj1]
        have h2 : posL k j = (2 * (k : ℤ) + 1, 1) := by
          unfold posL
          simp only [show j ≠ 0 by omega, if_false, show ¬ (j ≤ k) by omega, if_false]
          subst hj1
          push_cast
          ring_nf
        rw [h1] at hu ⊢
        rw [h2]
        exact hp_val_one_mid k u hu
      · have h1 : tyL k j = ZTile.zero := by
          unfold tyL; simp [show j ≠ 0 by omega, hj1]
        have h2 : posL k j = (2 * (j : ℤ) - 1, 1) := by
          unfold posL
          simp only [show j ≠ 0 by omega, if_false, show ¬ (j ≤ k) by omega, if_false]
        rw [h1] at hu ⊢
        rw [h2]
        exact hp_val_zero_tail k j (by omega) hj u hu

/-- The forward horizontal clause of the odd odometer of `3^k`: the paper ladder value `paperLadderValue (2k+2)` respects the
forward string `hStringAt (q p^k q p^{k+1}) (0,0)`. -/
theorem respects_hp_odd_three (k : ℕ) (hk : 1 ≤ k) :
    RespectsTiles .horizontal false (hStringAt (wL k) (0, 0)) (fun x => paperLadderValue (2 * (k : ℤ) + 2) x) := by
  apply respectsTiles_hp_of_tiles
  intro j hj x hx
  have hj' : j < 2 * k + 3 := by
    rw [HPE_n, wL_length] at hj
    exact hj
  have hdom : x ∈ (HPE (wL k)).dom j := hx
  unfold PTFamily.dom at hdom
  rw [tile_wL k j hk hj'] at hdom ⊢
  simp only [List.mem_map] at hdom
  obtain ⟨u, hu, rfl⟩ := hdom
  simp only [add_sub_cancel_right]
  exact hp_tile_value k j hk hj' u hu

end FLatticePaper.Tiles.BaseHpLadder
