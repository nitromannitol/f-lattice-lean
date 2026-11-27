import FLatticePaper.Tiles.RespectsLetters
import FLatticePaper.Tiles.NearLadderAltRespects
import FLatticePaper.Construction.BaseCaseRecurrence

/-! # The alternate ladder tile `T̂_{1/d}` as a partial `w_v`-pseudo-square (surgical `lemma:basecase_3k_odd_alt`, Moreover)

For `d = 2k+2` (`k ≥ 1`) and the word `w_v = p^{2k+1} q`, the tile `T̂_{1/d}` has the reversed vertical string of `w_v`
anchored at its lower-left point `(-1,-1)`, and the forward vertical string of `w_v` at a free anchor `(4k+1, 1)`; the
odometer `ĝ_{1/d}` (`paperLadderAltValue d`) respects both, by `PTFamily.respects_of_triples`.

Section 1 computes the placed vertical strings explicitly. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Construction (paperLadderAltTile paperLadderAltValue paperLadderAltA paperLadderAltB
  paperLadderAltC paperLadderAltD)

/-! ### 1. The placed vertical strings -/

theorem lv_cons_pp_s (w : BinaryWord) (c : GInt) :
    vStringAt (Letter.p :: Letter.p :: w) c =
      (ZTile.zero, c) :: vStringAt (Letter.p :: w) (c + ((-1 : ℤ), (1 : ℤ))) := by
  simp [vStringAt, vOffset, letterZTile, List.scanl_cons]

theorem lv_cons_pp_r (w : BinaryWord) (c : GInt) :
    vRevStringAt (Letter.p :: Letter.p :: w) c =
      (ZTile.zero, c) :: vRevStringAt (Letter.p :: w) (c + ((-1 : ℤ), (1 : ℤ))) := by
  simp [vRevStringAt, vRevOffset, letterZTile, List.scanl_cons]

theorem lv_cons_qp_r (w : BinaryWord) (c : GInt) :
    vRevStringAt (Letter.q :: Letter.p :: w) c =
      (ZTile.one, c) :: vRevStringAt (Letter.p :: w) (c + ((0 : ℤ), (1 : ℤ))) := by
  simp [vRevStringAt, vRevOffset, letterZTile, List.scanl_cons]

/-- The reversed run `p^{n+1}`: zero tiles at `c + (-j, j)`. -/
theorem lv_vRevP (n : ℕ) (c : GInt) :
    vRevStringAt (List.replicate (n + 1) Letter.p) c =
      (List.range (n + 1)).map (fun j : ℕ => (ZTile.zero, (c.1 - (j : ℤ), c.2 + (j : ℤ)))) := by
  induction n generalizing c with
  | zero => simp [vRevStringAt, letterZTile]
  | succ n ih =>
    have hr : List.range (n + 1 + 1) = 0 :: List.map Nat.succ (List.range (n + 1)) := by
      rw [List.range_succ_eq_map]
    rw [show List.replicate (n + 1 + 1) Letter.p = Letter.p :: Letter.p :: List.replicate n Letter.p from rfl,
      lv_cons_pp_r, show Letter.p :: List.replicate n Letter.p = List.replicate (n + 1) Letter.p from rfl,
      ih, hr, List.map_cons, List.map_map, List.cons_eq_cons]
    refine ⟨by simp, ?_⟩
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, Nat.succ_eq_add_one, Prod.mk.injEq, true_and, Prod.fst_add, Prod.snd_add]
    push_cast
    ring_nf
    simp

/-- The forward vertical string `p^{m+1} q` at `c`: zero tiles at `c + (-j, j)`, then the one tile at `c + (-m, m+2)`. -/
theorem lv_vString (m : ℕ) (c : GInt) :
    vStringAt (List.replicate (m + 1) Letter.p ++ [Letter.q]) c =
      (List.range (m + 1)).map (fun j : ℕ => (ZTile.zero, (c.1 - (j : ℤ), c.2 + (j : ℤ)))) ++
        [(ZTile.one, (c.1 - (m : ℤ), c.2 + (m : ℤ) + 2))] := by
  induction m generalizing c with
  | zero => simp [vStringAt, vOffset, letterZTile]; ext <;> simp
  | succ m ih =>
    have hr : List.range (m + 1 + 1) = 0 :: List.map Nat.succ (List.range (m + 1)) := by
      rw [List.range_succ_eq_map]
    rw [show List.replicate (m + 1 + 1) Letter.p ++ [Letter.q] =
        Letter.p :: Letter.p :: (List.replicate m Letter.p ++ [Letter.q]) from rfl,
      lv_cons_pp_s, show Letter.p :: (List.replicate m Letter.p ++ [Letter.q]) =
        List.replicate (m + 1) Letter.p ++ [Letter.q] from rfl,
      ih, hr, List.map_cons, List.cons_append, List.map_map, List.cons_eq_cons]
    refine ⟨by simp, ?_⟩
    congr 1
    · apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply, Nat.succ_eq_add_one, Prod.mk.injEq, true_and, Prod.fst_add, Prod.snd_add]
      push_cast
      ring_nf
      simp
    · simp only [List.cons.injEq, and_true, Prod.mk.injEq, Prod.fst_add, Prod.snd_add]
      push_cast
      ring_nf
      simp

/-- The reversed vertical string of `q p^{m+1}` at `c`: the one tile at `c`, then zero tiles at `c + (-1-j, 1+j)`... with
`c.2 + 1 + j` in the second coordinate. -/
theorem lv_vRevString (m : ℕ) (c : GInt) :
    vRevStringAt (Letter.q :: List.replicate (m + 1) Letter.p) c =
      (ZTile.one, c) :: (List.range (m + 1)).map (fun j : ℕ =>
        (ZTile.zero, (c.1 - (j : ℤ), c.2 + 1 + (j : ℤ)))) := by
  rw [show Letter.q :: List.replicate (m + 1) Letter.p = Letter.q :: Letter.p :: List.replicate m Letter.p from rfl,
    lv_cons_qp_r, show Letter.p :: List.replicate m Letter.p = List.replicate (m + 1) Letter.p from rfl,
    lv_vRevP m (c + ((0 : ℤ), (1 : ℤ)))]
  congr 1
  apply List.map_congr_left
  intro j _
  simp

/-! ### 2. The two families of `w_v = p^{2k+1} q` -/

/-- The word `p^{2k+1} q` of `lemma:basecase_3k_odd_alt`. -/
def lvWord (k : ℕ) : BinaryWord := List.replicate (2 * k + 1) Letter.p ++ [Letter.q]

/-- The forward family: zero tiles along `(4k+1-j, 1+j)`, then the one tile at `(2k+1, 2k+3)`; affine factors
`(0, -(j+1))` and constants `C(j+2,2) - 1`. -/
def lvFwd (k : ℕ) : PTFamily where
  ts := vStringAt (lvWord k) (4 * (k : ℤ) + 1, 1)
  a := fun j => ((0 : ℤ), -((j : ℤ) + 1))
  b := fun j => ((j : ℤ) + 1) * ((j : ℤ) + 1 + 1) / 2 - 1

/-- The reversed family: the one tile at `(-1,-1)`, then zero tiles along `(-(j+1), j)`; affine factors `(1, -j)` on
the zero tiles and `0` on the one tile; constants `C(j,2)`. -/
def lvRev (k : ℕ) : PTFamily where
  ts := vRevStringAt (lvWord k).reverse (-1, -1)
  a := fun j => if j = 0 then ((0 : ℤ), (0 : ℤ)) else ((1 : ℤ), -(j : ℤ))
  b := fun j => (j : ℤ) * ((j : ℤ) - 1) / 2

theorem lv_ind (d : ℤ) (x : GInt) :
    (paperLadderAltA d ∪ paperLadderAltB d).indicator (fun _ => (1 : ℤ)) x =
      if (x.1 = -1 ∧ x.2 = -1) ∨ (x.1 = d ∧ x.2 = d + 2) ∨ (x.1 + x.2 = d ∧ 0 < x.1 ∧ x.1 < d - 1)
        then 1 else 0 := by
  classical
  by_cases h : (x.1 = -1 ∧ x.2 = -1) ∨ (x.1 = d ∧ x.2 = d + 2) ∨ (x.1 + x.2 = d ∧ 0 < x.1 ∧ x.1 < d - 1)
  · have hm : x ∈ paperLadderAltA d ∪ paperLadderAltB d := by
      unfold paperLadderAltA paperLadderAltB
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff]
      tauto
    rw [Set.indicator_apply, if_pos hm, if_pos h]
  · have hm : x ∉ paperLadderAltA d ∪ paperLadderAltB d := by
      unfold paperLadderAltA paperLadderAltB
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff]
      tauto
    rw [Set.indicator_apply, if_neg hm, if_neg h]

theorem lv_value_eq (d : ℤ) (x : GInt) :
    paperLadderAltValue d x = -(x.2 * (x.2 + 1) / 2) + min 0 x.1 + min 0 (d - x.1 - 1) + max (x.1 + x.2 - d) 0 +
      (if (x.1 = -1 ∧ x.2 = -1) ∨ (x.1 = d ∧ x.2 = d + 2) ∨ (x.1 + x.2 = d ∧ 0 < x.1 ∧ x.1 < d - 1)
        then 1 else 0) := by
  unfold paperLadderAltValue
  rw [lv_ind]

theorem lvWord_reverse (k : ℕ) : (lvWord k).reverse = Letter.q :: List.replicate (2 * k + 1) Letter.p := by
  simp [lvWord]

theorem lvFwd_n (k : ℕ) : (lvFwd k).n = 2 * k + 2 := by
  simp [PTFamily.n, lvFwd, lvWord, lv_vString]

theorem lvFwd_tile (k j : ℕ) (hj : j ≤ 2 * k) :
    (lvFwd k).tile j = (ZTile.zero, (4 * (k : ℤ) + 1 - (j : ℤ), 1 + (j : ℤ))) := by
  unfold PTFamily.tile
  show (vStringAt (lvWord k) (4 * (k : ℤ) + 1, 1)).getD j _ = _
  rw [show lvWord k = List.replicate (2 * k + 1) Letter.p ++ [Letter.q] from rfl, lv_vString (2 * k),
    getD_append_left' _ _ _ _ (by simp; omega), altStair_getD_map_range _ _ _ _ (by omega)]

theorem lvFwd_tile_last (k : ℕ) :
    (lvFwd k).tile (2 * k + 1) = (ZTile.one, (2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3)) := by
  unfold PTFamily.tile
  show (vStringAt (lvWord k) (4 * (k : ℤ) + 1, 1)).getD (2 * k + 1) _ = _
  rw [show lvWord k = List.replicate (2 * k + 1) Letter.p ++ [Letter.q] from rfl, lv_vString (2 * k)]
  simp
  constructor <;> ring

theorem lvRev_n (k : ℕ) : (lvRev k).n = 2 * k + 2 := by
  simp [PTFamily.n, lvRev, lvWord_reverse, lv_vRevString]

theorem lvRev_tile_zero (k : ℕ) : (lvRev k).tile 0 = (ZTile.one, (-1, -1)) := by
  unfold PTFamily.tile
  show (vRevStringAt (lvWord k).reverse (-1, -1)).getD 0 _ = _
  rw [lvWord_reverse, lv_vRevString (2 * k)]
  simp

theorem lvRev_tile_succ (k j : ℕ) (hj : j ≤ 2 * k) :
    (lvRev k).tile (j + 1) = (ZTile.zero, (-1 - (j : ℤ), (j : ℤ))) := by
  unfold PTFamily.tile
  show (vRevStringAt (lvWord k).reverse (-1, -1)).getD (j + 1) _ = _
  rw [lvWord_reverse, lv_vRevString (2 * k), List.getD_cons_succ,
    altStair_getD_map_range _ _ _ _ (by omega)]
  simp only [Prod.mk.injEq, true_and]
  ring


/-! ### 3. The odometers and their agreement with `paperLadderAltValue` -/

theorem lvFwd_odo_zero_le (k j : ℕ) (hj : j ≤ 2 * k) (x : GInt) :
    (lvFwd k).odo j x = zTileOdo ZTile.zero (x - (4 * (k : ℤ) + 1 - (j : ℤ), 1 + (j : ℤ))) +
      (0 * x.1 + (-((j : ℤ) + 1)) * x.2) + (((j : ℤ) + 1) * ((j : ℤ) + 1 + 1) / 2 - 1) := by
  unfold PTFamily.odo
  rw [lvFwd_tile k j hj]
  simp [lvFwd]

theorem lvFwd_odo_last (k : ℕ) (x : GInt) :
    (lvFwd k).odo (2 * k + 1) x = zTileOdo ZTile.one (x - (2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3)) +
      (0 * x.1 + (-(2 * (k : ℤ) + 2)) * x.2) + ((2 * (k : ℤ) + 1 + 1) * (2 * (k : ℤ) + 1 + 1 + 1) / 2 - 1) := by
  unfold PTFamily.odo
  rw [lvFwd_tile_last k]
  simp only [lvFwd]
  push_cast
  ring

theorem lv_fwd_val_zero (k j : ℕ) (hk : 1 ≤ k) (hj : j ≤ 2 * k) (x : GInt)
    (hx : x ∈ (tileShape ZTile.zero).map (· + (4 * (k : ℤ) + 1 - (j : ℤ), 1 + (j : ℤ)))) :
    paperLadderAltValue (2 * (k : ℤ) + 2) x =
      zTileOdo ZTile.zero (x - (4 * (k : ℤ) + 1 - (j : ℤ), 1 + (j : ℤ))) + (0 * x.1 + (-((j : ℤ) + 1)) * x.2) +
        (((j : ℤ) + 1) * ((j : ℤ) + 1 + 1) / 2 - 1) := by
  rw [mem_shape_zero] at hx
  unfold zeroAt at hx
  obtain ⟨x1, x2⟩ := x
  simp only at hx ⊢
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hj' : (j : ℤ) ≤ 2 * (k : ℤ) := by exact_mod_cast hj
  rw [lv_value_eq]
  obtain ⟨s, rfl⟩ : ∃ s : ℤ, x1 = 4 * (k : ℤ) + 1 - (j : ℤ) + s := ⟨x1 - (4 * (k : ℤ) + 1 - (j : ℤ)), by ring⟩
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, x2 = 1 + (j : ℤ) + t := ⟨x2 - (1 + (j : ℤ)), by ring⟩
  have hs : s = 0 ∨ s = 1 := by omega
  have ht : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  have hq1 := Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self (1 + (j : ℤ) + t))
  have hq2 := Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self ((j : ℤ) + 1))
  generalize (1 + (j : ℤ) + t) * (1 + (j : ℤ) + t + 1) / 2 = q1 at hq1 ⊢
  generalize ((j : ℤ) + 1) * ((j : ℤ) + 1 + 1) / 2 = q2 at hq2 ⊢
  simp only [zTileOdo, zeroOdometer, Prod.mk_sub_mk, Prod.mk.injEq, min_def, max_def]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> ring_nf at hq1 hq2 ⊢ <;>
    generalize (j : ℤ) ^ 2 = J at hq1 hq2 ⊢ <;> split_ifs <;> (try simp only [true_and, and_true, true_or, or_true, not_true_eq_false] at *) <;> omega

theorem lv_fwd_val_last (k : ℕ) (hk : 1 ≤ k) (x : GInt)
    (hx : x ∈ (tileShape ZTile.one).map (· + (2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3))) :
    paperLadderAltValue (2 * (k : ℤ) + 2) x =
      zTileOdo ZTile.one (x - (2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3)) + (0 * x.1 + (-(2 * (k : ℤ) + 2)) * x.2) +
        ((2 * (k : ℤ) + 1 + 1) * (2 * (k : ℤ) + 1 + 1 + 1) / 2 - 1) := by
  rw [mem_shape_one] at hx
  unfold oneAt at hx
  obtain ⟨x1, x2⟩ := x
  simp only at hx ⊢
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  rw [lv_value_eq]
  obtain ⟨s, rfl⟩ : ∃ s : ℤ, x1 = 2 * (k : ℤ) + 1 + s := ⟨x1 - (2 * (k : ℤ) + 1), by ring⟩
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, x2 = 2 * (k : ℤ) + 3 + t := ⟨x2 - (2 * (k : ℤ) + 3), by ring⟩
  have hs : s = 0 ∨ s = 1 := by omega
  have ht : t = 0 ∨ t = 1 := by omega
  have hq1 := Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self (2 * (k : ℤ) + 3 + t))
  have hq2 := Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self (2 * (k : ℤ) + 1 + 1))
  generalize (2 * (k : ℤ) + 3 + t) * (2 * (k : ℤ) + 3 + t + 1) / 2 = q1 at hq1 ⊢
  generalize (2 * (k : ℤ) + 1 + 1) * (2 * (k : ℤ) + 1 + 1 + 1) / 2 = q2 at hq2 ⊢
  simp only [zTileOdo, oneOdometer, Prod.mk_sub_mk, Prod.mk.injEq, min_def, max_def]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> ring_nf at hq1 hq2 ⊢ <;>
    generalize (k : ℤ) ^ 2 = Q at hq1 hq2 ⊢ <;> split_ifs <;> (try simp only [true_and, and_true, true_or, or_true, not_true_eq_false] at *) <;> omega

theorem lvRev_odo_zero (k : ℕ) (x : GInt) :
    (lvRev k).odo 0 x = zTileOdo ZTile.one (x - (-1, -1)) + (0 * x.1 + 0 * x.2) + 0 := by
  unfold PTFamily.odo
  rw [lvRev_tile_zero]
  simp [lvRev]

theorem lvRev_odo_succ (k j : ℕ) (hj : j ≤ 2 * k) (x : GInt) :
    (lvRev k).odo (j + 1) x = zTileOdo ZTile.zero (x - (-1 - (j : ℤ), (j : ℤ))) +
      (1 * x.1 + (-((j : ℤ) + 1)) * x.2) + (((j : ℤ) + 1) * (((j : ℤ) + 1) - 1) / 2) := by
  unfold PTFamily.odo
  rw [lvRev_tile_succ k j hj]
  simp [lvRev]
  ring_nf

theorem lv_rev_val_one (k : ℕ) (hk : 1 ≤ k) (x : GInt)
    (hx : x ∈ (tileShape ZTile.one).map (· + (-1, -1))) :
    paperLadderAltValue (2 * (k : ℤ) + 2) x = zTileOdo ZTile.one (x - (-1, -1)) := by
  rw [mem_shape_one] at hx
  unfold oneAt at hx
  obtain ⟨x1, x2⟩ := x
  simp only at hx ⊢
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  rw [lv_value_eq]
  have h1 : x1 = -1 ∨ x1 = 0 := by omega
  have h2 : x2 = -1 ∨ x2 = 0 := by omega
  simp only [zTileOdo, oneOdometer, Prod.mk_sub_mk, Prod.mk.injEq, min_def, max_def]
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> norm_num <;> split_ifs <;> omega

-- The post-split cleanup below needs `false_and`/`or_false`/`not_false_eq_true` in some branches; the linter misreports them.
set_option linter.unusedSimpArgs false in
theorem lv_rev_val_zero (k j : ℕ) (hk : 1 ≤ k) (hj : j ≤ 2 * k) (x : GInt)
    (hx : x ∈ (tileShape ZTile.zero).map (· + (-1 - (j : ℤ), (j : ℤ)))) :
    paperLadderAltValue (2 * (k : ℤ) + 2) x =
      zTileOdo ZTile.zero (x - (-1 - (j : ℤ), (j : ℤ))) + (1 * x.1 + (-((j : ℤ) + 1)) * x.2) +
        (((j : ℤ) + 1) * (((j : ℤ) + 1) - 1) / 2) := by
  rw [mem_shape_zero] at hx
  unfold zeroAt at hx
  obtain ⟨x1, x2⟩ := x
  simp only at hx ⊢
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hj' : (j : ℤ) ≤ 2 * (k : ℤ) := by exact_mod_cast hj
  rw [lv_value_eq]
  obtain ⟨s, rfl⟩ : ∃ s : ℤ, x1 = -1 - (j : ℤ) + s := ⟨x1 - (-1 - (j : ℤ)), by ring⟩
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, x2 = (j : ℤ) + t := ⟨x2 - (j : ℤ), by ring⟩
  have hs : s = 0 ∨ s = 1 := by omega
  have ht : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  have hq1 := Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self ((j : ℤ) + t))
  have hq2 : 2 * (((j : ℤ) + 1) * ((j : ℤ) + 1 - 1) / 2) = ((j : ℤ) + 1) * ((j : ℤ) + 1 - 1) := by
    rw [show ((j : ℤ) + 1) * ((j : ℤ) + 1 - 1) = (j : ℤ) * ((j : ℤ) + 1) by ring]
    exact Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self _)
  generalize ((j : ℤ) + t) * ((j : ℤ) + t + 1) / 2 = q1 at hq1 ⊢
  generalize ((j : ℤ) + 1) * ((j : ℤ) + 1 - 1) / 2 = q2 at hq2 ⊢
  simp only [zTileOdo, zeroOdometer, Prod.mk_sub_mk, Prod.mk.injEq, min_def, max_def]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> ring_nf at hq1 hq2 ⊢ <;>
    generalize (j : ℤ) ^ 2 = J at hq1 hq2 ⊢ <;> split_ifs <;> (try simp only [true_and, and_true, true_or, or_true, false_and, and_false, false_or, or_false, not_true_eq_false, not_false_eq_true] at *) <;> omega


/-! ### 4. Agreement, containment and the lower-left point -/

theorem lv_fwd_agree (k : ℕ) (hk : 1 ≤ k) :
    ∀ j < (lvFwd k).n, ∀ x ∈ (lvFwd k).dom j,
      paperLadderAltValue (2 * (k : ℤ) + 2) x = (lvFwd k).odo j x := by
  intro j hj x hx
  rw [lvFwd_n] at hj
  by_cases hjk : j ≤ 2 * k
  · unfold PTFamily.dom at hx
    rw [lvFwd_tile k j hjk] at hx
    dsimp only at hx
    rw [lv_fwd_val_zero k j hk hjk x hx, lvFwd_odo_zero_le k j hjk x]
  · have hj' : j = 2 * k + 1 := by omega
    subst hj'
    unfold PTFamily.dom at hx
    rw [lvFwd_tile_last k] at hx
    dsimp only at hx
    rw [lv_fwd_val_last k hk x hx, lvFwd_odo_last k x]

theorem lv_rev_agree (k : ℕ) (hk : 1 ≤ k) :
    ∀ j < (lvRev k).n, ∀ x ∈ (lvRev k).dom j,
      paperLadderAltValue (2 * (k : ℤ) + 2) x = (lvRev k).odo j x := by
  intro j hj x hx
  rw [lvRev_n] at hj
  rcases j with _ | j
  · unfold PTFamily.dom at hx
    rw [lvRev_tile_zero] at hx
    dsimp only at hx
    rw [lv_rev_val_one k hk x hx, lvRev_odo_zero]
    simp
  · unfold PTFamily.dom at hx
    rw [lvRev_tile_succ k j (by omega)] at hx
    dsimp only at hx
    rw [lv_rev_val_zero k j hk (by omega) x hx, lvRev_odo_succ k j (by omega) x]

theorem lv_mem_tile (d : ℤ) (x : GInt) :
    x ∈ paperLadderAltTile d ↔
      ((((x.1 = -1 ∧ x.2 = -1) ∨ (x.1 = d ∧ x.2 = d + 2)) ∨ (x.1 + x.2 = d ∧ 0 < x.1 ∧ x.1 < d - 1)) ∨
        (1 - d ≤ x.1 ∧ x.1 ≤ 2 * d - 2 ∧ -1 ≤ x.2 ∧ x.2 ≤ d + 2 ∧ -1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 2 * d + 1)) ∧
      ¬ ((d ≤ x.1 ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∨ (x.1 ≤ -1 ∧ d + 1 ≤ x.2 ∧ x.2 ≤ d + 2)) := by
  unfold paperLadderAltTile paperLadderAltA paperLadderAltB paperLadderAltC paperLadderAltD
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Prod.ext_iff]

theorem lv_inside (k : ℕ) (hk : 1 ≤ k) :
    InsideTile (paperLadderAltTile (2 * (k : ℤ) + 2))
      (vPartialTiles (lvWord k) (-1, -1) (4 * (k : ℤ) + 1, 1)) := by
  apply inside_of_tiles
  intro tp htp y hy
  simp only [vPartialTiles, List.mem_append] at htp
  rcases htp with htp | htp
  · rw [lvWord_reverse, lv_vRevString (2 * k)] at htp
    simp only [List.mem_cons, List.mem_map, List.mem_range] at htp
    rcases htp with rfl | ⟨j, hj, rfl⟩
    · dsimp only at hy
      rw [mem_shape_one] at hy
      unfold oneAt at hy
      rw [lv_mem_tile]
      omega
    · dsimp only at hy
      rw [mem_shape_zero] at hy
      unfold zeroAt at hy
      rw [lv_mem_tile]
      omega
  · rw [show lvWord k = List.replicate (2 * k + 1) Letter.p ++ [Letter.q] from rfl, lv_vString (2 * k)] at htp
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at htp
    rcases htp with ⟨j, hj, rfl⟩ | rfl
    · dsimp only at hy
      rw [mem_shape_zero] at hy
      unfold zeroAt at hy
      rw [lv_mem_tile]
      omega
    · dsimp only at hy
      rw [mem_shape_one] at hy
      unfold oneAt at hy
      rw [lv_mem_tile]
      omega

theorem lv_lowerLeft (k : ℕ) (hk : 1 ≤ k) :
    IsLowerLeftPt (paperLadderAltTile (2 * (k : ℤ) + 2)) (-1, -1) := by
  refine ⟨?_, ?_⟩
  · rw [lv_mem_tile]
    dsimp only
    omega
  · intro x hx
    rw [lv_mem_tile] at hx
    unfold lowerLexLe
    dsimp only
    omega

/-! ### 5. The triples data for the forward family -/

theorem lv_fb_step (j : ℤ) :
    (j + 1 + 1) * (j + 1 + 1 + 1) / 2 - 1 = ((j + 1) * (j + 1 + 1) / 2 - 1) + (j + 2) := by
  have h : (j + 1 + 1) * (j + 1 + 1 + 1) = (j + 1) * (j + 1 + 1) + (j + 2) * 2 := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by norm_num : (2 : ℤ) ≠ 0)]
  ring

theorem lv_rb_step (j : ℤ) : (j + 1) * (j + 1 - 1) / 2 = j * (j - 1) / 2 + j := by
  have h : (j + 1) * (j + 1 - 1) = j * (j - 1) + j * 2 := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by norm_num : (2 : ℤ) ≠ 0)]

/-- The letter at position `j` of `lvWord m`: `p` except `q` at `2m+1`. -/
def lvFl (m : ℕ) (j : ℕ) : Letter := if j = 2 * m + 1 then Letter.q else Letter.p

/-- The predecessor letter: `p` before the first tile, then the letter at `j-1`. -/
def lvPrev (ℓ : ℕ → Letter) (j : ℕ) : Letter := if j = 0 then Letter.p else ℓ (j - 1)

/-- The positions of the forward family `lvFwd m`. -/
def lvFP (m : ℕ) (j : ℕ) : GInt :=
  if j = 2 * m + 1 then (2 * (m : ℤ) + 1, 2 * (m : ℤ) + 3) else (4 * (m : ℤ) + 1 - (j : ℤ), 1 + (j : ℤ))

theorem lv_F_hT (m k : ℕ) (hk : k < (lvFwd m).n) :
    (lvFwd m).tile k = (letterZTile (lvFl m k), lvFP m k) := by
  rw [lvFwd_n] at hk
  by_cases h : k = 2 * m + 1
  · subst h
    rw [lvFwd_tile_last m]
    simp [lvFl, lvFP, letterZTile]
  · rw [lvFwd_tile m k (by omega)]
    simp [lvFl, lvFP, letterZTile, h]

theorem lv_F_hD (m k : ℕ) (hk : k + 1 < 2 * m + 2) :
    lvFP m (k + 1) = lvFP m k + vOffset (lvFl m (k + 1)) := by
  by_cases h : k + 1 = 2 * m + 1
  · have hk' : k ≠ 2 * m + 1 := by omega
    have hkz : (k : ℤ) = 2 * (m : ℤ) := by omega
    simp only [lvFP, lvFl, vOffset, if_pos h, if_neg hk', Prod.mk_add_mk]
    refine Prod.ext ?_ ?_ <;> simp only <;> omega
  · have hk' : k ≠ 2 * m + 1 := by omega
    have hz : (k : ℤ) + 1 = (k + 1 : ℕ) := by push_cast; ring
    simp only [lvFP, lvFl, vOffset, if_neg h, if_neg hk', Prod.mk_add_mk]
    refine Prod.ext ?_ ?_ <;> simp only <;> push_cast <;> ring

theorem lv_F_hAa (k : ℕ) :
    ((0 : ℤ), -(((k + 1 : ℕ) : ℤ) + 1)) = ((0 : ℤ), -((k : ℤ) + 1)) + ((0 : ℤ), (-1 : ℤ)) :=
  by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]; ring
    · simp only [Prod.snd_add]; push_cast; ring

/-- The centred constants of the forward family `lvFwd m`: `c j = b j + a j · P j`. -/
def lvFc (m j : ℕ) : ℤ :=
  ((j : ℤ) + 1) * ((j : ℤ) + 1 + 1) / 2 - 1 + ptDot ((0 : ℤ), -((j : ℤ) + 1)) (lvFP m j)

theorem lv_F_hB (m k : ℕ) : (lvFwd m).b k = lvFc m k - ptDot ((lvFwd m).a k) (lvFP m k) := by
  simp only [lvFwd, lvFc]
  ring

theorem lv_F_hc (m k : ℕ) (hk : k + 1 < 2 * m + 2) :
    lvFc m (k + 1) = lvFc m k + (if lvFl m (k + 1) = Letter.q then (-1 : ℤ) else 0)
      + ptDot ((lvFwd m).a k) (vOffset (lvFl m (k + 1))) := by
  have hb := lv_fb_step (k : ℤ)
  by_cases h : k + 1 = 2 * m + 1
  · have hk' : k ≠ 2 * m + 1 := by omega
    have hkz : (k : ℤ) = 2 * (m : ℤ) := by omega
    simp only [lvFc, lvFwd, lvFP, lvFl, vOffset, ptDot, if_pos h, if_neg hk', Nat.cast_add, Nat.cast_one,
      ↓reduceIte]
    rw [hb]
    rw [hkz]
    ring
  · have hk' : k ≠ 2 * m + 1 := by omega
    simp only [lvFc, lvFwd, lvFP, lvFl, vOffset, ptDot, if_neg h, if_neg hk', Nat.cast_add, Nat.cast_one,
      ↓reduceIte, reduceCtorEq]
    rw [hb]
    ring

/-- The forward boundary check for the pair `(p,p)` then `p`: the vertical identity with `β + 1 = 1`. -/
theorem lv_bd_pp : ∀ u ∈ tileShape (letterZTile Letter.p), ∀ v ∈ tileShape (letterZTile Letter.p),
    (∀ u' ∈ tileShape (letterZTile Letter.p), ∀ v' ∈ tileShape (letterZTile Letter.p), u' - v' ≠ vOffset Letter.p) →
    (u - v - vOffset Letter.p).1.natAbs + (u - v - vOffset Letter.p).2.natAbs = 1 →
    zTileOdo (letterZTile Letter.p) u - zTileOdo (letterZTile Letter.p) v - ptDot ((0 : ℤ), (-1 : ℤ)) v = 0 + 1 := by
  decide

/-- The forward boundary check for the pair `(p,p)` then `q`: the vertical identity with `β + 1 = 0`. -/
theorem lv_bd_pq : ∀ u ∈ tileShape (letterZTile Letter.p), ∀ v ∈ tileShape (letterZTile Letter.q),
    (∀ u' ∈ tileShape (letterZTile Letter.p), ∀ v' ∈ tileShape (letterZTile Letter.q), u' - v' ≠ vOffset Letter.q) →
    (u - v - vOffset Letter.q).1.natAbs + (u - v - vOffset Letter.q).2.natAbs = 1 →
    zTileOdo (letterZTile Letter.p) u - zTileOdo (letterZTile Letter.q) v - ptDot ((0 : ℤ), (-1 : ℤ)) v = -1 + 1 := by
  decide

theorem lvFwd_respects (m : ℕ) : (lvFwd m).Respects .vertical false :=
  PTFamily.respects_of_triples (lvFwd m) .vertical false (lvFl m) (lvPrev (lvFl m)) (lvFP m)
    (fun _ y => letterZTile y) (fun _ y => vOffset y) (fun _ _ _ => ((0 : ℤ), (-1 : ℤ))) (lvFc m)
    (fun _ _ z => if z = Letter.q then (-1 : ℤ) else 0) (fun x y _ => x = Letter.p ∧ y = Letter.p)
    (fun k hk => lv_F_hT m k hk)
    (fun k _ => by
      show (if k + 1 = 0 then Letter.p else lvFl m (k + 1 - 1)) = lvFl m k
      simp)
    (fun k hk => lv_F_hD m k (by rw [lvFwd_n] at hk; exact hk))
    (fun k _ => lv_F_hAa k)
    (fun k _ => lv_F_hB m k)
    (fun k hk => lv_F_hc m k (by rw [lvFwd_n] at hk; exact hk))
    (fun k hk => by
      rw [lvFwd_n] at hk
      by_cases h0 : k = 0
      · refine ⟨?_, ?_⟩ <;> simp [lvPrev, lvFl, h0]
      · refine ⟨?_, ?_⟩ <;> simp [lvPrev, lvFl, h0] <;> omega)
    (fun _ y => zTileLetter_letterZTile y)
    (fun x y z hA => by
      obtain ⟨rfl, rfl⟩ := hA
      cases z <;> simp [slope_base_p, slope_base_q, surgicalSlopeDiff])
    (fun h => by cases h)
    (fun _ x y z hA u hu v hv hno hunit => by
      obtain ⟨rfl, rfl⟩ := hA
      cases z
      · exact lv_bd_pp u hu v hv hno hunit
      · exact lv_bd_pq u hu v hv hno hunit)

/-! ### 6. The reversed family respects the reversed vertical string -/

/-- The letter at position `j` of `(lvWord m).reverse`: `q` first, then `p`. -/
def lvRl (j : ℕ) : Letter := if j = 0 then Letter.q else Letter.p

/-- The positions of the reversed family `lvRev m`. -/
def lvRP (j : ℕ) : GInt := if j = 0 then (-1, -1) else (-(j : ℤ), (j : ℤ) - 1)

/-- The affine factors of the reversed family `lvRev m`. -/
def lvRa (j : ℕ) : GInt := if j = 0 then ((0 : ℤ), (0 : ℤ)) else ((1 : ℤ), -(j : ℤ))

/-- The reversed affine increments, keyed by `(T_{i-1}, T_i, T_{i+1})`: `(1,-1)` on `(p,q,p)`, else `(0,-1)`. -/
def lvRg : Letter → Letter → Letter → GInt
  | .p, .q, _ => ((1 : ℤ), (-1 : ℤ))
  | _, _, _ => ((0 : ℤ), (-1 : ℤ))

/-- The reversed boundary increments: `-1` on `(p,q,p)`, else `0`. -/
def lvRbeta : Letter → Letter → Letter → ℤ
  | .p, .q, _ => -1
  | _, _, _ => 0

/-- The reversed linear-in-`j` constant `b j = j(j-1)/2`. -/
def lvRb (j : ℕ) : ℤ := (j : ℤ) * ((j : ℤ) - 1) / 2

theorem lvRb_succ (k : ℕ) : lvRb (k + 1) = lvRb k + (k : ℤ) := by
  unfold lvRb
  push_cast
  exact lv_rb_step _

/-- The reversed centred constants `c j = b j + a j · P j`. -/
def lvRc (j : ℕ) : ℤ := lvRb j + ptDot (lvRa j) (lvRP j)

theorem lv_R_hT (m k : ℕ) (hk : k < (lvRev m).n) :
    (lvRev m).tile k = (letterZTile (lvRl k), lvRP k) := by
  rw [lvRev_n] at hk
  rcases k with _ | j
  · rw [lvRev_tile_zero]
    simp [lvRl, lvRP, letterZTile]
  · rw [lvRev_tile_succ m j (by omega)]
    have hj : j + 1 ≠ 0 := by omega
    have h1 : lvRl (j + 1) = Letter.p := by
      unfold lvRl
      rw [if_neg hj]
    have h2 : lvRP (j + 1) = (-1 - (j : ℤ), (j : ℤ)) := by
      unfold lvRP
      rw [if_neg hj]
      refine Prod.ext ?_ ?_
      · dsimp only; push_cast; ring
      · dsimp only; push_cast; ring
    rw [h1, h2]
    rfl

theorem lv_R_hD (k : ℕ) :
    lvRP (k + 1) = lvRP k + vRevOffset (lvRl k) (lvRl (k + 1)) := by
  rcases k with _ | j
  · simp [lvRP, lvRl, vRevOffset]
  · have hj : j + 1 ≠ 0 := by omega
    have hj2 : j + 1 + 1 ≠ 0 := by omega
    simp only [lvRP, lvRl, vRevOffset, if_neg hj, if_neg hj2]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]; push_cast; ring
    · simp only [Prod.snd_add]; push_cast; ring

theorem lv_R_hA (k : ℕ) : lvRa (k + 1) = lvRa k + lvRg (lvPrev lvRl k) (lvRl k) (lvRl (k + 1)) := by
  rcases k with _ | _ | j
  · simp [lvRa, lvRg, lvPrev, lvRl]
  · simp [lvRa, lvRg, lvPrev, lvRl]
  · have h1 : j + 1 + 1 ≠ 0 := by omega
    have h2 : j + 1 ≠ 0 := by omega
    have h3 : j + 1 + 1 + 1 ≠ 0 := by omega
    simp only [lvRa, lvRg, lvPrev, lvRl, if_neg h1, if_neg h2, if_neg h3, Nat.add_sub_cancel]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]; ring
    · simp only [Prod.snd_add]; push_cast; ring

theorem lv_R_hB (m k : ℕ) : (lvRev m).b k = lvRc k - ptDot ((lvRev m).a k) (lvRP k) := by
  simp only [lvRev, lvRc, lvRb, lvRa]
  ring

theorem lv_R_hc (k : ℕ) :
    lvRc (k + 1) = lvRc k + lvRbeta (lvPrev lvRl k) (lvRl k) (lvRl (k + 1))
      + ptDot (lvRa k) (vRevOffset (lvRl k) (lvRl (k + 1))) := by
  rw [lvRc, lvRc, lvRb_succ, lv_R_hA k, lv_R_hD k]
  rcases k with _ | _ | j
  · simp [lvRg, lvRbeta, lvPrev, lvRl, lvRa, lvRP, vRevOffset, ptDot, lvRb]
  · simp [lvRg, lvRbeta, lvPrev, lvRl, lvRa, lvRP, vRevOffset, ptDot, lvRb]
  · simp [lvRg, lvRbeta, lvPrev, lvRl, lvRa, lvRP, vRevOffset, ptDot, lvRb]
    ring

/-- The reversed boundary check for `(p,q,p)`: the one-tile against the zero-tile, `β + 1 = 0`. -/
theorem lv_bd_rq : ∀ u ∈ tileShape (letterZTile Letter.q), ∀ v ∈ tileShape (letterZTile Letter.p),
    (∀ u' ∈ tileShape (letterZTile Letter.q), ∀ v' ∈ tileShape (letterZTile Letter.p),
      u' - v' ≠ vRevOffset Letter.q Letter.p) →
    (u - v - vRevOffset Letter.q Letter.p).1.natAbs + (u - v - vRevOffset Letter.q Letter.p).2.natAbs = 1 →
    zTileOdo (letterZTile Letter.q) u - zTileOdo (letterZTile Letter.p) v - ptDot ((1 : ℤ), (-1 : ℤ)) v = -1 + 1 := by
  decide

/-- The reversed boundary check for the zero-tile pairs `(p,p)` and `(q,p,p)`: `β + 1 = 1`. -/
theorem lv_bd_rz : ∀ u ∈ tileShape (letterZTile Letter.p), ∀ v ∈ tileShape (letterZTile Letter.p),
    (∀ u' ∈ tileShape (letterZTile Letter.p), ∀ v' ∈ tileShape (letterZTile Letter.p),
      u' - v' ≠ vRevOffset Letter.p Letter.p) →
    (u - v - vRevOffset Letter.p Letter.p).1.natAbs + (u - v - vRevOffset Letter.p Letter.p).2.natAbs = 1 →
    zTileOdo (letterZTile Letter.p) u - zTileOdo (letterZTile Letter.p) v - ptDot ((0 : ℤ), (-1 : ℤ)) v = 0 + 1 := by
  decide

theorem lvRev_respects (m : ℕ) : (lvRev m).Respects .vertical true :=
  PTFamily.respects_of_triples (lvRev m) .vertical true lvRl (lvPrev lvRl) lvRP
    (fun _ y => letterZTile y) (fun y z => vRevOffset y z) lvRg lvRc lvRbeta
    (fun x y z => (x = Letter.p ∧ y = Letter.q ∧ z = Letter.p) ∨ (x = Letter.q ∧ y = Letter.p ∧ z = Letter.p)
      ∨ (x = Letter.p ∧ y = Letter.p ∧ z = Letter.p))
    (fun k hk => lv_R_hT m k hk)
    (fun k _ => by
      show (if k + 1 = 0 then Letter.p else lvRl (k + 1 - 1)) = lvRl k
      simp)
    (fun k _ => lv_R_hD k)
    (fun k _ => lv_R_hA k)
    (fun k _ => lv_R_hB m k)
    (fun k _ => lv_R_hc k)
    (fun k _ => by
      rcases k with _ | _ | j <;> simp [lvPrev, lvRl])
    (fun _ y => zTileLetter_letterZTile y)
    (fun x y z hA => by
      rcases hA with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        norm_num [slope_base_p, slope_base_q, surgicalSlopeDiff, lvRg])
    (fun h => by cases h)
    (fun _ x y z hA u hu v hv hno hunit => by
      rcases hA with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact lv_bd_rq u hu v hv hno hunit
      · exact lv_bd_rz u hu v hv hno hunit
      · exact lv_bd_rz u hu v hv hno hunit)

/-- The vertical respect of `paperLadderAltValue (2k+2)` on `T̂_{1/d}` for the word `w_v = p^{2k+1} q` (2470):
the reversed string anchored at the lower-left point `(-1,-1)` and the forward string at `(4k+1,1)`. -/
theorem lv_respectsPartialV (m : ℕ) (hm : 1 ≤ m) :
    RespectsPartialV (paperLadderAltTile (2 * (m : ℤ) + 2)) (lvWord m) (paperLadderAltValue (2 * (m : ℤ) + 2)) :=
  ⟨(-1, -1), lv_lowerLeft m hm, (4 * (m : ℤ) + 1, 1), lv_inside m hm,
    ⟨lvRev m, rfl, lv_rev_agree m hm, lvRev_respects m⟩,
    ⟨lvFwd m, rfl, lv_fwd_agree m hm, lvFwd_respects m⟩⟩

end FLatticePaper.Tiles
