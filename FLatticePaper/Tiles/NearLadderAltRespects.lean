import FLatticePaper.Tiles.AltStairRespects
import FLatticePaper.Construction.NearOneBaseCases

/-! # The alternate near-ladder tile `T̂_{q_1}` as a partial `w_h`-pseudo-square (surgical `lemma:basecase_2k_even_alt`)

For `d = 2k+2` (so `q_1 = (2k+1)/(2k+3)`, `k ≥ 1`), the word is `w_h = q^{2k+1} p`. The tile `T̂_{q_1}` contains the forward
string at its lower-left point `(0,1)` and the reversed string of `p q^{2k+1}` at a free anchor `(-2, 4k+2)`, and the odometer
`ĝ_{q_1}` (`paperNearLadderAltValue`) respects both strings, in the sense of the shared `RespectsTiles` of `PartialBoundary`.

Section 1 computes the placed lists explicitly, so that the tile of each index is known. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Construction (paperNearLadderAltTile paperNearLadderAltValue paperNearLadderAltA
  paperNearLadderAltB paperNearLadderAltC paperNearLadderAltD)

/-! ### 1. The placed lists -/

/-- The word `q^{2k+1} p` (the forward horizontal word of `w_h`). -/
def nlaWord (k : ℕ) : BinaryWord := List.replicate (2 * k + 1) Letter.q ++ [Letter.p]

theorem nla_word_reverse (k : ℕ) : (nlaWord k).reverse = Letter.p :: List.replicate (2 * k + 1) Letter.q := by
  simp [nlaWord]

theorem nla_tileSeqAux_q (m : ℕ) :
    tileSeqAux (some Letter.q) (List.replicate m Letter.q ++ [Letter.p]) =
      List.replicate m ZTile.oneD ++ [ZTile.zero] := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, tileSeqAux, ih]

theorem nla_tileSeq (m : ℕ) :
    tileSeq (List.replicate (m + 1) Letter.q ++ [Letter.p]) =
      ZTile.one :: (List.replicate m ZTile.oneD ++ [ZTile.zero]) := by
  simp only [tileSeq, List.replicate_succ, List.cons_append, tileSeqAux, nla_tileSeqAux_q]

/-- The offsets `(1,1)` of the `m` doubled letters `q`, then `(2,0)` of the letter `p`, from `c`. -/
theorem nla_scanl (m : ℕ) (c : GInt) :
    List.scanl (· + ·) c (List.replicate m ((1 : ℤ), (1 : ℤ)) ++ [((2 : ℤ), (0 : ℤ))]) =
      (List.range (m + 1)).map (fun j : ℕ => (c.1 + (j : ℤ), c.2 + (j : ℤ))) ++
        [(c.1 + ((m : ℤ) + 2), c.2 + (m : ℤ))] := by
  induction m generalizing c with
  | zero =>
    simp
    ext <;> simp
  | succ m ih =>
    have r1 : List.replicate (m + 1) ((1 : ℤ), (1 : ℤ)) ++ [((2 : ℤ), (0 : ℤ))] =
        ((1 : ℤ), (1 : ℤ)) :: (List.replicate m ((1 : ℤ), (1 : ℤ)) ++ [((2 : ℤ), (0 : ℤ))]) := rfl
    have hr : List.range (m + 1 + 1) = 0 :: List.map Nat.succ (List.range (m + 1)) := by
      rw [List.range_succ_eq_map]
    rw [r1, List.scanl_cons, ih, hr, List.map_cons, List.cons_append, List.map_map, List.cons_eq_cons]
    refine ⟨by simp, ?_⟩
    congr 1
    · apply List.map_congr_left
      intro j _
      (simp only [Function.comp_apply, Nat.succ_eq_add_one, Prod.fst_add, Prod.snd_add]; push_cast; ring_nf)
    · (simp only [List.cons.injEq, and_true, Prod.mk.injEq, Prod.fst_add, Prod.snd_add]; push_cast; ring_nf; simp)

theorem nla_zip_rep {α β : Type*} (m : ℕ) (a : α) (g : ℕ → β) :
    (List.replicate m a).zip ((List.range m).map g) = (List.range m).map fun j => (a, g j) := by
  induction m generalizing g with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.range_succ_eq_map, List.map_cons, List.map_cons, List.zip_cons_cons,
      List.map_map, List.map_map, ih]
    rfl

/-- The placed forward string `hStringAt (q^{m+1} p) c`: one tile at `c`, then `m` one-tiles `T_{q_d}` and the zero tile. -/
theorem nla_hStringAt (m : ℕ) (c : GInt) :
    hStringAt (List.replicate (m + 1) Letter.q ++ [Letter.p]) c =
      (ZTile.one, c) :: (((List.range m).map fun j : ℕ =>
          (ZTile.oneD, (c.1 + ((j : ℤ) + 1), c.2 + ((j : ℤ) + 1)))) ++
        [(ZTile.zero, (c.1 + ((m : ℤ) + 2), c.2 + (m : ℤ)))]) := by
  have hw : (List.replicate (m + 1) Letter.q ++ [Letter.p]).tail.map hOffset =
      List.replicate m ((1 : ℤ), (1 : ℤ)) ++ [((2 : ℤ), (0 : ℤ))] := by
    simp [hOffset, List.replicate_succ]
  unfold hStringAt
  rw [hw, nla_tileSeq, nla_scanl]
  have hr : List.range (m + 1) = 0 :: List.map Nat.succ (List.range m) := by
    rw [List.range_succ_eq_map]
  rw [hr, List.map_cons, List.cons_append, List.zip_cons_cons]
  simp [List.zip_append, nla_zip_rep, List.map_map, Function.comp_def]

theorem nla_rev_qq (w : BinaryWord) (c : GInt) :
    hRevStringAt (Letter.q :: Letter.q :: w) c =
      (ZTile.one, c) :: hRevStringAt (Letter.q :: w) (c + ((1 : ℤ), (1 : ℤ))) := by
  simp [hRevStringAt, hRevOffset, letterZTile, List.scanl_cons]

theorem nla_rev_pq (w : BinaryWord) (c : GInt) :
    hRevStringAt (Letter.p :: Letter.q :: w) c =
      (ZTile.zero, c) :: hRevStringAt (Letter.q :: w) (c + ((2 : ℤ), (1 : ℤ))) := by
  simp [hRevStringAt, hRevOffset, letterZTile, List.scanl_cons]

/-- The reversed run `q^{n+1}` at `c`: one tiles at `c + (j, j)`. -/
theorem nla_rev_qlist (n : ℕ) (c : GInt) :
    hRevStringAt (List.replicate (n + 1) Letter.q) c =
      (List.range (n + 1)).map fun j : ℕ => (ZTile.one, (c.1 + (j : ℤ), c.2 + (j : ℤ))) := by
  induction n generalizing c with
  | zero => simp [hRevStringAt, letterZTile]
  | succ n ih =>
    have e : List.replicate (n + 1 + 1) Letter.q = Letter.q :: Letter.q :: List.replicate n Letter.q := rfl
    have e2 : Letter.q :: List.replicate n Letter.q = List.replicate (n + 1) Letter.q := rfl
    have hr : List.range (n + 1 + 1) = 0 :: List.map Nat.succ (List.range (n + 1)) := by
      rw [List.range_succ_eq_map]
    rw [e, nla_rev_qq, e2, ih, hr, List.map_cons, List.map_map, List.cons_eq_cons]
    refine ⟨by simp, ?_⟩
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, Nat.succ_eq_add_one, Prod.mk.injEq, true_and, Prod.fst_add, Prod.snd_add]
    push_cast
    ring_nf
    simp

/-- The reversed string `p q^{m+1}` at `c`: the zero tile at `c`, then one tiles at `c + (2 + j, 1 + j)`. -/
theorem nla_rev_list (m : ℕ) (c : GInt) :
    hRevStringAt (Letter.p :: List.replicate (m + 1) Letter.q) c =
      (ZTile.zero, c) :: (List.range (m + 1)).map fun j : ℕ =>
        (ZTile.one, (c.1 + 2 + (j : ℤ), c.2 + 1 + (j : ℤ))) := by
  have e : Letter.p :: List.replicate (m + 1) Letter.q = Letter.p :: Letter.q :: List.replicate m Letter.q := rfl
  have e2 : Letter.q :: List.replicate m Letter.q = List.replicate (m + 1) Letter.q := rfl
  rw [e, nla_rev_pq, e2, nla_rev_qlist m]
  simp

/-! ### The two families -/

/-- The forward family of `q^{2k+1} p` at `(0,1)`: no affine part, no constant. -/
def nlaFwd (k : ℕ) : PTFamily where
  ts := hStringAt (nlaWord k) (0, 1)
  a := fun _ => 0
  b := fun _ => 0

/-- The reversed corner `(-2, 4k+2)` of the reversed string. -/
def nlaRevC (k : ℕ) : GInt := (-2, 4 * (k : ℤ) + 2)

/-- The reversed family of `p q^{2k+1}` at `(-2,4k+2)`: the zero tile has affine factor `(2k+1, -(2k+2))`, the one tiles
`(2k, -(2k+2))`, and every tile has constant `(2k+2)^2`. -/
def nlaRev (k : ℕ) : PTFamily where
  ts := hRevStringAt (nlaWord k).reverse (nlaRevC k)
  a := fun j => if j = 0 then (2 * (k : ℤ) + 1, -(2 * (k : ℤ) + 2)) else (2 * (k : ℤ), -(2 * (k : ℤ) + 2))
  b := fun _ => (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 2)

theorem nlaFwd_n (k : ℕ) : (nlaFwd k).n = 2 * k + 2 := by
  simp [PTFamily.n, nlaFwd, nlaWord, nla_hStringAt]

theorem nlaFwd_tile_zero (k : ℕ) : (nlaFwd k).tile 0 = (ZTile.one, (0, 1)) := by
  unfold PTFamily.tile
  show (hStringAt (nlaWord k) (0, 1)).getD 0 _ = _
  rw [show nlaWord k = List.replicate (2 * k + 1) Letter.q ++ [Letter.p] from rfl, nla_hStringAt]
  simp

theorem nlaFwd_tile_succ (k j : ℕ) (hj : j < 2 * k) :
    (nlaFwd k).tile (j + 1) = (ZTile.oneD, ((j : ℤ) + 1, (j : ℤ) + 2)) := by
  unfold PTFamily.tile
  show (hStringAt (nlaWord k) (0, 1)).getD (j + 1) _ = _
  rw [show nlaWord k = List.replicate (2 * k + 1) Letter.q ++ [Letter.p] from rfl, nla_hStringAt,
    List.getD_cons_succ, getD_append_left' _ _ _ _ (by simpa using hj), altStair_getD_map_range _ _ _ _ hj]
  simp only [Prod.mk.injEq, true_and]
  constructor <;> ring

theorem nlaFwd_tile_last (k : ℕ) :
    (nlaFwd k).tile (2 * k + 1) = (ZTile.zero, (2 * (k : ℤ) + 2, 2 * (k : ℤ) + 1)) := by
  unfold PTFamily.tile
  show (hStringAt (nlaWord k) (0, 1)).getD (2 * k + 1) _ = _
  rw [show nlaWord k = List.replicate (2 * k + 1) Letter.q ++ [Letter.p] from rfl, nla_hStringAt]
  simp
  ring

theorem nlaRev_n (k : ℕ) : (nlaRev k).n = 2 * k + 2 := by
  simp [PTFamily.n, nlaRev, nlaWord, nla_rev_list, nlaRevC]

theorem nlaRev_tile_zero (k : ℕ) : (nlaRev k).tile 0 = (ZTile.zero, nlaRevC k) := by
  unfold PTFamily.tile
  show (hRevStringAt (nlaWord k).reverse (nlaRevC k)).getD 0 _ = _
  rw [nla_word_reverse, nla_rev_list]
  simp

theorem nlaRev_tile_succ (k j : ℕ) (hj : j < 2 * k + 1) :
    (nlaRev k).tile (j + 1) = (ZTile.one, ((j : ℤ), 4 * (k : ℤ) + 3 + (j : ℤ))) := by
  unfold PTFamily.tile
  show (hRevStringAt (nlaWord k).reverse (nlaRevC k)).getD (j + 1) _ = _
  rw [nla_word_reverse, nla_rev_list, List.getD_cons_succ, altStair_getD_map_range _ _ _ _ hj]
  simp only [nlaRevC, Prod.mk.injEq, true_and]
  constructor <;> ring

/-! ### The point set `T̂_{q_1}` and its inside-tile clause -/

theorem mem_nlaTile (d : ℤ) (x : GInt) :
    x ∈ paperNearLadderAltTile d ↔
      (((x = (-2, 2 * d) ∨ x = (d + 1, d - 1)) ∨ (x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d - 1)) ∨
        (-2 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 2 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d + 1)) ∧
      ¬ ((x.1 ≤ -1 ∧ x.2 ≤ d - 1) ∨ (d ≤ x.1 ∧ 2 * d ≤ x.2)) := by
  unfold paperNearLadderAltTile paperNearLadderAltA paperNearLadderAltB paperNearLadderAltC paperNearLadderAltD
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]

theorem mem_shape_oneD (c y : GInt) :
    y ∈ (tileShape ZTile.oneD).map (· + c) ↔
      (y.1 - c.1 = 0 ∧ y.2 - c.2 = 0) ∨ (y.1 - c.1 = 0 ∧ y.2 - c.2 = 1) ∨ (y.1 - c.1 = 1 ∧ y.2 - c.2 = 0) ∨
        (y.1 - c.1 = 1 ∧ y.2 - c.2 = 1) ∨ (y.1 - c.1 = -1 ∧ y.2 - c.2 = 1) ∨ (y.1 - c.1 = 1 ∧ y.2 - c.2 = -1) := by
  simp only [tileShape, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false, Prod.ext_iff,
    Prod.fst_add, Prod.snd_add]
  constructor <;> intro h <;> omega

/-- A placed list is inside `T` when every tile of it lies in `T`. -/
theorem inside_of_tiles (T : Set GInt) (ts : List (ZTile × GInt))
    (h : ∀ tp ∈ ts, ∀ y ∈ (tileShape tp.1).map (· + tp.2), y ∈ T) : InsideTile T ts := by
  intro x hx
  simp only [placedSites, List.mem_flatMap] at hx
  obtain ⟨tp, htp, hx⟩ := hx
  exact h tp htp x hx

theorem nla_inside (k : ℕ) (hk : 1 ≤ k) :
    InsideTile (paperNearLadderAltTile (2 * (k : ℤ) + 2)) (hPartialTiles (nlaWord k) (0, 1) (nlaRevC k)) := by
  apply inside_of_tiles
  intro tp htp y hy
  simp only [hPartialTiles, List.mem_append] at htp
  rcases htp with htp | htp
  · rw [show nlaWord k = List.replicate (2 * k + 1) Letter.q ++ [Letter.p] from rfl, nla_hStringAt] at htp
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.mem_nil_iff, or_false] at htp
    rcases htp with rfl | ⟨j, hj, rfl⟩ | rfl
    · dsimp only at hy
      rw [mem_shape_one] at hy
      unfold oneAt at hy
      rw [mem_nlaTile]
      simp only [Prod.ext_iff]
      omega
    · dsimp only at hy
      rw [mem_shape_oneD] at hy
      rw [mem_nlaTile]
      simp only [Prod.ext_iff]
      omega
    · dsimp only at hy
      rw [mem_shape_zero] at hy
      unfold zeroAt at hy
      rw [mem_nlaTile]
      simp only [Prod.ext_iff]
      omega
  · rw [nla_word_reverse, nla_rev_list] at htp
    simp only [List.mem_cons, List.mem_map, List.mem_range] at htp
    rcases htp with rfl | ⟨j, hj, rfl⟩
    · dsimp only [nlaRevC] at hy
      rw [mem_shape_zero] at hy
      unfold zeroAt at hy
      rw [mem_nlaTile]
      simp only [Prod.ext_iff]
      omega
    · dsimp only [nlaRevC] at hy
      rw [mem_shape_one] at hy
      unfold oneAt at hy
      rw [mem_nlaTile]
      simp only [Prod.ext_iff]
      omega

/-- The lower-left point of `T̂_{q_1}` is `(0,1)` (surgical `c(T̂_{q_1})`, `d = 2k+2 ≥ 4`). -/
theorem nla_lowerLeft (k : ℕ) (hk : 1 ≤ k) :
    IsLowerLeftPt (paperNearLadderAltTile (2 * (k : ℤ) + 2)) (0, 1) := by
  refine ⟨?_, ?_⟩
  · rw [mem_nlaTile]
    simp only [Prod.ext_iff]
    omega
  · intro x hx
    rw [mem_nlaTile] at hx
    simp only [Prod.ext_iff] at hx
    simp only [lowerLexLe]
    omega


/-! ### 2. The closed form of `paperNearLadderAltValue`, the slopes, and the boundary keys -/

theorem nla_sq_div4 (m e : ℤ) : (2 * m + e) ^ 2 / 4 = m * m + m * e + e ^ 2 / 4 := by
  rw [show (2 * m + e) ^ 2 = e ^ 2 + 4 * (m * m + m * e) by ring]
  generalize e ^ 2 = q
  generalize m * m + m * e = c
  omega

theorem nla_ind (d : ℤ) (x : GInt) :
    (paperNearLadderAltA d ∪ paperNearLadderAltB d).indicator (fun _ => (1 : ℤ)) x =
      if (x.1 = -2 ∧ x.2 = 2 * d) ∨ (x.1 = d + 1 ∧ x.2 = d - 1) ∨ (x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d - 1)
        then 1 else 0 := by
  classical
  by_cases h : (x.1 = -2 ∧ x.2 = 2 * d) ∨ (x.1 = d + 1 ∧ x.2 = d - 1) ∨ (x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d - 1)
  · have hm : x ∈ paperNearLadderAltA d ∪ paperNearLadderAltB d := by
      unfold paperNearLadderAltA paperNearLadderAltB
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff]
      tauto
    rw [Set.indicator_apply, if_pos hm, if_pos h]
  · have hm : x ∉ paperNearLadderAltA d ∪ paperNearLadderAltB d := by
      unfold paperNearLadderAltA paperNearLadderAltB
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff]
      tauto
    rw [Set.indicator_apply, if_neg hm, if_neg h]

theorem nla_value_eq (d : ℤ) (x : GInt) :
    paperNearLadderAltValue d x = -((x.2 - x.1) ^ 2 / 4) + min 0 (d - x.2) + min 0 (2 * d - 1 - x.2) +
      max 0 (x.2 - x.1 - d) +
      (if (x.1 = -2 ∧ x.2 = 2 * d) ∨ (x.1 = d + 1 ∧ x.2 = d - 1) ∨ (x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d - 1)
        then 1 else 0) := by
  unfold paperNearLadderAltValue
  rw [nla_ind]

/-- The one tile of the forward string at `(0,1)`. -/
theorem nla_fwd_value_one (k : ℕ) (hk : 1 ≤ k) (x : GInt)
    (hx : x ∈ (tileShape ZTile.one).map (· + ((0 : ℤ), (1 : ℤ)))) :
    paperNearLadderAltValue (2 * (k : ℤ) + 2) x = zTileOdo ZTile.one (x - ((0 : ℤ), (1 : ℤ))) := by
  rw [mem_shape_one] at hx
  unfold oneAt at hx
  obtain ⟨x1, x2⟩ := x
  simp only at hx ⊢
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  rw [nla_value_eq]
  have h1 : x1 = 0 ∨ x1 = 1 := by omega
  have h2 : x2 = 1 ∨ x2 = 2 := by omega
  simp only [zTileOdo, oneOdometer, Prod.mk_sub_mk, sub_zero, Prod.mk.injEq, min_def, max_def]
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> norm_num <;> split_ifs <;> omega

/-- The one-tiles `T_{q_d}` of the forward string, at `(j+1, j+2)`: the odometer is the enlarged one-odometer there. -/
theorem nla_fwd_value_oneD (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 * k) (x : GInt)
    (hx : x ∈ (tileShape ZTile.oneD).map (· + (((j : ℤ) + 1), ((j : ℤ) + 2)))) :
    paperNearLadderAltValue (2 * (k : ℤ) + 2) x = zTileOdo ZTile.oneD (x - (((j : ℤ) + 1), ((j : ℤ) + 2))) := by
  obtain ⟨x1, x2⟩ := x
  rw [mem_shape_oneD] at hx
  simp only at hx
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hj' : (j : ℤ) < 2 * (k : ℤ) := by exact_mod_cast hj
  rw [nla_value_eq]
  simp only [zTileOdo, oneOdometer, Prod.mk_sub_mk, Prod.mk.injEq, min_def, max_def]
  have hu : x2 - x1 = (x2 - ((j : ℤ) + 2)) - (x1 - ((j : ℤ) + 1)) + 1 := by ring
  rw [hu]
  rcases hx with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rw [a1, a2] <;> norm_num <;> split_ifs <;> omega

/-- The zero tile of the forward string at `(2k+2, 2k+1)`. -/
theorem nla_fwd_value_zero (k : ℕ) (hk : 1 ≤ k) (x : GInt)
    (hx : x ∈ (tileShape ZTile.zero).map (· + (2 * ((k : ℤ)) + 2, 2 * (k : ℤ) + 1))) :
    paperNearLadderAltValue (2 * (k : ℤ) + 2) x = zTileOdo ZTile.zero (x - (2 * (k : ℤ) + 2, 2 * (k : ℤ) + 1)) := by
  rw [mem_shape_zero] at hx
  unfold zeroAt at hx
  obtain ⟨x1, x2⟩ := x
  simp only at hx ⊢
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  rw [nla_value_eq]
  have h1 : x1 - (2 * (k : ℤ) + 2) = 0 ∨ x1 - (2 * (k : ℤ) + 2) = 1 := by omega
  have h2 : x2 - (2 * (k : ℤ) + 1) = 0 ∨ x2 - (2 * (k : ℤ) + 1) = 1 ∨ x2 - (2 * (k : ℤ) + 1) = 2 := by omega
  simp only [zTileOdo, zeroOdometer, Prod.mk_sub_mk, Prod.mk.injEq, min_def, max_def]
  have hu : x2 - x1 = (x2 - (2 * (k : ℤ) + 1)) - (x1 - (2 * (k : ℤ) + 2)) - 1 := by ring
  rw [hu]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> rw [h1, h2] <;> norm_num <;> split_ifs <;> omega

/-- The reversed zero tile at `(-2, 4k+2)`: the affine factor `(2k+1, -(2k+2))` and constant `(2k+2)^2`. -/
theorem nla_rev_value_zero (k : ℕ) (hk : 1 ≤ k) (x : GInt)
    (hx : x ∈ (tileShape ZTile.zero).map (· + nlaRevC k)) :
    paperNearLadderAltValue (2 * (k : ℤ) + 2) x =
      zTileOdo ZTile.zero (x - nlaRevC k) + (2 * (k : ℤ) + 1) * x.1 + (-(2 * (k : ℤ) + 2)) * x.2 +
        (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 2) := by
  rw [mem_shape_zero] at hx
  unfold zeroAt nlaRevC at hx
  obtain ⟨x1, x2⟩ := x
  simp only at hx ⊢
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  rw [nla_value_eq]
  obtain ⟨s, rfl⟩ : ∃ s : ℤ, x1 = -2 + s := ⟨x1 + 2, by ring⟩
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, x2 = 4 * (k : ℤ) + 2 + t := ⟨x2 - (4 * (k : ℤ) + 2), by ring⟩
  have hs : s = 0 ∨ s = 1 := by omega
  have ht : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rw [show 4 * (k : ℤ) + 2 + t - (-2 + s) = 2 * (2 * (k : ℤ) + 2) + (t - s) by ring, nla_sq_div4]
  simp only [nlaRevC, zTileOdo, zeroOdometer, Prod.mk_sub_mk, Prod.mk.injEq, min_def, max_def]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> norm_num <;> ring_nf <;>
    generalize (k : ℤ) ^ 2 = Q <;> (try simp only [true_or] at ⊢) <;> split_ifs <;> omega

/-- The reversed one tiles at `(j, 4k+3+j)`, `j < 2k+1`. -/
theorem nla_rev_value_one (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 * k + 1) (x : GInt)
    (hx : x ∈ (tileShape ZTile.one).map (· + ((j : ℤ), 4 * (k : ℤ) + 3 + (j : ℤ)))) :
    paperNearLadderAltValue (2 * (k : ℤ) + 2) x =
      zTileOdo ZTile.one (x - ((j : ℤ), 4 * (k : ℤ) + 3 + (j : ℤ))) + (2 * (k : ℤ)) * x.1 +
        (-(2 * (k : ℤ) + 2)) * x.2 + (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 2) := by
  rw [mem_shape_one] at hx
  unfold oneAt at hx
  obtain ⟨x1, x2⟩ := x
  simp only at hx ⊢
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hj' : (j : ℤ) < 2 * (k : ℤ) + 1 := by exact_mod_cast hj
  rw [nla_value_eq]
  obtain ⟨s, rfl⟩ : ∃ s : ℤ, x1 = (j : ℤ) + s := ⟨x1 - (j : ℤ), by ring⟩
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, x2 = 4 * (k : ℤ) + 3 + (j : ℤ) + t := ⟨x2 - (4 * (k : ℤ) + 3 + (j : ℤ)), by ring⟩
  have hs : s = 0 ∨ s = 1 := by omega
  have ht : t = 0 ∨ t = 1 := by omega
  rw [show 4 * (k : ℤ) + 3 + (j : ℤ) + t - ((j : ℤ) + s) = 2 * (2 * (k : ℤ) + 2) + (t - s - 1) by ring,
    nla_sq_div4]
  simp only [zTileOdo, oneOdometer, Prod.mk_sub_mk, Prod.mk.injEq, min_def, max_def]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num <;> ring_nf <;>
    generalize (k : ℤ) ^ 2 = Q <;> split_ifs <;>
      (try simp only [false_and, false_or] at *) <;> omega

/-! ### Slopes -/

theorem unitSquares_oneD_ne' : unitSquares (tileShape ZTile.oneD) ≠ [] := by decide

theorem intrinsic_oneD : slopeOf (zTileOdo ZTile.oneD) (tileShape ZTile.oneD) = (1 / 2, -1 / 2) := by
  decide +kernel

/-! ### Boundary keys and overlap -/

/-- The enlarged one tile followed by a zero tile two columns to the right: the odometers agree at unit-apart points. -/
theorem key_dz (p p' x y : GInt) (hp1 : p'.1 = p.1 + 2) (hp2 : p'.2 = p.2)
    (hx : x ∈ (tileShape ZTile.oneD).map (· + p)) (hy : zeroAt p' y) (hu : unitApart x y) :
    zTileOdo ZTile.oneD (x - p) = zeroOdometer (y - p') := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := p'
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  rw [mem_shape_oneD] at hx
  unfold zeroAt at hy
  unfold unitApart at hu
  simp only [Prod.mk_sub_mk, zTileOdo, zeroOdometer, oneOdometer, Prod.mk.injEq] at hx hy hu ⊢
  split_ifs <;> omega

/-- Overlapping consecutive tiles: the boundary implication holds vacuously. -/
theorem boundary_vacuous (F : PTFamily) (o : Orientation) (j : ℕ) (z : GInt)
    (h1 : z ∈ F.dom j) (h2 : z ∈ F.dom (j + 1)) :
    ((¬ ∃ x, x ∈ F.dom j ∧ x ∈ F.dom (j + 1)) →
        ∀ x ∈ F.dom j, ∀ y ∈ F.dom (j + 1), unitApart x y →
          (o = .horizontal → F.odo j x - ptDot (F.a j) x = F.odo (j + 1) y - ptDot (F.a j) y) ∧
            (o = .vertical → (F.odo (j + 1) y - ptDot (F.a j) y) - (F.odo j x - ptDot (F.a j) x) = -1)) := by
  intro hno
  exact (hno ⟨z, h1, h2⟩).elim

theorem mem_dom_of_shape (F : PTFamily) (j : ℕ) (u : GInt) (hu : u ∈ tileShape (F.tile j).1) :
    u + (F.tile j).2 ∈ F.dom j :=
  List.mem_map_of_mem hu


/-! ### 3. The odometers, the slopes, the agreement and the respect conditions -/

theorem nlaFwd_a (k j : ℕ) : (nlaFwd k).a j = 0 := rfl

theorem nlaFwd_odo_zero (k : ℕ) (x : GInt) :
    (nlaFwd k).odo 0 x = zTileOdo ZTile.one (x - ((0 : ℤ), (1 : ℤ))) := by
  unfold PTFamily.odo
  rw [nlaFwd_tile_zero]
  simp [nlaFwd]

theorem nlaFwd_odo_succ (k j : ℕ) (hj : j < 2 * k) (x : GInt) :
    (nlaFwd k).odo (j + 1) x = zTileOdo ZTile.oneD (x - (((j : ℤ) + 1), ((j : ℤ) + 2))) := by
  unfold PTFamily.odo
  rw [nlaFwd_tile_succ k j hj]
  simp [nlaFwd]

theorem nlaFwd_odo_last (k : ℕ) (x : GInt) :
    (nlaFwd k).odo (2 * k + 1) x = zTileOdo ZTile.zero (x - (2 * (k : ℤ) + 2, 2 * (k : ℤ) + 1)) := by
  unfold PTFamily.odo
  rw [nlaFwd_tile_last k]
  simp [nlaFwd]

theorem nlaFwd_tile_2k (k : ℕ) (hk : 1 ≤ k) :
    (nlaFwd k).tile (2 * k) = (ZTile.oneD, (2 * (k : ℤ), 2 * (k : ℤ) + 1)) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 1 := ⟨2 * k - 1, by omega⟩
  rw [hm, nlaFwd_tile_succ k m (by omega)]
  have h1 : (m : ℤ) + 1 = 2 * (k : ℤ) := by omega
  have h2 : (m : ℤ) + 2 = 2 * (k : ℤ) + 1 := by omega
  rw [h1, h2]

theorem nlaFwd_odo_2k (k : ℕ) (hk : 1 ≤ k) (x : GInt) :
    (nlaFwd k).odo (2 * k) x = zTileOdo ZTile.oneD (x - (2 * (k : ℤ), 2 * (k : ℤ) + 1)) := by
  unfold PTFamily.odo
  rw [nlaFwd_tile_2k k hk]
  simp [nlaFwd]

theorem nlaFwd_slope_one (k : ℕ) :
    slopeOf ((nlaFwd k).odo 0) ((nlaFwd k).dom 0) = (1 / 2, -1 / 2) := by
  rw [slope_fam_odo _ _ (by rw [nlaFwd_tile_zero]; exact unitSquares_one_ne), nlaFwd_tile_zero]
  simp [nlaFwd, intrinsic_one]

theorem nlaFwd_slope_oneD (k j : ℕ) (hj : j < 2 * k) :
    slopeOf ((nlaFwd k).odo (j + 1)) ((nlaFwd k).dom (j + 1)) = (1 / 2, -1 / 2) := by
  rw [slope_fam_odo _ _ (by rw [nlaFwd_tile_succ k j hj]; exact unitSquares_oneD_ne'),
    nlaFwd_tile_succ k j hj]
  simp [nlaFwd, intrinsic_oneD]

theorem nlaFwd_slope_2k (k : ℕ) (hk : 1 ≤ k) :
    slopeOf ((nlaFwd k).odo (2 * k)) ((nlaFwd k).dom (2 * k)) = (1 / 2, -1 / 2) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 1 := ⟨2 * k - 1, by omega⟩
  rw [hm]
  exact nlaFwd_slope_oneD k m (by omega)

theorem nlaFwd_slope_zero (k : ℕ) :
    slopeOf ((nlaFwd k).odo (2 * k + 1)) ((nlaFwd k).dom (2 * k + 1)) = (0, -1 / 2) := by
  rw [slope_fam_odo _ _ (by rw [nlaFwd_tile_last k]; exact unitSquares_zero_ne), nlaFwd_tile_last k]
  simp [nlaFwd, intrinsic_zero]

theorem nlaRev_a_zero (k : ℕ) : (nlaRev k).a 0 = ((2 * (k : ℤ) + 1), -(2 * (k : ℤ) + 2)) := by
  simp [nlaRev]

theorem nlaRev_a_succ (k j : ℕ) : (nlaRev k).a (j + 1) = ((2 * (k : ℤ)), -(2 * (k : ℤ) + 2)) := by
  simp [nlaRev]

theorem nlaRev_odo_zero (k : ℕ) (x : GInt) :
    (nlaRev k).odo 0 x = zTileOdo ZTile.zero (x - nlaRevC k) + (2 * (k : ℤ) + 1) * x.1 +
      (-(2 * (k : ℤ) + 2)) * x.2 + (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 2) := by
  unfold PTFamily.odo
  rw [nlaRev_tile_zero, nlaRev_a_zero]
  simp [nlaRev]

theorem nlaRev_odo_succ (k j : ℕ) (hj : j < 2 * k + 1) (x : GInt) :
    (nlaRev k).odo (j + 1) x = zTileOdo ZTile.one (x - ((j : ℤ), 4 * (k : ℤ) + 3 + (j : ℤ))) +
      (2 * (k : ℤ)) * x.1 + (-(2 * (k : ℤ) + 2)) * x.2 + (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 2) := by
  unfold PTFamily.odo
  rw [nlaRev_tile_succ k j hj, nlaRev_a_succ k j]
  simp [nlaRev]

theorem nlaRev_slope_zero (k : ℕ) :
    slopeOf ((nlaRev k).odo 0) ((nlaRev k).dom 0) =
      (0, -1 / 2) + ((2 * (k : ℚ) + 1), -(2 * (k : ℚ) + 2)) := by
  rw [slope_fam_odo _ _ (by rw [nlaRev_tile_zero]; exact unitSquares_zero_ne), nlaRev_tile_zero,
    nlaRev_a_zero]
  simp [intrinsic_zero]

theorem nlaRev_slope_one (k j : ℕ) (hj : j < 2 * k + 1) :
    slopeOf ((nlaRev k).odo (j + 1)) ((nlaRev k).dom (j + 1)) =
      (1 / 2, -1 / 2) + ((2 * (k : ℚ)), -(2 * (k : ℚ) + 2)) := by
  rw [slope_fam_odo _ _ (by rw [nlaRev_tile_succ k j hj]; exact unitSquares_one_ne),
    nlaRev_tile_succ k j hj, nlaRev_a_succ k j]
  simp [intrinsic_one]

theorem nla_fwd_agree (k : ℕ) (hk : 1 ≤ k) :
    ∀ j < (nlaFwd k).n, ∀ x ∈ (nlaFwd k).dom j,
      paperNearLadderAltValue (2 * (k : ℤ) + 2) x = (nlaFwd k).odo j x := by
  intro j hj x hx
  rw [nlaFwd_n] at hj
  rcases j with _ | j
  · unfold PTFamily.dom at hx
    rw [nlaFwd_tile_zero] at hx
    dsimp only at hx
    rw [nla_fwd_value_one k hk x hx, nlaFwd_odo_zero]
  · by_cases hj2 : j < 2 * k
    · unfold PTFamily.dom at hx
      rw [nlaFwd_tile_succ k j hj2] at hx
      dsimp only at hx
      rw [nla_fwd_value_oneD k j hk hj2 x hx, nlaFwd_odo_succ k j hj2]
    · have hj3 : j = 2 * k := by omega
      subst hj3
      unfold PTFamily.dom at hx
      rw [nlaFwd_tile_last k] at hx
      dsimp only at hx
      rw [nla_fwd_value_zero k hk x hx, nlaFwd_odo_last k x]

theorem nla_rev_agree (k : ℕ) (hk : 1 ≤ k) :
    ∀ j < (nlaRev k).n, ∀ x ∈ (nlaRev k).dom j,
      paperNearLadderAltValue (2 * (k : ℤ) + 2) x = (nlaRev k).odo j x := by
  intro j hj x hx
  rw [nlaRev_n] at hj
  rcases j with _ | j
  · unfold PTFamily.dom at hx
    rw [nlaRev_tile_zero] at hx
    dsimp only at hx
    rw [nla_rev_value_zero k hk x hx, nlaRev_odo_zero]
  · unfold PTFamily.dom at hx
    rw [nlaRev_tile_succ k j (by omega)] at hx
    dsimp only at hx
    rw [nla_rev_value_one k j hk (by omega) x hx, nlaRev_odo_succ k j (by omega) x]

/-- The forward family respects `q^{2k+1} p`: the one tile, the enlarged one tiles and the zero tile. -/
theorem nla_fwd_respects (k : ℕ) (hk : 1 ≤ k) : (nlaFwd k).Respects .horizontal false := by
  intro J hJ
  rw [nlaFwd_n] at hJ
  rcases Nat.eq_zero_or_pos J with h0 | hpos
  · subst h0
    have e0 := nlaFwd_tile_zero k
    have e1 := nlaFwd_tile_succ k 0 (by omega)
    refine ⟨?_, boundary_vacuous _ _ _ ((1 : ℤ), (2 : ℤ)) ?_ ?_⟩
    · rw [nlaFwd_slope_oneD k 0 (by omega), nlaFwd_slope_one k, e0, e1]
      norm_num [surgicalSlopeDiff, zTileLetter, Prod.ext_iff]
    · unfold PTFamily.dom
      rw [e0]
      exact List.mem_map.2 ⟨((1 : ℤ), (1 : ℤ)), by decide, by decide⟩
    · unfold PTFamily.dom
      rw [e1]
      exact List.mem_map.2 ⟨((0 : ℤ), (0 : ℤ)), by decide, by decide⟩
  · obtain ⟨i, rfl⟩ : ∃ i, J = i + 1 := ⟨J - 1, by omega⟩
    by_cases hi : i + 2 ≤ 2 * k
    · have ea := nlaFwd_tile_succ k i (by omega)
      have eb := nlaFwd_tile_succ k (i + 1) (by omega)
      refine ⟨?_, boundary_vacuous _ _ _ (((i : ℤ) + 2), ((i : ℤ) + 3)) ?_ ?_⟩
      · rw [nlaFwd_slope_oneD k (i + 1) (by omega), nlaFwd_slope_oneD k i (by omega), ea, eb]
        norm_num [surgicalSlopeDiff, zTileLetter, Prod.ext_iff]
      · unfold PTFamily.dom
        rw [ea]
        exact List.mem_map.2 ⟨((1 : ℤ), (1 : ℤ)), by simp [tileShape], by
          ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring⟩
      · unfold PTFamily.dom
        rw [eb]
        exact List.mem_map.2 ⟨((0 : ℤ), (0 : ℤ)), by simp [tileShape], by
          ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one] <;> ring⟩
    · have hJ' : i + 1 = 2 * k := by omega
      rw [hJ']
      refine ⟨?_, fun _ x hx y hy hu => ⟨fun _ => ?_, fun h => by cases h⟩⟩
      · rw [nlaFwd_slope_zero k, nlaFwd_slope_2k k hk, nlaFwd_tile_2k k hk, nlaFwd_tile_last k]
        norm_num [surgicalSlopeDiff, zTileLetter, Prod.ext_iff]
      · rw [nlaFwd_odo_2k k hk x, nlaFwd_odo_last k y, nlaFwd_a]
        have hx' : x ∈ (tileShape ZTile.oneD).map (· + (2 * (k : ℤ), 2 * (k : ℤ) + 1)) := by
          unfold PTFamily.dom at hx
          rw [nlaFwd_tile_2k k hk] at hx
          exact hx
        have hy' : zeroAt (2 * (k : ℤ) + 2, 2 * (k : ℤ) + 1) y := by
          unfold PTFamily.dom at hy
          rw [nlaFwd_tile_last k, mem_shape_zero] at hy
          exact hy
        have key := key_dz (2 * (k : ℤ), 2 * (k : ℤ) + 1) (2 * (k : ℤ) + 2, 2 * (k : ℤ) + 1) x y rfl rfl hx' hy' hu
        simp only [ptDot, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, sub_zero]
        exact key

/-- The reversed family respects `p q^{2k+1}`: the zero tile, then the one tiles. -/
theorem nla_rev_respects (k : ℕ) (hk : 1 ≤ k) : (nlaRev k).Respects .horizontal true := by
  intro J hJ
  rw [nlaRev_n] at hJ
  rcases Nat.eq_zero_or_pos J with h0 | hpos
  · subst h0
    have e0 := nlaRev_tile_zero k
    have e1 := nlaRev_tile_succ k 0 (by omega)
    refine ⟨?_, fun _ x hx y hy hu => ⟨fun _ => ?_, fun h => by cases h⟩⟩
    · rw [nlaRev_slope_zero k, nlaRev_slope_one k 0 (by omega), e0, e1]
      ext <;> (norm_num [surgicalSlopeDiff, zTileLetter, Prod.ext_iff]; try ring_nf)
    · unfold PTFamily.dom at hx hy
      rw [e0, mem_shape_zero] at hx
      rw [e1] at hy
      rw [mem_shape_one] at hy
      rw [nlaRev_odo_zero, nlaRev_odo_succ k 0 (by omega), nlaRev_a_zero]
      have key := key_zo (nlaRevC k) (((0 : ℕ) : ℤ), 4 * (k : ℤ) + 3 + ((0 : ℕ) : ℤ)) x y
        (by simp [nlaRevC]) (by norm_num [nlaRevC]; try ring) hx hy hu
      simp only [Nat.cast_zero, add_zero, sub_zero, Prod.fst_sub, zTileOdo, ptDot] at key ⊢
      linarith [key]
  · obtain ⟨i, rfl⟩ : ∃ i, J = i + 1 := ⟨J - 1, by omega⟩
    have ea := nlaRev_tile_succ k i (by omega)
    have eb := nlaRev_tile_succ k (i + 1) (by omega)
    refine ⟨?_, boundary_vacuous _ _ _ (((i : ℤ) + 1), (4 * (k : ℤ) + 4 + (i : ℤ))) ?_ ?_⟩
    · rw [nlaRev_slope_one k (i + 1) (by omega), nlaRev_slope_one k i (by omega), ea, eb]
      norm_num [surgicalSlopeDiff, zTileLetter, Prod.ext_iff]
    · unfold PTFamily.dom
      rw [ea]
      exact List.mem_map.2 ⟨((1 : ℤ), (1 : ℤ)), by simp [tileShape], by
        ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring⟩
    · unfold PTFamily.dom
      rw [eb]
      exact List.mem_map.2 ⟨((0 : ℤ), (0 : ℤ)), by simp [tileShape], by
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one] <;> ring⟩

theorem nla_fwd_tiles (k : ℕ) (hk : 1 ≤ k) :
    RespectsTiles .horizontal false (hStringAt (nlaWord k) (0, 1))
      (paperNearLadderAltValue (2 * (k : ℤ) + 2)) :=
  ⟨nlaFwd k, rfl, nla_fwd_agree k hk, nla_fwd_respects k hk⟩

theorem nla_rev_tiles (k : ℕ) (hk : 1 ≤ k) :
    RespectsTiles .horizontal true (hRevStringAt (nlaWord k).reverse (nlaRevC k))
      (paperNearLadderAltValue (2 * (k : ℤ) + 2)) :=
  ⟨nlaRev k, rfl, nla_rev_agree k hk, nla_rev_respects k hk⟩

/-- `T̂_{q_1}` is a partial `w_h`-pseudo-square with the lower-left anchor `(0,1)` (surgical `lemma:basecase_2k_even_alt`,
Moreover, `w_h = q^{2k+1} p`), and `ĝ_{q_1}` respects it. -/
theorem nla_respectsPartialH (k : ℕ) (hk : 1 ≤ k) :
    RespectsPartialH (paperNearLadderAltTile (2 * (k : ℤ) + 2)) (nlaWord k)
      (paperNearLadderAltValue (2 * (k : ℤ) + 2)) :=
  ⟨(0, 1), nla_lowerLeft k hk, nlaRevC k, nla_inside k hk, nla_fwd_tiles k hk, nla_rev_tiles k hk⟩

end FLatticePaper.Tiles
