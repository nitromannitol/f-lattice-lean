import FLatticePaper.Tiles.AltStairPseudo
import FLatticePaper.Tiles.PartialBoundary
import FLatticePaper.Tiles.ZeroOneSlopes

/-! # The alternate staircase: its two `RespectsTiles` instances, for every `k`

For `d = 2k+3` (surgical `lemma:basecase_3k_even_alt`, lines 2262 and 2268-2269), the odometer `paperStairAltValue d`
respects the forward horizontal string `hStringAt (stairH k) (0,0)` (word `q p^{k+1}`) and the reversed horizontal string
`hRevStringAt (stairH k).reverse (4-2d, d-2)` (word `p^{k+1} q`), in the sense of the shared `RespectsTiles` of
`PartialBoundary.lean`. This file proves both instances for every `k`. The anchored predicate that combines them with the
containment `altStair_horizontal_contain` is stated once `PartialBoundary` takes point sets (w2).

Section 1 computes the placed lists explicitly, so that the tile of each index is known. -/

namespace FLatticePaper.Tiles

/-! ### 1. The placed lists -/

theorem tileSeqAux_replicate_p (m : ℕ) (prev : Option Letter) :
    tileSeqAux prev (List.replicate m Letter.p) = List.replicate m ZTile.zero := by
  induction m generalizing prev with
  | zero => rfl
  | succ m ih => simp only [List.replicate_succ, tileSeqAux, ih]

theorem tileSeq_stairH (k : ℕ) :
    tileSeq (stairH k) = ZTile.one :: List.replicate (k + 1) ZTile.zero := by
  simp only [tileSeq, stairH, tileSeqAux, tileSeqAux_replicate_p]

/-- `m+1` zero tiles zipped with the `m` offsets `(2,0)` from `c`: tile `j` sits at `c + (2j, 0)`. -/
theorem zip_zero_scanl (m : ℕ) (c : GInt) :
    (List.replicate (m + 1) ZTile.zero).zip
        (List.scanl (· + ·) c (List.replicate m ((2 : ℤ), (0 : ℤ)))) =
      (List.range (m + 1)).map fun j : ℕ => (ZTile.zero, (c.1 + 2 * (j : ℤ), c.2)) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    have r1 : List.replicate (m + 1 + 1) ZTile.zero = ZTile.zero :: List.replicate (m + 1) ZTile.zero := rfl
    have r2 : List.replicate (m + 1) ((2 : ℤ), (0 : ℤ)) = ((2 : ℤ), (0 : ℤ)) :: List.replicate m ((2 : ℤ), (0 : ℤ)) := rfl
    have hr : List.range (m + 1 + 1) = 0 :: List.map Nat.succ (List.range (m + 1)) := by
      rw [List.range_succ_eq_map]
    rw [r1, r2, List.scanl_cons, List.zip_cons_cons, ih, hr, List.map_cons, List.map_map, List.cons_eq_cons]
    refine ⟨by simp, ?_⟩
    apply List.map_congr_left
    intro j _
    (simp only [Function.comp_apply, Nat.succ_eq_add_one, Prod.mk.injEq, true_and, Prod.fst_add, Prod.snd_add];
      push_cast; ring_nf; simp)

/-- The forward horizontal string of `stairH k` at `(0,0)`: one tile at `(0,0)`, then `k+1` zero tiles at `(2(j+1), 0)`. -/
theorem hStringAt_stairH (k : ℕ) :
    hStringAt (stairH k) (0, 0) =
      (ZTile.one, (0, 0)) :: (List.range (k + 1)).map fun j : ℕ => (ZTile.zero, (2 * ((j : ℤ) + 1), 0)) := by
  have hw : (stairH k).tail.map hOffset = List.replicate (k + 1) ((2 : ℤ), (0 : ℤ)) := by
    simp [stairH, hOffset]
  unfold hStringAt
  have r2 : List.replicate (k + 1) ((2 : ℤ), (0 : ℤ)) = ((2 : ℤ), (0 : ℤ)) :: List.replicate k ((2 : ℤ), (0 : ℤ)) := rfl
  rw [hw, tileSeq_stairH, r2, List.scanl_cons, List.zip_cons_cons,
    zip_zero_scanl k (((0 : ℤ), (0 : ℤ)) + ((2 : ℤ), (0 : ℤ)))]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Prod.mk_add_mk, Prod.mk.injEq, true_and, zero_add, add_zero]
  constructor <;> (push_cast; try ring)

/-- The reversed horizontal string of a `pq`-free word: `hRevStringAt (p :: p :: w) c` starts with the zero tile at `c`. -/
theorem hRevStringAt_cons_pp (w : BinaryWord) (c : GInt) :
    hRevStringAt (Letter.p :: Letter.p :: w) c =
      (ZTile.zero, c) :: hRevStringAt (Letter.p :: w) (c + ((2 : ℤ), (0 : ℤ))) := by
  simp [hRevStringAt, hRevOffset, letterZTile, List.scanl_cons]

/-- The reversed string of `p^{m+1} q` at `c`: zero tiles at `c + (2j, 0)`, `j = 0..m`, then the one tile at `c + (2(m+1), 1)`. -/
theorem hRevStringAt_rep (m : ℕ) (c : GInt) :
    hRevStringAt (List.replicate (m + 1) Letter.p ++ [Letter.q]) c =
      (List.range (m + 1)).map (fun j : ℕ => (ZTile.zero, (c.1 + 2 * (j : ℤ), c.2))) ++
        [(ZTile.one, (c.1 + 2 * ((m : ℤ) + 1), c.2 + 1))] := by
  induction m generalizing c with
  | zero =>
    have e0 : (List.replicate 1 Letter.p) ++ [Letter.q] = [Letter.p, Letter.q] := rfl
    rw [e0]
    simp [hRevStringAt, hRevOffset, letterZTile, List.range_succ, Prod.ext_iff]
  | succ m ih =>
    have e : List.replicate (m + 1 + 1) Letter.p ++ [Letter.q] =
        Letter.p :: Letter.p :: (List.replicate m Letter.p ++ [Letter.q]) := rfl
    have e2 : Letter.p :: (List.replicate m Letter.p ++ [Letter.q]) =
        List.replicate (m + 1) Letter.p ++ [Letter.q] := rfl
    have hr : List.range (m + 1 + 1) = 0 :: List.map Nat.succ (List.range (m + 1)) := by
      rw [List.range_succ_eq_map]
    rw [e, hRevStringAt_cons_pp, e2, ih, hr, List.map_cons, List.cons_append, List.map_map, List.cons_eq_cons]
    refine ⟨by simp, ?_⟩
    congr 1
    · apply List.map_congr_left
      intro j _
      (simp only [Function.comp_apply, Nat.succ_eq_add_one, Prod.mk.injEq, true_and, Prod.fst_add, Prod.snd_add];
        push_cast; ring_nf; simp)
    · (simp only [List.cons.injEq, and_true, Prod.mk.injEq, Prod.fst_add, Prod.snd_add, true_and];
        push_cast; ring_nf; simp)

/-! ### 2. The two families and their tiles -/

/-- The lower-left corner `(4-2d, d-2)` of the reversed string, with `d = 2k+3`. -/
def revC (k : ℕ) : GInt := (4 - 2 * (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 - 2)

/-- The forward family of `hStringAt (stairH k) (0,0)`: zero affine part. -/
def fwdFam (k : ℕ) : PTFamily where
  ts := hStringAt (stairH k) (0, 0)
  a := fun _ => 0
  b := fun _ => 0

/-- The reversed family of `hRevStringAt (stairH k).reverse (revC k)`, with the affine factors of the alternate
staircase: `a = (1, -(2k+2))` and `b = (2k+1)(k+2)` on the zero tiles `j ≤ k`; `a = (0, -(2k+2))` and
`b = (2k+1)(k+2) - 2k` on the one tile `k+1`. -/
def revFam (k : ℕ) : PTFamily where
  ts := hRevStringAt (stairH k).reverse (revC k)
  a := fun j => if j ≤ k then ((1 : ℤ), -(2 * (k : ℤ) + 2)) else (0, -(2 * (k : ℤ) + 2))
  b := fun j =>
    if j ≤ k then (2 * (k : ℤ) + 1) * ((k : ℤ) + 2) else (2 * (k : ℤ) + 1) * ((k : ℤ) + 2) - 2 * (k : ℤ)

theorem altStair_getD_map_range {α : Type*} (n m : ℕ) (f : ℕ → α) (d : α) (hm : m < n) :
    ((List.range n).map f).getD m d = f m := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]

theorem fwdFam_n (k : ℕ) : (fwdFam k).n = k + 2 := by
  simp [PTFamily.n, fwdFam, hStringAt_stairH]

theorem fwdFam_tile_zero (k : ℕ) : (fwdFam k).tile 0 = (ZTile.one, (0, 0)) := by
  simp [PTFamily.tile, fwdFam, hStringAt_stairH]

theorem fwdFam_tile_succ (k m : ℕ) (hm : m < k + 1) :
    (fwdFam k).tile (m + 1) = (ZTile.zero, (2 * ((m : ℤ) + 1), 0)) := by
  unfold PTFamily.tile
  show (hStringAt (stairH k) (0, 0)).getD (m + 1) _ = _
  rw [hStringAt_stairH]
  simp only [List.getD_cons_succ]
  exact altStair_getD_map_range _ _ _ _ hm

theorem hRevStringAt_revC (k : ℕ) :
    hRevStringAt (stairH k).reverse (revC k) =
      (List.range (k + 1)).map (fun j : ℕ => (ZTile.zero, ((revC k).1 + 2 * (j : ℤ), (revC k).2))) ++
        [(ZTile.one, ((revC k).1 + 2 * ((k : ℤ) + 1), (revC k).2 + 1))] := by
  rw [stairH_reverse, hRevStringAt_rep k (revC k)]

theorem revFam_n (k : ℕ) : (revFam k).n = k + 2 := by
  simp [PTFamily.n, revFam, hRevStringAt_revC]

theorem getD_append_left' {α : Type*} (L1 L2 : List α) (j : ℕ) (d : α) (hj : j < L1.length) :
    (L1 ++ L2).getD j d = L1.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem revFam_tile_zero (k j : ℕ) (hj : j < k + 1) :
    (revFam k).tile j = (ZTile.zero, ((revC k).1 + 2 * (j : ℤ), (revC k).2)) := by
  unfold PTFamily.tile
  show (hRevStringAt (stairH k).reverse (revC k)).getD j _ = _
  rw [hRevStringAt_revC, getD_append_left' _ _ _ _ (by simpa using hj), altStair_getD_map_range _ _ _ _ hj]

theorem revFam_tile_last (k : ℕ) :
    (revFam k).tile (k + 1) = (ZTile.one, ((revC k).1 + 2 * ((k : ℤ) + 1), (revC k).2 + 1)) := by
  unfold PTFamily.tile
  show (hRevStringAt (stairH k).reverse (revC k)).getD (k + 1) _ = _
  rw [hRevStringAt_revC]
  simp

/-! ### 3. Slopes of the placed odometers -/

theorem unitSquares_zero_ne : unitSquares (tileShape ZTile.zero) ≠ [] := by decide

theorem unitSquares_one_ne : unitSquares (tileShape ZTile.one) ≠ [] := by decide

theorem intrinsic_zero : slopeOf (zTileOdo ZTile.zero) (tileShape ZTile.zero) = (0, -1 / 2) := by
  decide +kernel

theorem intrinsic_one : slopeOf (zTileOdo ZTile.one) (tileShape ZTile.one) = (1 / 2, -1 / 2) := by
  decide +kernel

/-- The slope of a placed zero-one tile with an affine part: the slope of the base tile plus the affine factor. -/
theorem slope_odo_tile (t : ZTile) (hU : unitSquares (tileShape t) ≠ []) (p a : GInt) (b : ℤ) :
    slopeOf (fun x => zTileOdo t (x - p) + a.1 * x.1 + a.2 * x.2 + b) ((tileShape t).map (· + p)) =
      slopeOf (zTileOdo t) (tileShape t) + (((a.1 : ℤ) : ℚ), ((a.2 : ℤ) : ℚ)) := by
  have e : (fun x : GInt => zTileOdo t (x - p) + a.1 * x.1 + a.2 * x.2 + b) =
      (fun x : GInt => zTileOdo t (x - p) + dotS a x + b) := by
    funext x
    simp only [dotS]
    ring
  have h1 := slopeOf_translate (zTileOdo t) (tileShape t) p
  have hU' : unitSquares ((tileShape t).map (· + p)) ≠ [] := by
    rw [unitSquares_map_add]
    simpa using hU
  have h2 := slopeOf_affine (fun x => zTileOdo t (x - p)) ((tileShape t).map (· + p)) a b hU'
  rw [e, ← h1]
  exact h2

/-! ### 4. The closed form of the alternate odometer on the tiles -/

open FLatticePaper.Construction (paperStairAltValue paperStairAltA paperStairAltB paperStairAltTile)

theorem ind_AB (d : ℤ) (x : GInt) :
    (paperStairAltA d ∪ paperStairAltB d).indicator (fun _ => (1 : ℤ)) x =
      if (x.1 = 1 - d ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∨ (x.1 = 3 ∧ d ≤ x.2 ∧ x.2 ≤ d + 1) ∨
          (x.1 + x.2 = 2 ∧ 0 < x.2 ∧ x.2 < d) then 1 else 0 := by
  by_cases h : (x.1 = 1 - d ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∨ (x.1 = 3 ∧ d ≤ x.2 ∧ x.2 ≤ d + 1) ∨
      (x.1 + x.2 = 2 ∧ 0 < x.2 ∧ x.2 < d)
  · classical
    have hm : x ∈ paperStairAltA d ∪ paperStairAltB d := by
      unfold paperStairAltA paperStairAltB
      simp only [Set.mem_union, Set.mem_setOf_eq]
      tauto
    rw [Set.indicator_apply, if_pos hm, if_pos h]
  · classical
    have hm : x ∉ paperStairAltA d ∪ paperStairAltB d := by
      unfold paperStairAltA paperStairAltB
      simp only [Set.mem_union, Set.mem_setOf_eq]
      tauto
    rw [Set.indicator_apply, if_neg hm, if_neg h]

theorem value_eq (d : ℤ) (x : GInt) :
    paperStairAltValue d x = -(x.2 * (x.2 + 1) / 2) + min 0 (2 - x.1) + min 0 (d - 2 + x.1) +
      max (x.1 + x.2 - 2) 0 +
      (if (x.1 = 1 - d ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∨ (x.1 = 3 ∧ d ≤ x.2 ∧ x.2 ≤ d + 1) ∨
          (x.1 + x.2 = 2 ∧ 0 < x.2 ∧ x.2 < d) then 1 else 0) := by
  unfold paperStairAltValue
  rw [ind_AB]

/-- The forward one tile at `(0,0)`: the alternate odometer is the one-odometer there. -/
theorem fwd_value_one (k : ℕ) (x : GInt) (hx : x ∈ (tileShape ZTile.one).map (· + ((0 : ℤ), (0 : ℤ)))) :
    paperStairAltValue (2 * (k : ℤ) + 3) x = oneOdometer x := by
  rw [mem_shape_one] at hx
  unfold oneAt at hx
  obtain ⟨x1, x2⟩ := x
  simp only at hx ⊢
  rw [value_eq]
  unfold oneOdometer
  simp only [min_def, max_def, Prod.mk.injEq]
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hx1 : x1 = 0 ∨ x1 = 1 := by omega
  have hx2 : x2 = 0 ∨ x2 = 1 := by omega
  rcases hx1 with rfl | rfl <;> rcases hx2 with rfl | rfl <;> split_ifs <;> omega

/-- The forward zero tile at `(2(m+1), 0)`: the alternate odometer is the zero-odometer there. -/
theorem fwd_value_zero (k m : ℕ) (hm : m < k + 1) (x : GInt)
    (hx : x ∈ (tileShape ZTile.zero).map (· + (2 * ((m : ℤ) + 1), (0 : ℤ)))) :
    paperStairAltValue (2 * (k : ℤ) + 3) x = zeroOdometer (x - (2 * ((m : ℤ) + 1), 0)) := by
  rw [mem_shape_zero] at hx
  unfold zeroAt at hx
  obtain ⟨x1, x2⟩ := x
  simp only at hx ⊢
  rw [value_eq]
  unfold zeroOdometer
  simp only [Prod.mk_sub_mk, sub_zero, Prod.mk.injEq, min_def, max_def]
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hx2 : x2 = 0 ∨ x2 = 1 ∨ x2 = 2 := by omega
  rcases hx2 with rfl | rfl | rfl <;> split_ifs <;> omega

/-- The reversed zero tiles `j ≤ k`: the alternate odometer minus the affine part `(1, -(2k+2))` is the zero-odometer plus
the constant `(2k+1)(k+2)`. -/
theorem rev_value_zero (k j : ℕ) (hj : j ≤ k) (x : GInt)
    (hx : x ∈ (tileShape ZTile.zero).map (· + ((revC k).1 + 2 * (j : ℤ), (revC k).2))) :
    paperStairAltValue (2 * (k : ℤ) + 3) x =
      zTileOdo ZTile.zero (x - ((revC k).1 + 2 * (j : ℤ), (revC k).2)) +
        (1 * x.1 + (-(2 * (k : ℤ) + 2)) * x.2) + (2 * (k : ℤ) + 1) * ((k : ℤ) + 2) := by
  rw [mem_shape_zero] at hx
  unfold zeroAt at hx
  obtain ⟨x1, x2⟩ := x
  simp only [revC] at hx ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hjk : (j : ℤ) ≤ (k : ℤ) := by exact_mod_cast hj
  have hx2 : x2 = 2 * (k : ℤ) + 1 ∨ x2 = 2 * (k : ℤ) + 2 ∨ x2 = 2 * (k : ℤ) + 3 := by omega
  rw [value_eq]
  simp only [zTileOdo, zeroOdometer, Prod.mk_sub_mk, Prod.mk.injEq, min_def, max_def]
  rcases hx2 with rfl | rfl | rfl
  · have hq : 2 * ((2 * (k : ℤ) + 1) * (2 * (k : ℤ) + 1 + 1) / 2) = (2 * (k : ℤ) + 1) * (2 * (k : ℤ) + 1 + 1) :=
      Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self _)
    generalize (2 * (k : ℤ) + 1) * (2 * (k : ℤ) + 1 + 1) / 2 = q at hq ⊢
    ring_nf at hq ⊢
    generalize (k : ℤ) ^ 2 = Q at hq ⊢
    try simp only [and_true] at ⊢
    split_ifs <;> omega
  · have hq : 2 * ((2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 2 + 1) / 2) = (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 2 + 1) :=
      Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self _)
    generalize (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 2 + 1) / 2 = q at hq ⊢
    ring_nf at hq ⊢
    generalize (k : ℤ) ^ 2 = Q at hq ⊢
    try simp only [and_true] at ⊢
    split_ifs <;> omega
  · have hq : 2 * ((2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3 + 1) / 2) = (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3 + 1) :=
      Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self _)
    generalize (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3 + 1) / 2 = q at hq ⊢
    ring_nf at hq ⊢
    generalize (k : ℤ) ^ 2 = Q at hq ⊢
    try simp only [and_true] at ⊢
    split_ifs <;> omega

/-- The reversed one tile at `(-2k, 2k+2)`: the alternate odometer minus the affine part `(0, -(2k+2))` is the one-odometer
plus the constant `(2k+1)(k+2) - 2k`. -/
theorem rev_value_one (k : ℕ) (x : GInt)
    (hx : x ∈ (tileShape ZTile.one).map (· + ((revC k).1 + 2 * ((k : ℤ) + 1), (revC k).2 + 1))) :
    paperStairAltValue (2 * (k : ℤ) + 3) x =
      zTileOdo ZTile.one (x - ((revC k).1 + 2 * ((k : ℤ) + 1), (revC k).2 + 1)) +
        (0 * x.1 + (-(2 * (k : ℤ) + 2)) * x.2) + ((2 * (k : ℤ) + 1) * ((k : ℤ) + 2) - 2 * (k : ℤ)) := by
  rw [mem_shape_one] at hx
  unfold oneAt at hx
  obtain ⟨x1, x2⟩ := x
  simp only [revC] at hx ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hx2 : x2 = 2 * (k : ℤ) + 2 ∨ x2 = 2 * (k : ℤ) + 3 := by omega
  rw [value_eq]
  simp only [zTileOdo, oneOdometer, Prod.mk_sub_mk, Prod.mk.injEq, min_def, max_def]
  rcases hx2 with rfl | rfl
  · have hq : 2 * ((2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 2 + 1) / 2) = (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 2 + 1) :=
      Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self _)
    generalize (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 2 + 1) / 2 = q at hq ⊢
    ring_nf at hq ⊢
    generalize (k : ℤ) ^ 2 = Q at hq ⊢
    try simp only [and_true] at ⊢
    split_ifs <;> omega
  · have hq : 2 * ((2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3 + 1) / 2) = (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3 + 1) :=
      Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self _)
    generalize (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3 + 1) / 2 = q at hq ⊢
    ring_nf at hq ⊢
    generalize (k : ℤ) ^ 2 = Q at hq ⊢
    try simp only [and_true] at ⊢
    split_ifs <;> omega

/-! ### 5. The boundary keys -/

/-- Two zero tiles at unit distance: the zero-odometers agree at the corresponding points. -/
theorem key_zz (p p' x y : GInt) (hp1 : p'.1 = p.1 + 2) (hp2 : p'.2 = p.2)
    (hx : zeroAt p x) (hy : zeroAt p' y) (hu : unitApart x y) :
    zeroOdometer (x - p) = zeroOdometer (y - p') := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := p'
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [zeroAt, unitApart, zeroOdometer, Prod.mk_sub_mk, Prod.mk.injEq] at *
  split_ifs <;> omega

/-- A zero tile followed by a one tile one row up. -/
theorem key_zo (p p' x y : GInt) (hp1 : p'.1 = p.1 + 2) (hp2 : p'.2 = p.2 + 1)
    (hx : zeroAt p x) (hy : oneAt p' y) (hu : unitApart x y) :
    zeroOdometer (x - p) = oneOdometer (y - p') - (y - p').1 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := p'
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [zeroAt, oneAt, unitApart, zeroOdometer, oneOdometer, Prod.mk_sub_mk, Prod.mk.injEq] at *
  split_ifs <;> omega

/-- A one tile followed by a zero tile in the same row. -/
theorem key_oz (p p' x y : GInt) (hp1 : p'.1 = p.1 + 2) (hp2 : p'.2 = p.2)
    (hx : oneAt p x) (hy : zeroAt p' y) (hu : unitApart x y) :
    oneOdometer (x - p) = zeroOdometer (y - p') := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := p'
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [zeroAt, oneAt, unitApart, zeroOdometer, oneOdometer, Prod.mk_sub_mk, Prod.mk.injEq] at *
  split_ifs <;> omega

/-! ### 6. The slopes of the two families -/

theorem slope_fam_odo (F : PTFamily) (j : ℕ) (hU : unitSquares (tileShape (F.tile j).1) ≠ []) :
    slopeOf (F.odo j) (F.dom j) =
      slopeOf (zTileOdo (F.tile j).1) (tileShape (F.tile j).1) +
        ((((F.a j).1 : ℤ) : ℚ), (((F.a j).2 : ℤ) : ℚ)) := by
  unfold PTFamily.odo PTFamily.dom
  exact slope_odo_tile _ hU _ _ _

theorem fwd_slope_one (k : ℕ) : slopeOf ((fwdFam k).odo 0) ((fwdFam k).dom 0) = (1 / 2, -1 / 2) := by
  rw [slope_fam_odo _ _ (by rw [fwdFam_tile_zero]; exact unitSquares_one_ne), fwdFam_tile_zero]
  simp [fwdFam, intrinsic_one]

theorem fwd_slope_zero (k m : ℕ) (hm : m < k + 1) :
    slopeOf ((fwdFam k).odo (m + 1)) ((fwdFam k).dom (m + 1)) = (0, -1 / 2) := by
  rw [slope_fam_odo _ _ (by rw [fwdFam_tile_succ k m hm]; exact unitSquares_zero_ne),
    fwdFam_tile_succ k m hm]
  simp [fwdFam, intrinsic_zero]

theorem rev_slope_zero (k j : ℕ) (hj : j ≤ k) :
    slopeOf ((revFam k).odo j) ((revFam k).dom j) = (0, -1 / 2) + (1, -(2 * (k : ℚ) + 2)) := by
  rw [slope_fam_odo _ _ (by rw [revFam_tile_zero k j (by omega)]; exact unitSquares_zero_ne),
    revFam_tile_zero k j (by omega)]
  simp [revFam, hj, intrinsic_zero]

theorem rev_slope_one (k : ℕ) :
    slopeOf ((revFam k).odo (k + 1)) ((revFam k).dom (k + 1)) = (1 / 2, -1 / 2) + (0, -(2 * (k : ℚ) + 2)) := by
  rw [slope_fam_odo _ _ (by rw [revFam_tile_last k]; exact unitSquares_one_ne), revFam_tile_last k]
  simp [revFam, intrinsic_one]

/-! ### 7. The odometers of the two families -/

theorem fwd_a (k j : ℕ) : (fwdFam k).a j = 0 := rfl

theorem fwd_b (k j : ℕ) : (fwdFam k).b j = 0 := rfl

theorem fwd_odo_zero (k : ℕ) (x : GInt) : (fwdFam k).odo 0 x = oneOdometer x := by
  unfold PTFamily.odo
  rw [fwdFam_tile_zero]
  simp [zTileOdo, fwdFam, Prod.mk_zero_zero]

theorem fwd_odo_succ (k m : ℕ) (hm : m < k + 1) (x : GInt) :
    (fwdFam k).odo (m + 1) x = zeroOdometer (x - (2 * ((m : ℤ) + 1), 0)) := by
  unfold PTFamily.odo
  rw [fwdFam_tile_succ k m hm]
  simp [zTileOdo, fwdFam]

theorem rev_a_le (k j : ℕ) (hj : j ≤ k) : (revFam k).a j = ((1 : ℤ), -(2 * (k : ℤ) + 2)) := by
  simp [revFam, hj]

theorem rev_b_le (k j : ℕ) (hj : j ≤ k) : (revFam k).b j = (2 * (k : ℤ) + 1) * ((k : ℤ) + 2) := by
  simp [revFam, hj]

theorem rev_a_gt (k : ℕ) : (revFam k).a (k + 1) = (0, -(2 * (k : ℤ) + 2)) := by
  simp [revFam]

theorem rev_b_gt (k : ℕ) : (revFam k).b (k + 1) = (2 * (k : ℤ) + 1) * ((k : ℤ) + 2) - 2 * (k : ℤ) := by
  simp [revFam]

theorem rev_odo_zero (k j : ℕ) (hj : j ≤ k) (x : GInt) :
    (revFam k).odo j x = zTileOdo ZTile.zero (x - ((revC k).1 + 2 * (j : ℤ), (revC k).2)) + 1 * x.1 +
      (-(2 * (k : ℤ) + 2)) * x.2 + (2 * (k : ℤ) + 1) * ((k : ℤ) + 2) := by
  unfold PTFamily.odo
  rw [revFam_tile_zero k j (by omega), rev_a_le k j hj, rev_b_le k j hj]

theorem rev_odo_last (k : ℕ) (x : GInt) :
    (revFam k).odo (k + 1) x = zTileOdo ZTile.one (x - ((revC k).1 + 2 * ((k : ℤ) + 1), (revC k).2 + 1)) + 0 * x.1 +
      (-(2 * (k : ℤ) + 2)) * x.2 + ((2 * (k : ℤ) + 1) * ((k : ℤ) + 2) - 2 * (k : ℤ)) := by
  unfold PTFamily.odo
  rw [revFam_tile_last k, rev_a_gt k, rev_b_gt k]

/-! ### 8. The respect conditions -/

theorem fwd_respects (k : ℕ) : (fwdFam k).Respects .horizontal false := by
  intro j hj
  rw [fwdFam_n] at hj
  rcases j with _ | m
  · have h0 := fwdFam_tile_zero k
    have h1 := fwdFam_tile_succ k 0 (by omega)
    refine ⟨?_, fun _ x hx y hy hu => ⟨fun _ => ?_, fun h => by cases h⟩⟩
    · rw [fwd_slope_zero k 0 (by omega), fwd_slope_one k, h0, h1]
      norm_num [surgicalSlopeDiff, zTileLetter]
    · simp only [PTFamily.dom, h0] at hx
      rw [mem_shape_one] at hx
      simp only [PTFamily.dom, h1] at hy
      rw [mem_shape_zero] at hy
      rw [fwd_odo_zero, fwd_odo_succ k 0 (by omega)]
      simp only [fwd_a]
      have key := key_oz (0, 0) (2 * (((0 : ℕ) : ℤ) + 1), 0) x y (by simp) (by simp) hx hy hu
      simpa [ptDot, Prod.mk_zero_zero] using key
  · have hm : m < k + 1 := by omega
    have hm' : m + 1 < k + 1 := by omega
    refine ⟨?_, fun _ x hx y hy hu => ⟨fun _ => ?_, fun h => by cases h⟩⟩
    · rw [fwd_slope_zero k (m + 1) hm', fwd_slope_zero k m hm, fwdFam_tile_succ k m hm,
        fwdFam_tile_succ k (m + 1) hm']
      norm_num [surgicalSlopeDiff, zTileLetter, Prod.ext_iff]
    · simp only [PTFamily.dom, fwdFam_tile_succ k m hm] at hx
      rw [mem_shape_zero] at hx
      simp only [PTFamily.dom, fwdFam_tile_succ k (m + 1) hm'] at hy
      rw [mem_shape_zero] at hy
      rw [fwd_odo_succ k m hm, fwd_odo_succ k (m + 1) hm']
      simp only [fwd_a]
      have key := key_zz (2 * ((m : ℤ) + 1), 0) (2 * (((m + 1 : ℕ) : ℤ) + 1), 0) x y
        (by push_cast; ring) (by simp) hx hy hu
      simpa [ptDot] using key

theorem rev_respects (k : ℕ) : (revFam k).Respects .horizontal true := by
  intro j hj
  rw [revFam_n] at hj
  by_cases hjk : j < k
  · have t0 := revFam_tile_zero k j (by omega)
    have t1 := revFam_tile_zero k (j + 1) (by omega)
    refine ⟨?_, fun _ x hx y hy hu => ⟨fun _ => ?_, fun h => by cases h⟩⟩
    · rw [rev_slope_zero k j (by omega), rev_slope_zero k (j + 1) (by omega), t0, t1]
      norm_num [surgicalSlopeDiff, zTileLetter, Prod.ext_iff]
    · simp only [PTFamily.dom, t0] at hx
      rw [mem_shape_zero] at hx
      simp only [PTFamily.dom, t1] at hy
      rw [mem_shape_zero] at hy
      rw [rev_odo_zero k j (by omega), rev_odo_zero k (j + 1) (by omega)]
      have key := key_zz ((revC k).1 + 2 * (j : ℤ), (revC k).2) ((revC k).1 + 2 * ((j + 1 : ℕ) : ℤ), (revC k).2) x y
        (by push_cast; ring) (by simp) hx hy hu
      simp only [ptDot, rev_a_le k j (by omega), zTileOdo]
      linarith [key]
  · have hjk' : j = k := by omega
    have t0 := revFam_tile_zero k j (by omega)
    have t1 : (revFam k).tile (j + 1) = (ZTile.one, ((revC k).1 + 2 * ((k : ℤ) + 1), (revC k).2 + 1)) := by
      rw [hjk']
      exact revFam_tile_last k
    refine ⟨?_, fun _ x hx y hy hu => ⟨fun _ => ?_, fun h => by cases h⟩⟩
    · rw [rev_slope_zero k j (by omega), t0, t1]
      have hs1 : slopeOf ((revFam k).odo (j + 1)) ((revFam k).dom (j + 1)) =
          (1 / 2, -1 / 2) + (0, -(2 * (k : ℚ) + 2)) := by
        rw [hjk']
        exact rev_slope_one k
      rw [hs1]
      norm_num [surgicalSlopeDiff, zTileLetter]
    · simp only [PTFamily.dom, t0] at hx
      rw [mem_shape_zero] at hx
      simp only [PTFamily.dom, t1] at hy
      rw [mem_shape_one] at hy
      rw [hjk'] at hx ⊢
      rw [rev_odo_zero k k le_rfl x, rev_odo_last k y]
      have key := key_zo ((revC k).1 + 2 * (k : ℤ), (revC k).2)
        ((revC k).1 + 2 * ((k : ℤ) + 1), (revC k).2 + 1) x y (by ring) (by simp) hx hy hu
      simp only [Prod.fst_sub] at key
      have hc1 : (revC k).1 = 4 - 2 * (2 * (k : ℤ) + 3) := rfl
      simp only [ptDot, rev_a_le k k le_rfl, zTileOdo]
      linarith [key, hc1]

/-! ### 9. The two `RespectsTiles` instances -/

theorem fwd_agree (k : ℕ) : ∀ j < (fwdFam k).n, ∀ x ∈ (fwdFam k).dom j,
    paperStairAltValue (2 * (k : ℤ) + 3) x = (fwdFam k).odo j x := by
  intro j hj x hx
  rw [fwdFam_n] at hj
  rcases j with _ | m
  · simp only [PTFamily.dom, fwdFam_tile_zero] at hx
    rw [fwd_value_one k x hx, fwd_odo_zero]
  · have hm : m < k + 1 := by omega
    simp only [PTFamily.dom, fwdFam_tile_succ k m hm] at hx
    rw [fwd_value_zero k m hm x hx, fwd_odo_succ k m hm]

theorem rev_agree (k : ℕ) : ∀ j < (revFam k).n, ∀ x ∈ (revFam k).dom j,
    paperStairAltValue (2 * (k : ℤ) + 3) x = (revFam k).odo j x := by
  intro j hj x hx
  rw [revFam_n] at hj
  by_cases hjk : j ≤ k
  · simp only [PTFamily.dom, revFam_tile_zero k j (by omega)] at hx
    rw [rev_value_zero k j hjk x hx, rev_odo_zero k j hjk x]
    ring
  · have hj' : j = k + 1 := by omega
    subst hj'
    simp only [PTFamily.dom, revFam_tile_last k] at hx
    rw [rev_value_one k x hx, rev_odo_last k x]
    ring

theorem altStair_tiles_fwd (k : ℕ) :
    RespectsTiles .horizontal false (hStringAt (stairH k) (0, 0)) (paperStairAltValue (2 * (k : ℤ) + 3)) :=
  ⟨fwdFam k, rfl, fwd_agree k, fwd_respects k⟩

theorem altStair_tiles_rev (k : ℕ) :
    RespectsTiles .horizontal true (hRevStringAt (stairH k).reverse (revC k))
      (paperStairAltValue (2 * (k : ℤ) + 3)) :=
  ⟨revFam k, rfl, rev_agree k, rev_respects k⟩

/-! ### 10. The partial predicate of the alternate staircase (point-set form of `PartialBoundary`) -/

/-- The two strings of the alternate staircase lie in `T̂_{1/d}`, in the form `InsideTile` of `PartialBoundary`. -/
theorem altStair_inside (k : ℕ) :
    InsideTile (paperStairAltTile (2 * (k : ℤ) + 3)) (hPartialTiles (stairH k) (0, 0) (revC k)) :=
  fun x hx => altStair_horizontal_contain k x hx

/-- `T̂_{1/d}` is a partial `w_h`-pseudo-square at the exceptional anchor `c(T̂_{1/d}) = (0,0)` (surgical
`lemma:basecase_3k_even_alt`, Moreover, `w_h = q p^{k+1}`, line 2262). -/
theorem altStair_isPartialHAt (k : ℕ) :
    IsPartialHAt (paperStairAltTile (2 * (k : ℤ) + 3)) (0, 0) (stairH k) :=
  ⟨revC k, altStair_inside k⟩

/-- The alternate odometer `ĝ_{1/d}` respects the partial `w_h`-pseudo-square `T̂_{1/d}` at the anchor `(0,0)`. -/
theorem altStair_respectsPartialHAt (k : ℕ) :
    RespectsPartialHAt (paperStairAltTile (2 * (k : ℤ) + 3)) (0, 0) (stairH k)
      (paperStairAltValue (2 * (k : ℤ) + 3)) :=
  ⟨revC k, altStair_inside k, altStair_tiles_fwd k, altStair_tiles_rev k⟩

end FLatticePaper.Tiles
