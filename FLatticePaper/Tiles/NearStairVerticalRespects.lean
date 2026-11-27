import FLatticePaper.Tiles.LadderVerticalRespects
import FLatticePaper.Construction.NearOneBaseCases

/-! # The vertical half of the Moreover of the alternate near-one staircase (surgical line 2303)

For `d = 2k+3` and the word `w_v = p q^{k+1}`, the tile `T̂_{p_1} = paperNearStairAltTile d` has the reversed vertical string of
`w_v` anchored at its lower-left point `(0,1)`, and the forward vertical string of `w_v` at `(2k+2, 4k+3)`. The forward family has
affine factors `(k,-(k+1))` at the first tile and `(k+j-1,-(k+1+j))` afterwards; the reversed family has `(j,-j)`, constant `j²`.
Both respect their strings by `PTFamily.respects_of_triples`, with letter-determined increments. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Construction (paperNearStairAltA paperNearStairAltB paperNearStairAltC paperNearStairAltD
  paperNearStairAltTile paperNearStairAltValue)

/-- The word `p q^{k+1}`. -/
def pqWord (k : ℕ) : BinaryWord := Letter.p :: List.replicate (k + 1) Letter.q

/-- The reversed word `q^{k+1} p`. -/
def pqRevWord (k : ℕ) : BinaryWord := List.replicate (k + 1) Letter.q ++ [Letter.p]

theorem pqWord_reverse (k : ℕ) : (pqWord k).reverse = pqRevWord k := by
  simp [pqWord, pqRevWord, List.reverse_replicate]

theorem pq_q_list (n : ℕ) (d : GInt) :
    vStringAt (Letter.q :: List.replicate n Letter.q) d =
      (List.range (n + 1)).map (fun j : ℕ => (ZTile.one, (d.1, d.2 + 2 * (j : ℤ)))) := by
  induction n generalizing d with
  | zero => simp [vStringAt, letterZTile]
  | succ n ih =>
    have hr : List.range (n + 1 + 1) = 0 :: List.map Nat.succ (List.range (n + 1)) := by
      rw [List.range_succ_eq_map]
    rw [show Letter.q :: List.replicate (n + 1) Letter.q =
        Letter.q :: Letter.q :: List.replicate n Letter.q from rfl, vStringAt_cons, ih, hr, List.map_cons,
      List.map_map]
    refine List.cons_eq_cons.mpr ⟨by simp [letterZTile], ?_⟩
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, Nat.succ_eq_add_one, vOffset, Prod.mk.injEq, true_and]
    constructor
    · simp
    · simp only [Prod.snd_add]
      push_cast
      ring

theorem pq_fwd_list (m : ℕ) (c : GInt) :
    vStringAt (pqWord m) c =
      (ZTile.zero, c) :: (List.range (m + 1)).map (fun j : ℕ => (ZTile.one, (c.1, c.2 + 2 * (j : ℤ) + 2))) := by
  rw [show pqWord m = Letter.p :: Letter.q :: List.replicate m Letter.q from rfl, vStringAt_cons, pq_q_list]
  refine List.cons_eq_cons.mpr ⟨by simp [letterZTile], ?_⟩
  simp only [List.map_inj_left]
  intro j _
  simp only [vOffset, Prod.mk.injEq, true_and]
  constructor
  · simp
  · simp only [Prod.snd_add]
    ring

theorem pq_rev_list (m : ℕ) (c : GInt) :
    vRevStringAt (List.replicate (m + 1) Letter.q ++ [Letter.p]) c =
      (List.range (m + 1)).map (fun j : ℕ => (ZTile.one, (c.1, c.2 + 2 * (j : ℤ)))) ++
        [(ZTile.zero, (c.1, c.2 + 2 * (m : ℤ) + 1))] := by
  induction m generalizing c with
  | zero =>
    simp [vRevStringAt, vRevOffset, letterZTile, List.scanl_cons]
    ext <;> simp
  | succ m ih =>
    have hr : List.range (m + 1 + 1) = 0 :: List.map Nat.succ (List.range (m + 1)) := by
      rw [List.range_succ_eq_map]
    rw [show List.replicate (m + 1 + 1) Letter.q ++ [Letter.p] =
        Letter.q :: Letter.q :: (List.replicate m Letter.q ++ [Letter.p]) from rfl, vRevStringAt_cons,
      show Letter.q :: (List.replicate m Letter.q ++ [Letter.p]) = List.replicate (m + 1) Letter.q ++ [Letter.p]
        from rfl, ih, hr, List.map_cons, List.cons_append, List.map_map]
    refine List.cons_eq_cons.mpr ⟨by simp [letterZTile], ?_⟩
    congr 1
    · apply List.map_congr_left
      intro j _
      refine congrArg (fun q : GInt => (ZTile.one, q)) (Prod.ext ?_ ?_)
      · simp [vRevOffset]
      · simp only [Nat.succ_eq_add_one, Prod.snd_add, vRevOffset]
        push_cast
        ring
    · refine congrArg (fun q : GInt => [((ZTile.zero : ZTile), q)]) (Prod.ext ?_ ?_)
      · simp [vRevOffset]
      · simp only [Prod.snd_add, vRevOffset]
        push_cast
        ring

/-- The forward affine factors of `pqFwd k`: `(k,-(k+1))` at the first tile, `(k+j-1,-(k+1+j))` after. -/
def pqFa (k j : ℕ) : GInt :=
  if j = 0 then ((k : ℤ), -((k : ℤ) + 1)) else (((k : ℤ) + (j : ℤ) - 1), -((k : ℤ) + 1 + (j : ℤ)))

/-- The forward constants of `pqFwd k`. -/
def pqFb (k j : ℕ) : ℤ :=
  if j = 0 then (k : ℤ) ^ 2 + 2 * (k : ℤ) + 2 else ((j : ℤ) + (k : ℤ)) ^ 2 + 4 * (k : ℤ) + 5

/-- The forward family for `p q^{k+1}`, placed at `(2k+2, 4k+3)`. -/
def pqFwd (k : ℕ) : PTFamily where
  ts := vStringAt (pqWord k) (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 3)
  a := pqFa k
  b := pqFb k

/-- The reversed affine factors `(j,-j)`. -/
def pqRa (j : ℕ) : GInt := ((j : ℤ), -(j : ℤ))

/-- The reversed constants `j²`. -/
def pqRb (j : ℕ) : ℤ := (j : ℤ) ^ 2

/-- The reversed family for `q^{k+1} p`, anchored at `(0,1)`. -/
def pqRev (k : ℕ) : PTFamily where
  ts := vRevStringAt (pqRevWord k) (0, 1)
  a := pqRa
  b := pqRb

theorem pqFwd_n (k : ℕ) : (pqFwd k).n = k + 2 := by
  simp [PTFamily.n, pqFwd, pq_fwd_list]

theorem pqRev_n (k : ℕ) : (pqRev k).n = k + 2 := by
  simp [PTFamily.n, pqRev, pqRevWord, pq_rev_list]

theorem pqFwd_tile_zero (k : ℕ) :
    (pqFwd k).tile 0 = (ZTile.zero, (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 3)) := by
  unfold PTFamily.tile
  show (vStringAt (pqWord k) (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 3)).getD 0 _ = _
  rw [pq_fwd_list]
  simp

theorem pqFwd_tile_succ (k j : ℕ) (hj : j < k + 1) :
    (pqFwd k).tile (j + 1) = (ZTile.one, (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 3 + 2 * ((j : ℤ) + 1))) := by
  unfold PTFamily.tile
  show (vStringAt (pqWord k) (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 3)).getD (j + 1) _ = _
  rw [pq_fwd_list, List.getD_cons_succ, altStair_getD_map_range (k + 1) j _ _ (by omega)]
  simp only [Prod.mk.injEq, true_and]
  ring

theorem pqRev_tile_lt (k j : ℕ) (hj : j < k + 1) :
    (pqRev k).tile j = (ZTile.one, (0, 1 + 2 * (j : ℤ))) := by
  unfold PTFamily.tile
  show (vRevStringAt (pqRevWord k) (0, 1)).getD j _ = _
  rw [show pqRevWord k = List.replicate (k + 1) Letter.q ++ [Letter.p] from rfl, pq_rev_list k (0, 1),
    getD_append_left' _ _ _ _ (by simp; omega), altStair_getD_map_range (k + 1) j _ _ hj]

theorem pqRev_tile_last (k : ℕ) : (pqRev k).tile (k + 1) = (ZTile.zero, (0, 2 * (k : ℤ) + 2)) := by
  unfold PTFamily.tile
  show (vRevStringAt (pqRevWord k) (0, 1)).getD (k + 1) _ = _
  rw [show pqRevWord k = List.replicate (k + 1) Letter.q ++ [Letter.p] from rfl, pq_rev_list k (0, 1),
    List.getD_append_right _ _ _ _ (by simp)]
  simp
  ring

/-! ### The forward family respects the forward vertical string -/

/-- The letter at position `j` of `pqWord k`: `p` first, then `q`. -/
def pqFl (j : ℕ) : Letter := if j = 0 then Letter.p else Letter.q

/-- The predecessor letter: `p` before the first tile, then the letter at `j-1`. -/
def pqPrev (ℓ : ℕ → Letter) (j : ℕ) : Letter := if j = 0 then Letter.p else ℓ (j - 1)

/-- The positions of `pqFwd k`: `(2k+2, 4k+3+2j)`. -/
def pqFP (k j : ℕ) : GInt := (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 3 + 2 * (j : ℤ))

/-- The forward affine increments, keyed by the middle letter: `(0,-1)` on `p`, else `(1,-1)`. -/
def pqFg : Letter → Letter → Letter → GInt
  | _, .p, _ => ((0 : ℤ), (-1 : ℤ))
  | _, _, _ => ((1 : ℤ), (-1 : ℤ))

/-- The forward boundary increments, keyed by the middle letter: `-1` on `p`, else `-2`. -/
def pqFbeta : Letter → Letter → Letter → ℤ
  | _, .p, _ => -1
  | _, _, _ => -2

/-- The forward centred constants `c j = b j + a j · P j`. -/
def pqFc (k j : ℕ) : ℤ := pqFb k j + ptDot (pqFa k j) (pqFP k j)

theorem pqF_hT (k j : ℕ) (hj : j < (pqFwd k).n) :
    (pqFwd k).tile j = (letterZTile (pqFl j), pqFP k j) := by
  rw [pqFwd_n] at hj
  rcases j with _ | j
  · rw [pqFwd_tile_zero]
    simp [pqFl, pqFP, letterZTile]
  · rw [pqFwd_tile_succ k j (by omega)]
    simp only [pqFl, pqFP, letterZTile, if_neg (by omega : j + 1 ≠ 0)]
    push_cast
    ring

theorem pqF_hD (k j : ℕ) : pqFP k (j + 1) = pqFP k j + vOffset (pqFl (j + 1)) := by
  simp only [pqFP, pqFl, if_neg (by omega : j + 1 ≠ 0), vOffset]
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Prod.snd_add]
    push_cast
    ring

theorem pqF_hAa (k j : ℕ) :
    pqFa k (j + 1) = pqFa k j + pqFg (pqPrev pqFl j) (pqFl j) (pqFl (j + 1)) := by
  rcases j with _ | j
  · refine Prod.ext ?_ ?_
    · simp [pqFa, pqFg, pqFl, pqPrev]
    · simp [pqFa, pqFg, pqFl, pqPrev]
      ring
  · refine Prod.ext ?_ ?_
    · simp [pqFa, pqFg, pqFl, pqPrev]
      ring
    · simp [pqFa, pqFg, pqFl, pqPrev]
      ring

theorem pqF_hB (k j : ℕ) : pqFb k j = pqFc k j - ptDot (pqFa k j) (pqFP k j) := by
  simp only [pqFc]
  ring

theorem pqF_hc (k j : ℕ) :
    pqFc k (j + 1) = pqFc k j + pqFbeta (pqPrev pqFl j) (pqFl j) (pqFl (j + 1))
      + ptDot (pqFa k j) (vOffset (pqFl (j + 1))) := by
  rcases j with _ | j
  · simp [pqFc, pqFb, pqFa, pqFP, pqFbeta, pqFl, pqPrev, vOffset, ptDot]
    ring
  · simp [pqFc, pqFb, pqFa, pqFP, pqFbeta, pqFl, pqPrev, vOffset, ptDot]
    ring

/-- The forward boundary check `(p, p, q)`: zero-tile against one-tile, `β + 1 = 0`. -/
theorem pq_bd_fpq : ∀ u ∈ tileShape (letterZTile Letter.p), ∀ v ∈ tileShape (letterZTile Letter.q),
    (∀ u' ∈ tileShape (letterZTile Letter.p), ∀ v' ∈ tileShape (letterZTile Letter.q), u' - v' ≠ vOffset Letter.q) →
    (u - v - vOffset Letter.q).1.natAbs + (u - v - vOffset Letter.q).2.natAbs = 1 →
    zTileOdo (letterZTile Letter.p) u - zTileOdo (letterZTile Letter.q) v - ptDot ((0 : ℤ), (-1 : ℤ)) v = -1 + 1 := by
  decide

/-- The forward boundary check `(·, q, q)`: one-tile against one-tile, `β + 1 = -1`. -/
theorem pq_bd_fqq : ∀ u ∈ tileShape (letterZTile Letter.q), ∀ v ∈ tileShape (letterZTile Letter.q),
    (∀ u' ∈ tileShape (letterZTile Letter.q), ∀ v' ∈ tileShape (letterZTile Letter.q) , u' - v' ≠ vOffset Letter.q) →
    (u - v - vOffset Letter.q).1.natAbs + (u - v - vOffset Letter.q).2.natAbs = 1 →
    zTileOdo (letterZTile Letter.q) u - zTileOdo (letterZTile Letter.q) v - ptDot ((1 : ℤ), (-1 : ℤ)) v = -2 + 1 := by
  decide

theorem pqFwd_respects (k : ℕ) : (pqFwd k).Respects .vertical false :=
  PTFamily.respects_of_triples (pqFwd k) .vertical false pqFl (pqPrev pqFl) (pqFP k)
    (fun _ y => letterZTile y) (fun _ z => vOffset z) pqFg (pqFc k) pqFbeta (fun _ _ z => z = Letter.q)
    (fun j hj => pqF_hT k j hj)
    (fun j _ => by
      show (if j + 1 = 0 then Letter.p else pqFl (j + 1 - 1)) = pqFl j
      simp)
    (fun j _ => pqF_hD k j)
    (fun j _ => pqF_hAa k j)
    (fun j _ => pqF_hB k j)
    (fun j _ => pqF_hc k j)
    (fun j _ => by simp [pqFl])
    (fun _ y => zTileLetter_letterZTile y)
    (fun x y z hA => by
      subst hA
      cases y <;> norm_num [slope_base_p, slope_base_q, surgicalSlopeDiff, pqFg])
    (fun h => by cases h)
    (fun _ x y z hA u hu v hv hno hunit => by
      subst hA
      cases y
      · exact pq_bd_fpq u hu v hv hno hunit
      · exact pq_bd_fqq u hu v hv hno hunit)

/-! ### The reversed family respects the reversed vertical string -/

/-- The letter at position `j` of `pqRevWord k`: `q` up to `k`, then `p`. -/
def pqRl (k j : ℕ) : Letter := if j = k + 1 then Letter.p else Letter.q

/-- The positions of `pqRev k`: `(0,1+2j)` up to `k`, then `(0,2k+2)`. -/
def pqRP (k j : ℕ) : GInt := if j = k + 1 then (0, 2 * (k : ℤ) + 2) else (0, 1 + 2 * (j : ℤ))

/-- The reversed affine increment `(1,-1)`. -/
def pqRg : Letter → Letter → Letter → GInt := fun _ _ _ => ((1 : ℤ), (-1 : ℤ))

/-- The reversed boundary increments, keyed by the last letter: `-1` on `p`, else `-2`. -/
def pqRbeta : Letter → Letter → Letter → ℤ
  | _, _, .p => -1
  | _, _, _ => -2

/-- The reversed centred constants `c j = b j + a j · P j`. -/
def pqRc (k j : ℕ) : ℤ := pqRb j + ptDot (pqRa j) (pqRP k j)

theorem pqR_hT (k j : ℕ) (hj : j < (pqRev k).n) :
    (pqRev k).tile j = (letterZTile (pqRl k j), pqRP k j) := by
  rw [pqRev_n] at hj
  by_cases h : j = k + 1
  · subst h
    rw [pqRev_tile_last k]
    simp [pqRl, pqRP, letterZTile]
  · rw [pqRev_tile_lt k j (by omega)]
    simp [pqRl, pqRP, letterZTile, h]

theorem pqR_hD (k j : ℕ) (hj : j + 1 < k + 2) :
    pqRP k (j + 1) = pqRP k j + vRevOffset (pqRl k j) (pqRl k (j + 1)) := by
  by_cases h : j = k
  · subst h
    simp [pqRP, pqRl, vRevOffset]
    ring
  · have h1 : j + 1 ≠ k + 1 := by omega
    have h2 : j ≠ k + 1 := by omega
    simp only [pqRP, pqRl, if_neg h1, if_neg h2, vRevOffset]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add]
      push_cast
      ring

theorem pqR_hAa (k j : ℕ) :
    pqRa (j + 1) = pqRa j + pqRg (pqPrev (pqRl k) j) (pqRl k j) (pqRl k (j + 1)) := by
  refine Prod.ext ?_ ?_
  · simp only [pqRa, pqRg, Prod.fst_add]
    push_cast
    ring
  · simp only [pqRa, pqRg, Prod.snd_add]
    push_cast
    ring

theorem pqR_hB (k j : ℕ) :
    (pqRev k).b j = pqRc k j - ptDot ((pqRev k).a j) (pqRP k j) := by
  show pqRb j = pqRc k j - ptDot (pqRa j) (pqRP k j)
  simp only [pqRc]
  ring

theorem pqR_hc (k j : ℕ) (hj : j + 1 < k + 2) :
    pqRc k (j + 1) = pqRc k j + pqRbeta (pqPrev (pqRl k) j) (pqRl k j) (pqRl k (j + 1))
      + ptDot (pqRa j) (vRevOffset (pqRl k j) (pqRl k (j + 1))) := by
  by_cases h : j = k
  · subst h
    simp [pqRc, pqRb, pqRa, pqRP, pqRl, pqRbeta, vRevOffset, ptDot]
    ring
  · have h1 : j + 1 ≠ k + 1 := by omega
    have h2 : j ≠ k + 1 := by omega
    simp [pqRc, pqRb, pqRa, pqRP, pqRl, pqRbeta, vRevOffset, ptDot, h, h2]
    ring

theorem pqR_hAdm (k j : ℕ) (hj : j + 1 < k + 2) : pqRl k j = Letter.q := by
  have h : j ≠ k + 1 := by omega
  simp [pqRl, h]

/-- The reversed boundary check `(·, q, p)`: one-tile against zero-tile, `β + 1 = 0`. -/
theorem pq_bd_rqp : ∀ u ∈ tileShape (letterZTile Letter.q), ∀ v ∈ tileShape (letterZTile Letter.p),
    (∀ u' ∈ tileShape (letterZTile Letter.q), ∀ v' ∈ tileShape (letterZTile Letter.p),
      u' - v' ≠ vRevOffset Letter.q Letter.p) →
    (u - v - vRevOffset Letter.q Letter.p).1.natAbs + (u - v - vRevOffset Letter.q Letter.p).2.natAbs = 1 →
    zTileOdo (letterZTile Letter.q) u - zTileOdo (letterZTile Letter.p) v - ptDot ((1 : ℤ), (-1 : ℤ)) v = -1 + 1 := by
  decide

/-- The reversed boundary check `(·, q, q)`: one-tile against one-tile, `β + 1 = -1`. -/
theorem pq_bd_rqq : ∀ u ∈ tileShape (letterZTile Letter.q), ∀ v ∈ tileShape (letterZTile Letter.q),
    (∀ u' ∈ tileShape (letterZTile Letter.q), ∀ v' ∈ tileShape (letterZTile Letter.q),
      u' - v' ≠ vRevOffset Letter.q Letter.q) →
    (u - v - vRevOffset Letter.q Letter.q).1.natAbs + (u - v - vRevOffset Letter.q Letter.q).2.natAbs = 1 →
    zTileOdo (letterZTile Letter.q) u - zTileOdo (letterZTile Letter.q) v - ptDot ((1 : ℤ), (-1 : ℤ)) v = -2 + 1 := by
  decide

theorem pqRev_respects (k : ℕ) : (pqRev k).Respects .vertical true :=
  PTFamily.respects_of_triples (pqRev k) .vertical true (pqRl k) (pqPrev (pqRl k)) (pqRP k)
    (fun _ y => letterZTile y) (fun y z => vRevOffset y z) pqRg (pqRc k) pqRbeta
    (fun _ y _ => y = Letter.q)
    (fun j hj => pqR_hT k j hj)
    (fun j _ => by
      show (if j + 1 = 0 then Letter.p else pqRl k (j + 1 - 1)) = pqRl k j
      simp)
    (fun j hj => pqR_hD k j (by rw [pqRev_n] at hj; exact hj))
    (fun j _ => pqR_hAa k j)
    (fun j _ => pqR_hB k j)
    (fun j hj => pqR_hc k j (by rw [pqRev_n] at hj; exact hj))
    (fun j hj => pqR_hAdm k j (by rw [pqRev_n] at hj; exact hj))
    (fun _ y => zTileLetter_letterZTile y)
    (fun x y z hA => by
      subst hA
      cases z <;> norm_num [slope_base_p, slope_base_q, surgicalSlopeDiff, pqRg])
    (fun h => by cases h)
    (fun _ x y z hA u hu v hv hno hunit => by
      subst hA
      cases z
      · exact pq_bd_rqp u hu v hv hno hunit
      · exact pq_bd_rqq u hu v hv hno hunit)

/-! ### The tile, its lower-left point and the containment of the placed strings -/

theorem pq_mem_AB (d : ℤ) (x : GInt) :
    x ∈ paperNearStairAltA d ∪ paperNearStairAltB d ↔
      ((-1 ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = 2 * d) ∨ (d ≤ x.1 ∧ x.1 ≤ d + 1 ∧ x.2 = d - 2)) ∨
        (x.2 - x.1 = d - 1 ∧ 0 < x.1 ∧ x.1 < d) := by
  unfold paperNearStairAltA paperNearStairAltB
  simp only [Set.mem_union, Set.mem_setOf_eq, or_assoc]

theorem pq_mem_tile (d : ℤ) (x : GInt) :
    x ∈ paperNearStairAltTile d ↔
      ((((-1 ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = 2 * d) ∨ (d ≤ x.1 ∧ x.1 ≤ d + 1 ∧ x.2 = d - 2)) ∨
          (x.2 - x.1 = d - 1 ∧ 0 < x.1 ∧ x.1 < d)) ∨
        ((x.1 = -1 ∧ d + 1 ≤ x.2 ∧ x.2 ≤ 2 * d) ∨ (x.1 = d + 1 ∧ d - 2 ≤ x.2 ∧ x.2 ≤ 2 * d - 3))) ∨
      (0 ≤ x.1 ∧ x.1 ≤ d ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 3 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d - 1) := by
  unfold paperNearStairAltTile paperNearStairAltA paperNearStairAltB paperNearStairAltC paperNearStairAltD
  simp only [Set.mem_union, Set.mem_setOf_eq, or_assoc]

theorem pq_lowerLeft (k : ℕ) : IsLowerLeftPt (paperNearStairAltTile (2 * (k : ℤ) + 3)) (0, 1) := by
  refine ⟨?_, ?_⟩
  · rw [pq_mem_tile]
    dsimp only
    omega
  · intro x hx
    rw [pq_mem_tile] at hx
    unfold lowerLexLe
    dsimp only
    omega

theorem pq_inside (k : ℕ) :
    InsideTile (paperNearStairAltTile (2 * (k : ℤ) + 3))
      (vPartialTiles (pqWord k) (0, 1) (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 3)) := by
  apply inside_of_tiles
  intro tp htp y hy
  simp only [vPartialTiles, List.mem_append] at htp
  rcases htp with htp | htp
  · rw [pqWord_reverse, show pqRevWord k = List.replicate (k + 1) Letter.q ++ [Letter.p] from rfl,
      pq_rev_list k (0, 1)] at htp
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at htp
    rcases htp with ⟨j, hj, rfl⟩ | rfl
    · dsimp only at hy
      rw [mem_shape_one] at hy
      unfold oneAt at hy
      rw [pq_mem_tile]
      omega
    · dsimp only at hy
      rw [mem_shape_zero] at hy
      unfold zeroAt at hy
      rw [pq_mem_tile]
      omega
  · rw [pq_fwd_list] at htp
    simp only [List.mem_cons, List.mem_map, List.mem_range] at htp
    rcases htp with rfl | ⟨j, hj, rfl⟩
    · dsimp only at hy
      rw [mem_shape_zero] at hy
      unfold zeroAt at hy
      rw [pq_mem_tile]
      omega
    · dsimp only at hy
      rw [mem_shape_one] at hy
      unfold oneAt at hy
      rw [pq_mem_tile]
      omega

/-! ### Agreement of the odometers with the value on the tile points -/

theorem pq_ind (d : ℤ) (x : GInt) :
    (paperNearStairAltA d ∪ paperNearStairAltB d).indicator (fun _ => (1 : ℤ)) x =
      if ((-1 ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = 2 * d) ∨ (d ≤ x.1 ∧ x.1 ≤ d + 1 ∧ x.2 = d - 2)) ∨
          (x.2 - x.1 = d - 1 ∧ 0 < x.1 ∧ x.1 < d) then (1 : ℤ) else 0 := by
  classical
  rw [Set.indicator_apply]
  simp only [pq_mem_AB]

theorem pq_fwd_zero_agree (k : ℕ) (x : GInt)
    (hx : x ∈ (tileShape ZTile.zero).map (· + (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 3))) :
    paperNearStairAltValue (2 * (k : ℤ) + 3) x =
      zTileOdo ZTile.zero (x - (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 3)) + (pqFa k 0).1 * x.1 + (pqFa k 0).2 * x.2
        + pqFb k 0 := by
  obtain ⟨x1, x2⟩ := x
  rw [mem_shape_zero] at hx
  unfold zeroAt at hx
  dsimp only at hx
  have hx1 : x1 = 2 * (k : ℤ) + 2 ∨ x1 = 2 * (k : ℤ) + 3 := by omega
  have hx2 : x2 = 4 * (k : ℤ) + 3 ∨ x2 = 4 * (k : ℤ) + 4 ∨ x2 = 4 * (k : ℤ) + 5 := by omega
  rcases hx1 with rfl | rfl <;> rcases hx2 with rfl | rfl | rfl <;>
    (unfold paperNearStairAltValue
     simp only [pqFa, pqFb, zTileOdo, zeroOdometer, pq_ind, min_def, max_def,
       Prod.mk_sub_mk, Prod.mk.injEq, ↓reduceIte]
     ring_nf
     (try norm_num [zeroOdometer, oneOdometer])
     (try generalize (k : ℤ) ^ 2 = K2)
     split_ifs <;> omega)

theorem pq_fwd_one_agree (k j : ℕ) (hj : j < k + 1) (x : GInt)
    (hx : x ∈ (tileShape ZTile.one).map (· + (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 3 + 2 * ((j : ℤ) + 1)))) :
    paperNearStairAltValue (2 * (k : ℤ) + 3) x =
      zTileOdo ZTile.one (x - (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 3 + 2 * ((j : ℤ) + 1)))
        + (pqFa k (j + 1)).1 * x.1 + (pqFa k (j + 1)).2 * x.2 + pqFb k (j + 1) := by
  obtain ⟨x1, x2⟩ := x
  rw [mem_shape_one] at hx
  unfold oneAt at hx
  dsimp only at hx
  have hx1 : x1 = 2 * (k : ℤ) + 2 ∨ x1 = 2 * (k : ℤ) + 3 := by omega
  have hx2 : x2 = 4 * (k : ℤ) + 3 + 2 * ((j : ℤ) + 1) ∨ x2 = 4 * (k : ℤ) + 3 + 2 * ((j : ℤ) + 1) + 1 := by
    omega
  rcases hx1 with rfl | rfl <;> rcases hx2 with rfl | rfl <;>
    (unfold paperNearStairAltValue
     simp only [pqFa, pqFb, zTileOdo, oneOdometer, pq_ind, min_def, max_def,
       Prod.mk_sub_mk, Prod.mk.injEq, Nat.add_one_ne_zero, Nat.cast_add, Nat.cast_one, ↓reduceIte]
     ring_nf
     (try norm_num [zeroOdometer, oneOdometer])
     (try generalize (k : ℤ) ^ 2 = K2)
     (try generalize (j : ℤ) ^ 2 = J2)
     (try generalize (k : ℤ) * (j : ℤ) = KJ1)
     (try generalize (j : ℤ) * (k : ℤ) = KJ2)
     split_ifs <;> omega)

theorem pq_rev_one_agree (k j : ℕ) (hj : j < k + 1) (x : GInt)
    (hx : x ∈ (tileShape ZTile.one).map (· + (0, 1 + 2 * (j : ℤ)))) :
    paperNearStairAltValue (2 * (k : ℤ) + 3) x =
      zTileOdo ZTile.one (x - (0, 1 + 2 * (j : ℤ))) + (pqRa j).1 * x.1 + (pqRa j).2 * x.2 + pqRb j := by
  obtain ⟨x1, x2⟩ := x
  rw [mem_shape_one] at hx
  unfold oneAt at hx
  dsimp only at hx
  have hx1 : x1 = 0 ∨ x1 = 1 := by omega
  have hx2 : x2 = 1 + 2 * (j : ℤ) ∨ x2 = 2 + 2 * (j : ℤ) := by omega
  rcases hx1 with rfl | rfl <;> rcases hx2 with rfl | rfl <;>
    (unfold paperNearStairAltValue
     simp only [pqRa, pqRb, zTileOdo, oneOdometer, pq_ind, min_def, max_def,
       Prod.mk_sub_mk, Prod.mk.injEq]
     ring_nf
     (try norm_num [zeroOdometer, oneOdometer])
     (try generalize (k : ℤ) ^ 2 = K2)
     (try generalize (j : ℤ) ^ 2 = J2)
     (try generalize (k : ℤ) * (j : ℤ) = KJ1)
     (try generalize (j : ℤ) * (k : ℤ) = KJ2)
     split_ifs <;> omega)

theorem pq_rev_zero_agree (k : ℕ) (x : GInt)
    (hx : x ∈ (tileShape ZTile.zero).map (· + (0, 2 * (k : ℤ) + 2))) :
    paperNearStairAltValue (2 * (k : ℤ) + 3) x =
      zTileOdo ZTile.zero (x - (0, 2 * (k : ℤ) + 2)) + (pqRa (k + 1)).1 * x.1 + (pqRa (k + 1)).2 * x.2
        + pqRb (k + 1) := by
  obtain ⟨x1, x2⟩ := x
  rw [mem_shape_zero] at hx
  unfold zeroAt at hx
  dsimp only at hx
  have hx1 : x1 = 0 ∨ x1 = 1 := by omega
  have hx2 : x2 = 2 * (k : ℤ) + 2 ∨ x2 = 2 * (k : ℤ) + 3 ∨ x2 = 2 * (k : ℤ) + 4 := by omega
  rcases hx1 with rfl | rfl <;> rcases hx2 with rfl | rfl | rfl <;>
    (unfold paperNearStairAltValue
     simp only [pqRa, pqRb, zTileOdo, zeroOdometer, pq_ind, min_def, max_def,
       Prod.mk_sub_mk, Prod.mk.injEq, Nat.cast_add, Nat.cast_one]
     ring_nf
     (try norm_num [zeroOdometer, oneOdometer])
     (try generalize (k : ℤ) ^ 2 = K2)
     split_ifs <;> omega)

theorem pq_fwd_agree (k : ℕ) : ∀ j < (pqFwd k).n, ∀ x ∈ (pqFwd k).dom j,
    paperNearStairAltValue (2 * (k : ℤ) + 3) x = (pqFwd k).odo j x := by
  intro j hj x hx
  rw [pqFwd_n] at hj
  rcases j with _ | j
  · unfold PTFamily.dom at hx
    rw [pqFwd_tile_zero] at hx
    dsimp only at hx
    unfold PTFamily.odo
    rw [pqFwd_tile_zero]
    exact pq_fwd_zero_agree k x hx
  · unfold PTFamily.dom at hx
    rw [pqFwd_tile_succ k j (by omega)] at hx
    dsimp only at hx
    unfold PTFamily.odo
    rw [pqFwd_tile_succ k j (by omega)]
    exact pq_fwd_one_agree k j (by omega) x hx

theorem pq_rev_agree (k : ℕ) : ∀ j < (pqRev k).n, ∀ x ∈ (pqRev k).dom j,
    paperNearStairAltValue (2 * (k : ℤ) + 3) x = (pqRev k).odo j x := by
  intro j hj x hx
  rw [pqRev_n] at hj
  by_cases h : j < k + 1
  · unfold PTFamily.dom at hx
    rw [pqRev_tile_lt k j h] at hx
    dsimp only at hx
    unfold PTFamily.odo
    rw [pqRev_tile_lt k j h]
    exact pq_rev_one_agree k j h x hx
  · have hj' : j = k + 1 := by omega
    subst hj'
    unfold PTFamily.dom at hx
    rw [pqRev_tile_last k] at hx
    dsimp only at hx
    unfold PTFamily.odo
    rw [pqRev_tile_last k]
    exact pq_rev_zero_agree k x hx

/-- The vertical respect of `paperNearStairAltValue (2k+3)` on `T̂_{p_1}` for the word `w_v = p q^{k+1}` (2303):
the reversed string anchored at the lower-left point `(0,1)` and the forward string at `(2k+2,4k+3)`. -/
theorem pq_respectsPartialV (k : ℕ) :
    RespectsPartialV (paperNearStairAltTile (2 * (k : ℤ) + 3)) (pqWord k) (paperNearStairAltValue (2 * (k : ℤ) + 3)) :=
  ⟨(0, 1), pq_lowerLeft k, (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 3), pq_inside k,
    ⟨pqRev k, by rw [pqWord_reverse]; rfl, pq_rev_agree k, pqRev_respects k⟩,
    ⟨pqFwd k, rfl, pq_fwd_agree k, pqFwd_respects k⟩⟩

end FLatticePaper.Tiles
