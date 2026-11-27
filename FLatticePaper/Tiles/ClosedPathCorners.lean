import FLatticePaper.Tiles.SurgicalCornerThird
import FLatticePaper.Tiles.ReversedTopShift

/-! # Condition (C): the corner values of a parent odometer

The closed-path computation of condition (C) reads each offset constant at one point of two corner tiles. It uses, for each
parent odometer `S` on a standard tile with vectors `X = v_{n/d,1}`, `Y = v_{n/d,2}` and second affine factor
`e = a_{n/d,2} = (n, -d)`, four differences of values on the corner tiles (table (1) of
`notes/C/C_other_proof_all_cases.md`): with `D_T = X + Y + 1 - i` and `σ` the affine factor of the first bottom tile,

`S(1) - S(0) = σ_x`, `S(X) - S(X - i) = σ_y`, `S(Y + 1) - S(Y + 1 - i) = σ_y + e_y`, `S(D_T) - S(D_T - 1) = σ_x + e_x`.

Only the two combinations without `σ` enter the closed path, and they are what `corner_diffs` proves:

* `S(D_T) - S(D_T - 1) - (S(1) - S(0)) = n`;
* `S(Y + 1) - S(Y + 1 - i) - (S(X) - S(X - i)) = -d`.

The inputs are the two horizontal respects of `RespectsAnchored` and the corner identities of
`lemma:weak_standard_odometer_properties` (b) in affine factors (`CornerAffineStatement`, proved for one odometer from its
respects by `corner_affine_12` and `corner_third`). The corner tiles are the first and last tiles of the bottom string
(`T_{1/1}` at `0`, `T_{0/1}` at `X - 1 - i`) and of the top string (`T_{0/1}` at `Y + 1 - 2i`, a one tile at `D_T - 1 - i`).
The position of the last top tile is `hRev_lastPos_reverse`: the offsets of a reversed horizontal string telescope to those of
the forward string plus `i`. -/

namespace FLatticePaper.Tiles.ClosedPathCorners

open FLatticePaper.Tiles FLatticePaper.Construction

/-! ### The last position of a string -/

/-- The last position of a tile list built from a start point and a list of steps is the start point plus the sum of the
steps. -/
theorem lastPos_zip_scanl : ∀ (L : List GInt) (ts : List ZTile) (c : GInt), ts.length = L.length + 1 →
    lastPosOf (ts.zip (List.scanl (· + ·) c L)) = c + L.sum
  | [], ts, c, h => by
    cases ts with
    | nil => simp at h
    | cons t ts' =>
      cases ts' with
      | nil => simp [lastPosOf]
      | cons _ _ => simp at h
  | x :: L, ts, c, h => by
    cases ts with
    | nil => simp at h
    | cons t ts' =>
      have hl : ts'.length = L.length + 1 := by simp at h; omega
      have hne : ts'.zip (List.scanl (· + ·) (c + x) L) ≠ [] := by
        intro he
        have h2 := congrArg List.length he
        simp only [List.length_zip, List.length_scanl, List.length_nil] at h2
        omega
      rw [List.scanl_cons, List.zip_cons_cons, lastPosOf_cons_ne _ _ hne, lastPos_zip_scanl L ts' (c + x) hl]
      simp [List.sum_cons, add_assoc]

/-- The shift `δ(q) = i`, `δ(p) = 0`: a reversed horizontal step is the forward step of its first letter, corrected by `δ`. -/
def revShift : Letter → GInt
  | .p => 0
  | .q => (0, 1)

theorem hRevOffset_eq (a b : Letter) : hRevOffset a b + revShift a = hOffset a + revShift b := by
  cases a <;> cases b <;> ext <;> simp [hRevOffset, hOffset, revShift]

/-- The steps of a reversed horizontal string telescope: their sum plus `δ` of the first letter is the sum of the forward
steps of all letters but the last, plus `δ` of the last letter. -/
theorem hRev_pair_sum : ∀ (u : BinaryWord) (a l : Letter), (a :: u).getLast? = some l →
    (((a :: u).zip u).map fun ab => hRevOffset ab.1 ab.2).sum + revShift a =
      (((a :: u).dropLast).map hOffset).sum + revShift l
  | [], a, l, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    simp
  | b :: u, a, l, h => by
    have h' : (b :: u).getLast? = some l := by
      rw [List.getLast?_cons_cons] at h
      exact h
    have ih := hRev_pair_sum u b l h'
    have e := hRevOffset_eq a b
    have hd : (a :: b :: u).dropLast = a :: (b :: u).dropLast := rfl
    rw [hd, List.zip_cons_cons, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    have i1 := congrArg Prod.fst ih
    have i2 := congrArg Prod.snd ih
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [Prod.fst_add, Prod.snd_add] at i1 i2 e1 e2
    ext
    · simp only [Prod.fst_add]
      linarith
    · simp only [Prod.snd_add]
      linarith

/-- The length of a forward horizontal string. -/
theorem hStringAt_length' (w : BinaryWord) (c : GInt) : (hStringAt w c).length = w.length := by
  unfold hStringAt
  simp only [List.length_zip, tileSeq, tileSeqAux_length_sac, List.length_scanl, List.length_map, List.length_tail]
  omega

/-- The first coordinates of the forward horizontal string are its doubled tile sequence. -/
theorem hStringAt_map_fst (w : BinaryWord) (c : GInt) : (hStringAt w c).map Prod.fst = tileSeq w := by
  unfold hStringAt
  apply List.map_fst_zip
  simp only [tileSeq, tileSeqAux_length_sac, List.length_map, List.length_scanl, List.length_tail]
  omega

theorem getD_fst_of_map (L : List (ZTile × GInt)) (T : List ZTile) (h : L.map Prod.fst = T) (i : ℕ) :
    (L.getD i (ZTile.zero, (0 : GInt))).1 = T.getD i ZTile.zero := by
  rw [← h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  generalize L[i]? = o
  cases o <;> simp

/-- The last position of the forward horizontal string of a nonempty word: its start plus the steps of the tail. -/
theorem hFwd_lastPos (wh : BinaryWord) (c : GInt) (hne : wh ≠ []) :
    lastPosOf (hStringAt wh c) = c + (wh.tail.map hOffset).sum := by
  unfold hStringAt
  apply lastPos_zip_scanl
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp [tileSeq, tileSeqAux_length_sac]

/-- **The last top tile.** For a horizontal word from `q` to `p`, the last position of the reversed horizontal string of the
reversed word from `c` is `c` plus the last position of the forward string from `0` plus `i`. -/
theorem hRev_lastPos_reverse (wh : BinaryWord) (c : GInt) (hhead : wh.head? = some .q)
    (hlast : wh.getLast? = some .p) :
    lastPosOf (hRevStringAt wh.reverse c) = c + lastPosOf (hStringAt wh 0) + (0, 1) := by
  have hne : wh ≠ [] := by
    rintro rfl
    simp at hhead
  obtain ⟨t, hwt⟩ : ∃ t, wh = Letter.q :: t := by
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.head?_cons, Option.some.injEq] at hhead
    exact ⟨t, by rw [hhead]⟩
  obtain ⟨s, hs⟩ : ∃ s, wh.reverse = Letter.p :: s := by
    have hr : wh.reverse ≠ [] := by simpa using hne
    obtain ⟨a, s, hs⟩ := List.exists_cons_of_ne_nil hr
    have h1 : wh.reverse.head? = some .p := by rw [List.head?_reverse]; exact hlast
    rw [hs] at h1
    simp only [List.head?_cons, Option.some.injEq] at h1
    exact ⟨s, by rw [hs, h1]⟩
  have hsum : lastPosOf (hRevStringAt wh.reverse c) =
      c + (((wh.reverse).zip (wh.reverse).tail).map fun ab => hRevOffset ab.1 ab.2).sum := by
    unfold hRevStringAt
    apply lastPos_zip_scanl
    rw [hs]
    simp [tileSeq, tileSeqAux_length_sac]
  have hs' : Letter.p :: s = t.reverse ++ [Letter.q] := by rw [← hs, hwt, List.reverse_cons]
  have hdl : (Letter.p :: s).dropLast = t.reverse := by rw [hs', List.dropLast_concat]
  have hgl : (Letter.p :: s).getLast? = some Letter.q := by rw [hs', List.getLast?_concat]
  have hps := hRev_pair_sum s Letter.p Letter.q hgl
  rw [hdl, List.map_reverse, List.sum_reverse] at hps
  simp only [revShift, add_zero] at hps
  rw [hsum, hs, List.tail_cons, hps, hFwd_lastPos wh 0 hne, hwt, List.tail_cons]
  abel

/-! ### Values on a tile of a family -/

/-- On the `k`-th tile of a family witness of `S`, the difference of two values of `S` is the difference of the base odometer
plus the affine factor of the tile. -/
theorem tile_val_diff (F : PTFamily) (S : GInt → ℤ) (k : ℕ) (hk : k < F.n)
    (hS : ∀ k < F.n, ∀ x ∈ F.dom k, S x = F.odo k x) (u v : GInt)
    (hu : u ∈ tileShape (F.tile k).1) (hv : v ∈ tileShape (F.tile k).1) :
    S ((F.tile k).2 + u) - S ((F.tile k).2 + v) =
      zTileOdo (F.tile k).1 u - zTileOdo (F.tile k).1 v + (F.a k).1 * (u.1 - v.1) + (F.a k).2 * (u.2 - v.2) := by
  have mem : ∀ x ∈ tileShape (F.tile k).1, (F.tile k).2 + x ∈ F.dom k := by
    intro x hx
    unfold PTFamily.dom
    rw [chain_mem_map_add_iff]
    simpa using hx
  rw [hS k hk _ (mem u hu), hS k hk _ (mem v hv)]
  unfold PTFamily.odo
  simp only [add_sub_cancel_left, Prod.fst_add, Prod.snd_add]
  ring

/-- A letter `p` of a word gives the zero tile in the doubled tile sequence. -/
theorem tileSeqAux_getD_p (xs : BinaryWord) : ∀ (prev : Option Letter) (k : ℕ), k < xs.length →
    xs.getD k Letter.p = Letter.p → (tileSeqAux prev xs).getD k ZTile.zero = ZTile.zero := by
  induction xs with
  | nil => intro prev k hk; simp at hk
  | cons y ys ih =>
    intro prev k hk hp
    cases k with
    | zero =>
      have hy : y = Letter.p := by simpa using hp
      subst hy
      rfl
    | succ k =>
      have hk' : k < ys.length := by simp at hk; omega
      have hp' : ys.getD k Letter.p = Letter.p := by simpa using hp
      simpa [tileSeqAux] using ih (some y) k hk' hp'

/-- The value form of `tile_val_diff` with the affine factor of the tile (`tileAffine`), for a tile `t` of the family. -/
theorem val_diff (F : PTFamily) (S : GInt → ℤ) (k : ℕ) (hk : k < F.n)
    (hS : ∀ k < F.n, ∀ x ∈ F.dom k, S x = F.odo k x) (t : ZTile × GInt) (ht : F.tile k = t) (u v : GInt)
    (hu : u ∈ tileShape t.1) (hv : v ∈ tileShape t.1) :
    ((S (t.2 + u) - S (t.2 + v) : ℤ) : ℚ) = ((zTileOdo t.1 u - zTileOdo t.1 v : ℤ) : ℚ) +
      (tileAffine S t).1 * ((u.1 - v.1 : ℤ) : ℚ) + (tileAffine S t).2 * ((u.2 - v.2 : ℤ) : ℚ) := by
  subst ht
  rw [tile_val_diff F S k hk hS u v hu hv,
    tileAffine_family F S k (hS k hk) (unitSquares_tileShape_ne _)]
  push_cast
  ring

/-! ### The corner differences -/

/-- **The two corner differences of a parent odometer** (table (1) of the closed-path computation, without `σ`). For a
horizontal word `wh` from `q` to `p` and a vertical word `wv`, an odometer `S` respecting the bottom string and the anchored top
string, with the corner identities of (b) for `(n, d)`, and with the corner positions `X - 1 - i` (last bottom tile) and
`Y + 1 - 2i` (first top tile):

* `S(X + Y + 1 - i) - S(X + Y - i) - (S(1) - S(0)) = n`;
* `S(Y + 1) - S(Y + 1 - i) - (S(X) - S(X - i)) = -d`. -/
theorem corner_diffs (wh wv : BinaryWord) (S : GInt → ℤ) (n d : ℤ) (X Y : GInt)
    (hhead : wh.head? = some .q) (hlast : wh.getLast? = some .p)
    (hA : RespectsTiles .horizontal false (hStringAt wh 0) S)
    (hC : RespectsTiles .horizontal true (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))) S)
    (hb : CornerAffineStatement wh wv n d S)
    (hX : lastPosOf (hStringAt wh 0) = X - (1, 1))
    (hY : lastPosOf (vRevStringAt wv.reverse 0) = Y + (1, -2)) :
    S (X + Y + (1, -1)) - S (X + Y + (0, -1)) - (S (1, 0) - S (0, 0)) = n ∧
    S (Y + (1, 0)) - S (Y + (1, -1)) - (S X - S (X - (0, 1))) = -d := by
  have hne : wh ≠ [] := by
    rintro rfl
    simp at hhead
  have hrne : wh.reverse ≠ [] := by simpa using hne
  obtain ⟨F, hF, hFS, -⟩ := hA
  obtain ⟨G, hG, hGS, -⟩ := hC
  have hlen : 0 < wh.length := List.length_pos_of_ne_nil hne
  have hFn : F.n = wh.length := by
    unfold PTFamily.n
    rw [hF, hStringAt_length']
  have hGn : G.n = wh.length := by
    unfold PTFamily.n
    rw [hG, hRevStringAt_length, List.length_reverse]
  -- the four corner tiles as tiles of the two families
  have hA0 : (cornerTiles wh wv 0).1 = F.tile 0 := by
    simp only [cornerTiles]
    rw [headD_eq_getD_zero', ← hF]
    rfl
  have hB0 : (cornerTiles wh wv 0).2.1 = F.tile (F.n - 1) := by
    simp only [cornerTiles]
    rw [getLastD_eq_getD', ← hF]
    rfl
  have hD0 : (cornerTiles wh wv 0).2.2.2 = G.tile 0 := by
    simp only [cornerTiles]
    rw [headD_eq_getD_zero', ← hG]
    rfl
  have hC0 : (cornerTiles wh wv 0).2.2.1 = G.tile (G.n - 1) := by
    simp only [cornerTiles]
    rw [getLastD_eq_getD', ← hG]
    rfl
  have hAt : F.tile 0 = (ZTile.one, 0) := by
    rw [← hA0]
    simp only [cornerTiles]
    exact hStringAt_head_q wh 0 hhead
  have hwl : wh.getD (wh.length - 1) Letter.p = Letter.p := by
    rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, hlast]
    rfl
  have hBt : F.tile (F.n - 1) = (ZTile.zero, X - (1, 1)) := by
    apply Prod.ext
    · show ((F.ts).getD (F.n - 1) (ZTile.zero, 0)).1 = _
      rw [hF, getD_fst_of_map _ _ (hStringAt_map_fst wh 0), hFn]
      exact tileSeqAux_getD_p wh none _ (by omega) hwl
    · show ((F.ts).getD (F.n - 1) (ZTile.zero, 0)).2 = _
      rw [← hX, lastPosOf_eq_getD, hF, hFn, hStringAt_length']
  have hwr0 : wh.reverse.getD 0 Letter.p = Letter.p := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, List.head?_reverse, hlast]
    rfl
  have hDt : G.tile 0 = (ZTile.zero, Y + (1, -2)) := by
    apply Prod.ext
    · show ((G.ts).getD 0 (ZTile.zero, 0)).1 = _
      rw [hG, hRevStringAt_getD_fst, tileSeq_getD_zero_head wh.reverse hrne hwr0]
    · show ((G.ts).getD 0 (ZTile.zero, 0)).2 = _
      rw [hG, hRevStringAt_getD_snd_zero wh.reverse _ hrne, hY]
  have hwrl : wh.reverse.getD (wh.reverse.length - 1) Letter.p = Letter.q := by
    rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, List.getLast?_reverse, hhead]
    rfl
  have hCpos : (G.tile (G.n - 1)).2 = X + Y + (0, -2) := by
    have h1 := hRev_lastPos_reverse wh (lastPosOf (vRevStringAt wv.reverse 0)) hhead hlast
    show ((G.ts).getD (G.ts.length - 1) (ZTile.zero, 0)).2 = _
    rw [hG, ← lastPosOf_eq_getD, h1, hY, hX]
    ext <;> simp <;> ring
  have hCt : (G.tile (G.n - 1)).1 = ZTile.one ∨ (G.tile (G.n - 1)).1 = ZTile.oneD := by
    show ((G.ts).getD (G.n - 1) (ZTile.zero, 0)).1 = _ ∨ ((G.ts).getD (G.n - 1) (ZTile.zero, 0)).1 = _
    rw [hG, hRevStringAt_getD_fst, hGn, ← List.length_reverse (as := wh)]
    exact tileSeq_getD_q wh.reverse _ (by rw [List.length_reverse]; omega) hwrl
  -- the corner identities of (b), in the affine factors of the family tiles
  obtain ⟨hb1, hb2, hb3⟩ := hb
  rw [hA0, hB0] at hb1
  rw [hC0, hD0] at hb2
  rw [hC0, hB0] at hb3
  -- the four value differences
  have eA := val_diff F S 0 (by omega) hFS _ hAt (1, 0) (0, 0) (show _ ∈ tileShape ZTile.one by decide)
    (show _ ∈ tileShape ZTile.one by decide)
  have eB := val_diff F S (F.n - 1) (by omega) hFS _ hBt (1, 1) (1, 0) (show _ ∈ tileShape ZTile.zero by decide)
    (show _ ∈ tileShape ZTile.zero by decide)
  have eD := val_diff G S 0 (by omega) hGS _ hDt (0, 2) (0, 1) (show _ ∈ tileShape ZTile.zero by decide)
    (show _ ∈ tileShape ZTile.zero by decide)
  have hCt' : G.tile (G.n - 1) = ((G.tile (G.n - 1)).1, X + Y + (0, -2)) := by
    rw [← hCpos]
  have hCmem : ∀ u ∈ [((1 : ℤ), (1 : ℤ)), ((0 : ℤ), (1 : ℤ))], u ∈ tileShape (G.tile (G.n - 1)).1 := by
    intro u hu
    rcases hCt with h | h <;> rw [h] <;> simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hu <;> rcases hu with rfl | rfl <;> decide
  have eC := val_diff G S (G.n - 1) (by omega) hGS _ hCt' (1, 1) (0, 1) (hCmem _ (by simp)) (hCmem _ (by simp))
  have hCv : zTileOdo (G.tile (G.n - 1)).1 (1, 1) - zTileOdo (G.tile (G.n - 1)).1 (0, 1) = 1 := by
    rcases hCt with h | h <;> rw [h] <;> decide
  simp only at eC
  rw [hCv] at eC
  rw [hAt] at hb1
  rw [hBt] at hb1 hb3
  rw [hDt] at hb2
  rw [hCt'] at hb2 hb3
  simp only at eA eB eD
  have vA : zTileOdo ZTile.one (1, 0) - zTileOdo ZTile.one (0, 0) = 0 := by decide
  have vB : zTileOdo ZTile.zero (1, 1) - zTileOdo ZTile.zero (1, 0) = 0 := by decide
  have vD : zTileOdo ZTile.zero (0, 2) - zTileOdo ZTile.zero (0, 1) = -1 := by decide
  rw [vA] at eA
  rw [vB] at eB
  rw [vD] at eD
  have pA : ((0 : GInt) + (1, 0)) = (1, 0) := by ext <;> simp
  have pA' : ((0 : GInt) + (0, 0)) = (0, 0) := by ext <;> simp
  have pB : X - (1, 1) + (1, 1) = X := by abel
  have pB' : X - (1, 1) + (1, 0) = X - (0, 1) := by
    ext <;> (simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring)
  have pD : Y + (1, -2) + (0, 2) = Y + (1, 0) := by
    ext <;> (simp only [Prod.fst_add, Prod.snd_add]; ring)
  have pD' : Y + (1, -2) + (0, 1) = Y + (1, -1) := by
    ext <;> (simp only [Prod.fst_add, Prod.snd_add]; ring)
  have pC : X + Y + (0, -2) + (1, 1) = X + Y + (1, -1) := by
    ext <;> (simp only [Prod.fst_add, Prod.snd_add]; ring)
  have pC' : X + Y + (0, -2) + (0, 1) = X + Y + (0, -1) := by
    ext <;> (simp only [Prod.fst_add, Prod.snd_add]; ring)
  rw [pA, pA'] at eA
  rw [pB, pB'] at eB
  rw [pD, pD'] at eD
  rw [pC, pC'] at eC
  have b11 := congrArg Prod.fst hb1
  have b12 := congrArg Prod.snd hb1
  have b21 := congrArg Prod.fst hb2
  have b22 := congrArg Prod.snd hb2
  have b31 := congrArg Prod.fst hb3
  have b32 := congrArg Prod.snd hb3
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at b11 b12 b21 b22 b31 b32
  constructor
  · have : ((S (X + Y + (1, -1)) - S (X + Y + (0, -1)) - (S (1, 0) - S (0, 0)) : ℤ) : ℚ) = (n : ℚ) := by
      push_cast at eA eB eC eD ⊢
      linarith
    exact_mod_cast this
  · have : ((S (Y + (1, 0)) - S (Y + (1, -1)) - (S X - S (X - (0, 1))) : ℤ) : ℚ) = (-d : ℚ) := by
      push_cast at eA eB eC eD ⊢
      linarith
    exact_mod_cast this

end FLatticePaper.Tiles.ClosedPathCorners
