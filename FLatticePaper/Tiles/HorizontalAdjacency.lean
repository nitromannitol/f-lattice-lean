import FLatticePaper.Tiles.VerticalAdjacency
import FLatticePaper.Tiles.TileListBridge
import FLatticePaper.Tiles.SurgicalAffineChain

/-! The adjacency dichotomy of the horizontal families: for consecutive tiles of a horizontal zero-one string (forward
`hStringAt`, reversed `hRevStringAt`), the two tiles overlap or contain a unit-apart pair of sites. The tile of letter
position `k` has type `hTt (tlPrev p w k) (w_k)` (with `oneD` after `q q`), and the step to position `k+1` is `hOffset`
(forward) or `hRevOffset` (reversed) of the letters. Every triple of letters is checked by `decide`. -/

namespace FLatticePaper.Tiles

theorem hTt_dich_fwd (a b c : Letter) : vDich (hTt a b) (hTt b c) (hOffset c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem hTt_dich_rev (a b c : Letter) : vDich (hTt a b) (hTt b c) (hRevOffset b c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem hOffset_hL (u : BinaryWord) (k : ℕ) (hk : k + 1 < u.length) :
    (u.tail.map hOffset).getD k 0 = hOffset (u.getD (k + 1) Letter.p) := by
  have h1 : k < (u.tail.map hOffset).length := by
    simp
    omega
  rw [List.getD_eq_getElem _ _ h1]
  simp only [List.getElem_map, List.getElem_tail]
  rw [List.getD_eq_getElem _ _ (by omega)]

/-- The tile of the forward horizontal string at `k`: its type `hTt` of the previous and the current letter, and its
position. -/
theorem hStringAt_getD_pair (w : BinaryWord) (c : GInt) (k : ℕ) (hk : k < w.length) :
    (hStringAt w c).getD k (ZTile.zero, (0 : GInt)) =
      (hTt (tlPrev Letter.p w k) (w.getD k Letter.p), (List.scanl (· + ·) c (w.tail.map hOffset)).getD k 0) := by
  have hw : 0 < w.length := by omega
  have hl : (List.scanl (· + ·) c (w.tail.map hOffset)).length ≤ (tileSeq w).length := by
    simp only [List.length_scanl, List.length_map, List.length_tail, tileSeq, tileSeqAux_length]
    omega
  have hsnd : (hStringAt w c).map Prod.snd = List.scanl (· + ·) c (w.tail.map hOffset) := by
    unfold hStringAt
    exact List.map_snd_zip hl
  apply Prod.ext
  · rw [hStringAt_getD_fst]
    unfold tileSeq
    rw [tileSeqAux_none_eq, tileSeqAux_getD w Letter.p k hk]
  · rw [← getD_map_snd' (hStringAt w c) k ZTile.zero (0 : GInt), hsnd]

/-- The tile of the reversed horizontal string at `k`: its type `hTt` of the previous and the current letter, and its
position. -/
theorem hRevStringAt_getD_pair (u : BinaryWord) (c : GInt) (k : ℕ) (hk : k < u.length) :
    (hRevStringAt u c).getD k (ZTile.zero, (0 : GInt)) =
      (hTt (tlPrev Letter.p u k) (u.getD k Letter.p),
        (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => hRevOffset ab.1 ab.2)).getD k 0) := by
  have hu : 0 < u.length := by omega
  have hl : (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => hRevOffset ab.1 ab.2)).length ≤
      (tileSeq u).length := by
    simp only [List.length_scanl, List.length_map, List.length_zip, List.length_tail, tileSeq,
      tileSeqAux_length]
    omega
  have hsnd : (hRevStringAt u c).map Prod.snd =
      List.scanl (· + ·) c ((u.zip u.tail).map fun ab => hRevOffset ab.1 ab.2) := by
    unfold hRevStringAt
    exact List.map_snd_zip hl
  apply Prod.ext
  · rw [hRevStringAt_getD_fst]
    unfold tileSeq
    rw [tileSeqAux_none_eq, tileSeqAux_getD u Letter.p k hk]
  · rw [← getD_map_snd' (hRevStringAt u c) k ZTile.zero (0 : GInt), hsnd]

/-- Consecutive tiles of a family on the forward horizontal string `hStringAt w c` overlap or are unit-apart. -/
theorem adj_hStringAt (w : BinaryWord) (c : GInt) (F : PTFamily) (hF : F.ts = hStringAt w c)
    (k : ℕ) (hk : k + 1 < F.n) :
    (∃ x, x ∈ F.dom k ∧ x ∈ F.dom (k + 1)) ∨
      ∃ x, x ∈ F.dom k ∧ ∃ y, y ∈ F.dom (k + 1) ∧ unitApart x y := by
  have hn : F.n = w.length := by
    unfold PTFamily.n
    rw [hF, hStringAt_length]
  rw [hn] at hk
  have hq : (List.scanl (· + ·) c (w.tail.map hOffset)).getD (k + 1) 0 =
      (List.scanl (· + ·) c (w.tail.map hOffset)).getD k 0 + hOffset (w.getD (k + 1) Letter.p) := by
    rw [scanl_getD_succ_gen _ c k (by simp; omega), hOffset_hL w k hk]
  have ht0 : F.tile k = (hTt (tlPrev Letter.p w k) (w.getD k Letter.p),
      (List.scanl (· + ·) c (w.tail.map hOffset)).getD k 0) := by
    unfold PTFamily.tile
    rw [hF, hStringAt_getD_pair w c k (by omega)]
  have ht1 : F.tile (k + 1) = (hTt (w.getD k Letter.p) (w.getD (k + 1) Letter.p),
      (List.scanl (· + ·) c (w.tail.map hOffset)).getD (k + 1) 0) := by
    unfold PTFamily.tile
    rw [hF, hStringAt_getD_pair w c (k + 1) hk]
    simp [tlPrev]
  unfold PTFamily.dom
  rw [ht0, ht1]
  exact dich_pos _ _ _ _ _ hq (hTt_dich_fwd _ _ _)

/-- Consecutive tiles of a family on the reversed horizontal string `hRevStringAt u c` overlap or are unit-apart. -/
theorem adj_hRevStringAt (u : BinaryWord) (c : GInt) (F : PTFamily) (hF : F.ts = hRevStringAt u c)
    (k : ℕ) (hk : k + 1 < F.n) :
    (∃ x, x ∈ F.dom k ∧ x ∈ F.dom (k + 1)) ∨
      ∃ x, x ∈ F.dom k ∧ ∃ y, y ∈ F.dom (k + 1) ∧ unitApart x y := by
  have hn : F.n = u.length := by
    unfold PTFamily.n
    rw [hF, hRevStringAt_length]
  rw [hn] at hk
  have hq : (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => hRevOffset ab.1 ab.2)).getD (k + 1) 0 =
      (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => hRevOffset ab.1 ab.2)).getD k 0 +
        hRevOffset (u.getD k Letter.p) (u.getD (k + 1) Letter.p) := by
    rw [scanl_getD_succ_gen _ c k (by simp; omega), hRev_zip_getD u k hk]
  have ht0 : F.tile k = (hTt (tlPrev Letter.p u k) (u.getD k Letter.p),
      (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => hRevOffset ab.1 ab.2)).getD k 0) := by
    unfold PTFamily.tile
    rw [hF, hRevStringAt_getD_pair u c k (by omega)]
  have ht1 : F.tile (k + 1) = (hTt (u.getD k Letter.p) (u.getD (k + 1) Letter.p),
      (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => hRevOffset ab.1 ab.2)).getD (k + 1) 0) := by
    unfold PTFamily.tile
    rw [hF, hRevStringAt_getD_pair u c (k + 1) hk]
    simp [tlPrev]
  unfold PTFamily.dom
  rw [ht0, ht1]
  exact dich_pos _ _ _ _ _ hq (hTt_dich_rev _ _ _)

end FLatticePaper.Tiles
