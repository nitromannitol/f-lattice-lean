import FLatticePaper.Tiles.GlueCorners

/-! # The end tiles of the four strings of a register

The first and the last tile of each of the four boundary strings of a register, with their types and positions, read off the
first and the last letters of its words: the bottom string runs from `T_{1/1}` to `T_{0/1}`, the left one from `T_{1/1}` to
`T_{0/1}`, the right one from `T_{0/1}` to `T_{1/1}`, and the top one from `T_{0/1}` to `T_{1/1}` or `T^d_{1/1}`. -/

namespace FLatticePaper.Tiles.GlueEnds

open FLatticePaper.Tiles

theorem headD_cons_zip {α β : Type*} (a : α) (as : List α) (b : β) (bs : List β) (d : α × β) :
    ((a :: as).zip (b :: bs)).headD d = (a, b) := rfl

/-- The last tile of a nonempty string, from the last tile type of its tile list. -/
theorem getLastD_of (s : List (ZTile × GInt)) (ts : List ZTile) (hs : s.map Prod.fst = ts) (t : ZTile)
    (ht : ts.getLast? = some t) (hne : s ≠ []) : s.getLastD (ZTile.zero, 0) = (t, lastPosOf s) := by
  obtain ⟨x, hx⟩ : ∃ x, s.getLast? = some x := Option.isSome_iff_exists.1 (by simpa using hne)
  have h1 : (s.map Prod.fst).getLast? = some x.1 := by rw [List.getLast?_map, hx]; rfl
  rw [hs, ht] at h1
  have hx1 : x.1 = t := (Option.some.inj h1).symm
  rw [List.getLastD_eq_getLast?, hx]
  unfold lastPosOf
  rw [hx]
  simp only [Option.getD_some, Option.map_some]
  exact Prod.ext hx1 rfl

theorem tileSeq_getLast_p (X' : BinaryWord) : (tileSeq (X' ++ [Letter.p])).getLast? = some ZTile.zero := by
  rw [GHJoin.tileSeq_snoc_p]
  simp

theorem tileSeqAux_getLast_q (prev : Option Letter) : ∀ (X' : BinaryWord),
    (tileSeqAux prev (X' ++ [Letter.q])).getLast? = some ZTile.one ∨
      (tileSeqAux prev (X' ++ [Letter.q])).getLast? = some ZTile.oneD
  | [] => by cases prev with
    | none => simp [tileSeqAux]
    | some l => cases l <;> simp [tileSeqAux]
  | x :: X' => by
    simp only [List.cons_append, tileSeqAux]
    rcases tileSeqAux_getLast_q (some x) X' with h | h
    · left
      rw [List.getLast?_cons, h]
      rfl
    · right
      rw [List.getLast?_cons, h]
      rfl

theorem map_fst_hStringAt (w : BinaryWord) (c : GInt) : (hStringAt w c).map Prod.fst = tileSeq w := by
  unfold hStringAt
  apply List.map_fst_zip
  cases w <;> simp [tileSeq, StringJoin.tileSeqAux_length]

theorem map_fst_hRevStringAt (w : BinaryWord) (c : GInt) : (hRevStringAt w c).map Prod.fst = tileSeq w := by
  unfold hRevStringAt
  apply List.map_fst_zip
  cases w <;> simp [tileSeq, StringJoin.tileSeqAux_length]

theorem map_fst_vStringAt (w : BinaryWord) (c : GInt) : (vStringAt w c).map Prod.fst = w.map letterZTile := by
  unfold vStringAt
  apply List.map_fst_zip
  cases w <;> simp

theorem map_fst_vRevStringAt (w : BinaryWord) (c : GInt) : (vRevStringAt w c).map Prod.fst = w.map letterZTile := by
  unfold vRevStringAt
  apply List.map_fst_zip
  cases w <;> simp

/-! ### The end tiles -/

theorem bot_head (wh : BinaryWord) (c : GInt) (hh : wh.head? = some Letter.q) :
    (hStringAt wh c).headD (ZTile.zero, 0) = (ZTile.one, c) := by
  obtain ⟨t, rfl⟩ := StringAppend.exists_cons_of_head wh _ hh
  cases t <;> simp [hStringAt, tileSeq, tileSeqAux, List.scanl_cons]

theorem bot_last (wh : BinaryWord) (c : GInt) (hl : wh.getLast? = some Letter.p) :
    (hStringAt wh c).getLastD (ZTile.zero, 0) = (ZTile.zero, lastPosOf (hStringAt wh c)) := by
  obtain ⟨X', rfl⟩ := StringAppend.exists_snoc_of_getLast wh _ hl
  exact getLastD_of _ _ (map_fst_hStringAt _ c) _ (tileSeq_getLast_p X')
    (GlueStringDecomp.hStringAt_ne _ _ (by simp))

theorem top_head (u : BinaryWord) (c : GInt) (hh : u.head? = some Letter.p) :
    (hRevStringAt u c).headD (ZTile.zero, 0) = (ZTile.zero, c) := by
  obtain ⟨t, rfl⟩ := StringAppend.exists_cons_of_head u _ hh
  cases t <;> simp [hRevStringAt, tileSeq, tileSeqAux, List.scanl_cons]

theorem top_last (u : BinaryWord) (c : GInt) (hl : u.getLast? = some Letter.q) :
    ∃ t, (t = ZTile.one ∨ t = ZTile.oneD) ∧
      (hRevStringAt u c).getLastD (ZTile.zero, 0) = (t, lastPosOf (hRevStringAt u c)) := by
  obtain ⟨X', rfl⟩ := StringAppend.exists_snoc_of_getLast u _ hl
  rcases tileSeqAux_getLast_q none X' with h | h
  · exact ⟨_, Or.inl rfl, getLastD_of _ _ (map_fst_hRevStringAt _ c) _ h
      (GlueStringDecomp.hRevStringAt_ne _ _ (by simp))⟩
  · exact ⟨_, Or.inr rfl, getLastD_of _ _ (map_fst_hRevStringAt _ c) _ h
      (GlueStringDecomp.hRevStringAt_ne _ _ (by simp))⟩

theorem left_head (u : BinaryWord) (c : GInt) (hh : u.head? = some Letter.q) :
    (vRevStringAt u c).headD (ZTile.zero, 0) = (ZTile.one, c) := by
  obtain ⟨t, rfl⟩ := StringAppend.exists_cons_of_head u _ hh
  cases t <;> simp [vRevStringAt, List.scanl_cons, letterZTile]

theorem left_last (u : BinaryWord) (c : GInt) (hl : u.getLast? = some Letter.p) :
    (vRevStringAt u c).getLastD (ZTile.zero, 0) = (ZTile.zero, lastPosOf (vRevStringAt u c)) := by
  obtain ⟨X', rfl⟩ := StringAppend.exists_snoc_of_getLast u _ hl
  exact getLastD_of _ _ (map_fst_vRevStringAt _ c) _ (by simp [letterZTile])
    (GlueStringDecomp.vRevStringAt_ne _ _ (by simp))

theorem right_head (w : BinaryWord) (c : GInt) (hh : w.head? = some Letter.p) :
    (vStringAt w c).headD (ZTile.zero, 0) = (ZTile.zero, c) := by
  obtain ⟨t, rfl⟩ := StringAppend.exists_cons_of_head w _ hh
  cases t <;> simp [vStringAt, List.scanl_cons, letterZTile]

theorem right_last (w : BinaryWord) (c : GInt) (hl : w.getLast? = some Letter.q) :
    (vStringAt w c).getLastD (ZTile.zero, 0) = (ZTile.one, lastPosOf (vStringAt w c)) := by
  obtain ⟨X', rfl⟩ := StringAppend.exists_snoc_of_getLast w _ hl
  exact getLastD_of _ _ (map_fst_vStringAt _ c) _ (by simp [letterZTile])
    (GlueStringDecomp.vStringAt_ne _ _ (by simp))

/-- The first and the last tiles of a family carrying a string. -/
theorem family_head (F : PTFamily) (s : List (ZTile × GInt)) (h : F.ts = s) : F.tile 0 = s.headD (ZTile.zero, 0) := by
  unfold PTFamily.tile
  rw [h, headD_eq_getD_zero']

theorem family_last (F : PTFamily) (s : List (ZTile × GInt)) (h : F.ts = s) :
    F.tile (F.n - 1) = s.getLastD (ZTile.zero, 0) := by
  unfold PTFamily.tile PTFamily.n
  rw [h, getLastD_eq_getD']

end FLatticePaper.Tiles.GlueEnds
