import FLatticePaper.Tiles.StackedTopCell
import FLatticePaper.Tiles.StackedEvenOrder
import FLatticePaper.Tiles.SiteHullEven
import FLatticePaper.Tiles.MarksIn
import FLatticePaper.Tiles.StackedEntry
import FLatticePaper.Tiles.CellExtremes
import FLatticePaper.Tiles.CommonExtensionWitness
import FLatticePaper.Tiles.RowInterval

/-! The even mirror of `StackedDBound`: the bounds of the top side of the translate `T - v` against the bottom walk of the even tile,
with `v = texV2 (fracEven w)`. The even bottom word ends with the horizontal step (`StackedEvenOrder.evenBottom_snoc`), and the
centre is `halfTurnCentre (evenTile w) = (num + 1, 2 num + den - 1)` (`SiteHullEven.centre_even`), so with `E1 = den` and
`E2 = num - 1` the top side of `T - v` is the reflection `(E1 + 1 - s, E2 - y)` of the bottom walk, as for the odd tile. -/

namespace FLatticePaper.Tiles.StackedEvenBound

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardBoundary
  FLatticePaper.Tiles.StackedTopCell FLatticePaper.Tiles.OverlapSides FLatticePaper.Tiles.StackedEvenOrder
  FLatticePaper.Tiles.BaseCellIdentities FLatticePaper.Tiles.StackedWalkPattern FLatticePaper.Tiles.CellExtremes

/-- A consecutive pair of the even bottom walk is a directed boundary edge of the even tile. -/
theorem bnd_pair_even (w : Word) (p q : GInt) (l1 l2 : List GInt)
    (h : F2Word.walk (0, 0) (evenBottom w) = l1 ++ [p, q] ++ l2) :
    (p, q) ∈ (cellTileOf (evenTile w)).boundaryEdges := by
  have hB := OverlapSides.boundary_even w
  unfold IsBoundaryWordAt at hB
  obtain ⟨-, -, -, hfin⟩ := hB
  rw [← hfin, List.mem_toFinset]
  have hw : boundaryWordOf (evenBottom w) (evenRight w) =
      evenBottom w ++ (evenRight w ++ ((F2Word.rev (evenBottom w)).hat ++ (F2Word.rev (evenRight w)).hat)) := by
    simp [boundaryWordOf, List.append_assoc]
  rw [hw, WalkDecomp.walk_append, h]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply zip_mem_of_mid
  exact ⟨_, _, rfl⟩

/-- Every point of the even bottom walk is a site of the even tile. -/
theorem walk_site_even (w : Word) : ∀ p ∈ F2Word.walk (0, 0) (evenBottom w), p ∈ evenTile w := by
  intro p hp
  by_cases hpc : p = ((0, 0) : GInt)
  · subst hpc
    exact CommonExtWitness.zero_mem_evenTile w
  · have hu : ∀ x ∈ evenBottom w, x = Unit4.one ∨ x = Unit4.i := (admissible_evenStandard w).1.1
    obtain ⟨q, l1, l2, hl⟩ := pattern_pred (evenBottom w) hu (0, 0) p hp hpc
    have he := bnd_pair_even w q p l1 l2 hl
    obtain ⟨s, hs, -, hpcorner⟩ := corners_of_boundaryEdge (cellTileOf (evenTile w)) (q, p) he
    exact ((mem_cellTileOf _ _).1 hs).2 hpcorner

/-- The bottom walk of the even tile meets every column between its start and its end. -/
theorem col_exists_even (w : Word) (r : ℤ) (hr0 : 0 ≤ r) (hr1 : r ≤ (F2Word.sum (evenBottom w)).1) :
    ∃ h : ℤ, ((r, h) : GInt) ∈ F2Word.walk (0, 0) (evenBottom w) := by
  have hu : ∀ x ∈ evenBottom w, x = Unit4.one ∨ x = Unit4.i := (admissible_evenStandard w).1.1
  have hn : ∀ x ∈ evenBottom w, x ≠ Unit4.negI := fun x hx => by
    rcases hu x hx with h | h <;> rw [h] <;> decide
  have hcol : colN (evenBottom w) (0, 0) (cntI (evenBottom w)) = (F2Word.sum (evenBottom w)).1 :=
    OverlapSides.colN_top (evenBottom w) hn (cntI (evenBottom w)) le_rfl
  obtain ⟨h, -, -, hw⟩ := FLatticePaper.Tiles.StackedBottomLink.walk_reach (evenBottom w) hu r
    (cntI (evenBottom w)) hr0 (cntI_nonneg _) le_rfl (by rw [hcol]; exact hr1)
  exact ⟨h, hw⟩

/-- **The top cell of the even bottom walk over a column.** -/
theorem top_cell_even (w : Word) (t : ℤ) (ht0 : 0 ≤ t) (ht1 : t + 1 ≤ (F2Word.sum (evenBottom w)).1) :
    ∃ B : ℤ, ((t, B) : GInt) ∈ F2Word.walk (0, 0) (evenBottom w) ∧
      (∀ q ∈ F2Word.walk (0, 0) (evenBottom w), q.1 = t → q.2 ≤ B) ∧
      ((t, B) : GInt) ∈ cellTileOf (evenTile w) := by
  have hu : ∀ x ∈ evenBottom w, x = Unit4.one ∨ x = Unit4.i := (admissible_evenStandard w).1.1
  obtain ⟨_, hh0⟩ := col_exists_even w t ht0 (by omega)
  obtain ⟨b, hbW, hb1, hbmax⟩ :=
    StackedTopCell.exists_top_col (F2Word.walk (0, 0) (evenBottom w)) t ⟨_, hh0, rfl⟩
  have hbeq : b = ((t, b.2) : GInt) := by
    ext
    · exact hb1
    · rfl
  rw [hbeq] at hbW hbmax
  have hnext : ∃ q ∈ F2Word.walk (0, 0) (evenBottom w), q.1 = t + 1 := by
    obtain ⟨_, hh1⟩ := col_exists_even w (t + 1) (by omega) ht1
    exact ⟨_, hh1, rfl⟩
  obtain ⟨l1, l2, hl⟩ := pattern_step (evenBottom w) hu (0, 0) t b.2 hbW hbmax hnext
  have he := bnd_pair_even w ((t, b.2) : GInt) ((t + 1, b.2) : GInt) l1 l2 hl
  refine ⟨b.2, hbW, hbmax, ?_⟩
  rcases boundary_out (cellTileOf (evenTile w)) ((t, b.2) : GInt) ((t + 1, b.2) : GInt) he with
      ⟨-, hv, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
  · exact hv
  · have := congrArg Prod.fst hb
    simp [gI] at this
  · have := congrArg Prod.fst hb
    simp [gOne] at this; omega
  · have := congrArg Prod.fst hb
    simp [gI] at this

/-- **The upper bound of the even translate's top side.** A point `(E1 + 1 - t, y)` of the even bottom walk gives over `t` a point
of the bottom walk at or above `E2 - y`. -/
theorem even_Dplus (w : Word) (t : ℤ) (ht1 : 1 ≤ t) (htE : t + 1 ≤ (F2Word.sum (evenBottom w)).1) (s y : ℤ)
    (hsy : ((s, y) : GInt) ∈ F2Word.walk (0, 0) (evenBottom w)) (hs : s = (F2Word.sum (evenBottom w)).1 + 1 - t) :
    ∃ B : ℤ, ((t, B) : GInt) ∈ F2Word.walk (0, 0) (evenBottom w) ∧
      (F2Word.sum (evenBottom w)).2 - y ≤ B := by
  have hu : ∀ x ∈ evenBottom w, x = Unit4.one ∨ x = Unit4.i := (admissible_evenStandard w).1.1
  have hE := evenBottom_sum w
  have hC : halfTurnCentre (evenTile w) =
      ((fracEven w).num + 1, 2 * (fracEven w).num + (fracEven w).den - 1) :=
    SiteHullEven.centre_even w
  have hC1 : (halfTurnCentre (evenTile w)).1 = (fracEven w).num + 1 := by rw [hC]
  have hC2 : (halfTurnCentre (evenTile w)).2 = 2 * (fracEven w).num + (fracEven w).den - 1 := by rw [hC]
  have hv1 : (texV2 (fracEven w)).1 = (fracEven w).num - (fracEven w).den := rfl
  have hv2 : (texV2 (fracEven w)).2 = (fracEven w).num + (fracEven w).den := rfl
  have hzv : ((t + (texV2 (fracEven w)).1, (F2Word.sum (evenBottom w)).2 - y + (texV2 (fracEven w)).2) : GInt) ∈
      evenTile w := by
    have h := MarksIn.halfTurn_evenTile w ((s, y) : GInt) (walk_site_even w (s, y) hsy)
    have e : halfTurn (evenTile w) ((s, y) : GInt) =
        ((t + (texV2 (fracEven w)).1, (F2Word.sum (evenBottom w)).2 - y + (texV2 (fracEven w)).2) : GInt) := by
      ext <;> simp [halfTurn] <;> omega
    rw [e] at h
    exact h
  obtain ⟨c, hc, hcorn⟩ := corner_of_hcc (Standard.evenTile_hcc w) hzv
  have key : (c.1 = t + (texV2 (fracEven w)).1 ∨ c.1 = t + (texV2 (fracEven w)).1 - 1) ∧
      (F2Word.sum (evenBottom w)).2 - y + (texV2 (fracEven w)).2 - 1 ≤ c.2 ∧
      c.2 ≤ (F2Word.sum (evenBottom w)).2 - y + (texV2 (fracEven w)).2 := by
    simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton] at hcorn
    rcases hcorn with h | h | h | h
    · have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      simp at e1 e2
      omega
    · have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      simp [gOne] at e1 e2
      omega
    · have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      simp [gI] at e1 e2
      omega
    · have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      simp [gOne, gI] at e1 e2
      omega
  obtain ⟨Bt, hBtW, hBtmax, hBtT⟩ := top_cell_even w t (by omega) htE
  obtain ⟨hcol, hlo, hhi⟩ := key
  rcases hcol with hcol | hcol
  · have hcT : ((t + (texV2 (fracEven w)).1, c.2 - (texV2 (fracEven w)).2 + (texV2 (fracEven w)).2) : GInt) ∈
        cellTileOf (evenTile w) := by
      rw [sub_add_cancel, ← hcol]
      exact hc
    have hlt := even_order_all w t (c.2 - (texV2 (fracEven w)).2) Bt hcT hBtT
    exact ⟨Bt, hBtW, by omega⟩
  · have hcT : ((t - 1 + (texV2 (fracEven w)).1, c.2 - (texV2 (fracEven w)).2 + (texV2 (fracEven w)).2) : GInt) ∈
        cellTileOf (evenTile w) := by
      rw [sub_add_cancel, show t - 1 + (texV2 (fracEven w)).1 = c.1 by omega]
      exact hc
    obtain ⟨Bt', hBt'W, hBt'max, hBt'T⟩ := top_cell_even w (t - 1) (by omega) (by omega)
    have hlt := even_order_all w (t - 1) (c.2 - (texV2 (fracEven w)).2) Bt' hcT hBt'T
    have hle : Bt' ≤ Bt :=
      StackedEntry.walk_later_above (evenBottom w) hu (0, 0) _ _ hBt'W hBtW (by show t - 1 < t; omega)
    exact ⟨Bt, hBtW, by omega⟩

/-- **The lower bound of the even translate's top side.** -/
theorem even_Dminus (w : Word) (t : ℤ) (ht1 : 1 ≤ t) (htE : t + 1 ≤ (F2Word.sum (evenBottom w)).1) :
    ∃ y : ℤ, ((((F2Word.sum (evenBottom w)).1 + 1 - t), y) : GInt) ∈ F2Word.walk (0, 0) (evenBottom w) ∧
      ∀ b ∈ F2Word.walk (0, 0) (evenBottom w), b.1 = t → (F2Word.sum (evenBottom w)).2 - y ≤ b.2 := by
  have hu : ∀ x ∈ evenBottom w, x = Unit4.one ∨ x = Unit4.i := (admissible_evenStandard w).1.1
  have hE := evenBottom_sum w
  rcases (show t = 1 ∨ 2 ≤ t by omega) with rfl | ht2
  · refine ⟨(F2Word.sum (evenBottom w)).2, ?_, ?_⟩
    · have hm := CellExtremes.mem_walk_last ((0, 0) : GInt) (evenBottom w)
      have e : ((0, 0) : GInt) + F2Word.sum (evenBottom w) =
          (((F2Word.sum (evenBottom w)).1 + 1 - 1, (F2Word.sum (evenBottom w)).2) : GInt) := by
        ext <;> simp
      rw [e] at hm
      exact hm
    · intro b hb _
      have hge : (0 : ℤ) ≤ b.2 := (StackedWalks.walk_ge_start (evenBottom w) hu (0, 0) b hb).2
      omega
  · obtain ⟨Bs, hBsW, hBsmax, -⟩ := top_cell_even w ((F2Word.sum (evenBottom w)).1 + 1 - t) (by omega) (by omega)
    refine ⟨Bs, hBsW, ?_⟩
    intro b hb hb1
    have hnext : ∃ q ∈ F2Word.walk (0, 0) (evenBottom w), q.1 = (F2Word.sum (evenBottom w)).1 + 1 - t + 1 := by
      obtain ⟨_, hh⟩ := col_exists_even w ((F2Word.sum (evenBottom w)).1 + 1 - t + 1) (by omega) (by omega)
      exact ⟨_, hh, rfl⟩
    obtain ⟨h, hhB, hhW⟩ := StackedEntry.walk_entry_le (evenBottom w) hu (0, 0) _ Bs hBsW hBsmax hnext
    obtain ⟨B', hB'W, hB'ge⟩ := even_Dplus w (t - 1) (by omega) (by omega)
      ((F2Word.sum (evenBottom w)).1 + 1 - t + 1) h hhW (by omega)
    have hle : B' ≤ b.2 :=
      StackedEntry.walk_later_above (evenBottom w) hu (0, 0) _ b hB'W hb (by show t - 1 < b.1; omega)
    omega

end FLatticePaper.Tiles.StackedEvenBound
