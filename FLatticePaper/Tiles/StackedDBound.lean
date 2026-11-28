import FLatticePaper.Tiles.StackedTopCell
import FLatticePaper.Tiles.StackedOrder
import FLatticePaper.Tiles.StackedBaseCentre
import FLatticePaper.Tiles.MarksIn
import FLatticePaper.Tiles.StackedEntry
import FLatticePaper.Tiles.CellExtremes
import FLatticePaper.Tiles.StackedWalks

/-! The bounds of the top side of the translate `T - v` against the bottom walk `B` of the odd tile (the lead's target, on every
common column `t` with `1 ≤ t` and `t + 1 ≤ sum (oddBottom w).1`).

The top side of `T - v` is the bottom walk reflected through `C - v`: its points over a column `t` are `(t, E2 - y)` for the
points `(E1 + 1 - t, y)` of the bottom walk, where `E = sum (oddBottom w)`. Each such point is a site of `T - v`, so its corner cell
of `T` is one of the cells of the column `t + v.1` or `t + v.1 - 1`. The cell order `odd_order_all` then puts its height below the
top cell of the bottom walk over `t` (or over `t - 1`, which is below the top over `t` by `walk_later_above`). -/

namespace FLatticePaper.Tiles.StackedDBound

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardBoundary
  FLatticePaper.Tiles.StackedTopCell FLatticePaper.Tiles.OverlapSides FLatticePaper.Tiles.StackedOrder
  FLatticePaper.Tiles.StackedBottomLink FLatticePaper.Tiles.BaseCellIdentities FLatticePaper.Tiles.StackedWalks

/-- **The upper bound of the translate's top side.** A point `(E1 + 1 - t, y)` of the bottom walk gives, over the column `t`, the
point `(t, E2 - y)` of the top side of `T - v`, which lies below the top point `(t, B)` of the bottom walk over `t` for some `B`. -/
theorem odd_Dplus (w : Word) (t : ℤ) (ht1 : 1 ≤ t) (htE : t + 1 ≤ (F2Word.sum (oddBottom w)).1) (s y : ℤ)
    (hsy : ((s, y) : GInt) ∈ F2Word.walk (0, 0) (oddBottom w)) (hs : s = (F2Word.sum (oddBottom w)).1 + 1 - t) :
    ∃ B : ℤ, ((t, B) : GInt) ∈ F2Word.walk (0, 0) (oddBottom w) ∧
      (F2Word.sum (oddBottom w)).2 - y ≤ B := by
  have hu : ∀ x ∈ oddBottom w, x = Unit4.one ∨ x = Unit4.i := (admissible_oddStandard w).1.1
  obtain ⟨hC1, hC2⟩ := FLatticePaper.Tiles.StackedBaseCentre.centre_odd_coords w
  -- the point of the top side of `T - v` over `t`, shifted by `v`, is a site of the tile
  have hzv : ((t + (texV2 (fracOdd w)).1, (F2Word.sum (oddBottom w)).2 - y + (texV2 (fracOdd w)).2) : GInt) ∈
      oddTile w := by
    have h := MarksIn.halfTurn_oddTile w ((s, y) : GInt) (walk_site w (s, y) hsy)
    have e : halfTurn (oddTile w) ((s, y) : GInt) =
        ((t + (texV2 (fracOdd w)).1, (F2Word.sum (oddBottom w)).2 - y + (texV2 (fracOdd w)).2) : GInt) := by
      ext <;> simp [halfTurn] <;> omega
    rw [e] at h
    exact h
  obtain ⟨c, hc, hcorn⟩ := corner_of_hcc (Standard.oddTile_hcc w) hzv
  have key : (c.1 = t + (texV2 (fracOdd w)).1 ∨ c.1 = t + (texV2 (fracOdd w)).1 - 1) ∧
      (F2Word.sum (oddBottom w)).2 - y + (texV2 (fracOdd w)).2 - 1 ≤ c.2 ∧
      c.2 ≤ (F2Word.sum (oddBottom w)).2 - y + (texV2 (fracOdd w)).2 := by
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
  obtain ⟨Bt, hBtW, hBtmax, hBtT⟩ := top_cell w t (by omega) htE
  obtain ⟨hcol, hlo, hhi⟩ := key
  rcases hcol with hcol | hcol
  · -- the cell `c` lies over the column `t + v.1`: compare with the cell of the top over `t`
    have hcT : ((t + (texV2 (fracOdd w)).1, c.2 - (texV2 (fracOdd w)).2 + (texV2 (fracOdd w)).2) : GInt) ∈
        cellTileOf (oddTile w) := by
      rw [sub_add_cancel, ← hcol]
      exact hc
    have hlt := odd_order_all w t (c.2 - (texV2 (fracOdd w)).2) Bt hcT hBtT
    exact ⟨Bt, hBtW, by omega⟩
  · -- the cell `c` lies over the column `t + v.1 - 1`, the column `t - 1` of the top side
    have hcT : ((t - 1 + (texV2 (fracOdd w)).1, c.2 - (texV2 (fracOdd w)).2 + (texV2 (fracOdd w)).2) : GInt) ∈
        cellTileOf (oddTile w) := by
      rw [sub_add_cancel, show t - 1 + (texV2 (fracOdd w)).1 = c.1 by omega]
      exact hc
    obtain ⟨Bt', hBt'W, hBt'max, hBt'T⟩ := top_cell w (t - 1) (by omega) (by omega)
    have hlt := odd_order_all w (t - 1) (c.2 - (texV2 (fracOdd w)).2) Bt' hcT hBt'T
    have hle : Bt' ≤ Bt :=
      StackedEntry.walk_later_above (oddBottom w) hu (0, 0) _ _ hBt'W hBtW (by simp)
    exact ⟨Bt, hBtW, by omega⟩

/-- **The top side of the translate lies below the bottom walk, on every common column.** For `2 ≤ t`, the point of the bottom walk
over `E1 + 1 - t` at its top gives, over `t`, the lowest point of the top side of `T - v`, which lies below the lowest point of the
bottom walk over `t`. The entry lemma puts the bottom walk over `E1 + 2 - t` below the top over `E1 + 1 - t`, and the upper bound
of the previous column (`odd_Dplus`) closes the chain. -/
theorem odd_Dminus (w : Word) (t : ℤ) (ht1 : 1 ≤ t) (htE : t + 1 ≤ (F2Word.sum (oddBottom w)).1) :
    ∃ y : ℤ, ((((F2Word.sum (oddBottom w)).1 + 1 - t), y) : GInt) ∈ F2Word.walk (0, 0) (oddBottom w) ∧
      ∀ b ∈ F2Word.walk (0, 0) (oddBottom w), b.1 = t → (F2Word.sum (oddBottom w)).2 - y ≤ b.2 := by
  have hu : ∀ x ∈ oddBottom w, x = Unit4.one ∨ x = Unit4.i := (admissible_oddStandard w).1.1
  rcases (show t = 1 ∨ 2 ≤ t by omega) with rfl | ht2
  · -- the first column: the end of the bottom walk is the lowest point of the top side
    refine ⟨(F2Word.sum (oddBottom w)).2, ?_, ?_⟩
    · have hm := CellExtremes.mem_walk_last ((0, 0) : GInt) (oddBottom w)
      have e : ((0, 0) : GInt) + F2Word.sum (oddBottom w) =
          (((F2Word.sum (oddBottom w)).1 + 1 - 1, (F2Word.sum (oddBottom w)).2) : GInt) := by
        ext <;> simp
      rw [e] at hm
      exact hm
    · intro b hb _
      have hge : (0 : ℤ) ≤ b.2 := (StackedWalks.walk_ge_start (oddBottom w) hu (0, 0) b hb).2
      omega
  · -- for `2 ≤ t`: the entry of the bottom walk into the column `E1 + 2 - t` lies below its top over `E1 + 1 - t`
    obtain ⟨Bs, hBsW, hBsmax, -⟩ := top_cell w ((F2Word.sum (oddBottom w)).1 + 1 - t) (by omega) (by omega)
    refine ⟨Bs, hBsW, ?_⟩
    intro b hb hb1
    have hnext : ∃ q ∈ F2Word.walk (0, 0) (oddBottom w), q.1 = (F2Word.sum (oddBottom w)).1 + 1 - t + 1 := by
      obtain ⟨_, hh⟩ := col_exists w ((F2Word.sum (oddBottom w)).1 + 1 - t + 1) (by omega) (by omega)
      exact ⟨_, hh, rfl⟩
    obtain ⟨h, hhB, hhW⟩ := StackedEntry.walk_entry_le (oddBottom w) hu (0, 0) _ Bs hBsW hBsmax hnext
    obtain ⟨B', hB'W, hB'ge⟩ := odd_Dplus w (t - 1) (by omega) (by omega)
      ((F2Word.sum (oddBottom w)).1 + 1 - t + 1) h hhW (by omega)
    have hle : B' ≤ b.2 :=
      StackedEntry.walk_later_above (oddBottom w) hu (0, 0) _ b hB'W hb (by show t - 1 < b.1; omega)
    omega
