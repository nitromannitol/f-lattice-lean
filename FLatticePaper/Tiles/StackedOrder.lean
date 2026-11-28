import FLatticePaper.Tiles.StackedBaseOrder
import FLatticePaper.Tiles.StackedColumnFacts
import FLatticePaper.Tiles.RowOverlap
import FLatticePaper.Tiles.CoveringRows
import FLatticePaper.Tiles.ClosedWalkHorizontal
import FLatticePaper.Tiles.StandardAll
import FLatticePaper.Tiles.SiteHullOdd
import FLatticePaper.Tiles.AlmostTilingAssembly
import FLatticePaper.Tiles.RowInterval

/-! The order of the odd tile `T` and its translate `T - v` over the common columns (Step 1 of the stacked (d)).

The cells of `T` over a column `t` form an interval of heights `[ordLo t, ordHi t]`, read off the row form of the even tile of
the swapped word through the quarter turn (`StackedColumnFacts.odd_column_iff`). Consecutive rows of that tile overlap
(`RowOverlap.row_overlap`) and its rows are nonempty (`CoveringRows.rows_nonempty`), so the column intervals are nonempty on the
column range, and consecutive columns are adjacent in the sense of `below_succ`. The cells of `T - v` over `t` are the cells
`(t + v.1, y + v.2)` of `T`, and they are disjoint from the cells of `T` (`ClosedWalkHorizontal.odd_hdisj_neg2`), so the two
intervals are disjoint in each column. The propagation of `StackedOrder.order_interval` then puts `T - v` below `T` on the
common columns, from the base at column `1`. -/

namespace FLatticePaper.Tiles.StackedOrder

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StackedBaseOrder FLatticePaper.Tiles.StackedColumnFacts

/-- **The propagation along an interval of columns.** Two intervals of heights per column, `[loT t, hiT t]` for `T` and
`[loS t, hiS t]` for the translate, with consecutive columns overlapping and the two intervals of each column disjoint: if the
translate is below `T` at column `1`, it is below `T` at every column of `[p, q]` (`p ≤ 1 ≤ q`). -/
theorem order_interval (loT hiT loS hiS : ℤ → ℤ) (p q : ℤ) (hp : p ≤ 1) (hq : 1 ≤ q)
    (hT : ∀ t, p ≤ t → t < q → loT (t + 1) ≤ hiT t ∧ loT t ≤ hiT (t + 1))
    (hS : ∀ t, p ≤ t → t < q → loS (t + 1) ≤ hiS t ∧ loS t ≤ hiS (t + 1))
    (hd : ∀ t, p ≤ t → t ≤ q → hiS t < loT t ∨ hiT t < loS t)
    (hb : hiS 1 < loT 1) :
    ∀ t, p ≤ t → t ≤ q → hiS t < loT t := by
  have fwd : ∀ k : ℕ, ∀ t : ℤ, t = 1 + (k : ℤ) → t ≤ q → hiS t < loT t := by
    intro k
    induction k with
    | zero =>
      intro t ht _
      have e : t = 1 := by omega
      rw [e]
      exact hb
    | succ k ih =>
      intro t ht htq
      have hprev : hiS (t - 1) < loT (t - 1) := ih (t - 1) (by omega) (by omega)
      have h1 := hT (t - 1) (by omega) (by omega)
      have h2 := hS (t - 1) (by omega) (by omega)
      have h3 := hd t (by omega) htq
      rw [sub_add_cancel] at h1 h2
      omega
  have bwd : ∀ k : ℕ, ∀ t : ℤ, t = 1 - (k : ℤ) → p ≤ t → hiS t < loT t := by
    intro k
    induction k with
    | zero =>
      intro t ht _
      have e : t = 1 := by omega
      rw [e]
      exact hb
    | succ k ih =>
      intro t ht hpt
      have hnext : hiS (t + 1) < loT (t + 1) := ih (t + 1) (by omega) (by omega)
      have h1 := hT t (by omega) (by omega)
      have h2 := hS t (by omega) (by omega)
      have h3 := hd t hpt (by omega)
      omega
  intro t hpt htq
  rcases le_total 1 t with h | h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ t - 1 by omega)
    exact fwd k t (by omega) htq
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ 1 - t by omega)
    exact bwd k t (by omega) hpt

/-- The lower end of the cells of the odd tile over a column `t`, read off the row form of the even tile of the swapped word. -/
def ordLo (w : Word) (a : GInt) (t : ℤ) : ℤ :=
  -Nrow (0, 0) (evenBottom (swapW w)) (evenRight (swapW w)) (t - a.2) - a.1

/-- The upper end of the cells of the odd tile over a column `t`. -/
def ordHi (w : Word) (a : GInt) (t : ℤ) : ℤ :=
  -Srow (0, 0) (evenBottom (swapW w)) (evenRight (swapW w)) (t - a.2) - 1 - a.1

/-- **The cells of the odd tile over a column form the interval `[ordLo, ordHi]`**, on the column range of the rows. -/
theorem ordCol_iff (w : Word) (a : GInt) (hrot : rot (oddTile w) = shift (evenTile (swapW w)) a) (t y : ℤ) :
    ((t, y) : GInt) ∈ cellTileOf (oddTile w) ↔
      (0 ≤ t - a.2 ∧ t - a.2 < cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w))) ∧
        ordLo w a t ≤ y ∧ y ≤ ordHi w a t := by
  rw [odd_column_iff w a hrot t y]
  unfold ordLo ordHi
  constructor
  · rintro ⟨hr, h1, h2⟩
    exact ⟨hr, by omega, by omega⟩
  · rintro ⟨hr, h1, h2⟩
    exact ⟨hr, by omega, by omega⟩

/-- The column intervals are nonempty on the column range: the rows of the even tile of the swapped word are nonempty. -/
theorem ordCol_nonempty (w : Word) (a : GInt) (t : ℤ)
    (hr : 0 ≤ t - a.2 ∧ t - a.2 < cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w))) :
    ordLo w a t ≤ ordHi w a t := by
  have hne := rows_nonempty (OverlapSides.boundary_even (swapW w))
    (StandardBoundary.admissible_evenStandard (swapW w)).1.1
    (OverlapSides.letters_w2 (StandardBoundary.admissible_evenStandard (swapW w)).2) (t - a.2) hr.1 hr.2
  unfold ordLo ordHi
  omega

/-- **Adjacent columns overlap.** If the columns `s` and `s + 1` lie on the column range, the interval of `s + 1` meets the
interval of `s` in both directions (the consecutive rows of the even tile overlap). -/
theorem ordCol_adj (w : Word) (a : GInt) (s : ℤ)
    (hs : 0 ≤ s - a.2 ∧ s - a.2 < cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w)))
    (hs1 : 0 ≤ s + 1 - a.2 ∧ s + 1 - a.2 < cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w))) :
    ordLo w a (s + 1) ≤ ordHi w a s ∧ ordLo w a s ≤ ordHi w a (s + 1) := by
  have hov := row_overlap (OverlapSides.boundary_even (swapW w)) (StandardAll.simpleEven_all (swapW w)).2
    (StandardBoundary.admissible_evenStandard (swapW w)).1.1
    (OverlapSides.letters_w2 (StandardBoundary.admissible_evenStandard (swapW w)).2) (t := s - a.2) hs.1 (by omega)
  have e1 : s + 1 - a.2 = s - a.2 + 1 := by ring
  unfold ordLo ordHi
  rw [e1]
  omega

/-- **The translate lies below the tile over every common column.** Let `T` be the odd tile and `v = texV2 (fracOdd w)`. If `T`
has cells over column `1` and over column `1 + v.1`, then for every column `t`, every cell `(t + v.1, y + v.2)` of `T` lies
strictly below every cell `(t, y')` of `T`: the cells of the translate `T - v` over `t` lie below the cells of `T` over `t`. -/
theorem odd_order (w : Word) (a : GInt) (hrot : rot (oddTile w) = shift (evenTile (swapW w)) a)
    (h1 : ∃ y : ℤ, ((1, y) : GInt) ∈ cellTileOf (oddTile w))
    (h2 : ∃ y : ℤ, ((1 + (texV2 (fracOdd w)).1, y) : GInt) ∈ cellTileOf (oddTile w)) :
    ∀ t y y' : ℤ, ((t + (texV2 (fracOdd w)).1, y + (texV2 (fracOdd w)).2) : GInt) ∈ cellTileOf (oddTile w) →
      ((t, y') : GInt) ∈ cellTileOf (oddTile w) → y < y' := by
  obtain ⟨y1, hy1⟩ := h1
  obtain ⟨y2, hy2⟩ := h2
  obtain ⟨⟨R1a, R1b⟩, -, -⟩ := (ordCol_iff w a hrot 1 y1).1 hy1
  obtain ⟨⟨R2a, R2b⟩, -, -⟩ := (ordCol_iff w a hrot (1 + (texV2 (fracOdd w)).1) y2).1 hy2
  obtain ⟨p, hpR⟩ : ∃ p : ℤ, ∀ t, p ≤ t ↔ (a.2 ≤ t ∧ a.2 - (texV2 (fracOdd w)).1 ≤ t) :=
    ⟨max a.2 (a.2 - (texV2 (fracOdd w)).1), fun t => max_le_iff⟩
  obtain ⟨q, hqR⟩ : ∃ q : ℤ, ∀ t, t ≤ q ↔ (t ≤ a.2 + (cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w))) - 1 ∧ t ≤ a.2 + (cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w))) - 1 - (texV2 (fracOdd w)).1) :=
    ⟨min (a.2 + (cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w))) - 1) (a.2 + (cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w))) - 1 - (texV2 (fracOdd w)).1), fun t => le_min_iff⟩
  have hp1 : p ≤ 1 := (hpR 1).2 ⟨by omega, by omega⟩
  have hq1 : 1 ≤ q := (hqR 1).2 ⟨by omega, by omega⟩
  have hrange : ∀ t, p ≤ t → t ≤ q →
      (0 ≤ t - a.2 ∧ t - a.2 < (cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w)))) ∧ (0 ≤ t + (texV2 (fracOdd w)).1 - a.2 ∧ t + (texV2 (fracOdd w)).1 - a.2 < (cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w)))) := by
    intro t ht1 ht2
    obtain ⟨ha1, ha2⟩ := (hpR t).1 ht1
    obtain ⟨hb1, hb2⟩ := (hqR t).1 ht2
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  -- the base at column `1`: the cells of `T` there lie at height `0` or above, those of `T - v` at `-1` or below
  have hlo1 : 0 ≤ ordLo w a 1 := by
    have hm : ((1, ordLo w a 1) : GInt) ∈ cellTileOf (oddTile w) :=
      (ordCol_iff w a hrot 1 (ordLo w a 1)).2 ⟨⟨R1a, R1b⟩, le_rfl, ordCol_nonempty w a 1 ⟨R1a, R1b⟩⟩
    exact odd_column_one_low w _ hm
  have hhi1 : ordHi w a (1 + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2 ≤ -1 := by
    have hm : ((1 + (texV2 (fracOdd w)).1, ordHi w a (1 + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2 + (texV2 (fracOdd w)).2) : GInt) ∈ cellTileOf (oddTile w) := by
      rw [sub_add_cancel]
      exact (ordCol_iff w a hrot (1 + (texV2 (fracOdd w)).1) (ordHi w a (1 + (texV2 (fracOdd w)).1))).2
        ⟨⟨R2a, R2b⟩, ordCol_nonempty w a (1 + (texV2 (fracOdd w)).1) ⟨R2a, R2b⟩, le_rfl⟩
    exact odd_column_one_high w _ hm
  have hb : ordHi w a (1 + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2 < ordLo w a 1 := by omega
  have hT : ∀ t, p ≤ t → t < q →
      ordLo w a (t + 1) ≤ ordHi w a t ∧ ordLo w a t ≤ ordHi w a (t + 1) := by
    intro t ht1 ht2
    obtain ⟨hA, -⟩ := hrange t ht1 (by omega)
    obtain ⟨hB, -⟩ := hrange (t + 1) (by omega) (by omega)
    exact ordCol_adj w a t hA hB
  have hS : ∀ t, p ≤ t → t < q →
      ordLo w a (t + 1 + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2 ≤ ordHi w a (t + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2 ∧
        ordLo w a (t + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2 ≤ ordHi w a (t + 1 + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2 := by
    intro t ht1 ht2
    obtain ⟨-, hC⟩ := hrange t ht1 (by omega)
    obtain ⟨-, hD⟩ := hrange (t + 1) (by omega) (by omega)
    have hC1 : 0 ≤ t + (texV2 (fracOdd w)).1 + 1 - a.2 ∧ t + (texV2 (fracOdd w)).1 + 1 - a.2 < (cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w))) := by
      constructor <;> omega
    have hadj := ordCol_adj w a (t + (texV2 (fracOdd w)).1) hC hC1
    rw [show t + 1 + (texV2 (fracOdd w)).1 = t + (texV2 (fracOdd w)).1 + 1 by ring]
    constructor <;> omega
  have hd : ∀ t, p ≤ t → t ≤ q →
      ordHi w a (t + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2 < ordLo w a t ∨ ordHi w a t < ordLo w a (t + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2 := by
    intro t ht1 ht2
    obtain ⟨hA, hC⟩ := hrange t ht1 ht2
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2⟩ := hcon
    have hne1 := ordCol_nonempty w a t hA
    have hne2 := ordCol_nonempty w a (t + (texV2 (fracOdd w)).1) hC
    obtain ⟨y0, hy0⟩ : ∃ y0 : ℤ, y0 = max (ordLo w a t) (ordLo w a (t + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2) := ⟨_, rfl⟩
    have hy0a : ordLo w a t ≤ y0 := by rw [hy0]; exact le_max_left _ _
    have hy0b : ordLo w a (t + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2 ≤ y0 := by rw [hy0]; exact le_max_right _ _
    have hy0c : y0 ≤ ordHi w a t := by rw [hy0]; exact max_le hne1 c2
    have hy0d : y0 ≤ ordHi w a (t + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2 := by rw [hy0]; exact max_le c1 (by omega)
    have hA' : ((t, y0) : GInt) ∈ cellTileOf (oddTile w) :=
      (ordCol_iff w a hrot t y0).2 ⟨hA, hy0a, hy0c⟩
    have hB' : ((t + (texV2 (fracOdd w)).1, y0 + (texV2 (fracOdd w)).2) : GInt) ∈ cellTileOf (oddTile w) :=
      (ordCol_iff w a hrot (t + (texV2 (fracOdd w)).1) (y0 + (texV2 (fracOdd w)).2)).2 ⟨hC, by omega, by omega⟩
    have hneg : ((t, y0) : GInt) - -(texV2 (fracOdd w)) = ((t + (texV2 (fracOdd w)).1, y0 + (texV2 (fracOdd w)).2) : GInt) := by
      ext <;> simp [sub_neg_eq_add]
    exact odd_hdisj_neg2 w (t, y0) hA' (by rw [hneg]; exact hB')
  have key := order_interval (fun t => ordLo w a t) (fun t => ordHi w a t)
    (fun t => ordLo w a (t + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2) (fun t => ordHi w a (t + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2) p q hp1 hq1 hT hS hd hb
  intro t y y' hS' hT'
  obtain ⟨⟨hr2a, hr2b⟩, hl2, hh2⟩ := (ordCol_iff w a hrot (t + (texV2 (fracOdd w)).1) (y + (texV2 (fracOdd w)).2)).1 hS'
  obtain ⟨⟨hr1a, hr1b⟩, hl1, hh1⟩ := (ordCol_iff w a hrot t y').1 hT'
  have hpt : p ≤ t := (hpR t).2 ⟨by omega, by omega⟩
  have htq : t ≤ q := (hqR t).2 ⟨by omega, by omega⟩
  have hk : ordHi w a (t + (texV2 (fracOdd w)).1) - (texV2 (fracOdd w)).2 < ordLo w a t := key t hpt htq
  omega

/-- **The order of the odd tile and its translate, with no remaining input.** For every odd standard tile, every cell of
`T - v` over a column `t` lies strictly below every cell of `T` over `t`, where `v = texV2 (fracOdd w)`. The two base facts of
`odd_order` follow from the arithmetic of the odd fraction: the rotation offset is `tF (fracOdd w)`, whose second coordinate is
`v.1 + 1` (the leftmost column of `T` is `1 + v.1`); the bottom word has `sum (oddBottom w)).1 = 2 · den`; and the cell of `T` over
the leftmost column is mirrored by the cell half-turn to column `2·den − 1`, which bounds the column range from above. -/
theorem odd_order_all (w : Word) :
    ∀ t y y' : ℤ, ((t + (texV2 (fracOdd w)).1, y + (texV2 (fracOdd w)).2) : GInt) ∈ cellTileOf (oddTile w) →
      ((t, y') : GInt) ∈ cellTileOf (oddTile w) → y < y' := by
  obtain ⟨a, ha⟩ : ∃ a : GInt, a = tF (fracOdd w) := ⟨_, rfl⟩
  have hrot : rot (oddTile w) = shift (evenTile (swapW w)) a := by
    rw [ha]; exact (rot_standard_tiles w).1
  obtain ⟨hn1, hn2⟩ : 0 < (fracOdd w).num ∧ (fracOdd w).num < (fracOdd w).den :=
    FLatticePaper.Tiles.SiteHullOdd.curO_pos_lt w
  have hv1 : (texV2 (fracOdd w)).1 = (fracOdd w).num - (fracOdd w).den := rfl
  have hA2 : a.2 = (texV2 (fracOdd w)).1 + 1 := by
    rw [ha]
    show (fracOdd w).num + 1 - (fracOdd w).den = (texV2 (fracOdd w)).1 + 1
    rw [hv1]
    ring
  have hE1 : (F2Word.sum (oddBottom w)).1 = 2 * (fracOdd w).den := by
    have e := congrArg Prod.fst (sum_oddBottom w)
    simp [almostV₁, gI, texV1Odd] at e
    omega
  obtain ⟨hC1, -⟩ := FLatticePaper.Tiles.StackedBaseCentre.centre_odd_coords w
  have hcnt : 1 ≤ cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w)) := by
    have h2 := cntI_w2_pos (admissible_evenStandard (swapW w)).2
    have h1 := cntI_nonneg (evenBottom (swapW w))
    omega
  -- the leftmost column `a.2` of `T` and its cell, mirrored to column `2·den - 1`
  have hm : ((a.2, ordLo w a a.2) : GInt) ∈ cellTileOf (oddTile w) :=
    (ordCol_iff w a hrot a.2 (ordLo w a a.2)).2
      ⟨⟨by omega, by omega⟩, le_rfl, ordCol_nonempty w a a.2 ⟨by omega, by omega⟩⟩
  have hmir := FLatticePaper.Tiles.StackedBase.cell_halfTurn_mem w a.2 (ordLo w a a.2) hm
  have hM : ((F2Word.sum (oddBottom w)).1 - 1,
      (SiteStrings.halfTurnCentre (oddTile w)).2 - ordLo w a a.2 - 1) ∈ cellTileOf (oddTile w) := by
    have e : (SiteStrings.halfTurnCentre (oddTile w)).1 - a.2 - 1 = (F2Word.sum (oddBottom w)).1 - 1 := by omega
    rw [← e]
    exact hmir
  have hMr := (ordCol_iff w a hrot _ _).1 hM
  have h1 : ∃ y : ℤ, ((1, y) : GInt) ∈ cellTileOf (oddTile w) :=
    ⟨ordLo w a 1, (ordCol_iff w a hrot 1 (ordLo w a 1)).2
      ⟨⟨by omega, by omega⟩, le_rfl, ordCol_nonempty w a 1 ⟨by omega, by omega⟩⟩⟩
  have h2 : ∃ y : ℤ, ((1 + (texV2 (fracOdd w)).1, y) : GInt) ∈ cellTileOf (oddTile w) :=
    ⟨ordLo w a (1 + (texV2 (fracOdd w)).1),
      (ordCol_iff w a hrot (1 + (texV2 (fracOdd w)).1) (ordLo w a (1 + (texV2 (fracOdd w)).1))).2
        ⟨⟨by omega, by omega⟩, le_rfl,
          ordCol_nonempty w a (1 + (texV2 (fracOdd w)).1) ⟨by omega, by omega⟩⟩⟩
  exact odd_order w a hrot h1 h2

end FLatticePaper.Tiles.StackedOrder
