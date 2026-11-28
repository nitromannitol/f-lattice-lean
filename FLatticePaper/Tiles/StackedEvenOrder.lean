import FLatticePaper.Tiles.StackedOrder
import FLatticePaper.Tiles.StackedEvenColumns
import FLatticePaper.Tiles.StackedBaseColumn
import FLatticePaper.Tiles.ClosedWalkEven
import FLatticePaper.Tiles.SiteHullEven
import FLatticePaper.Tiles.StandardAll
import FLatticePaper.Tiles.RowOverlap
import FLatticePaper.Tiles.CoveringRows
import FLatticePaper.Tiles.AlmostTilingAssembly
import FLatticePaper.Tiles.RowInterval
import FLatticePaper.Tiles.MarksIn

/-! The order of the even tile and its translate by `texV2 (fracEven w)` over the common columns: the even mirror of
`StackedOrder.odd_order_all`. The column intervals come from the row form of the odd tile of the swapped word
(`StackedEvenColumns.even_column_iff`), the adjacency from the row overlap, the disjointness from `even_hdisj_neg2`, and the base
at column `1` from the lower link of the bottom walk and the cell half-turn about `halfTurnCentre (evenTile w)`. -/

namespace FLatticePaper.Tiles.StackedEvenOrder

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.BaseCellIdentities FLatticePaper.Tiles.OverlapSides

/-- The lower end of the cells of the even tile over a column `t`, read off the row form of the odd tile of the swapped word. -/
def evLo (w : Word) (a : GInt) (t : ℤ) : ℤ :=
  -Nrow (0, 0) (oddBottom (swapW w)) (oddRight (swapW w)) (t - a.2) - a.1

/-- The upper end of the cells of the even tile over a column `t`. -/
def evHi (w : Word) (a : GInt) (t : ℤ) : ℤ :=
  -Srow (0, 0) (oddBottom (swapW w)) (oddRight (swapW w)) (t - a.2) - 1 - a.1

theorem evCol_iff (w : Word) (a : GInt) (hrot : rot (evenTile w) = shift (oddTile (swapW w)) a) (t y : ℤ) :
    ((t, y) : GInt) ∈ cellTileOf (evenTile w) ↔
      (0 ≤ t - a.2 ∧ t - a.2 < (cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w)))) ∧ evLo w a t ≤ y ∧ y ≤ evHi w a t := by
  rw [FLatticePaper.Tiles.StackedEvenColumns.even_column_iff w a hrot t y]
  unfold evLo evHi
  constructor
  · rintro ⟨hr, h1, h2⟩
    exact ⟨hr, by omega, by omega⟩
  · rintro ⟨hr, h1, h2⟩
    exact ⟨hr, by omega, by omega⟩

theorem evCol_nonempty (w : Word) (a : GInt) (t : ℤ)
    (hr : 0 ≤ t - a.2 ∧ t - a.2 < (cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w)))) : evLo w a t ≤ evHi w a t := by
  have hne := rows_nonempty (OverlapSides.boundary_odd (swapW w))
    (StandardBoundary.admissible_oddStandard (swapW w)).1.1
    (OverlapSides.letters_w2 (StandardBoundary.admissible_oddStandard (swapW w)).2) (t - a.2) hr.1 hr.2
  unfold evLo evHi
  omega

theorem evCol_adj (w : Word) (a : GInt) (s : ℤ)
    (hs : 0 ≤ s - a.2 ∧ s - a.2 < (cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w)))) (hs1 : 0 ≤ s + 1 - a.2 ∧ s + 1 - a.2 < (cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w)))) :
    evLo w a (s + 1) ≤ evHi w a s ∧ evLo w a s ≤ evHi w a (s + 1) := by
  have hov := row_overlap (OverlapSides.boundary_odd (swapW w)) (StandardAll.simpleOdd_all (swapW w)).2
    (StandardBoundary.admissible_oddStandard (swapW w)).1.1
    (OverlapSides.letters_w2 (StandardBoundary.admissible_oddStandard (swapW w)).2) (t := s - a.2) hs.1 (by omega)
  have e1 : s + 1 - a.2 = s - a.2 + 1 := by ring
  unfold evLo evHi
  rw [e1]
  omega

/-- The cell half-turn of the even standard tile: the even analogue of `StackedBase.cell_halfTurn_mem`. -/
theorem cell_halfTurn_even (w : Word) (x y : Int) (hc : ((x, y) : GInt) ∈ cellTileOf (evenTile w)) :
    (((halfTurnCentre (evenTile w)).1 - x - 1, (halfTurnCentre (evenTile w)).2 - y - 1) : GInt) ∈
      cellTileOf (evenTile w) := by
  have hT : ∀ z : GInt, z ∈ evenTile w →
      (((halfTurnCentre (evenTile w)).1 - z.1, (halfTurnCentre (evenTile w)).2 - z.2) : GInt) ∈ evenTile w :=
    fun z hz => MarksIn.halfTurn_evenTile w z hz
  obtain ⟨-, hsub⟩ := (mem_cellTileOf _ _).1 hc
  rw [cellCorners_subset_iff] at hsub
  obtain ⟨h0, h1, h2, h3⟩ := hsub
  rw [mem_cellTileOf]
  refine ⟨?_, ?_⟩
  · have := hT (x + 1, y + 1) h3
    convert this using 2 <;> ring
  · rw [cellCorners_subset_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := hT (x + 1, y + 1) h3
      convert this using 2 <;> ring
    · have := hT (x, y + 1) h2
      convert this using 2 <;> ring
    · have := hT (x + 1, y) h1
      convert this using 2 <;> ring
    · have := hT (x, y) h0
      convert this using 2 <;> ring

/-- The even bottom word ends with the horizontal unit step. -/
theorem evenBottom_snoc (w : Word) : ∃ u : F2Word, evenBottom w = u ++ [Unit4.one] :=
  ⟨_, FLatticePaper.Tiles.RegisterLink.evenBottom_eq_gH w⟩

/-- The sum of the even bottom word: its first coordinate is the denominator and its second is the numerator minus one. -/
theorem evenBottom_sum (w : Word) :
    (F2Word.sum (evenBottom w)).1 = (fracEven w).den ∧ (F2Word.sum (evenBottom w)).2 = (fracEven w).num - 1 := by
  have e := sum_evenBottom w
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  simp [almostV₁, gI, texV1Even] at e1 e2
  constructor <;> omega

/-- The lower bound of the even cells over column `1`, at height `0` or above. -/
theorem even_column_one_low (w : Word) (y : ℤ) (hc : ((1, y) : GInt) ∈ cellTileOf (evenTile w)) : 0 ≤ y := by
  have hsite : ((1, y) : GInt) ∈ evenTile w := ((mem_cellTileOf _ _).1 hc).1
  have hn : 0 < (fracEven w).num ∧ (fracEven w).num < (fracEven w).den :=
    FLatticePaper.Tiles.SiteHullEven.curE_pos_lt w
  have hE := evenBottom_sum w
  have hwb : ∀ x ∈ evenBottom w, x = Unit4.one ∨ x = Unit4.i := (admissible_evenStandard w).1.1
  obtain ⟨h, hh, hmem⟩ := FLatticePaper.Tiles.StackedEvenColumns.even_lower_link w (1, y) hsite 1 rfl (by norm_num)
    (by omega)
  have hw := (FLatticePaper.Tiles.StackedWalks.walk_ge_start (evenBottom w) hwb (0, 0) _ hmem).2
  have h0 : (0 : ℤ) ≤ h := by simpa using hw
  omega

/-- The upper bound of the even cells over the column `1 + v.1`, at height `v.2 - 1` or below. -/
theorem even_column_one_high (w : Word) (y : ℤ)
    (hc : ((1 + (texV2 (fracEven w)).1, y + (texV2 (fracEven w)).2) : GInt) ∈ cellTileOf (evenTile w)) : y ≤ -1 := by
  obtain ⟨u, hu⟩ := evenBottom_snoc w
  have hC : halfTurnCentre (evenTile w) = ((fracEven w).num + 1, 2 * (fracEven w).num + (fracEven w).den - 1) :=
    SiteHullEven.centre_even w
  have hE := evenBottom_sum w
  have hm := cell_halfTurn_even w (1 + (texV2 (fracEven w)).1) (y + (texV2 (fracEven w)).2) hc
  have hm' : (((F2Word.sum (evenBottom w)).1 - 1, (halfTurnCentre (evenTile w)).2 - (y + (texV2 (fracEven w)).2) - 1) : GInt) ∈
      cellTileOf (evenTile w) := by
    have hC1 : (halfTurnCentre (evenTile w)).1 = (fracEven w).num + 1 := by rw [hC]
    have hv : (texV2 (fracEven w)).1 = (fracEven w).num - (fracEven w).den := rfl
    have e1 : (halfTurnCentre (evenTile w)).1 - (1 + (texV2 (fracEven w)).1) - 1 = (F2Word.sum (evenBottom w)).1 - 1 := by
      omega
    rw [← e1]
    exact hm
  have hab := FLatticePaper.Tiles.StackedBaseColumn.cell_above_end (evenTile w) (evenBottom w) (evenRight w) u
    (OverlapSides.boundary_even w) (admissible_evenStandard w).1.1
    (OverlapSides.letters_w2 (admissible_evenStandard w).2) hu _ hm'
  have hC2 : (halfTurnCentre (evenTile w)).2 = 2 * (fracEven w).num + (fracEven w).den - 1 := by
    rw [hC]
  have hv2 : (texV2 (fracEven w)).2 = (fracEven w).num + (fracEven w).den := rfl
  rw [hC2, hv2] at hab
  omega

/-- **The order of the even tile and its translate, with the base at column `1` given.** -/
theorem even_order (w : Word) (a : GInt) (hrot : rot (evenTile w) = shift (oddTile (swapW w)) a)
    (h1 : ∃ y : ℤ, ((1, y) : GInt) ∈ cellTileOf (evenTile w))
    (h2 : ∃ y : ℤ, ((1 + (texV2 (fracEven w)).1, y) : GInt) ∈ cellTileOf (evenTile w)) :
    ∀ t y y' : ℤ, ((t + (texV2 (fracEven w)).1, y + (texV2 (fracEven w)).2) : GInt) ∈ cellTileOf (evenTile w) →
      ((t, y') : GInt) ∈ cellTileOf (evenTile w) → y < y' := by
  obtain ⟨y1, hy1⟩ := h1
  obtain ⟨y2, hy2⟩ := h2
  obtain ⟨⟨R1a, R1b⟩, -, -⟩ := (evCol_iff w a hrot 1 y1).1 hy1
  obtain ⟨⟨R2a, R2b⟩, -, -⟩ := (evCol_iff w a hrot (1 + (texV2 (fracEven w)).1) y2).1 hy2
  obtain ⟨p, hpR⟩ : ∃ p : ℤ, ∀ t, p ≤ t ↔ (a.2 ≤ t ∧ a.2 - (texV2 (fracEven w)).1 ≤ t) :=
    ⟨max a.2 (a.2 - (texV2 (fracEven w)).1), fun t => max_le_iff⟩
  obtain ⟨q, hqR⟩ : ∃ q : ℤ, ∀ t, t ≤ q ↔ (t ≤ a.2 + (cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w))) - 1 ∧ t ≤ a.2 + (cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w))) - 1 - (texV2 (fracEven w)).1) :=
    ⟨min (a.2 + (cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w))) - 1) (a.2 + (cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w))) - 1 - (texV2 (fracEven w)).1), fun t => le_min_iff⟩
  have hp1 : p ≤ 1 := (hpR 1).2 ⟨by omega, by omega⟩
  have hq1 : 1 ≤ q := (hqR 1).2 ⟨by omega, by omega⟩
  have hrange : ∀ t, p ≤ t → t ≤ q →
      (0 ≤ t - a.2 ∧ t - a.2 < (cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w)))) ∧ (0 ≤ t + (texV2 (fracEven w)).1 - a.2 ∧ t + (texV2 (fracEven w)).1 - a.2 < (cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w)))) := by
    intro t ht1 ht2
    obtain ⟨ha1, ha2⟩ := (hpR t).1 ht1
    obtain ⟨hb1, hb2⟩ := (hqR t).1 ht2
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hlo1 : 0 ≤ evLo w a 1 := by
    have hm : ((1, evLo w a 1) : GInt) ∈ cellTileOf (evenTile w) :=
      (evCol_iff w a hrot 1 (evLo w a 1)).2 ⟨⟨R1a, R1b⟩, le_rfl, evCol_nonempty w a 1 ⟨R1a, R1b⟩⟩
    exact even_column_one_low w _ hm
  have hhi1 : evHi w a (1 + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2 ≤ -1 := by
    have hm : ((1 + (texV2 (fracEven w)).1, evHi w a (1 + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2 + (texV2 (fracEven w)).2) : GInt) ∈ cellTileOf (evenTile w) := by
      rw [sub_add_cancel]
      exact (evCol_iff w a hrot (1 + (texV2 (fracEven w)).1) (evHi w a (1 + (texV2 (fracEven w)).1))).2
        ⟨⟨R2a, R2b⟩, evCol_nonempty w a (1 + (texV2 (fracEven w)).1) ⟨R2a, R2b⟩, le_rfl⟩
    exact even_column_one_high w _ hm
  have hb : evHi w a (1 + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2 < evLo w a 1 := by omega
  have hT : ∀ t, p ≤ t → t < q →
      evLo w a (t + 1) ≤ evHi w a t ∧ evLo w a t ≤ evHi w a (t + 1) := by
    intro t ht1 ht2
    obtain ⟨hA, -⟩ := hrange t ht1 (by omega)
    obtain ⟨hB, -⟩ := hrange (t + 1) (by omega) (by omega)
    exact evCol_adj w a t hA hB
  have hS : ∀ t, p ≤ t → t < q →
      evLo w a (t + 1 + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2 ≤ evHi w a (t + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2 ∧
        evLo w a (t + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2 ≤ evHi w a (t + 1 + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2 := by
    intro t ht1 ht2
    obtain ⟨-, hC⟩ := hrange t ht1 (by omega)
    obtain ⟨-, hD⟩ := hrange (t + 1) (by omega) (by omega)
    have hC1 : 0 ≤ t + (texV2 (fracEven w)).1 + 1 - a.2 ∧ t + (texV2 (fracEven w)).1 + 1 - a.2 < (cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w))) := by
      constructor <;> omega
    have hadj := evCol_adj w a (t + (texV2 (fracEven w)).1) hC hC1
    rw [show t + 1 + (texV2 (fracEven w)).1 = t + (texV2 (fracEven w)).1 + 1 by ring]
    constructor <;> omega
  have hd : ∀ t, p ≤ t → t ≤ q →
      evHi w a (t + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2 < evLo w a t ∨ evHi w a t < evLo w a (t + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2 := by
    intro t ht1 ht2
    obtain ⟨hA, hC⟩ := hrange t ht1 ht2
    by_contra hcon
    push_neg at hcon
    obtain ⟨c1, c2⟩ := hcon
    have hne1 := evCol_nonempty w a t hA
    have hne2 := evCol_nonempty w a (t + (texV2 (fracEven w)).1) hC
    obtain ⟨y0, hy0⟩ : ∃ y0 : ℤ, y0 = max (evLo w a t) (evLo w a (t + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2) := ⟨_, rfl⟩
    have hy0a : evLo w a t ≤ y0 := by rw [hy0]; exact le_max_left _ _
    have hy0b : evLo w a (t + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2 ≤ y0 := by rw [hy0]; exact le_max_right _ _
    have hy0c : y0 ≤ evHi w a t := by rw [hy0]; exact max_le hne1 c2
    have hy0d : y0 ≤ evHi w a (t + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2 := by rw [hy0]; exact max_le c1 (by omega)
    have hA' : ((t, y0) : GInt) ∈ cellTileOf (evenTile w) :=
      (evCol_iff w a hrot t y0).2 ⟨hA, hy0a, hy0c⟩
    have hB' : ((t + (texV2 (fracEven w)).1, y0 + (texV2 (fracEven w)).2) : GInt) ∈ cellTileOf (evenTile w) :=
      (evCol_iff w a hrot (t + (texV2 (fracEven w)).1) (y0 + (texV2 (fracEven w)).2)).2 ⟨hC, by omega, by omega⟩
    have hneg : ((t, y0) : GInt) - -(texV2 (fracEven w)) = ((t + (texV2 (fracEven w)).1, y0 + (texV2 (fracEven w)).2) : GInt) := by
      ext <;> simp [sub_neg_eq_add]
    exact even_hdisj_neg2 w (t, y0) hA' (by rw [hneg]; exact hB')
  have key := FLatticePaper.Tiles.StackedOrder.order_interval (fun t => evLo w a t) (fun t => evHi w a t)
    (fun t => evLo w a (t + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2) (fun t => evHi w a (t + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2) p q hp1 hq1 hT hS hd hb
  intro t y y' hS' hT'
  obtain ⟨⟨hr2a, hr2b⟩, hl2, hh2⟩ := (evCol_iff w a hrot (t + (texV2 (fracEven w)).1) (y + (texV2 (fracEven w)).2)).1 hS'
  obtain ⟨⟨hr1a, hr1b⟩, hl1, hh1⟩ := (evCol_iff w a hrot t y').1 hT'
  have hpt : p ≤ t := (hpR t).2 ⟨by omega, by omega⟩
  have htq : t ≤ q := (hqR t).2 ⟨by omega, by omega⟩
  have hk : evHi w a (t + (texV2 (fracEven w)).1) - (texV2 (fracEven w)).2 < evLo w a t := key t hpt htq
  omega

/-- **The order of the even tile and its translate, with no remaining input.** Every cell of `T - v` over a column `t` lies
strictly below every cell of `T` over `t`, for `v = texV2 (fracEven w)`. -/
theorem even_order_all (w : Word) :
    ∀ t y y' : ℤ, ((t + (texV2 (fracEven w)).1, y + (texV2 (fracEven w)).2) : GInt) ∈ cellTileOf (evenTile w) →
      ((t, y') : GInt) ∈ cellTileOf (evenTile w) → y < y' := by
  obtain ⟨a, ha⟩ : ∃ a : GInt, a = tF (fracEven w) := ⟨_, rfl⟩
  have hrot : rot (evenTile w) = shift (oddTile (swapW w)) a := by
    rw [ha]; exact (rot_standard_tiles w).2
  obtain ⟨hn1, hn2⟩ : 0 < (fracEven w).num ∧ (fracEven w).num < (fracEven w).den :=
    FLatticePaper.Tiles.SiteHullEven.curE_pos_lt w
  have hv1 : (texV2 (fracEven w)).1 = (fracEven w).num - (fracEven w).den := rfl
  have hA2 : a.2 = (texV2 (fracEven w)).1 + 1 := by
    rw [ha]
    show (fracEven w).num + 1 - (fracEven w).den = (texV2 (fracEven w)).1 + 1
    rw [hv1]
    ring
  have hE := evenBottom_sum w
  have hC : halfTurnCentre (evenTile w) = ((fracEven w).num + 1, 2 * (fracEven w).num + (fracEven w).den - 1) :=
    SiteHullEven.centre_even w
  have hC1 : (halfTurnCentre (evenTile w)).1 = (fracEven w).num + 1 := by rw [hC]
  have hcnt : 1 ≤ cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w)) := by
    have h2 := cntI_w2_pos (StandardBoundary.admissible_oddStandard (swapW w)).2
    have h1 := cntI_nonneg (oddBottom (swapW w))
    omega
  have hm : ((a.2, evLo w a a.2) : GInt) ∈ cellTileOf (evenTile w) :=
    (evCol_iff w a hrot a.2 (evLo w a a.2)).2
      ⟨⟨by omega, by omega⟩, le_rfl, evCol_nonempty w a a.2 ⟨by omega, by omega⟩⟩
  have hmir := cell_halfTurn_even w a.2 (evLo w a a.2) hm
  have hM : ((fracEven w).den - 1, (halfTurnCentre (evenTile w)).2 - evLo w a a.2 - 1) ∈
      cellTileOf (evenTile w) := by
    have e : (halfTurnCentre (evenTile w)).1 - a.2 - 1 = (fracEven w).den - 1 := by omega
    rw [← e]
    exact hmir
  have hMr := (evCol_iff w a hrot _ _).1 hM
  have h1 : ∃ y : ℤ, ((1, y) : GInt) ∈ cellTileOf (evenTile w) :=
    ⟨evLo w a 1, (evCol_iff w a hrot 1 (evLo w a 1)).2
      ⟨⟨by omega, by omega⟩, le_rfl, evCol_nonempty w a 1 ⟨by omega, by omega⟩⟩⟩
  have h2 : ∃ y : ℤ, ((1 + (texV2 (fracEven w)).1, y) : GInt) ∈ cellTileOf (evenTile w) :=
    ⟨evLo w a (1 + (texV2 (fracEven w)).1),
      (evCol_iff w a hrot (1 + (texV2 (fracEven w)).1) (evLo w a (1 + (texV2 (fracEven w)).1))).2
        ⟨⟨by omega, by omega⟩, le_rfl, evCol_nonempty w a (1 + (texV2 (fracEven w)).1) ⟨by omega, by omega⟩⟩⟩
  exact even_order w a hrot h1 h2

end FLatticePaper.Tiles.StackedEvenOrder
