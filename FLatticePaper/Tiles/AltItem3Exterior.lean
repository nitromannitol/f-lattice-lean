import FLatticePaper.Tiles.AltItem3Strings
import FLatticePaper.Tiles.AltItem4Tools
import FLatticePaper.Tiles.StackedEvenBound

/-! # Item (3) of `lemma:alternate_tile_properties`: the placed paths stay on the exterior

The correction of the referee report on E34 to the proof of (3): for consecutive vertices `x, x + u` of the bottom edge
`G(w_h(s))` of `T(s)`, `s = q₀`, `u ∈ {1, i}`, the vertex `z = x + 1 - i` (`u = 1`) or `z = x + 1` (`u = i`) is not in `T̂(s)`,
so the unit square `s_{z-1}` on the right of the step is not in `T̂(s)`: the forward horizontal path of `T̂(s)` (which starts at
`c(T̂) = c(T(s)) = 0` with the same word) stays on its exterior.

* `z ∉ T(s)`: the cell rows of `T(s)` (`OverlapSides.corner_row`) end at the north columns of the bottom word, and the north
  column of the row of `x` is `x₁` after an `i` step (`walk_up_col`) and at most `x₁` below the row of `x` (`walk_east_col`);
* `L_s(z) < 0`: `z` is not in the closed form `H_s` of `T(s)` while its neighbour on the path is, and of the four inequalities of
  `H_s` only the lower bound of `L_s` can fail there (`east_L`, `up_L`);
* so `z ∉ T̂(s)` by `(B2)` (`AltItem4.even_far_points`). -/

namespace FLatticePaper.Tiles.AltItem3

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.SiteInduction (InH tCo sCo aOf lOf tOf)

/-! ### North columns along a walk in `1` and `i` -/

theorem walk_eq_cons (c : GInt) (u : F2Word) : F2Word.walk c u = c :: (F2Word.walk c u).tail := by
  cases u with
  | nil => simp [WalkDecomp.walk_nil]
  | cons x u => simp [WalkDecomp.walk_cons]

theorem zip_walk_cons (c : GInt) (x : Unit4) (u : F2Word) :
    (F2Word.walk c (x :: u)).zip (F2Word.walk c (x :: u)).tail =
      (c, c + x.vec) :: (F2Word.walk (c + x.vec) u).zip (F2Word.walk (c + x.vec) u).tail := by
  rcases u with _ | ⟨y, u⟩ <;> simp [WalkDecomp.walk_cons, WalkDecomp.walk_nil]

/-- After a north step at `x`, the north column of the row of `x` is `x₁`. -/
theorem walk_up_col (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) :
    ∀ (p : GInt) (e : GInt × GInt), e ∈ (F2Word.walk p u).zip (F2Word.walk p u).tail → e.2 = e.1 + (0, 1) →
      colN u p e.1.2 = e.1.1 := by
  induction u with
  | nil => intro p e he; simp [WalkDecomp.walk_nil] at he
  | cons x u ih =>
    intro p e he hstep
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .one ∨ y = .i := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    rw [zip_walk_cons, List.mem_cons] at he
    rcases he with rfl | he
    · rcases hx with rfl | rfl
      · simp [Unit4.vec] at hstep
      · simp [colN]
    · have h1 := (CellExtremes.walk_range_one_i u hu' (p + x.vec) e.1 (List.of_mem_zip he).1)
      have hc := ih hu' (p + x.vec) e he hstep
      rcases hx with rfl | rfl
      · simp only [colN, reduceCtorEq, false_and, if_false]; exact hc
      · simp only [Unit4.vec, Prod.snd_add] at h1
        simp only [colN, true_and]
        rw [if_neg (by omega)]
        exact hc

/-- Below the row of a point `x` of the walk, the north column is at most `x₁`. -/
theorem walk_east_col (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) :
    ∀ (p x : GInt), x ∈ F2Word.walk p u → p.2 < x.2 → colN u p (x.2 - 1) ≤ x.1 := by
  induction u with
  | nil => intro p x hx hlt; simp [WalkDecomp.walk_nil] at hx; subst hx; omega
  | cons y u ih =>
    intro p x hx hlt
    have hy := hu y (List.mem_cons_self ..)
    have hu' : ∀ z ∈ u, z = .one ∨ z = .i := fun z hz => hu z (List.mem_cons_of_mem _ hz)
    rw [WalkDecomp.walk_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have hr := CellExtremes.walk_range_one_i u hu' (p + y.vec) x hx
      rcases hy with rfl | rfl
      · simp only [Unit4.vec, Prod.fst_add, Prod.snd_add, add_zero] at hr
        simp only [colN, reduceCtorEq, false_and, if_false]
        exact ih hu' _ x hx (by simp [Unit4.vec]; omega)
      · simp only [Unit4.vec, Prod.fst_add, Prod.snd_add, add_zero] at hr
        simp only [colN, true_and]
        by_cases h : p.2 = x.2 - 1
        · rw [if_pos h]; omega
        · rw [if_neg h]; exact ih hu' _ x hx (by simp [Unit4.vec]; omega)

/-! ### The vertex outside the step is not in `T(s)` -/

theorem bottom_letters (w : Word) : ∀ x ∈ StandardBoundary.evenBottom w, x = .one ∨ x = .i :=
  (StandardBoundary.admissible_evenStandard w).1.1

theorem notMem_east (w : Word) (x : GInt) (e : GInt × GInt)
    (he : e ∈ (F2Word.walk 0 (StandardBoundary.evenBottom w)).zip (F2Word.walk 0 (StandardBoundary.evenBottom w)).tail)
    (h1 : e.1 = x) (_hstep : e.2 = x + (1, 0)) : x + (1, -1) ∉ evenTile w := by
  intro hz
  have h1w := bottom_letters w
  have h2w := OverlapSides.letters_w2 (StandardBoundary.admissible_evenStandard w).2
  obtain ⟨c, hc, hzc⟩ := OverlapSides.corner_of_hcc (Standard.evenTile_hcc w) hz
  obtain ⟨t, ht, ht0, -, -, hN⟩ := OverlapSides.corner_row (OverlapSides.boundary_even w) h1w h2w hc hzc
  have hxw : x ∈ F2Word.walk (0, 0) (StandardBoundary.evenBottom w) := h1 ▸ (List.of_mem_zip he).1
  have hr := CellExtremes.walk_range_one_i _ h1w (0, 0) x hxw
  simp only [Prod.fst_add, Prod.snd_add] at ht hN hr
  have hlt : t < cntI (StandardBoundary.evenBottom w) := by omega
  rw [OverlapSides.nrow_lo hlt] at hN
  have hm := OverlapSides.colN_mono _ h1w t (x.2 - 1) ht0 (by omega)
  have hE := walk_east_col _ h1w (0, 0) x hxw (by simp; omega)
  omega

theorem notMem_up (w : Word) (x : GInt) (e : GInt × GInt)
    (he : e ∈ (F2Word.walk 0 (StandardBoundary.evenBottom w)).zip (F2Word.walk 0 (StandardBoundary.evenBottom w)).tail)
    (h1 : e.1 = x) (hstep : e.2 = x + (0, 1)) : x + (1, 0) ∉ evenTile w := by
  intro hz
  have h1w := bottom_letters w
  have h2w := OverlapSides.letters_w2 (StandardBoundary.admissible_evenStandard w).2
  obtain ⟨c, hc, hzc⟩ := OverlapSides.corner_of_hcc (Standard.evenTile_hcc w) hz
  obtain ⟨t, ht, ht0, -, -, hN⟩ := OverlapSides.corner_row (OverlapSides.boundary_even w) h1w h2w hc hzc
  have hyw : e.2 ∈ F2Word.walk (0, 0) (StandardBoundary.evenBottom w) := (List.mem_of_mem_tail (List.of_mem_zip he).2)
  have hr := CellExtremes.walk_range_one_i _ h1w (0, 0) e.2 hyw
  rw [hstep] at hr
  simp only [Prod.fst_add, Prod.snd_add] at ht hN hr
  have hlt : t < cntI (StandardBoundary.evenBottom w) := by omega
  rw [OverlapSides.nrow_lo hlt] at hN
  have hm := OverlapSides.colN_mono _ h1w t x.2 ht0 (by omega)
  have hU := walk_up_col _ h1w (0, 0) e he (by rw [hstep, h1])
  rw [h1] at hU
  omega

/-! ### `L_s < 0` at the vertex outside the step -/

theorem aOf_bounds (f : Fraction) (hf : 0 < f.num ∧ f.num < f.den) (b b' : Bool) :
    0 ≤ aOf f b ∧ aOf f b ≤ f.den - 1 ∧ aOf f b ≤ aOf f b' + f.num := by
  cases b <;> cases b' <;> simp only [aOf, if_true, if_false, Bool.false_eq_true] <;>
    refine ⟨?_, ?_, ?_⟩ <;> omega

theorem lOf_bounds (f : Fraction) (hf : 0 < f.num ∧ f.num < f.den) (b b' : Bool) :
    lOf f b ≤ 2 * f.num ∧ lOf f b ≤ f.den - f.num ∧ lOf f b ≤ lOf f b' + (f.den - f.num) := by
  cases b <;> cases b' <;> simp only [lOf, if_true, if_false, Bool.false_eq_true] <;>
    refine ⟨?_, ?_, ?_⟩ <;> omega

/-- After an east step to `y`, the vertex `y - i` outside the closed form has `L < 0`. -/
theorem east_L (f : Fraction) (hf : 0 < f.num ∧ f.num < f.den) (y : Site) (hy1 : 1 ≤ y.1) (hy2 : 0 ≤ y.2)
    (hy : InH f y) (hz : ¬ InH f (y - (0, 1))) : f.den * (y - (0, 1)).2 - f.num * (y - (0, 1)).1 < 0 := by
  unfold SiteInduction.InH at hy hz
  generalize decide ((y.1 + y.2) % 2 = 0) = by' at hy
  generalize decide (((y - (0, 1)).1 + (y - (0, 1)).2) % 2 = 0) = bz at hz
  obtain ⟨i1, i2, i3, i4⟩ := hy
  obtain ⟨a0, a1, a2⟩ := aOf_bounds f hf bz by'
  obtain ⟨l0, l1, l2⟩ := lOf_bounds f hf bz by'
  have hmu : 1 ≤ SiteInduction.muOf f := by unfold SiteInduction.muOf; split_ifs <;> norm_num
  have hT : 0 < tOf f := by unfold tOf; nlinarith
  simp only [tCo, sCo, Prod.fst_sub, Prod.snd_sub, sub_zero] at hz i1 i2 i3 i4 ⊢
  by_contra hc
  apply hz
  refine ⟨by nlinarith, by nlinarith, ?_, by nlinarith⟩
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ f.den + f.num by omega) (show (0 : ℤ) ≤ y.1 - 1 by omega),
    mul_nonneg (show (0 : ℤ) ≤ f.den - f.num by omega) (show (0 : ℤ) ≤ y.2 by omega)]

/-- After a north step from `x` (`x₂ ≤ n - 2`, `x₁ ≤ d`), the vertex `x + 1` outside the closed form has `L < 0`. -/
theorem up_L (f : Fraction) (hf : 0 < f.num ∧ f.num < f.den) (hmu : SiteInduction.muOf f = 1) (x : Site) (_hx0 : 0 ≤ x.1)
    (hx1 : x.1 ≤ f.den) (hx2 : 0 ≤ x.2) (hx3 : x.2 ≤ f.num - 2)
    (hx : InH f x) (hz : ¬ InH f (x + (1, 0))) : f.den * (x + (1, 0)).2 - f.num * (x + (1, 0)).1 < 0 := by
  unfold SiteInduction.InH at hx hz
  generalize decide ((x.1 + x.2) % 2 = 0) = bx at hx
  generalize decide (((x + (1, 0)).1 + (x + (1, 0)).2) % 2 = 0) = bz at hz
  obtain ⟨i1, i2, i3, i4⟩ := hx
  obtain ⟨a0, a1, a2⟩ := aOf_bounds f hf bz bx
  obtain ⟨l0, l1, l2⟩ := lOf_bounds f hf bz bx
  simp only [tCo, sCo, tOf, hmu, one_mul, Prod.fst_add, Prod.snd_add, add_zero] at hz i1 i2 i3 i4 ⊢
  by_contra hc
  apply hz
  refine ⟨by nlinarith, by nlinarith, by nlinarith, ?_⟩
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ f.den + f.num by omega) (show (0 : ℤ) ≤ f.den - x.1 by omega),
    mul_nonneg (show (0 : ℤ) ≤ f.den - f.num by omega) (show (0 : ℤ) ≤ f.num - 2 - x.2 by omega)]

/-! ### The exterior clause -/

theorem sum_bottom (w : Word) :
    F2Word.sum (StandardBoundary.evenBottom w) = ((SiteInduction.curE w).den, (SiteInduction.curE w).num - 1) := by
  have h := StandardBoundary.sum_evenBottom w
  simp only [almostV₁, texV1Even, gI] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  ext
  · show (F2Word.sum (StandardBoundary.evenBottom w)).1 = (StandardClause.fracEven w).den
    omega
  · show (F2Word.sum (StandardBoundary.evenBottom w)).2 = (StandardClause.fracEven w).num - 1
    omega

/-- **The exterior clause of item (3), even alternate child**: for consecutive vertices `x, x + u` of the bottom path
`G(w_h(q₀))` of `T(q₀)`, which is the path of the forward horizontal string of `T̂(q₀)`, the vertex `x + 1 - i` (`u = 1`) or
`x + 1` (`u = i`) on the right of the step is not in `T̂(q₀)`. -/
theorem item3_exterior {w : Word} (hw : ¬ IsBase w) (e : GInt × GInt)
    (he : e ∈ (F2Word.walk 0 (StandardBoundary.evenBottom w)).zip (F2Word.walk 0 (StandardBoundary.evenBottom w)).tail) :
    (e.2 = e.1 + (1, 0) → e.1 + (1, -1) ∉ altEvenTile AltRotStep.B w) ∧
      (e.2 = e.1 + (0, 1) → e.1 + (1, 0) ∉ altEvenTile AltRotStep.B w) := by
  have hpos := SiteHullEven.curE_pos_lt w
  have hmu : SiteInduction.muOf (SiteInduction.curE w) = 1 :=
    H3Data.muOf_of_even _ (parentsAt_valid w).current_even_parity
  have hdn : 7 ≤ (SiteInduction.curE w).den + (SiteInduction.curE w).num := by
    obtain ⟨a1, a2, a3, a4, -⟩ := AltPieces.parents_facts hw
    simp only [SiteInduction.curE, Parents.current, Parents.combine]; omega
  have h1w := bottom_letters w
  have hS := sum_bottom w
  have hcnt := sum_snd (StandardBoundary.evenBottom w)
    (fun x hx => by rcases h1w x hx with h | h <;> simp [h])
  rw [hS] at hcnt
  simp only at hcnt
  have hx := (List.of_mem_zip he).1
  have hy := List.mem_of_mem_tail (List.of_mem_zip he).2
  have rx := CellExtremes.walk_range_one_i _ h1w (0, 0) e.1 hx
  have ry := CellExtremes.walk_range_one_i _ h1w (0, 0) e.2 hy
  rw [hS] at rx ry
  simp only [zero_add] at rx ry
  have tx := (SubEvenCopy.mem_evenTile_iff w _).1 (StackedEvenBound.walk_site_even w _ hx)
  have ty := (SubEvenCopy.mem_evenTile_iff w _).1 (StackedEvenBound.walk_site_even w _ hy)
  refine ⟨fun hstep hzT => ?_, fun hstep hzT => ?_⟩
  · have hz := notMem_east w e.1 e he rfl hstep
    rcases AltItem4.even_far_points hw _ hzT with h | h
    · exact hz h
    · rw [SubEvenCopy.mem_evenTile_iff] at hz
      rw [hstep] at ty ry
      simp only [Prod.fst_add, Prod.snd_add] at ry
      have hL := east_L _ hpos (e.1 + (1, 0)) (by simp; omega) (by simp; omega) ty
        (by convert hz using 2; ext <;> (simp; try ring))
      have e1 : e.1 + (1, 0) - (0, 1) = e.1 + (1, -1) := by ext <;> (simp; try ring)
      rw [e1] at hL
      omega
  · have hz := notMem_up w e.1 e he rfl hstep
    rcases AltItem4.even_far_points hw _ hzT with h | h
    · exact hz h
    · rw [SubEvenCopy.mem_evenTile_iff] at hz
      rw [hstep] at ry
      simp only [Prod.fst_add, Prod.snd_add] at ry
      have hL := up_L _ hpos hmu e.1 (by omega) (by omega) (by omega) (by omega) tx hz
      omega

/-- The unit square on the right of each step of the path is not a cell of `T̂(q₀)`. -/
theorem item3_exterior_cells {w : Word} (hw : ¬ IsBase w) (e : GInt × GInt)
    (he : e ∈ (F2Word.walk 0 (StandardBoundary.evenBottom w)).zip (F2Word.walk 0 (StandardBoundary.evenBottom w)).tail) :
    (e.2 = e.1 + (1, 0) → e.1 - (0, 1) ∉ StandardClause.cellTileOf (altEvenTile AltRotStep.B w)) ∧
      (e.2 = e.1 + (0, 1) → e.1 ∉ StandardClause.cellTileOf (altEvenTile AltRotStep.B w)) := by
  obtain ⟨h1, h2⟩ := item3_exterior hw e he
  refine ⟨fun hs hc => h1 hs ?_, fun hs hc => h2 hs ?_⟩
  · have hc' := (Finset.mem_filter.1 hc).2
    apply hc'
    rw [Standard.mem_cellCorners_iff]
    right; left
    ext <;> (simp [gOne]; try ring)
  · have hc' := (Finset.mem_filter.1 hc).2
    apply hc'
    rw [Standard.mem_cellCorners_iff]
    right; left
    ext <;> simp [gOne]

/-- **The exterior clause for `rev(w_h(q₀))`**, by the half-turn `z ↦ D - z` of `T̂(q₀)`, which maps the path of the forward
string onto the path of the reversed one (`ReflectedCoverConverse.placed_hRev_iff`, `item3_revH`). -/
theorem item3_exterior_rev {w : Word} (hw : ¬ IsBase w) (e : GInt × GInt)
    (he : e ∈ (F2Word.walk 0 (StandardBoundary.evenBottom w)).zip (F2Word.walk 0 (StandardBoundary.evenBottom w)).tail) :
    (e.2 = e.1 + (1, 0) → AltPieces.centreEven (phase w == 1) (parentsAt w).odd (parentsAt w).even - (e.1 + (1, -1)) ∉
        altEvenTile AltRotStep.B w) ∧
      (e.2 = e.1 + (0, 1) → AltPieces.centreEven (phase w == 1) (parentsAt w).odd (parentsAt w).even - (e.1 + (1, 0)) ∉
        altEvenTile AltRotStep.B w) := by
  obtain ⟨h1, h2⟩ := item3_exterior hw e he
  exact ⟨fun hs hz => h1 hs ((AltPieces.altEven_halfTurn w _).2 hz),
    fun hs hz => h2 hs ((AltPieces.altEven_halfTurn w _).2 hz)⟩

/-- **The exterior clause for the odd alternate child**, by the rotation of item (1): `T̂(p₀)` of `w` is the quarter-turn of
`T̂(q₀)` of `swapW w` (`AltRotStep.altRot`), which maps the horizontal paths onto the vertical ones. -/
theorem item3_exterior_odd {w : Word} (hw : ¬ IsBase w) (e : GInt × GInt)
    (he : e ∈ (F2Word.walk 0 (StandardBoundary.evenBottom (Standard.swapW w))).zip
      (F2Word.walk 0 (StandardBoundary.evenBottom (Standard.swapW w))).tail) :
    (e.2 = e.1 + (1, 0) →
        mulI (e.1 + (1, -1)) + AltRotStep.tauE (Standard.swapW w) ∉ altOddTile AltRotStep.B w) ∧
      (e.2 = e.1 + (0, 1) →
        mulI (e.1 + (1, 0)) + AltRotStep.tauE (Standard.swapW w) ∉ altOddTile AltRotStep.B w) := by
  have hR := (AltRotStep.altRot (Standard.swapW w)).2
  rw [AltRotStep.swapW_swapW] at hR
  obtain ⟨h1, h2⟩ := item3_exterior (Standard.nonbase_swap hw) e he
  have key : ∀ z : GInt, z ∉ altEvenTile AltRotStep.B (Standard.swapW w) →
      mulI z + AltRotStep.tauE (Standard.swapW w) ∉ altOddTile AltRotStep.B w := by
    intro z hz hm
    rw [← hR, mem_shift, Standard.mem_rot] at hm
    apply hz
    convert hm using 1
    ext <;> simp [mulI]
  exact ⟨fun hs => key _ (h1 hs), fun hs => key _ (h2 hs)⟩

end FLatticePaper.Tiles.AltItem3
