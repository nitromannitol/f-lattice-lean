import FLatticePaper.Tiles.SameParentCopies
import FLatticePaper.Tiles.TileStepAssembly
import FLatticePaper.Tiles.MixedCompatGeneral
import FLatticePaper.Tiles.MixedFromCells
import FLatticePaper.Tiles.AltItem5

/-! # Local compatibility of the full copies of the corrected tile decompositions

`stdPairCompat_paper`: `TileStepAssembly.StdPairCompatInput` for the paper data. In a corrected decomposition two entries that are
not L-corrections are either copies of different parents, whose difference is constant on the marks
(`MixedCompatGeneral.mixedCompatInput`, `MixedCompatGeneral.alt_mixed`) and whose common points lie in the marks (item (d) of
`lemma:standard_tile_properties`, `MixedFromCells.mixedOdd_all`, `mixedEven_all`; item (5) of `lemma:alternate_tile_properties`,
`AltItem5.item5_marks_odd`, `item5_marks_even`), or copies of one parent, which do not meet (`SameParentCopies`). -/

namespace FLatticePaper.Tiles.StdPairCompatPaper

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow regsAt_lt)
open FLatticePaper.Tiles.JointGlue (pieceVal)
open FLatticePaper.Tiles.TileCompatInputs (PairCompat oddLIdx evenLIdx altOddLIdx altEvenLIdx)
open FLatticePaper.Tiles.TileStepAssembly
open FLatticePaper.Tiles.Standard (IsBase oddTile evenTile stateAt)
open FLatticePaper.Tiles.SurgicalWeak (regOdo regsAt)
open FLatticePaper.Tiles.ChildGlue (oddP oddQ evenP evenQ)
open FLatticePaper.Tiles.ClosedPathAssembly (placedOdd placedEven affOdd affEven)
open FLatticePaper.Tiles.ClosedPathSum (dot2)
open FLatticePaper.Tiles.SurgicalDict (offsetP0 offsetQ0)

/-! ### Pairs of entries -/

theorem sub_mem_placed {p : Piece} {x : Site} (h : x ∈ p.placed) : x - p.off ∈ p.odo.dom := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
  simpa using hy

/-- Two entries that never meet are compatible. -/
theorem pairCompat_of_disj {ps : List Piece} {i j : ℕ} {P Q : PartialOdometer} {a b s t : Site}
    (hi : ps[i]? = some (stdPiece P a s)) (hj : ps[j]? = some (stdPiece Q b t))
    (h : ∀ x, x - a ∈ P.dom → x - b ∈ Q.dom → False) : PairCompat ps i j := by
  intro p q hp hq
  rw [hi, Option.some.injEq] at hp
  rw [hj, Option.some.injEq] at hq
  subst hp hq
  exact ⟨0, fun x hx hx' _ _ => (h x (sub_mem_placed hx) (sub_mem_placed hx')).elim⟩

/-- Two entries whose values differ by a constant on their common points are compatible. -/
theorem pairCompat_of_const {ps : List Piece} {i j : ℕ} {P Q : PartialOdometer} {a b s t : Site}
    (hi : ps[i]? = some (stdPiece P a s)) (hj : ps[j]? = some (stdPiece Q b t)) (C : ℤ)
    (h : ∀ x, x - a ∈ P.dom → x - b ∈ Q.dom → P.val (x - a) + dot2 s x - (Q.val (x - b) + dot2 t x) = C) :
    PairCompat ps i j := by
  intro p q hp hq
  rw [hi, Option.some.injEq] at hp
  rw [hj, Option.some.injEq] at hq
  subst hp hq
  exact ⟨C, fun x hx hx' _ _ => h x (sub_mem_placed hx) (sub_mem_placed hx')⟩

/-- `PairCompat` for the entries outside `L` of a six-entry decomposition, from the pairs `i < j < 6`. -/
theorem pairs6 (ps : List Piece) (hlen : ps.length = 6) (L : List ℕ)
    (hp : ∀ i j, i < j → j < 6 → i ∉ L → j ∉ L → PairCompat ps i j) : ∀ i j, i ∉ L → j ∉ L → PairCompat ps i j := by
  intro i j hi hj
  rcases lt_trichotomy i j with h | rfl | h
  · by_cases hj6 : j < 6
    · exact hp i j h hj6 hi hj
    · exact pairCompat_of_none_right (by rw [List.getElem?_eq_none_iff]; omega)
  · exact pairCompat_refl ps i
  · by_cases hi6 : i < 6
    · exact pairCompat_symm (hp j i h hi6 hj hi)
    · exact pairCompat_of_none_left (by rw [List.getElem?_eq_none_iff]; omega)

/-! ### The data of a non-base word -/

/-- The registers of a non-base word, their tiles and the domains of their tile odometers. -/
theorem regs_data (D : JointData) (hS : D.S = WeakStepPaper.paperS) (f : Word → JSlice) (w : Word)
    (hG : GoodBelow D f w.length) (hb : ¬ IsBase w) :
    ∃ u1 u2 : Word, regsAt w = (some u1, some u2) ∧ u1.length < w.length ∧ u2.length < w.length ∧
      (f u1).tOdd.dom = oddTile u1 ∧ (f u2).tEven.dom = evenTile u2 ∧
      SiteInduction.curO u1 = (parentsAt w).odd ∧ SiteInduction.curE u2 = (parentsAt w).even ∧
      (stateAt w).tOdd = oddTile u1 ∧ (stateAt w).tEven = evenTile u2 := by
  obtain ⟨u1, u2, hr⟩ := WeakStepAssembly.regsAt_nonbase w hb
  have hl1 : u1.length < w.length := regsAt_lt w u1 (Or.inl (by rw [hr]))
  have hl2 : u2.length < w.length := regsAt_lt w u2 (Or.inr (by rw [hr]))
  refine ⟨u1, u2, hr, hl1, hl2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(WeakStepAssembly.slice_domains D f u1 (hG u1 hl1).1).1, hS]; rfl
  · rw [(WeakStepAssembly.slice_domains D f u2 (hG u2 hl2).1).2, hS]; rfl
  · exact ((WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hr])).symm
  · exact ((WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hr])).symm
  · exact (WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hr])
  · exact (WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hr])

theorem w1Odd_of {w : Word} (h : phase w = 1) : W1Odd w = true := by simp [W1Odd, h]

theorem w1Odd_ef {w : Word} (h : phase w ≠ 1) : W1Odd w = false := by simp [W1Odd, h]

theorem mem_shift_tile {T : Finset Site} {a x : Site} (h : x - a ∈ T) : x ∈ SiteInduction.shiftS (T : Set Site) a := by
  rw [AltItem5.mem_shiftS_iff']
  exact h

/-! ### The standard odd child after a `3` -/

/-- The full copies of the odd standard decomposition after a `3`. -/
theorem tOP_get (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h3 : w.getLast? = some Digit.three) :
    (tOP D f w)[0]? = some (stdPiece (f u1).tOdd (p0Off w .p1Plus) (p0Aff w .p1Plus)) ∧
    (tOP D f w)[1]? = some (stdPiece (f u1).tOdd (p0Off w .p1Minus) (p0Aff w .p1Minus)) ∧
    (W1Odd w = true →
      (tOP D f w)[3]? = some (stdPiece (f u2).tEven (p0Off w .q1DPlus + vQ1 w) (p0Aff w .q1DPlus)) ∧
      (tOP D f w)[4]? = some (stdPiece (f u2).tEven (p0Off w .q1DMinus) (p0Aff w .q1DMinus))) ∧
    (W1Odd w = false →
      (tOP D f w)[2]? = some (stdPiece (f u2).tEven (p0Off w .q1DPlus) (p0Aff w .q1DPlus)) ∧
      (tOP D f w)[5]? = some (stdPiece (f u2).tEven (p0Off w .q1DMinus + vQ1 w) (p0Aff w .q1DMinus))) := by
  have e1 : below f w u1 = f u1 := JointRot.below_of_lt f w u1 hl1
  have e2 : below f w u2 = f u2 := JointRot.below_of_lt f w u2 hl2
  refine ⟨?_, ?_, fun ho => ?_, fun ho => ?_⟩
  · simp [tOP, tileOddPieces, hr, regOdo, e1]
  · simp [tOP, tileOddPieces, hr, regOdo, e1]
  · simp [tOP, tileOddPieces, hr, regOdo, e2, h3, ho]
  · simp [tOP, tileOddPieces, hr, regOdo, e2, h3, ho]

theorem tOP_length (D : JointData) (f : Word → JSlice) (w : Word) : (tOP D f w).length = 6 := by
  simp [tOP, tileOddPieces]

/-- The offsets of the odd standard decomposition are those of `ChildGlue`. -/
theorem odd_offs (w : Word) :
    (oddP w).getD 0 0 = p0Off w .p1Plus ∧ (oddP w).getD 1 0 = p0Off w .p1Minus ∧
      (oddQ w).getD 0 0 = p0Off w .q1DPlus ∧ (oddQ w).getD 1 0 = p0Off w .q1DPlus + vQ1 w ∧
      (oddQ w).getD 2 0 = p0Off w .q1DMinus ∧ (oddQ w).getD 3 0 = p0Off w .q1DMinus + vQ1 w := by
  unfold oddP oddQ MixedPieces.pOffsetsOdd MixedPieces.qOffsetsOdd p0Off offsetP0 vP1 vP2 vQ1 vQ2
  cases h : (phase w == 1) <;> simp [W1Odd, h]

/-- The affine factors of the odd standard decomposition are those of `ClosedPathAssembly`. -/
theorem odd_affs (w : Word) :
    affOdd (parentsAt w).odd (parentsAt w).even 0 = p0Aff w .p1Plus ∧
      affOdd (parentsAt w).odd (parentsAt w).even 1 = p0Aff w .p1Minus ∧
      affOdd (parentsAt w).odd (parentsAt w).even 2 = p0Aff w .q1DPlus ∧
      affOdd (parentsAt w).odd (parentsAt w).even 3 = p0Aff w .q1DPlus ∧
      affOdd (parentsAt w).odd (parentsAt w).even 4 = p0Aff w .q1DMinus ∧
      affOdd (parentsAt w).odd (parentsAt w).even 5 = p0Aff w .q1DMinus := by
  unfold affOdd p0Aff pairAffine offsetA
  cases h : W1Odd w <;> simp <;> rfl

/-- A mixed pair of the odd standard decomposition, from the compatibility on the marks and item (d). -/
theorem mixed_odd (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w u1 u2 : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (hr : regsAt w = (some u1, some u2)) (hdO : (f u1).tOdd.dom = oddTile u1) (hdE : (f u2).tEven.dom = evenTile u2)
    (hT1 : (stateAt w).tOdd = oddTile u1) (hT2 : (stateAt w).tEven = evenTile u2) (i j : ℕ) (hi : i < 2) (hj2 : 2 ≤ j)
    (hj6 : j < 6) (k : ℕ) (hk : k = j - 2) {s t : Site}
    (hpi : (tOP D f w)[i]? = some (stdPiece (f u1).tOdd ((oddP w).getD i 0) s))
    (hpj : (tOP D f w)[j]? = some (stdPiece (f u2).tEven ((oddQ w).getD k 0) t))
    (hs : s = affOdd (parentsAt w).odd (parentsAt w).even i) (ht : t = affOdd (parentsAt w).odd (parentsAt w).even j) :
    PairCompat (tOP D f w) i j := by
  subst hk hs ht
  obtain ⟨C, hC⟩ := (MixedCompatGeneral.mixedCompatInput D hS hA f w u1 u2 hG hb hr).1 i j hi hj2 hj6
  have hlP : (oddP w).length = 2 := by unfold oddP MixedPieces.pOffsetsOdd; split_ifs <;> rfl
  have hlQ : (oddQ w).length = 4 := by unfold oddQ MixedPieces.qOffsetsOdd; split_ifs <;> rfl
  refine pairCompat_of_const hpi hpj C (fun x hx hx' => ?_)
  rw [hdO] at hx
  rw [hdE] at hx'
  have hma : (oddP w).getD i 0 ∈ oddP w := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hmb : (oddQ w).getD (j - 2) 0 ∈ oddQ w := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  obtain ⟨m1, m2⟩ := MixedFromCells.mixedOdd_all w hb u1 u2 hT1 hT2 _ hma _ hmb x (mem_shift_tile hx)
    (mem_shift_tile hx')
  have h := hC x (by simp only [ClosedPathAssembly.mOdd, ChildGlue.pieceSet, hlP, if_pos hi]; exact m1)
    (by simp only [ClosedPathAssembly.mOdd, ChildGlue.pieceSet, hlP, if_neg (show ¬ j < 2 by omega)]; exact m2)
  simp only [placedOdd, if_pos hi, if_neg (show ¬ j < 2 by omega), Pi.zero_apply, add_zero] at h
  exact h

/-- **The full copies of the corrected odd standard decomposition are compatible.** -/
theorem stdPair_odd (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (h3 : w.getLast? = some Digit.three) : ∀ i j, i ∉ oddLIdx w → j ∉ oddLIdx w → PairCompat (tOP D f w) i j := by
  obtain ⟨u1, u2, hr, hl1, hl2, hdO, hdE, hU1, hU2, hT1, hT2⟩ := regs_data D hS f w hG hb
  obtain ⟨g0, g1, gO, gE⟩ := tOP_get D f w u1 u2 hr hl1 hl2 h3
  obtain ⟨o0, o1, o2, o3, o4, o5⟩ := odd_offs w
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := odd_affs w
  have mix := mixed_odd D hS hA f w u1 u2 hG hb hr hdO hdE hT1 hT2
  apply pairs6 _ (tOP_length D f w)
  by_cases hph : phase w = 1
  · obtain ⟨g3, g4⟩ := gO (w1Odd_of hph)
    have e0 : p0Off w .p1Plus = 0 := by simp [p0Off, offsetP0, w1Odd_of hph]
    have e1 : p0Off w .p1Minus = texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even := by
      simp [p0Off, offsetP0, w1Odd_of hph, vQ1, vQ2]
    have e3 : p0Off w .q1DPlus + vQ1 w = texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even := by
      simp [p0Off, offsetP0, w1Odd_of hph, vP1, vQ1]
    have e4 : p0Off w .q1DMinus = texV2 (parentsAt w).odd := by simp [p0Off, offsetP0, w1Odd_of hph, vP2]
    have p01 : PairCompat (tOP D f w) 0 1 := pairCompat_of_disj g0 g1 (fun x h0 h1 => by
      rw [hdO, e0] at h0; rw [hdO, e1] at h1
      exact SameParentCopies.so01_of w hb h3 hph u1 hU1 h0 h1)
    have p34 : PairCompat (tOP D f w) 3 4 := pairCompat_of_disj g3 g4 (fun x h0 h1 => by
      rw [hdE, e3] at h0; rw [hdE, e4] at h1
      exact SameParentCopies.so34_of w hb h3 hph u2 hU2 h0 h1)
    have p03 := mix 0 3 (by omega) (by omega) (by omega) 1 rfl (by rw [o0]; exact g0) (by rw [o3]; exact g3) a0.symm a3.symm
    have p04 := mix 0 4 (by omega) (by omega) (by omega) 2 rfl (by rw [o0]; exact g0) (by rw [o4]; exact g4) a0.symm a4.symm
    have p13 := mix 1 3 (by omega) (by omega) (by omega) 1 rfl (by rw [o1]; exact g1) (by rw [o3]; exact g3) a1.symm a3.symm
    have p14 := mix 1 4 (by omega) (by omega) (by omega) 2 rfl (by rw [o1]; exact g1) (by rw [o4]; exact g4) a1.symm a4.symm
    intro i j hij hj6 hi hj
    simp [oddLIdx, w1Odd_of hph] at hi hj
    obtain ⟨hi1, hi2⟩ := hi
    obtain ⟨hj1, hj2⟩ := hj
    interval_cases j <;> interval_cases i <;> first | assumption | omega
  · obtain ⟨g2, g5⟩ := gE (w1Odd_ef hph)
    have e0 : p0Off w .p1Plus = texV1Even (parentsAt w).even + texV1Even (parentsAt w).even := by
      simp [p0Off, offsetP0, w1Odd_ef hph, vQ1]
    have e1 : p0Off w .p1Minus = texV2 (parentsAt w).even := by simp [p0Off, offsetP0, w1Odd_ef hph, vQ2]
    have e2 : p0Off w .q1DPlus = 0 := by simp [p0Off, offsetP0, w1Odd_ef hph]
    have e5 : p0Off w .q1DMinus + vQ1 w =
        texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV1Even (parentsAt w).even := by
      simp [p0Off, offsetP0, w1Odd_ef hph, vP1, vP2, vQ1]
    have p01 : PairCompat (tOP D f w) 0 1 := pairCompat_of_disj g0 g1 (fun x h0 h1 => by
      rw [hdO, e0] at h0; rw [hdO, e1] at h1
      exact SameParentCopies.so01_ef w hb h3 hph u1 hU1 h0 h1)
    have p25 : PairCompat (tOP D f w) 2 5 := pairCompat_of_disj g2 g5 (fun x h0 h1 => by
      rw [hdE, e2] at h0; rw [hdE, e5] at h1
      exact SameParentCopies.so25_ef w hb h3 hph u2 hU2 h0 h1)
    have p02 := mix 0 2 (by omega) (by omega) (by omega) 0 rfl (by rw [o0]; exact g0) (by rw [o2]; exact g2) a0.symm a2.symm
    have p05 := mix 0 5 (by omega) (by omega) (by omega) 3 rfl (by rw [o0]; exact g0) (by rw [o5]; exact g5) a0.symm a5.symm
    have p12 := mix 1 2 (by omega) (by omega) (by omega) 0 rfl (by rw [o1]; exact g1) (by rw [o2]; exact g2) a1.symm a2.symm
    have p15 := mix 1 5 (by omega) (by omega) (by omega) 3 rfl (by rw [o1]; exact g1) (by rw [o5]; exact g5) a1.symm a5.symm
    intro i j hij hj6 hi hj
    simp [oddLIdx, w1Odd_ef hph] at hi hj
    obtain ⟨hi1, hi2⟩ := hi
    obtain ⟨hj1, hj2⟩ := hj
    interval_cases j <;> interval_cases i <;> first | assumption | omega

/-! ### The standard even child after a `2` -/

/-- The full copies of the even standard decomposition after a `2`. -/
theorem tEP_get (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) :
    (tEP D f w)[0]? = some (stdPiece (f u1).tOdd (q0Off w .p1DPlus) (q0Aff w .p1DPlus)) ∧
    (tEP D f w)[3]? = some (stdPiece (f u1).tOdd (q0Off w .p1DMinus + vP2 w) (q0Aff w .p1DMinus + aP2 w)) ∧
    (tEP D f w)[4]? = some (stdPiece (f u2).tEven (q0Off w .q1Plus) (q0Aff w .q1Plus)) ∧
    (tEP D f w)[5]? = some (stdPiece (f u2).tEven (q0Off w .q1Minus) (q0Aff w .q1Minus)) := by
  have e1 : below f w u1 = f u1 := JointRot.below_of_lt f w u1 hl1
  have e2 : below f w u2 = f u2 := JointRot.below_of_lt f w u2 hl2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [tEP, tileEvenPieces, hr, regOdo, e1]
  · simp [tEP, tileEvenPieces, hr, regOdo, e1]
  · simp [tEP, tileEvenPieces, hr, regOdo, e2]
  · simp [tEP, tileEvenPieces, hr, regOdo, e2]

theorem tEP_length (D : JointData) (f : Word → JSlice) (w : Word) : (tEP D f w).length = 6 := by
  simp [tEP, tileEvenPieces]

/-- The offsets of the even standard decomposition are those of `ChildGlue`. -/
theorem even_offs (w : Word) :
    (evenP w).getD 0 0 = q0Off w .p1DPlus ∧ (evenP w).getD 3 0 = q0Off w .p1DMinus + vP2 w ∧
      (evenQ w).getD 0 0 = q0Off w .q1Plus ∧ (evenQ w).getD 1 0 = q0Off w .q1Minus := by
  unfold evenP evenQ MixedPieces.pOffsetsEven MixedPieces.qOffsetsEven q0Off offsetQ0 vP1 vP2 vQ1 vQ2
  cases h : (phase w == 1) <;> simp [W1Odd, h, add_assoc]

/-- The affine factors of the even standard decomposition are those of `ClosedPathAssembly`. -/
theorem even_affs (w : Word) :
    affEven (parentsAt w).odd (parentsAt w).even 0 = q0Aff w .p1DPlus ∧
      affEven (parentsAt w).odd (parentsAt w).even 3 = q0Aff w .p1DMinus + aP2 w ∧
      affEven (parentsAt w).odd (parentsAt w).even 4 = q0Aff w .q1Plus ∧
      affEven (parentsAt w).odd (parentsAt w).even 5 = q0Aff w .q1Minus := by
  unfold affEven q0Aff pairAffine aP2 offsetA
  cases h : W1Odd w <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp <;> ring

/-- A mixed pair of the even standard decomposition, from the compatibility on the marks and item (d). -/
theorem mixed_even (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w u1 u2 : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (hr : regsAt w = (some u1, some u2)) (hdO : (f u1).tOdd.dom = oddTile u1) (hdE : (f u2).tEven.dom = evenTile u2)
    (hT1 : (stateAt w).tOdd = oddTile u1) (hT2 : (stateAt w).tEven = evenTile u2) (i j : ℕ) (hi : i < 4) (hj4 : 4 ≤ j)
    (hj6 : j < 6) (k : ℕ) (hk : k = j - 4) {s t : Site}
    (hpi : (tEP D f w)[i]? = some (stdPiece (f u1).tOdd ((evenP w).getD i 0) s))
    (hpj : (tEP D f w)[j]? = some (stdPiece (f u2).tEven ((evenQ w).getD k 0) t))
    (hs : s = affEven (parentsAt w).odd (parentsAt w).even i) (ht : t = affEven (parentsAt w).odd (parentsAt w).even j) :
    PairCompat (tEP D f w) i j := by
  subst hk hs ht
  obtain ⟨C, hC⟩ := (MixedCompatGeneral.mixedCompatInput D hS hA f w u1 u2 hG hb hr).2 i j hi hj4 hj6
  have hlP : (evenP w).length = 4 := by unfold evenP MixedPieces.pOffsetsEven; split_ifs <;> rfl
  have hlQ : (evenQ w).length = 2 := by unfold evenQ MixedPieces.qOffsetsEven; split_ifs <;> rfl
  refine pairCompat_of_const hpi hpj C (fun x hx hx' => ?_)
  rw [hdO] at hx
  rw [hdE] at hx'
  have hma : (evenP w).getD i 0 ∈ evenP w := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hmb : (evenQ w).getD (j - 4) 0 ∈ evenQ w := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  obtain ⟨m1, m2⟩ := MixedFromCells.mixedEven_all w hb u1 u2 hT1 hT2 _ hma _ hmb x (mem_shift_tile hx)
    (mem_shift_tile hx')
  have h := hC x (by simp only [ClosedPathAssembly.mEven, ChildGlue.pieceSet, hlP, if_pos hi]; exact m1)
    (by simp only [ClosedPathAssembly.mEven, ChildGlue.pieceSet, hlP, if_neg (show ¬ j < 4 by omega)]; exact m2)
  simp only [placedEven, if_pos hi, if_neg (show ¬ j < 4 by omega), Pi.zero_apply, add_zero] at h
  exact h

/-- **The full copies of the corrected even standard decomposition are compatible.** -/
theorem stdPair_even (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (h2 : w.getLast? = some Digit.two) : ∀ i j, i ∉ evenLIdx → j ∉ evenLIdx → PairCompat (tEP D f w) i j := by
  obtain ⟨u1, u2, hr, hl1, hl2, hdO, hdE, hU1, hU2, hT1, hT2⟩ := regs_data D hS f w hG hb
  obtain ⟨g0, g3, g4, g5⟩ := tEP_get D f w u1 u2 hr hl1 hl2
  obtain ⟨o0, o3, o4, o5⟩ := even_offs w
  obtain ⟨a0, a3, a4, a5⟩ := even_affs w
  have mix := mixed_even D hS hA f w u1 u2 hG hb hr hdO hdE hT1 hT2
  have p04 := mix 0 4 (by omega) (by omega) (by omega) 0 rfl (by rw [o0]; exact g0) (by rw [o4]; exact g4) a0.symm a4.symm
  have p05 := mix 0 5 (by omega) (by omega) (by omega) 1 rfl (by rw [o0]; exact g0) (by rw [o5]; exact g5) a0.symm a5.symm
  have p34 := mix 3 4 (by omega) (by omega) (by omega) 0 rfl (by rw [o3]; exact g3) (by rw [o4]; exact g4) a3.symm a4.symm
  have p35 := mix 3 5 (by omega) (by omega) (by omega) 1 rfl (by rw [o3]; exact g3) (by rw [o5]; exact g5) a3.symm a5.symm
  have p03 : PairCompat (tEP D f w) 0 3 := pairCompat_of_disj g0 g3 (fun x h0 h1 => by
    rw [hdO] at h0 h1
    by_cases hph : phase w = 1
    · have e0 : q0Off w .p1DPlus = 0 := by simp [q0Off, offsetQ0, w1Odd_of hph]
      have e3 : q0Off w .p1DMinus + vP2 w = texV2 (parentsAt w).odd + texV1Even (parentsAt w).even +
          texV2 (parentsAt w).even := by simp [q0Off, offsetQ0, w1Odd_of hph, vP2, vQ1, vQ2]; abel
      rw [e0] at h0; rw [e3] at h1
      exact SameParentCopies.se03_of w hb h2 hph u1 hU1 h0 h1
    · have e0 : q0Off w .p1DPlus = texV1Even (parentsAt w).even := by simp [q0Off, offsetQ0, w1Odd_ef hph, vQ1]
      have e3 : q0Off w .p1DMinus + vP2 w = texV2 (parentsAt w).odd + texV2 (parentsAt w).even := by
        simp [q0Off, offsetQ0, w1Odd_ef hph, vP2, vQ2]; abel
      rw [e0] at h0; rw [e3] at h1
      exact SameParentCopies.se03_ef w hb h2 hph u1 hU1 h0 h1)
  have p45 : PairCompat (tEP D f w) 4 5 := pairCompat_of_disj g4 g5 (fun x h0 h1 => by
    rw [hdE] at h0 h1
    by_cases hph : phase w = 1
    · have e4 : q0Off w .q1Plus = texV1Odd (parentsAt w).odd := by simp [q0Off, offsetQ0, w1Odd_of hph, vP1]
      have e5 : q0Off w .q1Minus = texV2 (parentsAt w).odd + texV2 (parentsAt w).odd := by
        simp [q0Off, offsetQ0, w1Odd_of hph, vP2]
      rw [e4] at h0; rw [e5] at h1
      exact SameParentCopies.se45_of w hb h2 hph u2 hU2 h0 h1
    · have e4 : q0Off w .q1Plus = 0 := by simp [q0Off, offsetQ0, w1Odd_ef hph]
      have e5 : q0Off w .q1Minus = texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV2 (parentsAt w).odd := by
        simp [q0Off, offsetQ0, w1Odd_ef hph, vP1, vP2]
      rw [e4] at h0; rw [e5] at h1
      exact SameParentCopies.se45_ef w hb h2 hph u2 hU2 h0 h1)
  apply pairs6 _ (tEP_length D f w)
  intro i j hij hj6 hi hj
  simp [evenLIdx] at hi hj
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> interval_cases i <;> first | assumption | omega

/-! ### The alternate children -/

theorem mem_of_eq {T : Finset Site} {x a b : Site} (h : x - a ∈ T) (e : a = b) : x - b ∈ T := e ▸ h

theorem mem_std_shift {T : Finset Site} {a x : Site} (h : x - a ∈ T) : x ∈ Standard.shift T a :=
  Standard.mem_shift.2 h

/-- The full copies of the even alternate decomposition after a `3` (it has no parent piece there). -/
theorem aEP_get (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h3 : w.getLast? = some Digit.three) :
    (aEP D f w)[1]? = some (stdPiece (f u2).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) +
      (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2) (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) + aP2 w)) ∧
    (aEP D f w)[2]? = some (stdPiece (f u2).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus))
      (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus))) ∧
    (aEP D f w)[4]? = some (stdPiece (f u1).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus))
      (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus))) ∧
    (aEP D f w)[5]? = some (stdPiece (f u1).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus))
      (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus))) ∧
    (aEP D f w).length = 6 := by
  have e1 : below f w u1 = f u1 := JointRot.below_of_lt f w u1 hl1
  have e2 : below f w u2 = f u2 := JointRot.below_of_lt f w u2 hl2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [aEP, tileAltEvenPieces, hr, regOdo, e1, e2, h3, SurgicalAlt.altTypeOf, SurgicalAlt.altP1Coeff]

/-- The full copies of the odd alternate decomposition after a `2` (it has no parent piece there). -/
theorem aOP_get (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h2 : w.getLast? = some Digit.two) :
    (aOP D f w)[0]? = some (stdPiece (f u1).tOdd (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus))
      (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus))) ∧
    (aOP D f w)[3]? = some (stdPiece (f u1).tOdd (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) +
      (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + aP2 w)) ∧
    (aOP D f w)[4]? = some (stdPiece (f u2).tEven (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus))
      (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus))) ∧
    (aOP D f w)[5]? = some (stdPiece (f u2).tEven (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus))
      (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus))) ∧
    (aOP D f w).length = 6 := by
  have e1 : below f w u1 = f u1 := JointRot.below_of_lt f w u1 hl1
  have e2 : below f w u2 = f u2 := JointRot.below_of_lt f w u2 hl2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [aOP, tileAltOddPieces, hr, regOdo, e1, e2, h2, SurgicalAlt.altTypeOf, SurgicalAlt.altQ1Coeff]

/-- A mixed pair of the even alternate decomposition, from the compatibility on the marks and item (5). -/
theorem mixed_altEven (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w u1 u2 : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (hr : regsAt w = (some u1, some u2)) (hdO : (f u1).tOdd.dom = oddTile u1) (hdE : (f u2).tEven.dom = evenTile u2)
    (hT1 : (stateAt w).tOdd = oddTile u1) (hT2 : (stateAt w).tEven = evenTile u2) (i j : ℕ) (hi : i < 4) (hj4 : 4 ≤ j)
    (hj6 : j < 6) {a b s t : Site}
    (hpi : (aEP D f w)[i]? = some (stdPiece (f u2).tEven a s)) (hpj : (aEP D f w)[j]? = some (stdPiece (f u1).tOdd b t))
    (ha : a = (ClosedPathAlt.altEvenD w).getD i 0) (hb' : b = (ClosedPathAlt.altEvenR w).getD (j - 4) 0)
    (hs : s = (ClosedPathAlt.altEvenAff w).getD i 0) (ht : t = (ClosedPathAlt.altEvenAff w).getD j 0) :
    PairCompat (aEP D f w) i j := by
  subst ha hb' hs ht
  obtain ⟨C, hC⟩ := (MixedCompatGeneral.alt_mixed D hS hA f w u1 u2 hG hb hr 0).2 i j hi hj4 hj6
  have hlD : (ClosedPathAlt.altEvenD w).length = 4 := rfl
  have hDQ : ClosedPathAlt.altEvenD w = AltPieces.evenQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := rfl
  have hRP : ClosedPathAlt.altEvenR w = AltPieces.evenPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := rfl
  refine pairCompat_of_const hpi hpj C (fun x hx hx' => ?_)
  rw [hdE, ← hT2] at hx
  rw [hdO, ← hT1] at hx'
  have hma : (ClosedPathAlt.altEvenD w).getD i 0 ∈ AltPieces.evenQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := by
    rw [← hDQ, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hmb : (ClosedPathAlt.altEvenR w).getD (j - 4) 0 ∈
      AltPieces.evenPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := by
    rw [← hRP, List.getD_eq_getElem _ _ (by rw [hRP]; simp [AltPieces.evenPOffs]; omega)]; exact List.getElem_mem _
  obtain ⟨m1, m2⟩ := AltItem5.item5_marks_even hb u1 u2 hT1 hT2 _ hmb _ hma x (mem_std_shift hx') (mem_std_shift hx)
  have h := hC x (by simp only [ClosedPathAlt.mAE, ChildGlue.pieceSet, hlD, if_pos hi]; exact m2)
    (by simp only [ClosedPathAlt.mAE, ChildGlue.pieceSet, hlD, if_neg (show ¬ j < 4 by omega)]; exact m1)
  simp only [ClosedPathAlt.placedAltEven, if_pos hi, if_neg (show ¬ j < 4 by omega), Pi.zero_apply, add_zero] at h
  exact h

/-- A mixed pair of the odd alternate decomposition, from the compatibility on the marks and item (5). -/
theorem mixed_altOdd (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w u1 u2 : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (hr : regsAt w = (some u1, some u2)) (hdO : (f u1).tOdd.dom = oddTile u1) (hdE : (f u2).tEven.dom = evenTile u2)
    (hT1 : (stateAt w).tOdd = oddTile u1) (hT2 : (stateAt w).tEven = evenTile u2) (i j : ℕ) (hi : i < 4) (hj4 : 4 ≤ j)
    (hj6 : j < 6) {a b s t : Site}
    (hpi : (aOP D f w)[i]? = some (stdPiece (f u1).tOdd a s)) (hpj : (aOP D f w)[j]? = some (stdPiece (f u2).tEven b t))
    (ha : a = (ClosedPathAlt.altOddD w).getD i 0) (hb' : b = (ClosedPathAlt.altOddR w).getD (j - 4) 0)
    (hs : s = (ClosedPathAlt.altOddAff w).getD i 0) (ht : t = (ClosedPathAlt.altOddAff w).getD j 0) :
    PairCompat (aOP D f w) i j := by
  subst ha hb' hs ht
  obtain ⟨C, hC⟩ := (MixedCompatGeneral.alt_mixed D hS hA f w u1 u2 hG hb hr 0).1 i j hi hj4 hj6
  have hlD : (ClosedPathAlt.altOddD w).length = 4 := rfl
  have hDP : ClosedPathAlt.altOddD w = AltPieces.oddPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := rfl
  have hRQ : ClosedPathAlt.altOddR w = AltPieces.oddQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := rfl
  refine pairCompat_of_const hpi hpj C (fun x hx hx' => ?_)
  rw [hdO, ← hT1] at hx
  rw [hdE, ← hT2] at hx'
  have hma : (ClosedPathAlt.altOddD w).getD i 0 ∈ AltPieces.oddPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := by
    rw [← hDP, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hmb : (ClosedPathAlt.altOddR w).getD (j - 4) 0 ∈
      AltPieces.oddQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := by
    rw [← hRQ, List.getD_eq_getElem _ _ (by rw [hRQ]; simp [AltPieces.oddQOffs]; omega)]; exact List.getElem_mem _
  obtain ⟨m1, m2⟩ := AltItem5.item5_marks_odd hb u1 u2 hT1 hT2 _ hma _ hmb x (mem_std_shift hx) (mem_std_shift hx')
  have h := hC x (by simp only [ClosedPathAlt.mAO, ChildGlue.pieceSet, hlD, if_pos hi]; exact m1)
    (by simp only [ClosedPathAlt.mAO, ChildGlue.pieceSet, hlD, if_neg (show ¬ j < 4 by omega)]; exact m2)
  simp only [ClosedPathAlt.placedAltOdd, if_pos hi, if_neg (show ¬ j < 4 by omega), Pi.zero_apply, add_zero] at h
  exact h

/-- **The full copies of the corrected even alternate decomposition are compatible.** -/
theorem altPair_even (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (h3 : w.getLast? = some Digit.three) : ∀ i j, i ∉ altEvenLIdx → j ∉ altEvenLIdx → PairCompat (aEP D f w) i j := by
  obtain ⟨u1, u2, hr, hl1, hl2, hdO, hdE, hU1, hU2, hT1, hT2⟩ := regs_data D hS f w hG hb
  obtain ⟨g1, g2, g4, g5, hlen⟩ := aEP_get D f w u1 u2 hr hl1 hl2 h3
  have o1 : altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2 =
      (ClosedPathAlt.altEvenD w).getD 1 0 := (add_comm _ _).trans rfl
  have o2 : altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) = (ClosedPathAlt.altEvenD w).getD 2 0 := rfl
  have o4 : altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus) = (ClosedPathAlt.altEvenR w).getD 0 0 := rfl
  have o5 : altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus) = (ClosedPathAlt.altEvenR w).getD 1 0 := rfl
  have mix := mixed_altEven D hS hA f w u1 u2 hG hb hr hdO hdE hT1 hT2
  have p14 := mix 1 4 (by omega) (by omega) (by omega) g1 g4 o1 o4 rfl rfl
  have p15 := mix 1 5 (by omega) (by omega) (by omega) g1 g5 o1 o5 rfl rfl
  have p24 := mix 2 4 (by omega) (by omega) (by omega) g2 g4 o2 o4 rfl rfl
  have p25 := mix 2 5 (by omega) (by omega) (by omega) g2 g5 o2 o5 rfl rfl
  have p12 : PairCompat (aEP D f w) 1 2 := pairCompat_of_disj g1 g2 (fun x h0 h1 => by
    rw [hdE, o1] at h0
    rw [hdE, o2] at h1
    by_cases hph : phase w = 1
    · obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_of w hph
      rw [hD] at h0 h1
      simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at h0 h1
      exact SameParentCopies.ae12_of w hb h3 hph u2 hU2 (mem_of_eq h0 (by abel)) h1
    · obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_ef w hph
      rw [hD] at h0 h1
      simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at h0 h1
      exact SameParentCopies.ae12_ef w hb h3 hph u2 hU2 (mem_of_eq h0 (by abel)) h1)
  have p45 : PairCompat (aEP D f w) 4 5 := pairCompat_of_disj g4 g5 (fun x h0 h1 => by
    rw [hdO, o4] at h0
    rw [hdO, o5] at h1
    by_cases hph : phase w = 1
    · obtain ⟨-, hR, -, -⟩ := ClosedPathAlt.altEven_of w hph
      rw [hR] at h0 h1
      simp only [List.getD_cons_succ, List.getD_cons_zero] at h0 h1
      exact SameParentCopies.ae45_of w hb h3 hph u1 hU1 h0 h1
    · obtain ⟨-, hR, -, -⟩ := ClosedPathAlt.altEven_ef w hph
      rw [hR] at h0 h1
      simp only [List.getD_cons_succ, List.getD_cons_zero] at h0 h1
      exact SameParentCopies.ae45_ef w hb h3 hph u1 hU1 h0 h1)
  apply pairs6 _ hlen
  intro i j hij hj6 hi hj
  simp [altEvenLIdx] at hi hj
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> interval_cases i <;> first | assumption | omega

/-- **The full copies of the corrected odd alternate decomposition are compatible.** -/
theorem altPair_odd (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hG : GoodBelow D f w.length) (hb : ¬ IsBase w)
    (h2 : w.getLast? = some Digit.two) : ∀ i j, i ∉ altOddLIdx → j ∉ altOddLIdx → PairCompat (aOP D f w) i j := by
  obtain ⟨u1, u2, hr, hl1, hl2, hdO, hdE, hU1, hU2, hT1, hT2⟩ := regs_data D hS f w hG hb
  obtain ⟨g0, g3, g4, g5, hlen⟩ := aOP_get D f w u1 u2 hr hl1 hl2 h2
  have o0 : altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) = (ClosedPathAlt.altOddD w).getD 0 0 := rfl
  have o3 : altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1 =
      (ClosedPathAlt.altOddD w).getD 3 0 := (add_comm _ _).trans rfl
  have o4 : altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus) = (ClosedPathAlt.altOddR w).getD 0 0 := rfl
  have o5 : altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus) = (ClosedPathAlt.altOddR w).getD 1 0 := rfl
  have mix := mixed_altOdd D hS hA f w u1 u2 hG hb hr hdO hdE hT1 hT2
  have p04 := mix 0 4 (by omega) (by omega) (by omega) g0 g4 o0 o4 rfl rfl
  have p05 := mix 0 5 (by omega) (by omega) (by omega) g0 g5 o0 o5 rfl rfl
  have p34 := mix 3 4 (by omega) (by omega) (by omega) g3 g4 o3 o4 rfl rfl
  have p35 := mix 3 5 (by omega) (by omega) (by omega) g3 g5 o3 o5 rfl rfl
  have p03 : PairCompat (aOP D f w) 0 3 := pairCompat_of_disj g0 g3 (fun x h0 h1 => by
    rw [hdO, o0] at h0
    rw [hdO, o3] at h1
    by_cases hph : phase w = 1
    · obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_of w hph
      rw [hD] at h0 h1
      simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at h0 h1
      exact SameParentCopies.ao03_of w hb h2 hph u1 hU1 h0 (mem_of_eq h1 (by abel))
    · obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_ef w hph
      rw [hD] at h0 h1
      simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at h0 h1
      exact SameParentCopies.ao03_ef w hb h2 hph u1 hU1 h0 (mem_of_eq h1 (by abel)))
  have p45 : PairCompat (aOP D f w) 4 5 := pairCompat_of_disj g4 g5 (fun x h0 h1 => by
    rw [hdE, o4] at h0
    rw [hdE, o5] at h1
    by_cases hph : phase w = 1
    · obtain ⟨-, hR, -, -⟩ := ClosedPathAlt.altOdd_of w hph
      rw [hR] at h0 h1
      simp only [List.getD_cons_succ, List.getD_cons_zero] at h0 h1
      exact SameParentCopies.ao45_of w hb h2 hph u2 hU2 h0 h1
    · obtain ⟨-, hR, -, -⟩ := ClosedPathAlt.altOdd_ef w hph
      rw [hR] at h0 h1
      simp only [List.getD_cons_succ, List.getD_cons_zero] at h0 h1
      exact SameParentCopies.ao45_ef w hb h2 hph u2 hU2 h0 h1)
  apply pairs6 _ hlen
  intro i j hij hj6 hi hj
  simp [altOddLIdx] at hi hj
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> interval_cases i <;> first | assumption | omega

/-! ### The input -/

/-- **`StdPairCompatInput` for the paper data**: in every corrected tile decomposition (both standard children and both
alternate children) the entries that are not L-corrections are pairwise compatible. -/
theorem stdPairCompat_paper (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) : StdPairCompatInput D := by
  intro f w hG hb
  exact ⟨fun h3 => ⟨stdPair_odd D hS hA f w hG hb h3.2, altPair_even D hS hA f w hG hb h3.2⟩,
    fun h2 => ⟨stdPair_even D hS hA f w hG hb h2.2, altPair_odd D hS hA f w hG hb h2.2⟩⟩

end FLatticePaper.Tiles.StdPairCompatPaper
