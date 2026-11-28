import FLatticePaper.Tiles.ConnectedAltL

/-!
# The connectivity of the L decompositions

The overlap graphs of the decompositions of the L-corrected odometers (`oddLPieces`, `evenLPieces`) are connected
(`JointRot.ConnectedL`): every piece other than the first overlaps an earlier one (the previous stem, the last stem, the bridge or
the enlarged copy, the previous head), witnessed by corner points of the standard copies, the first tile and its half-turn image
of the heads, corners of the pieces of the decompositions of the heads, and explicit points of the base alternate tiles.
-/

namespace FLatticePaper.Tiles.ConnectedL

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointRot (StdCorners adj_of_mem connected_of_reach mem_placed)
open FLatticePaper.Tiles.JointGlue (goodPart)
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.SurgicalWeak (regsAt WeakData regOdo)
open FLatticePaper.Tiles.SurgicalAlt (AltCoeff altP0Coeff altQ0Coeff altQ1Coeff altP1Coeff altTypeOf coeffOff)
open FLatticePaper.Tiles.SurgicalDict (altShifts)
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles.ConnectedAltL (oStemPos oHeadPos eStemPos eHeadPos)

/-! ### Generic tools -/

/-- A decomposition is connected when every piece other than the first overlaps an earlier piece. -/
theorem connected_of_parent (ps : List Piece) (h0 : 0 < ps.length)
    (hpar : ∀ m (hm : m < ps.length), 0 < m → ∃ j, ∃ hj : j < m,
      (overlapGraph (goodPart ps)).Adj ⟨j, by omega⟩ ⟨m, hm⟩) :
    (overlapGraph (goodPart ps)).Connected := by
  refine connected_of_reach _ h0 (fun k => ?_)
  obtain ⟨m, hm⟩ := k
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact SimpleGraph.Reachable.refl _
    · obtain ⟨j, hj, hadj⟩ := hpar m hm hpos
      exact (ih j hj (by omega)).trans hadj.reachable

/-- Two pieces overlap at a point given in the frames of both. -/
theorem adj_fields (ps : List Piece) (i j : ℕ) (hi : i < ps.length) (hj : j < ps.length) (hij : i ≠ j)
    (oi oj : PartialOdometer) (fi fj a b : Site) (hoi : (ps.get ⟨i, hi⟩).odo = oi) (hoj : (ps.get ⟨j, hj⟩).odo = oj)
    (hfi : (ps.get ⟨i, hi⟩).off = fi) (hfj : (ps.get ⟨j, hj⟩).off = fj) (ha : a ∈ oi.dom) (hb : b ∈ oj.dom)
    (he : fi + a = fj + b) (hei : fi + a ∉ (ps.get ⟨i, hi⟩).exc) (hej : fi + a ∉ (ps.get ⟨j, hj⟩).exc) :
    (overlapGraph (goodPart ps)).Adj ⟨i, hi⟩ ⟨j, hj⟩ := by
  refine adj_of_mem ps ⟨i, hi⟩ ⟨j, hj⟩ hij (fi + a) ?_ ?_ hei hej
  · rw [mem_placed, hfi, hoi, add_sub_cancel_left]; exact ha
  · rw [mem_placed, hfj, hoj, he, add_sub_cancel_left]; exact hb

/-! ### The pieces of the odd L-correction by index -/

theorem oL_length (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool) :
    (oddLPieces S pO pE aO aE w plus elong).length =
      trailingCount Digit.two w + 2 + (2 * (trailingCount Digit.two w + 1) - (if elong then 0 else 1)) := by
  unfold oddLPieces; simp; omega

theorem oL_stem (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool) (j : ℕ)
    (hj : j ≤ trailingCount Digit.two w) (h : j < (oddLPieces S pO pE aO aE w plus elong).length) :
    ((oddLPieces S pO pE aO aE w plus elong).get ⟨j, h⟩).odo = regOdo S pO pE (regsAt (stripTrailing Digit.two w)).2 false ∧
    ((oddLPieces S pO pE aO aE w plus elong).get ⟨j, h⟩).off = oStemPos w plus j ∧
    ((oddLPieces S pO pE aO aE w plus elong).get ⟨j, h⟩).exc = ∅ := by
  simp only [List.get_eq_getElem]
  unfold oddLPieces
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
  simp [oStemPos, stdPiece]

theorem oL_bridge (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool)
    (h : trailingCount Digit.two w + 1 < (oddLPieces S pO pE aO aE w plus elong).length) :
    ((oddLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.two w + 1, h⟩).odo =
      regOdo S pO pE (regsAt (stripTrailing Digit.two w)).1 true ∧
    ((oddLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.two w + 1, h⟩).off =
      oddLInitOff w plus + altOff (stripTrailing Digit.two w)
        ((trailingCount Digit.two w : ℤ) • (oddKCoeff (W1Odd w) plus).1 + (oddKCoeff (W1Odd w) plus).2.1) +
        LCorrections.oddBridgeShift (!(stripTrailing Digit.two w).isEmpty &&
          (stripTrailing Digit.two w).all (fun d => decide (d = Digit.three))) (W1Odd w) plus ∧
    ((oddLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.two w + 1, h⟩).exc = ∅ := by
  simp only [List.get_eq_getElem]
  unfold oddLPieces
  rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
  simp [stdPiece]

theorem oL_head (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool) (i : ℕ)
    (h : trailingCount Digit.two w + 2 + i < (oddLPieces S pO pE aO aE w plus elong).length) :
    ((oddLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.two w + 2 + i, h⟩).odo =
      regOdo S aO aE (regsAt (stripTrailing Digit.two w)).2 false ∧
    ((oddLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.two w + 2 + i, h⟩).off = oHeadPos w plus i ∧
    (((!(stripTrailing Digit.two w).isEmpty && (stripTrailing Digit.two w).all (fun d => decide (d = Digit.three))) = false ∨
      0 < i) → ((oddLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.two w + 2 + i, h⟩).exc = ∅) := by
  simp only [List.get_eq_getElem]
  unfold oddLPieces
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_append, List.length_map, List.length_range, List.length_singleton, List.getElem_map,
    List.getElem_range, show trailingCount Digit.two w + 2 + i - (trailingCount Digit.two w + 1 + 1) = i by omega]
  refine ⟨by trivial, by trivial, fun hc => ?_⟩
  rcases hc with hc | hc
  · simp [hc]
  · simp [show i ≠ 0 by omega]

/-- The exceptional points of the first head of the odd L-correction lie in the set `A` of the base staircase, in the frame of the
head. -/
theorem oL_head0_exc (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool)
    (h : trailingCount Digit.two w + 2 + 0 < (oddLPieces S pO pE aO aE w plus elong).length) (x : Site)
    (hx : x ∈ ((oddLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.two w + 2 + 0, h⟩).exc) :
    x - oHeadPos w plus 0 ∈ Construction.paperStairAltA (2 * ((stripTrailing Digit.two w).length : ℤ) + 1) := by
  simp only [List.get_eq_getElem] at hx
  unfold oddLPieces at hx
  rw [List.getElem_append_right (by simp)] at hx
  simp only [List.length_append, List.length_map, List.length_range, List.length_singleton, List.getElem_map,
    List.getElem_range, show trailingCount Digit.two w + 2 + 0 - (trailingCount Digit.two w + 1 + 1) = 0 by omega] at hx
  split_ifs at hx
  · exact hx.1
  · simp at hx

/-! ### The pieces of the even L-correction by index -/

theorem eL_length (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool) :
    (evenLPieces S pO pE aO aE w plus elong).length =
      trailingCount Digit.three w + 1 +
        (if (!(stripTrailing Digit.three w).isEmpty && (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) &&
          (!W1Odd w && !plus) then 0 else 1) +
        (if (!(stripTrailing Digit.three w).isEmpty && (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two)))
          then 1 else 0) +
        (2 * (trailingCount Digit.three w + 1) - (if elong then 0 else 1)) := by
  unfold evenLPieces; simp only [List.length_append, List.length_map, List.length_range]; split_ifs <;> simp

theorem eL_stem (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool) (j : ℕ)
    (hj : j ≤ trailingCount Digit.three w) (h : j < (evenLPieces S pO pE aO aE w plus elong).length) :
    ((evenLPieces S pO pE aO aE w plus elong).get ⟨j, h⟩).odo = regOdo S pO pE (regsAt (stripTrailing Digit.three w)).1 true ∧
    ((evenLPieces S pO pE aO aE w plus elong).get ⟨j, h⟩).off = eStemPos w plus j ∧
    ((evenLPieces S pO pE aO aE w plus elong).get ⟨j, h⟩).exc = ∅ := by
  simp only [List.get_eq_getElem]
  unfold evenLPieces
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
    List.getElem_append_left (by simp; omega)]
  simp [eStemPos, stdPiece]

/-- The piece after the stems and its successors, when the prefix is not `2^j`. -/
theorem eL_gen (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool)
    (hd : (!(stripTrailing Digit.three w).isEmpty && (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false) :
    (∀ h : trailingCount Digit.three w + 1 < (evenLPieces S pO pE aO aE w plus elong).length,
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 1, h⟩).odo =
        regOdo S pO pE (regsAt (stripTrailing Digit.three w)).2 false ∧
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 1, h⟩).off =
        evenLInitOff w plus + altOff (stripTrailing Digit.three w)
          ((trailingCount Digit.three w : ℤ) • (evenKCoeff (W1Odd w) plus
            (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).1 +
          (evenKCoeff (W1Odd w) plus (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).2.1) ∧
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 1, h⟩).exc = ∅) ∧
    (∀ i (h : trailingCount Digit.three w + 2 + i < (evenLPieces S pO pE aO aE w plus elong).length),
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 2 + i, h⟩).odo =
        regOdo S aO aE (regsAt (stripTrailing Digit.three w)).1 true ∧
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 2 + i, h⟩).off = eHeadPos w plus i ∧
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 2 + i, h⟩).exc = ∅) := by
  refine ⟨fun h => ?_, fun i h => ?_⟩
  · simp only [List.get_eq_getElem]
    unfold evenLPieces
    simp only [hd, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
    simp [stdPiece]
  · simp only [List.get_eq_getElem]
    unfold evenLPieces
    simp only [hd, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    rw [List.getElem_append_right (by simp)]
    simp only [List.length_append, List.length_map, List.length_range, List.length_singleton, List.getElem_map,
      List.getElem_range, show trailingCount Digit.three w + 2 + i - (trailingCount Digit.three w + 1 + 1) = i by omega]
    refine ⟨by trivial, by simp only [eHeadPos], ?_⟩
    simp

/-- The pieces after the stems at the prefix `2^j`, case `01` (no bridge): the enlarged copy, then the heads. -/
theorem eL_dbl01 (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool)
    (hd : (!(stripTrailing Digit.three w).isEmpty && (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = true)
    (hc : (!W1Odd w && !plus) = true) :
    (∀ h : trailingCount Digit.three w + 1 < (evenLPieces S pO pE aO aE w plus elong).length,
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 1, h⟩).odo = enlOdo ∧
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 1, h⟩).off =
        evenLInitOff w plus + altOff (stripTrailing Digit.three w)
          ((trailingCount Digit.three w : ℤ) • (evenKCoeff (W1Odd w) plus
            (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).1 +
          (evenKCoeff (W1Odd w) plus (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).2.1) +
          ((1 : ℤ), (1 : ℤ)) ∧
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 1, h⟩).exc = ∅) ∧
    (∀ i (h : trailingCount Digit.three w + 2 + i < (evenLPieces S pO pE aO aE w plus elong).length),
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 2 + i, h⟩).odo =
        regOdo S aO aE (regsAt (stripTrailing Digit.three w)).1 true ∧
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 2 + i, h⟩).off = eHeadPos w plus i ∧
      (0 < i → ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 2 + i, h⟩).exc = ∅) ∧
      (∀ x ∈ ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 2 + i, h⟩).exc,
        x - eHeadPos w plus 0 + ((0 : ℤ), (1 : ℤ)) ∈
          Construction.paperNearStairAltA (2 * ((stripTrailing Digit.three w).length : ℤ) + 1))) := by
  refine ⟨fun h => ?_, fun i h => ?_⟩
  · simp only [List.get_eq_getElem]
    unfold evenLPieces
    simp only [hd, hc, Bool.true_and, ↓reduceIte, List.append_nil]
    rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
    simp [stdPiece]
  · simp only [List.get_eq_getElem]
    unfold evenLPieces
    simp only [hd, hc, Bool.true_and, ↓reduceIte, List.append_nil]
    rw [List.getElem_append_right (by simp)]
    simp only [List.length_append, List.length_map, List.length_range, List.length_singleton,
      List.getElem_map, List.getElem_range, show trailingCount Digit.three w + 2 + i - (trailingCount Digit.three w + 1 + 0 + 1) = i by omega]
    refine ⟨by trivial, by simp only [eHeadPos], fun hi => by simp [show i ≠ 0 by omega], fun x hx => ?_⟩
    split_ifs at hx with hi0
    · simp only [beq_iff_eq] at hi0
      subst hi0
      exact hx.1
    · simp at hx

/-- The pieces after the stems at the prefix `2^j`, not case `01`: the bridge, the enlarged copy, then the heads. -/
theorem eL_dbl (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool)
    (hd : (!(stripTrailing Digit.three w).isEmpty && (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = true)
    (hc : (!W1Odd w && !plus) = false) :
    (∀ h : trailingCount Digit.three w + 1 < (evenLPieces S pO pE aO aE w plus elong).length,
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 1, h⟩).odo =
        regOdo S pO pE (regsAt (stripTrailing Digit.three w)).2 false ∧
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 1, h⟩).off =
        evenLInitOff w plus + altOff (stripTrailing Digit.three w)
          ((trailingCount Digit.three w : ℤ) • (evenKCoeff (W1Odd w) plus
            (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).1 +
          (evenKCoeff (W1Odd w) plus (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).2.1) ∧
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 1, h⟩).exc = ∅) ∧
    (∀ h : trailingCount Digit.three w + 2 < (evenLPieces S pO pE aO aE w plus elong).length,
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 2, h⟩).odo = enlOdo ∧
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 2, h⟩).off =
        evenLInitOff w plus + altOff (stripTrailing Digit.three w)
          ((trailingCount Digit.three w : ℤ) • (evenKCoeff (W1Odd w) plus
            (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).1 +
          (evenKCoeff (W1Odd w) plus (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).2.1) +
          ((1 : ℤ), (1 : ℤ)) ∧
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 2, h⟩).exc = ∅) ∧
    (∀ i (h : trailingCount Digit.three w + 3 + i < (evenLPieces S pO pE aO aE w plus elong).length),
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 3 + i, h⟩).odo =
        regOdo S aO aE (regsAt (stripTrailing Digit.three w)).1 true ∧
      ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 3 + i, h⟩).off = eHeadPos w plus i ∧
      (0 < i → ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 3 + i, h⟩).exc = ∅) ∧
      (∀ x ∈ ((evenLPieces S pO pE aO aE w plus elong).get ⟨trailingCount Digit.three w + 3 + i, h⟩).exc,
        x - eHeadPos w plus 0 + ((0 : ℤ), (1 : ℤ)) ∈
          Construction.paperNearStairAltA (2 * ((stripTrailing Digit.three w).length : ℤ) + 1))) := by
  refine ⟨fun h => ?_, fun h => ?_, fun i h => ?_⟩
  · simp only [List.get_eq_getElem]
    unfold evenLPieces
    simp only [hd, hc, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
    simp [stdPiece]
  · simp only [List.get_eq_getElem]
    unfold evenLPieces
    simp only [hd, hc, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
    simp [stdPiece]
  · simp only [List.get_eq_getElem]
    unfold evenLPieces
    simp only [hd, hc, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [List.getElem_append_right (by simp)]
    simp only [List.length_append, List.length_map, List.length_range, List.length_singleton,
      List.getElem_map, List.getElem_range, show trailingCount Digit.three w + 3 + i - (trailingCount Digit.three w + 1 + 1 + 1) = i by omega]
    refine ⟨by trivial, by simp only [eHeadPos], fun hi => by simp [show i ≠ 0 by omega], fun x hx => ?_⟩
    split_ifs at hx with hi0
    · simp only [beq_iff_eq] at hi0
      subst hi0
      exact hx.1
    · simp at hx

theorem W1Odd_strip_two (w : Word) : W1Odd (stripTrailing Digit.two w) = W1Odd w := by
  conv_rhs => rw [← JointRot.strip_append_replicate Digit.two w]
  unfold W1Odd phase
  simp [List.count_append, List.count_replicate]

/-! ### The odd L-correction, prefix not `3^j`, head register not a base word -/

set_option hygiene false in
macro "oL_id" : tactic => `(tactic| (
  simp only [oStemPos, oHeadPos, oddLInitOff, p0Off, q0Off, SurgicalDict.offsetP0, SurgicalDict.offsetQ0, oddKCoeff, altOff,
    coeffOff, altD, altQ0Coeff, altShifts, hst, hW, hW1, htr, ↓reduceIte, Bool.false_eq_true, LCorrections.oddBridgeShift,
    vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2, hpw, parentsAt_append_singleton, Parents.step, Parents.current,
    Parents.combine, Prod.smul_mk, smul_eq_mul]
  refine Prod.ext ?_ ?_ <;> simp <;> push_cast <;> ring))

theorem oddL_conn_one_false_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.two w = (w1 ++ [Digit.one])) (hW1 : W1Odd w1 = false)
    (htr : (!((w1 ++ [Digit.one])).isEmpty && ((w1 ++ [Digit.one])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE w1) (vQ1 (w1 ++ [Digit.one])) (vQ2 (w1 ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.one])).1 true) (vP1 (w1 ++ [Digit.one])) (vP2 (w1 ++ [Digit.one])))
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (aE w1).dom ∧ altD w1 false - a ∈ (aE w1).dom)
    (hX : (altOff w1 (altQ0Coeff false .p1Plus) + (vP1 w1)) ∈ (aE w1).dom) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_two w, hst]; simp [ConnectedAltL.W1Odd_snoc_one, hW1]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd w1 _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt (w1 ++ [Digit.one])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.one])).even.num,
      (parentsAt (w1 ++ [Digit.one])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.one])).even.den⟩, (parentsAt (w1 ++ [Digit.one])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w true elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨j, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong j (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w true elong (j + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 (w1 ++ [Digit.one]) + vQ2 (w1 ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (vQ1 (w1 ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hS.cXi (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w true elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 (w1 ++ [Digit.one]) + vQ2 (w1 ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (vP1 (w1 ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hB.cXi (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w true elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP2 (w1 ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (altD w1 false - ((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hB.cY1i (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).2 (by oL_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w true elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (altOff w1 (altQ0Coeff false .p1Plus) + (vP1 w1)) o1 o2 f1 f2 (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).1 hX (by oL_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_one_false_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.two w = (w1 ++ [Digit.one])) (hW1 : W1Odd w1 = false)
    (htr : (!((w1 ++ [Digit.one])).isEmpty && ((w1 ++ [Digit.one])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE w1) (vQ1 (w1 ++ [Digit.one])) (vQ2 (w1 ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.one])).1 true) (vP1 (w1 ++ [Digit.one])) (vP2 (w1 ++ [Digit.one])))
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (aE w1).dom ∧ altD w1 false - a ∈ (aE w1).dom)
    (hX : (altOff w1 (altQ0Coeff false .p1Minus) + (vP2 w1 + ((1 : ℤ), (-1 : ℤ)))) ∈ (aE w1).dom) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_two w, hst]; simp [ConnectedAltL.W1Odd_snoc_one, hW1]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd w1 _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt (w1 ++ [Digit.one])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.one])).even.num,
      (parentsAt (w1 ++ [Digit.one])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.one])).even.den⟩, (parentsAt (w1 ++ [Digit.one])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w false elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨j, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong j (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w false elong (j + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vQ2 (w1 ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hS.cY1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w false elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vP2 (w1 ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hB.cY1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w false elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 (w1 ++ [Digit.one])) (((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hB.cX (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w false elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (altD w1 false - ((0 : ℤ), (0 : ℤ))) (altOff w1 (altQ0Coeff false .p1Minus) + (vP2 w1 + ((1 : ℤ), (-1 : ℤ)))) o1 o2 f1 f2 (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).2 hX (by oL_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_one_true_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.two w = (w1 ++ [Digit.one])) (hW1 : W1Odd w1 = true)
    (htr : (!((w1 ++ [Digit.one])).isEmpty && ((w1 ++ [Digit.one])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE w1) (vQ1 (w1 ++ [Digit.one])) (vQ2 (w1 ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.one])).1 true) (vP1 (w1 ++ [Digit.one])) (vP2 (w1 ++ [Digit.one])))
    (hX : (altOff w1 (altQ0Coeff true .dsQ1Minus) + (vQ1 w1)) ∈ (aE w1).dom ∧ (altOff w1 (altQ0Coeff true .dsQ1Plus) + (altShifts true (vP2 w1) (vQ1 w1)).2 + (((0 : ℤ), (0 : ℤ)))) ∈ (aE w1).dom ∧ (altOff w1 (altQ0Coeff true .dsQ1Minus) + (((0 : ℤ), (0 : ℤ)))) ∈ (aE w1).dom) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_two w, hst]; simp [ConnectedAltL.W1Odd_snoc_one, hW1]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd w1 _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt (w1 ++ [Digit.one])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.one])).even.num,
      (parentsAt (w1 ++ [Digit.one])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.one])).even.den⟩, (parentsAt (w1 ++ [Digit.one])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w true elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨j, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong j (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w true elong (j + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 (w1 ++ [Digit.one]) + vQ2 (w1 ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (vQ1 (w1 ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hS.cXi (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w true elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ2 (w1 ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.cY1 hB.c1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w true elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 (w1 ++ [Digit.one])) (altOff w1 (altQ0Coeff true .dsQ1Minus) + (vQ1 w1)) o1 o2 f1 f2 hB.cX hX.1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w true elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (altOff w1 (altQ0Coeff true .dsQ1Plus) + (altShifts true (vP2 w1) (vQ1 w1)).2 + (((0 : ℤ), (0 : ℤ)))) (altOff w1 (altQ0Coeff true .dsQ1Minus) + (((0 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 hX.2.1 hX.2.2 (by oL_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_one_true_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.two w = (w1 ++ [Digit.one])) (hW1 : W1Odd w1 = true)
    (htr : (!((w1 ++ [Digit.one])).isEmpty && ((w1 ++ [Digit.one])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE w1) (vQ1 (w1 ++ [Digit.one])) (vQ2 (w1 ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.one])).1 true) (vP1 (w1 ++ [Digit.one])) (vP2 (w1 ++ [Digit.one])))
    (hX : (altOff w1 (altQ0Coeff true .dsQ1Plus) + (altShifts true (vP2 w1) (vQ1 w1)).2 + (vQ2 w1 + ((1 : ℤ), (0 : ℤ)))) ∈ (aE w1).dom ∧ (altOff w1 (altQ0Coeff true .dsQ1Minus) + (((0 : ℤ), (0 : ℤ)))) ∈ (aE w1).dom ∧ (altOff w1 (altQ0Coeff true .dsQ1Plus) + (altShifts true (vP2 w1) (vQ1 w1)).2 + (((0 : ℤ), (0 : ℤ)))) ∈ (aE w1).dom) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_two w, hst]; simp [ConnectedAltL.W1Odd_snoc_one, hW1]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd w1 _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt (w1 ++ [Digit.one])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.one])).even.num,
      (parentsAt (w1 ++ [Digit.one])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.one])).even.den⟩, (parentsAt (w1 ++ [Digit.one])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w false elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨j, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong j (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w false elong (j + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vQ2 (w1 ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hS.cY1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w false elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 (w1 ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) (vP1 (w1 ++ [Digit.one]) + vP2 (w1 ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cXi hB.cD1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w false elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP2 (w1 ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) (altOff w1 (altQ0Coeff true .dsQ1Plus) + (altShifts true (vP2 w1) (vQ1 w1)).2 + (vQ2 w1 + ((1 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 hB.cY1 hX.1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w false elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (altOff w1 (altQ0Coeff true .dsQ1Minus) + (((0 : ℤ), (0 : ℤ)))) (altOff w1 (altQ0Coeff true .dsQ1Plus) + (altShifts true (vP2 w1) (vQ1 w1)).2 + (((0 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 hX.2.1 hX.2.2 (by oL_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_three_false_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.two w = (w1 ++ [Digit.three])) (hW1 : W1Odd w1 = false)
    (htr : (!((w1 ++ [Digit.three])).isEmpty && ((w1 ++ [Digit.three])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE w1) (vQ1 (w1 ++ [Digit.three])) (vQ2 (w1 ++ [Digit.three])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.three])).1 true) (vP1 (w1 ++ [Digit.three])) (vP2 (w1 ++ [Digit.three])))
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (aE w1).dom ∧ altD w1 false - a ∈ (aE w1).dom)
    (hX : (altOff w1 (altQ0Coeff false .p1Minus) + (vP2 w1 + ((1 : ℤ), (-1 : ℤ)))) ∈ (aE w1).dom) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_two w, hst]; simp [ConnectedAltL.W1Odd_snoc_three, hW1]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd w1 _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt (w1 ++ [Digit.three])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.three])).even.num,
      (parentsAt (w1 ++ [Digit.three])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.three])).even.den⟩, (parentsAt (w1 ++ [Digit.three])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w true elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨j, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong j (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w true elong (j + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 (w1 ++ [Digit.three]) + vQ2 (w1 ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) (vQ1 (w1 ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hS.cXi (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w true elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ2 (w1 ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.cY1 hB.c1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w true elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 (w1 ++ [Digit.three]) + vP2 (w1 ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (altOff w1 (altQ0Coeff false .p1Minus) + (vP2 w1 + ((1 : ℤ), (-1 : ℤ)))) o1 o2 f1 f2 hB.cD hX (by oL_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w true elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (altD w1 false - ((0 : ℤ), (0 : ℤ))) (altOff w1 (altQ0Coeff false .p1Minus) + (vP2 w1 + ((1 : ℤ), (-1 : ℤ)))) o1 o2 f1 f2 (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).2 hX (by oL_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_three_false_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.two w = (w1 ++ [Digit.three])) (hW1 : W1Odd w1 = false)
    (htr : (!((w1 ++ [Digit.three])).isEmpty && ((w1 ++ [Digit.three])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE w1) (vQ1 (w1 ++ [Digit.three])) (vQ2 (w1 ++ [Digit.three])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.three])).1 true) (vP1 (w1 ++ [Digit.three])) (vP2 (w1 ++ [Digit.three])))
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (aE w1).dom ∧ altD w1 false - a ∈ (aE w1).dom)
    (hX : (altOff w1 (altQ0Coeff false .p1Plus) + (vP1 w1)) ∈ (aE w1).dom) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_two w, hst]; simp [ConnectedAltL.W1Odd_snoc_three, hW1]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd w1 _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt (w1 ++ [Digit.three])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.three])).even.num,
      (parentsAt (w1 ++ [Digit.three])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.three])).even.den⟩, (parentsAt (w1 ++ [Digit.three])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w false elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨j, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong j (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w false elong (j + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vQ2 (w1 ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hS.cY1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w false elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 (w1 ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) (vP1 (w1 ++ [Digit.three]) + vP2 (w1 ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cXi hB.cD1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w false elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (altOff w1 (altQ0Coeff false .p1Plus) + (vP1 w1)) o1 o2 f1 f2 hB.c0 hX (by oL_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w false elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (altOff w1 (altQ0Coeff false .p1Plus) + (vP1 w1)) o1 o2 f1 f2 (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).1 hX (by oL_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_three_true_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.two w = (w1 ++ [Digit.three])) (hW1 : W1Odd w1 = true)
    (htr : (!((w1 ++ [Digit.three])).isEmpty && ((w1 ++ [Digit.three])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE w1) (vQ1 (w1 ++ [Digit.three])) (vQ2 (w1 ++ [Digit.three])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.three])).1 true) (vP1 (w1 ++ [Digit.three])) (vP2 (w1 ++ [Digit.three])))
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (aE w1).dom ∧ altD w1 false - a ∈ (aE w1).dom)
    (hX : (altOff w1 (altQ0Coeff true .dsQ1Minus) + (((0 : ℤ), (0 : ℤ)))) ∈ (aE w1).dom ∧ (altOff w1 (altQ0Coeff true .dsQ1Plus) + (altShifts true (vP2 w1) (vQ1 w1)).2 + (((0 : ℤ), (0 : ℤ)))) ∈ (aE w1).dom) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_two w, hst]; simp [ConnectedAltL.W1Odd_snoc_three, hW1]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd w1 _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt (w1 ++ [Digit.three])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.three])).even.num,
      (parentsAt (w1 ++ [Digit.three])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.three])).even.den⟩, (parentsAt (w1 ++ [Digit.three])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w true elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨j, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong j (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w true elong (j + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 (w1 ++ [Digit.three]) + vQ2 (w1 ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) (vQ1 (w1 ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hS.cXi (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w true elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 (w1 ++ [Digit.three]) + vQ2 (w1 ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) (vP1 (w1 ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hB.cXi (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w true elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP2 (w1 ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (altD w1 false - ((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hB.cY1i (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).2 (by oL_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w true elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (altOff w1 (altQ0Coeff true .dsQ1Minus) + (((0 : ℤ), (0 : ℤ)))) (altOff w1 (altQ0Coeff true .dsQ1Plus) + (altShifts true (vP2 w1) (vQ1 w1)).2 + (((0 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 hX.1 hX.2 (by oL_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_three_true_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.two w = (w1 ++ [Digit.three])) (hW1 : W1Odd w1 = true)
    (htr : (!((w1 ++ [Digit.three])).isEmpty && ((w1 ++ [Digit.three])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE w1) (vQ1 (w1 ++ [Digit.three])) (vQ2 (w1 ++ [Digit.three])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.three])).1 true) (vP1 (w1 ++ [Digit.three])) (vP2 (w1 ++ [Digit.three])))
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (aE w1).dom ∧ altD w1 false - a ∈ (aE w1).dom)
    (hX : (altOff w1 (altQ0Coeff true .dsQ1Plus) + (altShifts true (vP2 w1) (vQ1 w1)).2 + (((0 : ℤ), (0 : ℤ)))) ∈ (aE w1).dom ∧ (altOff w1 (altQ0Coeff true .dsQ1Minus) + (((0 : ℤ), (0 : ℤ)))) ∈ (aE w1).dom) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_two w, hst]; simp [ConnectedAltL.W1Odd_snoc_three, hW1]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd w1 _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt (w1 ++ [Digit.three])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.three])).even.num,
      (parentsAt (w1 ++ [Digit.three])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt (w1 ++ [Digit.three])).even.den⟩, (parentsAt (w1 ++ [Digit.three])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w false elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨j, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong j (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w false elong (j + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vQ2 (w1 ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hS.cY1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w false elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vP2 (w1 ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hB.cY1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w false elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 (w1 ++ [Digit.three])) (((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hB.cX (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).1 (by oL_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w false elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (altOff w1 (altQ0Coeff true .dsQ1Plus) + (altShifts true (vP2 w1) (vQ1 w1)).2 + (((0 : ℤ), (0 : ℤ)))) (altOff w1 (altQ0Coeff true .dsQ1Minus) + (((0 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 hX.1 hX.2 (by oL_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

/-! ### The odd L-correction, prefix not `3^j`, head register a base word -/

open FLatticePaper.Construction (paperStairAltTile paperStairAltA paperStairAltB paperStairAltC paperStairAltD
  paperNearLadderAltTile paperNearLadderAltA paperNearLadderAltB paperNearLadderAltC paperNearLadderAltD
  paperLadderAltTile paperLadderAltA paperLadderAltB paperLadderAltC paperLadderAltD
  paperNearStairAltTile paperNearStairAltA paperNearStairAltB paperNearStairAltC paperNearStairAltD)

theorem parents_nil : parentsAt ([] : Word) = ⟨⟨0, 1⟩, ⟨1, 1⟩⟩ := rfl

set_option hygiene false in
macro "base_mem" : tactic => `(tactic| (
  simp only [paperStairAltTile, paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD, paperNearLadderAltTile,
    paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, paperLadderAltTile, paperLadderAltA,
    paperLadderAltB, paperLadderAltC, paperLadderAltD, paperNearStairAltTile, paperNearStairAltA, paperNearStairAltB,
    paperNearStairAltC, paperNearStairAltD, Set.mem_union, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq, Prod.mk_add_mk, Prod.mk_sub_mk]
  omega))

set_option hygiene false in
macro "oLb_id" : tactic => `(tactic| (
  simp only [oStemPos, oHeadPos, oddLInitOff, p0Off, q0Off, SurgicalDict.offsetP0, SurgicalDict.offsetQ0, oddKCoeff, altOff,
    coeffOff, hst, hW, htr, ↓reduceIte, Bool.false_eq_true, LCorrections.oddBridgeShift,
    vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2, hpw, parentsAt_append_singleton, Parents.step, Parents.current,
    Parents.combine, Prod.smul_mk, smul_eq_mul, SpecialCells.parents_threes, SpecialCells.parents_twos, parents_nil]
  refine Prod.ext ?_ ?_ <;> simp <;> push_cast <;> ring))

theorem oddL_conn_base_empty_one_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (elong : Bool)
    (hst : stripTrailing Digit.two w = ([] ++ [Digit.one]))
    (htr : (!(([] ++ [Digit.one])).isEmpty && (([] ++ [Digit.one])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE []) (vQ1 ([] ++ [Digit.one])) (vQ2 ([] ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt ([] ++ [Digit.one])).1 true) (vP1 ([] ++ [Digit.one])) (vP2 ([] ++ [Digit.one])))
    (hBase : ∀ x : Site, x ∈ (aE []).dom ↔ x ∈ paperStairAltTile 3) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_two w, hst]; simp [W1Odd, phase]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some [] := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd _ _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt ([] ++ [Digit.one])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt ([] ++ [Digit.one])).even.num,
      (parentsAt ([] ++ [Digit.one])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt ([] ++ [Digit.one])).even.den⟩, (parentsAt ([] ++ [Digit.one])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w true elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ([] ++ [Digit.one]) + vQ2 ([] ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (vQ1 ([] ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hS.cXi (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w true elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ([] ++ [Digit.one]) + vQ2 ([] ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (vP1 ([] ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hB.cXi (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w true elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (((0 : ℤ) * 3 + (1 : ℤ), (0 : ℤ) * 3 + (1 : ℤ))) o1 o2 f1 f2 hB.c0 ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w true elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * 3 + (-1 : ℤ), (0 : ℤ) * 3 + (-1 : ℤ))) (((0 : ℤ) * 3 + (2 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_base_empty_one_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (elong : Bool)
    (hst : stripTrailing Digit.two w = ([] ++ [Digit.one]))
    (htr : (!(([] ++ [Digit.one])).isEmpty && (([] ++ [Digit.one])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE []) (vQ1 ([] ++ [Digit.one])) (vQ2 ([] ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt ([] ++ [Digit.one])).1 true) (vP1 ([] ++ [Digit.one])) (vP2 ([] ++ [Digit.one])))
    (hBase : ∀ x : Site, x ∈ (aE []).dom ↔ x ∈ paperStairAltTile 3) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_two w, hst]; simp [W1Odd, phase]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some [] := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd _ _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt ([] ++ [Digit.one])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt ([] ++ [Digit.one])).even.num,
      (parentsAt ([] ++ [Digit.one])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt ([] ++ [Digit.one])).even.den⟩, (parentsAt ([] ++ [Digit.one])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w false elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vQ2 ([] ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hS.cY1 (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w false elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vP2 ([] ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hB.cY1 (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w false elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ([] ++ [Digit.one]) + vP2 ([] ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (((0 : ℤ) * 3 + (0 : ℤ), (0 : ℤ) * 3 + (2 : ℤ))) o1 o2 f1 f2 hB.cD ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w false elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * 3 + (1 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) (((0 : ℤ) * 3 + (-2 : ℤ), (0 : ℤ) * 3 + (-1 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_base_threes_one_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.two w = ((List.replicate j Digit.three) ++ [Digit.one]))
    (htr : (!(((List.replicate j Digit.three) ++ [Digit.one])).isEmpty && (((List.replicate j Digit.three) ++ [Digit.one])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE (List.replicate j Digit.three)) (vQ1 ((List.replicate j Digit.three) ++ [Digit.one])) (vQ2 ((List.replicate j Digit.three) ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt ((List.replicate j Digit.three) ++ [Digit.one])).1 true) (vP1 ((List.replicate j Digit.three) ++ [Digit.one])) (vP2 ((List.replicate j Digit.three) ++ [Digit.one])))
    (hBase : ∀ x : Site, x ∈ (aE (List.replicate j Digit.three)).dom ↔ x ∈ paperStairAltTile (2 * (j : ℤ) + 3)) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_two w, hst]; simp [W1Odd, phase, List.count_replicate]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some (List.replicate j Digit.three) := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd _ _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).even.num,
      (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).even.den⟩, (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w true elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ((List.replicate j Digit.three) ++ [Digit.one]) + vQ2 ((List.replicate j Digit.three) ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (vQ1 ((List.replicate j Digit.three) ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hS.cXi (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w true elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ((List.replicate j Digit.three) ++ [Digit.one]) + vQ2 ((List.replicate j Digit.three) ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (vP1 ((List.replicate j Digit.three) ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hB.cXi (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w true elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ))) o1 o2 f1 f2 hB.c0 ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w true elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((-1 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (3 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (4 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_base_threes_one_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.two w = ((List.replicate j Digit.three) ++ [Digit.one]))
    (htr : (!(((List.replicate j Digit.three) ++ [Digit.one])).isEmpty && (((List.replicate j Digit.three) ++ [Digit.one])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE (List.replicate j Digit.three)) (vQ1 ((List.replicate j Digit.three) ++ [Digit.one])) (vQ2 ((List.replicate j Digit.three) ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt ((List.replicate j Digit.three) ++ [Digit.one])).1 true) (vP1 ((List.replicate j Digit.three) ++ [Digit.one])) (vP2 ((List.replicate j Digit.three) ++ [Digit.one])))
    (hBase : ∀ x : Site, x ∈ (aE (List.replicate j Digit.three)).dom ↔ x ∈ paperStairAltTile (2 * (j : ℤ) + 3)) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_two w, hst]; simp [W1Odd, phase, List.count_replicate]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some (List.replicate j Digit.three) := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd _ _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).even.num,
      (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).even.den⟩, (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w false elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vQ2 ((List.replicate j Digit.three) ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hS.cY1 (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w false elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vP2 ((List.replicate j Digit.three) ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hB.cY1 (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w false elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ((List.replicate j Digit.three) ++ [Digit.one])) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 hB.cX ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w false elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (4 : ℤ))) (((-1 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (3 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_base_twos_one_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.two w = ((List.replicate j Digit.two) ++ [Digit.one]))
    (htr : (!(((List.replicate j Digit.two) ++ [Digit.one])).isEmpty && (((List.replicate j Digit.two) ++ [Digit.one])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE (List.replicate j Digit.two)) (vQ1 ((List.replicate j Digit.two) ++ [Digit.one])) (vQ2 ((List.replicate j Digit.two) ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt ((List.replicate j Digit.two) ++ [Digit.one])).1 true) (vP1 ((List.replicate j Digit.two) ++ [Digit.one])) (vP2 ((List.replicate j Digit.two) ++ [Digit.one])))
    (hBase : ∀ x : Site, x ∈ (aE (List.replicate j Digit.two)).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (j : ℤ) + 2)) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_two w, hst]; simp [W1Odd, phase, List.count_replicate]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some (List.replicate j Digit.two) := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd _ _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).even.num,
      (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).even.den⟩, (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w true elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ((List.replicate j Digit.two) ++ [Digit.one]) + vQ2 ((List.replicate j Digit.two) ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (vQ1 ((List.replicate j Digit.two) ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hS.cXi (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w true elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ((List.replicate j Digit.two) ++ [Digit.one]) + vQ2 ((List.replicate j Digit.two) ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (vP1 ((List.replicate j Digit.two) ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hB.cXi (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w true elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (((1 : ℤ) * (2 * (j : ℤ) + 3) + (-2 : ℤ), (2 : ℤ) * (2 * (j : ℤ) + 3) + (-5 : ℤ))) o1 o2 f1 f2 hB.c0 ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w true elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) (((1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (-2 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_base_twos_one_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.two w = ((List.replicate j Digit.two) ++ [Digit.one]))
    (htr : (!(((List.replicate j Digit.two) ++ [Digit.one])).isEmpty && (((List.replicate j Digit.two) ++ [Digit.one])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE (List.replicate j Digit.two)) (vQ1 ((List.replicate j Digit.two) ++ [Digit.one])) (vQ2 ((List.replicate j Digit.two) ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt ((List.replicate j Digit.two) ++ [Digit.one])).1 true) (vP1 ((List.replicate j Digit.two) ++ [Digit.one])) (vP2 ((List.replicate j Digit.two) ++ [Digit.one])))
    (hBase : ∀ x : Site, x ∈ (aE (List.replicate j Digit.two)).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (j : ℤ) + 2)) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_two w, hst]; simp [W1Odd, phase, List.count_replicate]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some (List.replicate j Digit.two) := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd _ _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).even.num,
      (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).even.den⟩, (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w false elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vQ2 ((List.replicate j Digit.two) ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hS.cY1 (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w false elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vP2 ((List.replicate j Digit.two) ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hB.cY1 (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w false elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ((List.replicate j Digit.two) ++ [Digit.one])) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 hB.cX ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w false elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_base_twos_three_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.two w = ((List.replicate j Digit.two) ++ [Digit.three]))
    (htr : (!(((List.replicate j Digit.two) ++ [Digit.three])).isEmpty && (((List.replicate j Digit.two) ++ [Digit.three])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE (List.replicate j Digit.two)) (vQ1 ((List.replicate j Digit.two) ++ [Digit.three])) (vQ2 ((List.replicate j Digit.two) ++ [Digit.three])))
    (hB : StdCorners (regOdo S pO pE (regsAt ((List.replicate j Digit.two) ++ [Digit.three])).1 true) (vP1 ((List.replicate j Digit.two) ++ [Digit.three])) (vP2 ((List.replicate j Digit.two) ++ [Digit.three])))
    (hBase : ∀ x : Site, x ∈ (aE (List.replicate j Digit.two)).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (j : ℤ) + 2)) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_two w, hst]; simp [W1Odd, phase, List.count_replicate]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some (List.replicate j Digit.two) := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd _ _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt ((List.replicate j Digit.two) ++ [Digit.three])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.three])).even.num,
      (parentsAt ((List.replicate j Digit.two) ++ [Digit.three])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.three])).even.den⟩, (parentsAt ((List.replicate j Digit.two) ++ [Digit.three])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w true elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ((List.replicate j Digit.two) ++ [Digit.three]) + vQ2 ((List.replicate j Digit.two) ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) (vQ1 ((List.replicate j Digit.two) ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hS.cXi (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w true elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ2 ((List.replicate j Digit.two) ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.cY1 hB.c1 (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w true elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ((List.replicate j Digit.two) ++ [Digit.three])) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-2 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ))) o1 o2 f1 f2 hB.cX ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w true elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

theorem oddL_conn_base_twos_three_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.two w = ((List.replicate j Digit.two) ++ [Digit.three]))
    (htr : (!(((List.replicate j Digit.two) ++ [Digit.three])).isEmpty && (((List.replicate j Digit.two) ++ [Digit.three])).all (fun d => decide (d = Digit.three))) = false)
    (hS : StdCorners (pE (List.replicate j Digit.two)) (vQ1 ((List.replicate j Digit.two) ++ [Digit.three])) (vQ2 ((List.replicate j Digit.two) ++ [Digit.three])))
    (hB : StdCorners (regOdo S pO pE (regsAt ((List.replicate j Digit.two) ++ [Digit.three])).1 true) (vP1 ((List.replicate j Digit.two) ++ [Digit.three])) (vP2 ((List.replicate j Digit.two) ++ [Digit.three])))
    (hBase : ∀ x : Site, x ∈ (aE (List.replicate j Digit.two)).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (j : ℤ) + 2)) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_two w, hst]; simp [W1Odd, phase, List.count_replicate]
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some (List.replicate j Digit.two) := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd _ _ (by decide)
  have hpw : parentsAt w = ⟨⟨(parentsAt ((List.replicate j Digit.two) ++ [Digit.three])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.three])).even.num,
      (parentsAt ((List.replicate j Digit.two) ++ [Digit.three])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.three])).even.den⟩, (parentsAt ((List.replicate j Digit.two) ++ [Digit.three])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w false elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1 | h1
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vQ2 ((List.replicate j Digit.two) ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hS.cY1 (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w false elong hm
    rw [h2] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ((List.replicate j Digit.two) ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) (vP1 ((List.replicate j Digit.two) ++ [Digit.three]) + vP2 ((List.replicate j Digit.two) ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cXi hB.cD1 (by oLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_bridge S pO pE aO aE w false elong (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong 0 hm
    rw [hst] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (((1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (-2 : ℤ))) o1 o2 f1 f2 hB.c0 ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1]; simp) (by rw [e2 (Or.inl (by rw [hst]; exact htr))]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w false elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong (i' + 1) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) (((1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (-2 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by oLb_id)
      (by rw [e1 (Or.inl (by rw [hst]; exact htr))]; simp) (by rw [e2 (Or.inr (by omega))]; simp)

/-! ### The odd L-correction at the prefixes `3^j` -/

set_option hygiene false in
macro "oLs_id" : tactic => `(tactic| (
  simp only [oStemPos, oHeadPos, oddLInitOff, p0Off, q0Off, SurgicalDict.offsetP0, SurgicalDict.offsetQ0, oddKCoeff, altOff,
    coeffOff, hst, hW, htr, ↓reduceIte, Bool.false_eq_true, LCorrections.oddBridgeShift, Bool.true_and, Bool.not_false,
    vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2, hpw, parentsAt_append_singleton, Parents.step, Parents.current,
    Parents.combine, Prod.smul_mk, smul_eq_mul, SpecialCells.parents_threes, parents_nil]
  refine Prod.ext ?_ ?_ <;> simp <;> push_cast <;> ring))

theorem oddL_conn_special_empty_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (elong : Bool)
    (hst : stripTrailing Digit.two w = ([] ++ [Digit.three]))
    (hS : StdCorners (pE []) (vQ1 ([] ++ [Digit.three])) (vQ2 ([] ++ [Digit.three])))
    (hZ : ∀ x ∈ tileShape ZTile.zero, x ∈ S.zeroO.dom)
    (hBase : ∀ x : Site, x ∈ (aE []).dom ↔ x ∈ paperStairAltTile 3) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_two w, hst]; simp [W1Odd, phase]
  have htr : (!(([] ++ [Digit.three])).isEmpty && (([] ++ [Digit.three])).all (fun d => decide (d = Digit.three))) = true := by simp
  have h1 : (regsAt (stripTrailing Digit.two w)).1 = none := by
    rw [hst]; rfl
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some [] := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd _ _ (by decide)
  have hd : 2 * ((stripTrailing Digit.two w).length : ℤ) + 1 = 3 := by rw [hst]; simp
  have hpw : parentsAt w = ⟨⟨(parentsAt ([] ++ [Digit.three])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt ([] ++ [Digit.three])).even.num,
      (parentsAt ([] ++ [Digit.three])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt ([] ++ [Digit.three])).even.den⟩, (parentsAt ([] ++ [Digit.three])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w true elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ([] ++ [Digit.three]) + vQ2 ([] ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) (vQ1 ([] ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hS.cXi (by oLs_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w true elong hm
    rw [h2] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ2 ([] ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cY1 (hZ ((1 : ℤ), (1 : ℤ)) (by simp [tileShape])) (by oLs_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong 0 hm
    rw [h2] at o1 o2
    have he : oStemPos w true (trailingCount Digit.two w) + (vQ1 ([] ++ [Digit.three]) + vQ2 ([] ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) = oHeadPos w true 0 + (((0 : ℤ) * 3 + (0 : ℤ), (0 : ℤ) * 3 + (2 : ℤ))) := by oLs_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ([] ++ [Digit.three]) + vQ2 ([] ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (((0 : ℤ) * 3 + (0 : ℤ), (0 : ℤ) * 3 + (2 : ℤ))) o1 o2 f1 f2 hS.cD ((hBase _).2 (by base_mem)) he
      (by rw [e1]; simp) (fun hx => ?_)
    have hA := oL_head0_exc S pO pE aO aE w true elong hm _ hx
    rw [he, add_sub_cancel_left, hd] at hA
    simp only [paperStairAltA, Set.mem_union, Set.mem_setOf_eq] at hA
    omega
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w true elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong (i' + 1) hm
    rw [h2] at o1 o2
    have he : oHeadPos w true i' + (((0 : ℤ) * 3 + (1 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) = oHeadPos w true (i' + 1) + (((0 : ℤ) * 3 + (-2 : ℤ), (0 : ℤ) * 3 + (-1 : ℤ))) := by oLs_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * 3 + (1 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) (((0 : ℤ) * 3 + (-2 : ℤ), (0 : ℤ) * 3 + (-1 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) he ?_
      (by rw [e2 (Or.inr (by omega))]; simp)
    rcases Nat.eq_zero_or_pos i' with rfl | hi'
    · intro hx
      have hA := oL_head0_exc S pO pE aO aE w true elong (by omega) _ hx
      rw [add_sub_cancel_left, hd] at hA
      simp only [paperStairAltA, Set.mem_union, Set.mem_setOf_eq] at hA
      omega
    · rw [e1 (Or.inr hi')]; simp

theorem oddL_conn_special_empty_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (elong : Bool)
    (hst : stripTrailing Digit.two w = ([] ++ [Digit.three]))
    (hS : StdCorners (pE []) (vQ1 ([] ++ [Digit.three])) (vQ2 ([] ++ [Digit.three])))
    (hZ : ∀ x ∈ tileShape ZTile.zero, x ∈ S.zeroO.dom)
    (hBase : ∀ x : Site, x ∈ (aE []).dom ↔ x ∈ paperStairAltTile 3) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_two w, hst]; simp [W1Odd, phase]
  have htr : (!(([] ++ [Digit.three])).isEmpty && (([] ++ [Digit.three])).all (fun d => decide (d = Digit.three))) = true := by simp
  have h1 : (regsAt (stripTrailing Digit.two w)).1 = none := by
    rw [hst]; rfl
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some [] := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd _ _ (by decide)
  have hd : 2 * ((stripTrailing Digit.two w).length : ℤ) + 1 = 3 := by rw [hst]; simp
  have hpw : parentsAt w = ⟨⟨(parentsAt ([] ++ [Digit.three])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt ([] ++ [Digit.three])).even.num,
      (parentsAt ([] ++ [Digit.three])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt ([] ++ [Digit.three])).even.den⟩, (parentsAt ([] ++ [Digit.three])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w false elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vQ2 ([] ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hS.cY1 (by oLs_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w false elong hm
    rw [h2] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ([] ++ [Digit.three])) (((0 : ℤ), (2 : ℤ))) o1 o2 f1 f2 hS.cX (hZ ((0 : ℤ), (2 : ℤ)) (by simp [tileShape])) (by oLs_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong 0 hm
    rw [h2] at o1 o2
    have he : oStemPos w false (trailingCount Digit.two w) + (((0 : ℤ), (0 : ℤ))) = oHeadPos w false 0 + (((0 : ℤ) * 3 + (1 : ℤ), (0 : ℤ) * 3 + (1 : ℤ))) := by oLs_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (((0 : ℤ) * 3 + (1 : ℤ), (0 : ℤ) * 3 + (1 : ℤ))) o1 o2 f1 f2 hS.c0 ((hBase _).2 (by base_mem)) he
      (by rw [e1]; simp) (fun hx => ?_)
    have hA := oL_head0_exc S pO pE aO aE w false elong hm _ hx
    rw [he, add_sub_cancel_left, hd] at hA
    simp only [paperStairAltA, Set.mem_union, Set.mem_setOf_eq] at hA
    omega
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w false elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong (i' + 1) hm
    rw [h2] at o1 o2
    have he : oHeadPos w false i' + (((0 : ℤ) * 3 + (-1 : ℤ), (0 : ℤ) * 3 + (-1 : ℤ))) = oHeadPos w false (i' + 1) + (((0 : ℤ) * 3 + (2 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) := by oLs_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * 3 + (-1 : ℤ), (0 : ℤ) * 3 + (-1 : ℤ))) (((0 : ℤ) * 3 + (2 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) he ?_
      (by rw [e2 (Or.inr (by omega))]; simp)
    rcases Nat.eq_zero_or_pos i' with rfl | hi'
    · intro hx
      have hA := oL_head0_exc S pO pE aO aE w false elong (by omega) _ hx
      rw [add_sub_cancel_left, hd] at hA
      simp only [paperStairAltA, Set.mem_union, Set.mem_setOf_eq] at hA
      omega
    · rw [e1 (Or.inr hi')]; simp

theorem oddL_conn_special_threes_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.two w = ((List.replicate j Digit.three) ++ [Digit.three]))
    (hS : StdCorners (pE (List.replicate j Digit.three)) (vQ1 ((List.replicate j Digit.three) ++ [Digit.three])) (vQ2 ((List.replicate j Digit.three) ++ [Digit.three])))
    (hZ : ∀ x ∈ tileShape ZTile.zero, x ∈ S.zeroO.dom)
    (hBase : ∀ x : Site, x ∈ (aE (List.replicate j Digit.three)).dom ↔ x ∈ paperStairAltTile (2 * (j : ℤ) + 3)) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_two w, hst]; simp [W1Odd, phase, List.count_replicate]
  have htr : (!(((List.replicate j Digit.three) ++ [Digit.three])).isEmpty && (((List.replicate j Digit.three) ++ [Digit.three])).all (fun d => decide (d = Digit.three))) = true := by simp
  have h1 : (regsAt (stripTrailing Digit.two w)).1 = none := by
    rw [hst]
    rw [show (List.replicate j Digit.three ++ [Digit.three]) = List.replicate (j + 1) Digit.three by rw [List.replicate_succ']]
    exact SpecialCells.regs_threes_fst (j + 1)
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some (List.replicate j Digit.three) := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd _ _ (by decide)
  have hd : 2 * ((stripTrailing Digit.two w).length : ℤ) + 1 = (2 * (j : ℤ) + 3) := by rw [hst]; simp; ring
  have hpw : parentsAt w = ⟨⟨(parentsAt ((List.replicate j Digit.three) ++ [Digit.three])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.three])).even.num,
      (parentsAt ((List.replicate j Digit.three) ++ [Digit.three])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.three])).even.den⟩, (parentsAt ((List.replicate j Digit.three) ++ [Digit.three])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w true elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ((List.replicate j Digit.three) ++ [Digit.three]) + vQ2 ((List.replicate j Digit.three) ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) (vQ1 ((List.replicate j Digit.three) ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cD1 hS.cXi (by oLs_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w true elong hm
    rw [h2] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ2 ((List.replicate j Digit.three) ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.cY1 (hZ ((1 : ℤ), (1 : ℤ)) (by simp [tileShape])) (by oLs_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w true elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong 0 hm
    rw [h2] at o1 o2
    have he : oStemPos w true (trailingCount Digit.two w) + (vQ1 ((List.replicate j Digit.three) ++ [Digit.three]) + vQ2 ((List.replicate j Digit.three) ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) = oHeadPos w true 0 + (((-1 : ℤ) * (2 * (j : ℤ) + 3) + (3 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ))) := by oLs_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ((List.replicate j Digit.three) ++ [Digit.three]) + vQ2 ((List.replicate j Digit.three) ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (((-1 : ℤ) * (2 * (j : ℤ) + 3) + (3 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ))) o1 o2 f1 f2 hS.cD ((hBase _).2 (by base_mem)) he
      (by rw [e1]; simp) (fun hx => ?_)
    have hA := oL_head0_exc S pO pE aO aE w true elong hm _ hx
    rw [he, add_sub_cancel_left, hd] at hA
    simp only [paperStairAltA, Set.mem_union, Set.mem_setOf_eq] at hA
    omega
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w true elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w true elong (i' + 1) hm
    rw [h2] at o1 o2
    have he : oHeadPos w true i' + (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (4 : ℤ))) = oHeadPos w true (i' + 1) + (((-1 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (3 : ℤ))) := by oLs_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (4 : ℤ))) (((-1 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (3 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) he ?_
      (by rw [e2 (Or.inr (by omega))]; simp)
    rcases Nat.eq_zero_or_pos i' with rfl | hi'
    · intro hx
      have hA := oL_head0_exc S pO pE aO aE w true elong (by omega) _ hx
      rw [add_sub_cancel_left, hd] at hA
      simp only [paperStairAltA, Set.mem_union, Set.mem_setOf_eq] at hA
      omega
    · rw [e1 (Or.inr hi')]; simp

theorem oddL_conn_special_threes_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.two w = ((List.replicate j Digit.three) ++ [Digit.three]))
    (hS : StdCorners (pE (List.replicate j Digit.three)) (vQ1 ((List.replicate j Digit.three) ++ [Digit.three])) (vQ2 ((List.replicate j Digit.three) ++ [Digit.three])))
    (hZ : ∀ x ∈ tileShape ZTile.zero, x ∈ S.zeroO.dom)
    (hBase : ∀ x : Site, x ∈ (aE (List.replicate j Digit.three)).dom ↔ x ∈ paperStairAltTile (2 * (j : ℤ) + 3)) :
    (overlapGraph (goodPart (oddLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_two w, hst]; simp [W1Odd, phase, List.count_replicate]
  have htr : (!(((List.replicate j Digit.three) ++ [Digit.three])).isEmpty && (((List.replicate j Digit.three) ++ [Digit.three])).all (fun d => decide (d = Digit.three))) = true := by simp
  have h1 : (regsAt (stripTrailing Digit.two w)).1 = none := by
    rw [hst]
    rw [show (List.replicate j Digit.three ++ [Digit.three]) = List.replicate (j + 1) Digit.three by rw [List.replicate_succ']]
    exact SpecialCells.regs_threes_fst (j + 1)
  have h2 : (regsAt (stripTrailing Digit.two w)).2 = some (List.replicate j Digit.three) := by
    rw [hst]; exact ConnectedAltL.regs_pre_snd _ _ (by decide)
  have hd : 2 * ((stripTrailing Digit.two w).length : ℤ) + 1 = (2 * (j : ℤ) + 3) := by rw [hst]; simp; ring
  have hpw : parentsAt w = ⟨⟨(parentsAt ((List.replicate j Digit.three) ++ [Digit.three])).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.three])).even.num,
      (parentsAt ((List.replicate j Digit.three) ++ [Digit.three])).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.three])).even.den⟩, (parentsAt ((List.replicate j Digit.three) ++ [Digit.three])).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two w, hst]
    exact JointRot.parents_append_twos _ _
  have hlen := oL_length S pO pE aO aE w false elong
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h2] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (vQ2 ((List.replicate j Digit.three) ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.c1 hS.cY1 (by oLs_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.two w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.two w + 1 := by omega
    refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_bridge S pO pE aO aE w false elong hm
    rw [h2] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ((List.replicate j Digit.three) ++ [Digit.three])) (((0 : ℤ), (2 : ℤ))) o1 o2 f1 f2 hS.cX (hZ ((0 : ℤ), (2 : ℤ)) (by simp [tileShape])) (by oLs_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.two w + 2 + i := ⟨m - (trailingCount Digit.two w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.two w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_stem S pO pE aO aE w false elong (trailingCount Digit.two w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong 0 hm
    rw [h2] at o1 o2
    have he : oStemPos w false (trailingCount Digit.two w) + (((0 : ℤ), (0 : ℤ))) = oHeadPos w false 0 + (((0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ))) := by oLs_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ))) o1 o2 f1 f2 hS.c0 ((hBase _).2 (by base_mem)) he
      (by rw [e1]; simp) (fun hx => ?_)
    have hA := oL_head0_exc S pO pE aO aE w false elong hm _ hx
    rw [he, add_sub_cancel_left, hd] at hA
    simp only [paperStairAltA, Set.mem_union, Set.mem_setOf_eq] at hA
    omega
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.two w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := oL_head S pO pE aO aE w false elong i' (by omega)
    obtain ⟨o2, f2, e2⟩ := oL_head S pO pE aO aE w false elong (i' + 1) hm
    rw [h2] at o1 o2
    have he : oHeadPos w false i' + (((-1 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (3 : ℤ))) = oHeadPos w false (i' + 1) + (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (4 : ℤ))) := by oLs_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((-1 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (3 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (4 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) he ?_
      (by rw [e2 (Or.inr (by omega))]; simp)
    rcases Nat.eq_zero_or_pos i' with rfl | hi'
    · intro hx
      have hA := oL_head0_exc S pO pE aO aE w false elong (by omega) _ hx
      rw [add_sub_cancel_left, hd] at hA
      simp only [paperStairAltA, Set.mem_union, Set.mem_setOf_eq] at hA
      omega
    · rw [e1 (Or.inr hi')]; simp

/-! ### The even L-correction -/

set_option hygiene false in
macro "eL_id" : tactic => `(tactic| (
  simp only [eStemPos, eHeadPos, evenLInitOff, p0Off, q0Off, SurgicalDict.offsetP0, SurgicalDict.offsetQ0, evenKCoeff, altOff,
    coeffOff, altD, altP0Coeff, altShifts, hst, hW, hW1, hs2, ↓reduceIte, Bool.false_eq_true, Bool.true_and,
    Bool.not_false, Bool.not_true, beq_self_eq_true, Bool.false_beq, Bool.true_beq,
    vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2, hpw, parentsAt_append_singleton, Parents.step, Parents.current,
    Parents.combine, Prod.smul_mk, smul_eq_mul, SpecialCells.parents_threes, SpecialCells.parents_twos, parents_nil]
  refine Prod.ext ?_ ?_ <;> simp <;> push_cast <;> ring))

set_option hygiene false in
macro "eLb_id" : tactic => `(tactic| (
  simp only [eStemPos, eHeadPos, evenLInitOff, p0Off, q0Off, SurgicalDict.offsetP0, SurgicalDict.offsetQ0, evenKCoeff, altOff,
    coeffOff, hst, hW, hs2, ↓reduceIte, Bool.false_eq_true, Bool.true_and,
    Bool.not_false, Bool.not_true, beq_self_eq_true, Bool.false_beq, Bool.true_beq,
    vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2, hpw, parentsAt_append_singleton, Parents.step, Parents.current,
    Parents.combine, Prod.smul_mk, smul_eq_mul, SpecialCells.parents_threes, SpecialCells.parents_twos, parents_nil]
  refine Prod.ext ?_ ?_ <;> simp <;> push_cast <;> ring))

theorem W1Odd_strip_three (w : Word) : W1Odd (stripTrailing Digit.three w) = W1Odd w := by
  conv_rhs => rw [← JointRot.strip_append_replicate Digit.three w]
  unfold W1Odd phase
  simp [List.count_append, List.count_replicate]

theorem evenL_conn_one_false_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.three w = (w1 ++ [Digit.one]))
    (hdb : (!((w1 ++ [Digit.one])).isEmpty && ((w1 ++ [Digit.one])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO w1) (vP1 (w1 ++ [Digit.one])) (vP2 (w1 ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.one])).2 false) (vQ1 (w1 ++ [Digit.one])) (vQ2 (w1 ++ [Digit.one])))
    (hW1 : W1Odd w1 = false)
    (hX : (altOff w1 (altP0Coeff false .dsP1Plus) + (vP2 w1 + ((1 : ℤ), (0 : ℤ)))) ∈ (aO w1).dom ∧ (altOff w1 (altP0Coeff false .dsP1Minus) + (altShifts false (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) ∈ (aO w1).dom ∧ (altOff w1 (altP0Coeff false .dsP1Plus) + (((0 : ℤ), (0 : ℤ)))) ∈ (aO w1).dom) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_three w, hst]; simp [ConnectedAltL.W1Odd_snoc_one, hW1]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = false := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt (w1 ++ [Digit.one])).odd, ⟨(parentsAt (w1 ++ [Digit.one])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.one])).odd.num,
      (parentsAt (w1 ++ [Digit.one])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.one])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w true elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w true elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 (w1 ++ [Digit.one]) + vP2 (w1 ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vP2 (w1 ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hS.cY1i (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 (w1 ++ [Digit.one])) (((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.cX hB.c0 (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ2 (w1 ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) (altOff w1 (altP0Coeff false .dsP1Plus) + (vP2 w1 + ((1 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 hB.cY1 (hX.1) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (altOff w1 (altP0Coeff false .dsP1Minus) + (altShifts false (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) (altOff w1 (altP0Coeff false .dsP1Plus) + (((0 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 (hX.2.1) (hX.2.2) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_one_false_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.three w = (w1 ++ [Digit.one]))
    (hdb : (!((w1 ++ [Digit.one])).isEmpty && ((w1 ++ [Digit.one])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO w1) (vP1 (w1 ++ [Digit.one])) (vP2 (w1 ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.one])).2 false) (vQ1 (w1 ++ [Digit.one])) (vQ2 (w1 ++ [Digit.one])))
    (hW1 : W1Odd w1 = false)
    (hX : (altOff w1 (altP0Coeff false .dsP1Minus) + (altShifts false (vP2 w1) (vQ1 w1)).1 + (vP1 w1)) ∈ (aO w1).dom ∧ (altOff w1 (altP0Coeff false .dsP1Plus) + (((0 : ℤ), (0 : ℤ)))) ∈ (aO w1).dom ∧ (altOff w1 (altP0Coeff false .dsP1Minus) + (altShifts false (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) ∈ (aO w1).dom) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_three w, hst]; simp [ConnectedAltL.W1Odd_snoc_one, hW1]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = false := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt (w1 ++ [Digit.one])).odd, ⟨(parentsAt (w1 ++ [Digit.one])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.one])).odd.num,
      (parentsAt (w1 ++ [Digit.one])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.one])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w false elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w false elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vP1 (w1 ++ [Digit.one])) o1 o2 f1 f2 hS.c0 hS.cX (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP2 (w1 ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vQ1 (w1 ++ [Digit.one]) + vQ2 (w1 ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cY1i hB.cD (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 (w1 ++ [Digit.one])) (altOff w1 (altP0Coeff false .dsP1Minus) + (altShifts false (vP2 w1) (vQ1 w1)).1 + (vP1 w1)) o1 o2 f1 f2 hB.cX (hX.1) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (altOff w1 (altP0Coeff false .dsP1Plus) + (((0 : ℤ), (0 : ℤ)))) (altOff w1 (altP0Coeff false .dsP1Minus) + (altShifts false (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 (hX.2.1) (hX.2.2) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_one_true_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.three w = (w1 ++ [Digit.one]))
    (hdb : (!((w1 ++ [Digit.one])).isEmpty && ((w1 ++ [Digit.one])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO w1) (vP1 (w1 ++ [Digit.one])) (vP2 (w1 ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.one])).2 false) (vQ1 (w1 ++ [Digit.one])) (vQ2 (w1 ++ [Digit.one])))
    (hW1 : W1Odd w1 = true)
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (aO w1).dom ∧ altD w1 true - a ∈ (aO w1).dom)
    (hX : (altOff w1 (altP0Coeff true .dsP1Plus) + (vP1 w1 + vP2 w1 + ((1 : ℤ), (-1 : ℤ)))) ∈ (aO w1).dom) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_three w, hst]; simp [ConnectedAltL.W1Odd_snoc_one, hW1]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = false := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt (w1 ++ [Digit.one])).odd, ⟨(parentsAt (w1 ++ [Digit.one])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.one])).odd.num,
      (parentsAt (w1 ++ [Digit.one])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.one])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w true elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w true elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vP1 (w1 ++ [Digit.one])) o1 o2 f1 f2 hS.c0 hS.cX (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vQ1 (w1 ++ [Digit.one])) o1 o2 f1 f2 hS.c0 hB.cX (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 (w1 ++ [Digit.one]) + vQ2 (w1 ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (altOff w1 (altP0Coeff true .dsP1Plus) + (vP1 w1 + vP2 w1 + ((1 : ℤ), (-1 : ℤ)))) o1 o2 f1 f2 hB.cD (hX) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (altD w1 true - ((0 : ℤ), (0 : ℤ))) (altOff w1 (altP0Coeff true .dsP1Plus) + (vP1 w1 + vP2 w1 + ((1 : ℤ), (-1 : ℤ)))) o1 o2 f1 f2 ((hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).2) (hX) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_one_true_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.three w = (w1 ++ [Digit.one]))
    (hdb : (!((w1 ++ [Digit.one])).isEmpty && ((w1 ++ [Digit.one])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO w1) (vP1 (w1 ++ [Digit.one])) (vP2 (w1 ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.one])).2 false) (vQ1 (w1 ++ [Digit.one])) (vQ2 (w1 ++ [Digit.one])))
    (hW1 : W1Odd w1 = true)
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (aO w1).dom ∧ altD w1 true - a ∈ (aO w1).dom)
    (hX : (altOff w1 (altP0Coeff true .dsP1Minus) + (altShifts true (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) ∈ (aO w1).dom) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_three w, hst]; simp [ConnectedAltL.W1Odd_snoc_one, hW1]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = false := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt (w1 ++ [Digit.one])).odd, ⟨(parentsAt (w1 ++ [Digit.one])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.one])).odd.num,
      (parentsAt (w1 ++ [Digit.one])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.one])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w false elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w false elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 (w1 ++ [Digit.one]) + vP2 (w1 ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vP2 (w1 ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hS.cY1i (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 (w1 ++ [Digit.one]) + vP2 (w1 ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vQ2 (w1 ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hB.cY1i (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (altOff w1 (altP0Coeff true .dsP1Minus) + (altShifts true (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 hB.c0 (hX) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (altOff w1 (altP0Coeff true .dsP1Minus) + (altShifts true (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 ((hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).1) (hX) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_two_false_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.three w = (w1 ++ [Digit.two]))
    (hdb : (!((w1 ++ [Digit.two])).isEmpty && ((w1 ++ [Digit.two])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO w1) (vP1 (w1 ++ [Digit.two])) (vP2 (w1 ++ [Digit.two])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.two])).2 false) (vQ1 (w1 ++ [Digit.two])) (vQ2 (w1 ++ [Digit.two])))
    (hW1 : W1Odd w1 = false)
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (aO w1).dom ∧ altD w1 true - a ∈ (aO w1).dom)
    (hX : (altOff w1 (altP0Coeff false .dsP1Minus) + (altShifts false (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) ∈ (aO w1).dom ∧ (altOff w1 (altP0Coeff false .dsP1Plus) + (((0 : ℤ), (0 : ℤ)))) ∈ (aO w1).dom) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_three w, hst]; simp [ConnectedAltL.W1Odd_snoc_two, hW1]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = true := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt (w1 ++ [Digit.two])).odd, ⟨(parentsAt (w1 ++ [Digit.two])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.two])).odd.num,
      (parentsAt (w1 ++ [Digit.two])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.two])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w true elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w true elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vP1 (w1 ++ [Digit.two])) o1 o2 f1 f2 hS.c0 hS.cX (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vQ1 (w1 ++ [Digit.two])) o1 o2 f1 f2 hS.c0 hB.cX (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ2 (w1 ++ [Digit.two]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hB.cY1 ((hH ((1 : ℤ), (0 : ℤ)) (by simp [tileShape])).1) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (altOff w1 (altP0Coeff false .dsP1Minus) + (altShifts false (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) (altOff w1 (altP0Coeff false .dsP1Plus) + (((0 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 (hX.1) (hX.2) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_two_false_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.three w = (w1 ++ [Digit.two]))
    (hdb : (!((w1 ++ [Digit.two])).isEmpty && ((w1 ++ [Digit.two])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO w1) (vP1 (w1 ++ [Digit.two])) (vP2 (w1 ++ [Digit.two])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.two])).2 false) (vQ1 (w1 ++ [Digit.two])) (vQ2 (w1 ++ [Digit.two])))
    (hW1 : W1Odd w1 = false)
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (aO w1).dom ∧ altD w1 true - a ∈ (aO w1).dom)
    (hX : (altOff w1 (altP0Coeff false .dsP1Plus) + (((0 : ℤ), (0 : ℤ)))) ∈ (aO w1).dom ∧ (altOff w1 (altP0Coeff false .dsP1Minus) + (altShifts false (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) ∈ (aO w1).dom) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_three w, hst]; simp [ConnectedAltL.W1Odd_snoc_two, hW1]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = true := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt (w1 ++ [Digit.two])).odd, ⟨(parentsAt (w1 ++ [Digit.two])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.two])).odd.num,
      (parentsAt (w1 ++ [Digit.two])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.two])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w false elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w false elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 (w1 ++ [Digit.two]) + vP2 (w1 ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (vP2 (w1 ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hS.cY1i (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 (w1 ++ [Digit.two]) + vP2 (w1 ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (vQ2 (w1 ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hB.cY1i (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 (w1 ++ [Digit.two]) - ((0 : ℤ), (1 : ℤ))) (altD w1 true - ((1 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hB.cXi ((hH ((1 : ℤ), (0 : ℤ)) (by simp [tileShape])).2) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (altOff w1 (altP0Coeff false .dsP1Plus) + (((0 : ℤ), (0 : ℤ)))) (altOff w1 (altP0Coeff false .dsP1Minus) + (altShifts false (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 (hX.1) (hX.2) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_two_true_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.three w = (w1 ++ [Digit.two]))
    (hdb : (!((w1 ++ [Digit.two])).isEmpty && ((w1 ++ [Digit.two])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO w1) (vP1 (w1 ++ [Digit.two])) (vP2 (w1 ++ [Digit.two])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.two])).2 false) (vQ1 (w1 ++ [Digit.two])) (vQ2 (w1 ++ [Digit.two])))
    (hW1 : W1Odd w1 = true)
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (aO w1).dom ∧ altD w1 true - a ∈ (aO w1).dom)
    (hX : (altOff w1 (altP0Coeff true .q1Plus) + (vQ1 w1 - ((0 : ℤ), (1 : ℤ)))) ∈ (aO w1).dom ∧ (altOff w1 (altP0Coeff true .dsP1Plus) + (vP1 w1 + vP2 w1 + ((1 : ℤ), (-1 : ℤ)))) ∈ (aO w1).dom) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_three w, hst]; simp [ConnectedAltL.W1Odd_snoc_two, hW1]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = true := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt (w1 ++ [Digit.two])).odd, ⟨(parentsAt (w1 ++ [Digit.two])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.two])).odd.num,
      (parentsAt (w1 ++ [Digit.two])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.two])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w true elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w true elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 (w1 ++ [Digit.two]) + vP2 (w1 ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (vP2 (w1 ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hS.cY1i (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 (w1 ++ [Digit.two])) (((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.cX hB.c0 (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 (w1 ++ [Digit.two]) + vQ2 (w1 ++ [Digit.two]) + ((0 : ℤ), (-1 : ℤ))) (altOff w1 (altP0Coeff true .q1Plus) + (vQ1 w1 - ((0 : ℤ), (1 : ℤ)))) o1 o2 f1 f2 hB.cD1 (hX.1) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (altD w1 true - ((0 : ℤ), (0 : ℤ))) (altOff w1 (altP0Coeff true .dsP1Plus) + (vP1 w1 + vP2 w1 + ((1 : ℤ), (-1 : ℤ)))) o1 o2 f1 f2 ((hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).2) (hX.2) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_two_true_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w w1 : Word) (elong : Bool)
    (hst : stripTrailing Digit.three w = (w1 ++ [Digit.two]))
    (hdb : (!((w1 ++ [Digit.two])).isEmpty && ((w1 ++ [Digit.two])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO w1) (vP1 (w1 ++ [Digit.two])) (vP2 (w1 ++ [Digit.two])))
    (hB : StdCorners (regOdo S pO pE (regsAt (w1 ++ [Digit.two])).2 false) (vQ1 (w1 ++ [Digit.two])) (vQ2 (w1 ++ [Digit.two])))
    (hW1 : W1Odd w1 = true)
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (aO w1).dom ∧ altD w1 true - a ∈ (aO w1).dom)
    (hX : (altOff w1 (altP0Coeff true .q1Minus) + (vQ2 w1 + ((1 : ℤ), (0 : ℤ)))) ∈ (aO w1).dom ∧ (altOff w1 (altP0Coeff true .dsP1Minus) + (altShifts true (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) ∈ (aO w1).dom) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_three w, hst]; simp [ConnectedAltL.W1Odd_snoc_two, hW1]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = true := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some w1 := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt (w1 ++ [Digit.two])).odd, ⟨(parentsAt (w1 ++ [Digit.two])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.two])).odd.num,
      (parentsAt (w1 ++ [Digit.two])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt (w1 ++ [Digit.two])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w false elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w false elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vP1 (w1 ++ [Digit.two])) o1 o2 f1 f2 hS.c0 hS.cX (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP2 (w1 ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (vQ1 (w1 ++ [Digit.two]) + vQ2 (w1 ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cY1i hB.cD (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (0 : ℤ))) (altOff w1 (altP0Coeff true .q1Minus) + (vQ2 w1 + ((1 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 hB.c1 (hX.1) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (altOff w1 (altP0Coeff true .dsP1Minus) + (altShifts true (vP2 w1) (vQ1 w1)).1 + (((0 : ℤ), (0 : ℤ)))) o1 o2 f1 f2 ((hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).1) (hX.2) (by eL_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_base_empty_one_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (elong : Bool)
    (hst : stripTrailing Digit.three w = ([] ++ [Digit.one]))
    (hdb : (!(([] ++ [Digit.one])).isEmpty && (([] ++ [Digit.one])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO []) (vP1 ([] ++ [Digit.one])) (vP2 ([] ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt ([] ++ [Digit.one])).2 false) (vQ1 ([] ++ [Digit.one])) (vQ2 ([] ++ [Digit.one])))
    (hBase : ∀ x : Site, x ∈ (aO []).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile 3) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_three w, hst]; simp [W1Odd, phase]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = false := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some [] := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt ([] ++ [Digit.one])).odd, ⟨(parentsAt ([] ++ [Digit.one])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt ([] ++ [Digit.one])).odd.num,
      (parentsAt ([] ++ [Digit.one])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt ([] ++ [Digit.one])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w true elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w true elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ([] ++ [Digit.one]) + vP2 ([] ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vP2 ([] ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hS.cY1i (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ([] ++ [Digit.one])) (((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.cX hB.c0 (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ([] ++ [Digit.one]) + vQ2 ([] ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (((0 : ℤ) * 3 + (4 : ℤ), (0 : ℤ) * 3 + (2 : ℤ))) o1 o2 f1 f2 hB.cD ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * 3 + (-1 : ℤ), (0 : ℤ) * 3 + (3 : ℤ))) (((0 : ℤ) * 3 + (0 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_base_empty_one_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (elong : Bool)
    (hst : stripTrailing Digit.three w = ([] ++ [Digit.one]))
    (hdb : (!(([] ++ [Digit.one])).isEmpty && (([] ++ [Digit.one])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO []) (vP1 ([] ++ [Digit.one])) (vP2 ([] ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt ([] ++ [Digit.one])).2 false) (vQ1 ([] ++ [Digit.one])) (vQ2 ([] ++ [Digit.one])))
    (hBase : ∀ x : Site, x ∈ (aO []).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile 3) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_three w, hst]; simp [W1Odd, phase]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = false := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some [] := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt ([] ++ [Digit.one])).odd, ⟨(parentsAt ([] ++ [Digit.one])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt ([] ++ [Digit.one])).odd.num,
      (parentsAt ([] ++ [Digit.one])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt ([] ++ [Digit.one])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w false elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w false elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vP1 ([] ++ [Digit.one])) o1 o2 f1 f2 hS.c0 hS.cX (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP2 ([] ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vQ1 ([] ++ [Digit.one]) + vQ2 ([] ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cY1i hB.cD (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (((0 : ℤ) * 3 + (-1 : ℤ), (0 : ℤ) * 3 + (3 : ℤ))) o1 o2 f1 f2 hB.c0 ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * 3 + (0 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) (((0 : ℤ) * 3 + (-1 : ℤ), (0 : ℤ) * 3 + (3 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_base_twos_one_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.three w = ((List.replicate j Digit.two) ++ [Digit.one]))
    (hdb : (!(((List.replicate j Digit.two) ++ [Digit.one])).isEmpty && (((List.replicate j Digit.two) ++ [Digit.one])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO (List.replicate j Digit.two)) (vP1 ((List.replicate j Digit.two) ++ [Digit.one])) (vP2 ((List.replicate j Digit.two) ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt ((List.replicate j Digit.two) ++ [Digit.one])).2 false) (vQ1 ((List.replicate j Digit.two) ++ [Digit.one])) (vQ2 ((List.replicate j Digit.two) ++ [Digit.one])))
    (hBase : ∀ x : Site, x ∈ (aO (List.replicate j Digit.two)).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (j : ℤ) + 3)) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_three w, hst]; simp [W1Odd, phase, List.count_replicate]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = false := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some (List.replicate j Digit.two) := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).odd, ⟨(parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).odd.num,
      (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w true elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w true elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ((List.replicate j Digit.two) ++ [Digit.one]) + vP2 ((List.replicate j Digit.two) ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vP2 ((List.replicate j Digit.two) ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hS.cY1i (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ((List.replicate j Digit.two) ++ [Digit.one])) (((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.cX hB.c0 (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ2 ((List.replicate j Digit.two) ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ))) o1 o2 f1 f2 hB.cY1 ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_base_twos_one_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.three w = ((List.replicate j Digit.two) ++ [Digit.one]))
    (hdb : (!(((List.replicate j Digit.two) ++ [Digit.one])).isEmpty && (((List.replicate j Digit.two) ++ [Digit.one])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO (List.replicate j Digit.two)) (vP1 ((List.replicate j Digit.two) ++ [Digit.one])) (vP2 ((List.replicate j Digit.two) ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt ((List.replicate j Digit.two) ++ [Digit.one])).2 false) (vQ1 ((List.replicate j Digit.two) ++ [Digit.one])) (vQ2 ((List.replicate j Digit.two) ++ [Digit.one])))
    (hBase : ∀ x : Site, x ∈ (aO (List.replicate j Digit.two)).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (j : ℤ) + 3)) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_three w, hst]; simp [W1Odd, phase, List.count_replicate]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = false := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some (List.replicate j Digit.two) := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).odd, ⟨(parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).odd.num,
      (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.one])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w false elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w false elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vP1 ((List.replicate j Digit.two) ++ [Digit.one])) o1 o2 f1 f2 hS.c0 hS.cX (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP2 ((List.replicate j Digit.two) ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vQ1 ((List.replicate j Digit.two) ++ [Digit.one]) + vQ2 ((List.replicate j Digit.two) ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cY1i hB.cD (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 hB.c0 ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_base_threes_one_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.three w = ((List.replicate j Digit.three) ++ [Digit.one]))
    (hdb : (!(((List.replicate j Digit.three) ++ [Digit.one])).isEmpty && (((List.replicate j Digit.three) ++ [Digit.one])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO (List.replicate j Digit.three)) (vP1 ((List.replicate j Digit.three) ++ [Digit.one])) (vP2 ((List.replicate j Digit.three) ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt ((List.replicate j Digit.three) ++ [Digit.one])).2 false) (vQ1 ((List.replicate j Digit.three) ++ [Digit.one])) (vQ2 ((List.replicate j Digit.three) ++ [Digit.one])))
    (hBase : ∀ x : Site, x ∈ (aO (List.replicate j Digit.three)).dom ↔ x - ((1 : ℤ), (1 : ℤ)) ∈ paperLadderAltTile (2 * (j : ℤ) + 2)) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_three w, hst]; simp [W1Odd, phase, List.count_replicate]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = false := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some (List.replicate j Digit.three) := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).odd, ⟨(parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).odd.num,
      (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w true elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w true elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ((List.replicate j Digit.three) ++ [Digit.one]) + vP2 ((List.replicate j Digit.three) ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vP2 ((List.replicate j Digit.three) ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hS.cY1i (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ((List.replicate j Digit.three) ++ [Digit.one])) (((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.cX hB.c0 (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ2 ((List.replicate j Digit.three) ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ) * (2 * (j : ℤ) + 3) + (-2 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (2 : ℤ))) o1 o2 f1 f2 hB.cY1 ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((-1 : ℤ) * (2 * (j : ℤ) + 3) + (3 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_base_threes_one_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.three w = ((List.replicate j Digit.three) ++ [Digit.one]))
    (hdb : (!(((List.replicate j Digit.three) ++ [Digit.one])).isEmpty && (((List.replicate j Digit.three) ++ [Digit.one])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO (List.replicate j Digit.three)) (vP1 ((List.replicate j Digit.three) ++ [Digit.one])) (vP2 ((List.replicate j Digit.three) ++ [Digit.one])))
    (hB : StdCorners (regOdo S pO pE (regsAt ((List.replicate j Digit.three) ++ [Digit.one])).2 false) (vQ1 ((List.replicate j Digit.three) ++ [Digit.one])) (vQ2 ((List.replicate j Digit.three) ++ [Digit.one])))
    (hBase : ∀ x : Site, x ∈ (aO (List.replicate j Digit.three)).dom ↔ x - ((1 : ℤ), (1 : ℤ)) ∈ paperLadderAltTile (2 * (j : ℤ) + 2)) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = true := by
    rw [← W1Odd_strip_three w, hst]; simp [W1Odd, phase, List.count_replicate]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = false := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some (List.replicate j Digit.three) := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).odd, ⟨(parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).odd.num,
      (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.one])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w false elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w false elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vP1 ((List.replicate j Digit.three) ++ [Digit.one])) o1 o2 f1 f2 hS.c0 hS.cX (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP2 ((List.replicate j Digit.three) ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vQ1 ((List.replicate j Digit.three) ++ [Digit.one]) + vQ2 ((List.replicate j Digit.three) ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cY1i hB.cD (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ1 ((List.replicate j Digit.three) ++ [Digit.one])) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (2 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ))) o1 o2 f1 f2 hB.cX ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) (((-1 : ℤ) * (2 * (j : ℤ) + 3) + (3 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_base_threes_two_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.three w = ((List.replicate j Digit.three) ++ [Digit.two]))
    (hdb : (!(((List.replicate j Digit.three) ++ [Digit.two])).isEmpty && (((List.replicate j Digit.three) ++ [Digit.two])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO (List.replicate j Digit.three)) (vP1 ((List.replicate j Digit.three) ++ [Digit.two])) (vP2 ((List.replicate j Digit.three) ++ [Digit.two])))
    (hB : StdCorners (regOdo S pO pE (regsAt ((List.replicate j Digit.three) ++ [Digit.two])).2 false) (vQ1 ((List.replicate j Digit.three) ++ [Digit.two])) (vQ2 ((List.replicate j Digit.three) ++ [Digit.two])))
    (hBase : ∀ x : Site, x ∈ (aO (List.replicate j Digit.three)).dom ↔ x - ((1 : ℤ), (1 : ℤ)) ∈ paperLadderAltTile (2 * (j : ℤ) + 2)) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_three w, hst]; simp [W1Odd, phase, List.count_replicate]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = true := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some (List.replicate j Digit.three) := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt ((List.replicate j Digit.three) ++ [Digit.two])).odd, ⟨(parentsAt ((List.replicate j Digit.three) ++ [Digit.two])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.two])).odd.num,
      (parentsAt ((List.replicate j Digit.three) ++ [Digit.two])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.two])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w true elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w true elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vP1 ((List.replicate j Digit.three) ++ [Digit.two])) o1 o2 f1 f2 hS.c0 hS.cX (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vQ1 ((List.replicate j Digit.three) ++ [Digit.two])) o1 o2 f1 f2 hS.c0 hB.cX (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vQ2 ((List.replicate j Digit.three) ++ [Digit.two]) + ((1 : ℤ), (0 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 hB.cY1 ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((-1 : ℤ) * (2 * (j : ℤ) + 3) + (3 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_base_threes_two_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.three w = ((List.replicate j Digit.three) ++ [Digit.two]))
    (hdb : (!(((List.replicate j Digit.three) ++ [Digit.two])).isEmpty && (((List.replicate j Digit.three) ++ [Digit.two])).all (fun d => decide (d = Digit.two))) = false)
    (hS : StdCorners (pO (List.replicate j Digit.three)) (vP1 ((List.replicate j Digit.three) ++ [Digit.two])) (vP2 ((List.replicate j Digit.three) ++ [Digit.two])))
    (hB : StdCorners (regOdo S pO pE (regsAt ((List.replicate j Digit.three) ++ [Digit.two])).2 false) (vQ1 ((List.replicate j Digit.three) ++ [Digit.two])) (vQ2 ((List.replicate j Digit.three) ++ [Digit.two])))
    (hBase : ∀ x : Site, x ∈ (aO (List.replicate j Digit.three)).dom ↔ x - ((1 : ℤ), (1 : ℤ)) ∈ paperLadderAltTile (2 * (j : ℤ) + 2)) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_three w, hst]; simp [W1Odd, phase, List.count_replicate]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = true := by
    rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some (List.replicate j Digit.three) := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt ((List.replicate j Digit.three) ++ [Digit.two])).odd, ⟨(parentsAt ((List.replicate j Digit.three) ++ [Digit.two])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.two])).odd.num,
      (parentsAt ((List.replicate j Digit.three) ++ [Digit.two])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.three) ++ [Digit.two])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb' : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by rw [hst]; exact hdb
  have hlen := eL_length S pO pE aO aE w false elong
  rw [hdb'] at hlen
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hlen
  obtain ⟨hBr, hHd⟩ := eL_gen S pO pE aO aE w false elong hdb'
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ((List.replicate j Digit.three) ++ [Digit.two]) + vP2 ((List.replicate j Digit.three) ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (vP2 ((List.replicate j Digit.three) ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hS.cY1i (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [hst] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ((List.replicate j Digit.three) ++ [Digit.two]) + vP2 ((List.replicate j Digit.three) ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (vQ2 ((List.replicate j Digit.three) ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hB.cY1i (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd 0 hm
    rw [hst] at o1
    rw [h1] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (2 : ℤ))) o1 o2 f1 f2 hB.c0 ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * (2 * (j : ℤ) + 3) + (1 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) (((-1 : ℤ) * (2 * (j : ℤ) + 3) + (3 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)

theorem evenL_conn_special_empty_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (elong : Bool)
    (hst : stripTrailing Digit.three w = ([] ++ [Digit.two]))
    (hS : StdCorners (pO []) (vP1 ([] ++ [Digit.two])) (vP2 ([] ++ [Digit.two])))
    (hOne : ∀ x ∈ tileShape ZTile.one, x ∈ S.oneO.dom)
    (hBase : ∀ x : Site, x ∈ (aO []).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile 3) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_three w, hst]; simp [W1Odd, phase]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = true := by rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some [] := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt ([] ++ [Digit.two])).odd, ⟨(parentsAt ([] ++ [Digit.two])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt ([] ++ [Digit.two])).odd.num,
      (parentsAt ([] ++ [Digit.two])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt ([] ++ [Digit.two])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = true := by rw [hst]; simp
  have hc : (!W1Odd w && !true) = false := by rw [hW]; rfl
  have hd : 2 * ((stripTrailing Digit.three w).length : ℤ) + 1 = 3 := by rw [hst]; simp
  have hlen := eL_length S pO pE aO aE w true elong
  rw [hdb, hc] at hlen
  simp only [Bool.true_and, Bool.false_eq_true, ↓reduceIte] at hlen
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vP1 ([] ++ [Digit.two])) o1 o2 f1 f2 hS.c0 hS.cX (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  have h2 : (regsAt (stripTrailing Digit.three w)).2 = none := by
    rw [hst]; rfl
  obtain ⟨hBr, hEn, hHd⟩ := eL_dbl S pO pE aO aE w true elong hdb hc
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (((1 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.c0 (hOne ((1 : ℤ), (1 : ℤ)) (by simp [tileShape])) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 3) with h3' | h3'
  · obtain rfl : m = trailingCount Digit.three w + 2 := by omega
    refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hEn hm
    rw [h2] at o1
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (1 : ℤ))) (((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 (hOne ((1 : ℤ), (1 : ℤ)) (by simp [tileShape])) (by simp [JointFamily.enlOdo, tileShape]) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 3 + i := ⟨m - (trailingCount Digit.three w + 3), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 2, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hEn (by omega)
    obtain ⟨o2, f2, -, x2⟩ := hHd 0 hm
    rw [h1] at o2
    have he : evenLInitOff w true + altOff (stripTrailing Digit.three w)
        ((trailingCount Digit.three w : ℤ) • (evenKCoeff (W1Odd w) true
          (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).1 +
        (evenKCoeff (W1Odd w) true (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).2.1) +
        ((1 : ℤ), (1 : ℤ)) + (((-1 : ℤ), (1 : ℤ))) = eHeadPos w true 0 + (((0 : ℤ) * 3 + (0 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) := by eLb_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((-1 : ℤ), (1 : ℤ))) (((0 : ℤ) * 3 + (0 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) o1 o2 f1 f2 (by simp [JointFamily.enlOdo, tileShape]) ((hBase _).2 (by base_mem)) he
      (by rw [e1]; simp) (fun hx => ?_)
    have hA := x2 _ hx
    rw [he, add_sub_cancel_left, hd] at hA
    simp only [paperNearStairAltA, Set.mem_union, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at hA
    omega
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 3 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1', x1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2, -⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    have he : eHeadPos w true i' + (((0 : ℤ) * 3 + (-1 : ℤ), (0 : ℤ) * 3 + (3 : ℤ))) = eHeadPos w true (i' + 1) + (((0 : ℤ) * 3 + (0 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) := by eLb_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * 3 + (-1 : ℤ), (0 : ℤ) * 3 + (3 : ℤ))) (((0 : ℤ) * 3 + (0 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) he ?_
      (by rw [e2 (by omega)]; simp)
    rcases Nat.eq_zero_or_pos i' with rfl | hi'
    · intro hx
      have hA := x1 _ hx
      rw [add_sub_cancel_left, hd] at hA
      simp only [paperNearStairAltA, Set.mem_union, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at hA
      omega
    · rw [e1' hi']; simp

theorem evenL_conn_special_empty_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (elong : Bool)
    (hst : stripTrailing Digit.three w = ([] ++ [Digit.two]))
    (hS : StdCorners (pO []) (vP1 ([] ++ [Digit.two])) (vP2 ([] ++ [Digit.two])))
    (hBase : ∀ x : Site, x ∈ (aO []).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile 3) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_three w, hst]; simp [W1Odd, phase]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = true := by rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some [] := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt ([] ++ [Digit.two])).odd, ⟨(parentsAt ([] ++ [Digit.two])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt ([] ++ [Digit.two])).odd.num,
      (parentsAt ([] ++ [Digit.two])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt ([] ++ [Digit.two])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = true := by rw [hst]; simp
  have hc : (!W1Odd w && !false) = true := by rw [hW]; rfl
  have hd : 2 * ((stripTrailing Digit.three w).length : ℤ) + 1 = 3 := by rw [hst]; simp
  have hlen := eL_length S pO pE aO aE w false elong
  rw [hdb, hc] at hlen
  simp only [Bool.true_and, ↓reduceIte] at hlen
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ([] ++ [Digit.two]) + vP2 ([] ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (vP2 ([] ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hS.cY1i (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨hEn, hHd⟩ := eL_dbl01 S pO pE aO aE w false elong hdb hc
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hEn hm
    rw [h1] at o1
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ([] ++ [Digit.two]) + vP2 ([] ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.cD (by simp [JointFamily.enlOdo, tileShape]) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hEn (by omega)
    obtain ⟨o2, f2, -, x2⟩ := hHd 0 hm
    rw [h1] at o2
    have he : evenLInitOff w false + altOff (stripTrailing Digit.three w)
        ((trailingCount Digit.three w : ℤ) • (evenKCoeff (W1Odd w) false
          (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).1 +
        (evenKCoeff (W1Odd w) false (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).2.1) +
        ((1 : ℤ), (1 : ℤ)) + (((1 : ℤ), (-1 : ℤ))) = eHeadPos w false 0 + (((0 : ℤ) * 3 + (3 : ℤ), (0 : ℤ) * 3 + (5 : ℤ))) := by eLb_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (-1 : ℤ))) (((0 : ℤ) * 3 + (3 : ℤ), (0 : ℤ) * 3 + (5 : ℤ))) o1 o2 f1 f2 (by simp [JointFamily.enlOdo, tileShape]) ((hBase _).2 (by base_mem)) he
      (by rw [e1]; simp) (fun hx => ?_)
    have hA := x2 _ hx
    rw [he, add_sub_cancel_left, hd] at hA
    simp only [paperNearStairAltA, Set.mem_union, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at hA
    omega
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1', x1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2, -⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    have he : eHeadPos w false i' + (((0 : ℤ) * 3 + (0 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) = eHeadPos w false (i' + 1) + (((0 : ℤ) * 3 + (-1 : ℤ), (0 : ℤ) * 3 + (3 : ℤ))) := by eLb_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * 3 + (0 : ℤ), (0 : ℤ) * 3 + (0 : ℤ))) (((0 : ℤ) * 3 + (-1 : ℤ), (0 : ℤ) * 3 + (3 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) he ?_
      (by rw [e2 (by omega)]; simp)
    rcases Nat.eq_zero_or_pos i' with rfl | hi'
    · intro hx
      have hA := x1 _ hx
      rw [add_sub_cancel_left, hd] at hA
      simp only [paperNearStairAltA, Set.mem_union, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at hA
      omega
    · rw [e1' hi']; simp

theorem evenL_conn_special_twos_true (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.three w = ((List.replicate j Digit.two) ++ [Digit.two]))
    (hS : StdCorners (pO (List.replicate j Digit.two)) (vP1 ((List.replicate j Digit.two) ++ [Digit.two])) (vP2 ((List.replicate j Digit.two) ++ [Digit.two])))
    (hOne : ∀ x ∈ tileShape ZTile.one, x ∈ S.oneO.dom)
    (hBase : ∀ x : Site, x ∈ (aO (List.replicate j Digit.two)).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (j : ℤ) + 3)) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w true elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_three w, hst]; simp [W1Odd, phase, List.count_replicate]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = true := by rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some (List.replicate j Digit.two) := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt ((List.replicate j Digit.two) ++ [Digit.two])).odd, ⟨(parentsAt ((List.replicate j Digit.two) ++ [Digit.two])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.two])).odd.num,
      (parentsAt ((List.replicate j Digit.two) ++ [Digit.two])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.two])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = true := by rw [hst]; simp
  have hc : (!W1Odd w && !true) = false := by rw [hW]; rfl
  have hd : 2 * ((stripTrailing Digit.three w).length : ℤ) + 1 = (2 * (j : ℤ) + 3) := by rw [hst]; simp; ring
  have hlen := eL_length S pO pE aO aE w true elong
  rw [hdb, hc] at hlen
  simp only [Bool.true_and, Bool.false_eq_true, ↓reduceIte] at hlen
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w true elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (vP1 ((List.replicate j Digit.two) ++ [Digit.two])) o1 o2 f1 f2 hS.c0 hS.cX (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  have h2 : (regsAt (stripTrailing Digit.three w)).2 = none := by
    rw [hst]
    rw [show (List.replicate j Digit.two ++ [Digit.two]) = List.replicate (j + 1) Digit.two by rw [List.replicate_succ']]
    exact SpecialCells.regs_twos_snd (j + 1)
  obtain ⟨hBr, hEn, hHd⟩ := eL_dbl S pO pE aO aE w true elong hdb hc
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w true elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hBr hm
    rw [h1] at o1
    rw [h2] at o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ), (0 : ℤ))) (((1 : ℤ), (1 : ℤ))) o1 o2 f1 f2 hS.c0 (hOne ((1 : ℤ), (1 : ℤ)) (by simp [tileShape])) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 3) with h3' | h3'
  · obtain rfl : m = trailingCount Digit.three w + 2 := by omega
    refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hBr (by omega)
    obtain ⟨o2, f2, e2⟩ := hEn hm
    rw [h2] at o1
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (1 : ℤ))) (((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 (hOne ((1 : ℤ), (1 : ℤ)) (by simp [tileShape])) (by simp [JointFamily.enlOdo, tileShape]) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 3 + i := ⟨m - (trailingCount Digit.three w + 3), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 2, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hEn (by omega)
    obtain ⟨o2, f2, -, x2⟩ := hHd 0 hm
    rw [h1] at o2
    have he : evenLInitOff w true + altOff (stripTrailing Digit.three w)
        ((trailingCount Digit.three w : ℤ) • (evenKCoeff (W1Odd w) true
          (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).1 +
        (evenKCoeff (W1Odd w) true (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).2.1) +
        ((1 : ℤ), (1 : ℤ)) + (((-1 : ℤ), (1 : ℤ))) = eHeadPos w true 0 + (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) := by eLb_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((-1 : ℤ), (1 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 (by simp [JointFamily.enlOdo, tileShape]) ((hBase _).2 (by base_mem)) he
      (by rw [e1]; simp) (fun hx => ?_)
    have hA := x2 _ hx
    rw [he, add_sub_cancel_left, hd] at hA
    simp only [paperNearStairAltA, Set.mem_union, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at hA
    omega
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 3 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1', x1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2, -⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    have he : eHeadPos w true i' + (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) = eHeadPos w true (i' + 1) + (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) := by eLb_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) he ?_
      (by rw [e2 (by omega)]; simp)
    rcases Nat.eq_zero_or_pos i' with rfl | hi'
    · intro hx
      have hA := x1 _ hx
      rw [add_sub_cancel_left, hd] at hA
      simp only [paperNearStairAltA, Set.mem_union, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at hA
      omega
    · rw [e1' hi']; simp

theorem evenL_conn_special_twos_false (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (j : ℕ) (hj : 1 ≤ j) (elong : Bool)
    (hst : stripTrailing Digit.three w = ((List.replicate j Digit.two) ++ [Digit.two]))
    (hS : StdCorners (pO (List.replicate j Digit.two)) (vP1 ((List.replicate j Digit.two) ++ [Digit.two])) (vP2 ((List.replicate j Digit.two) ++ [Digit.two])))
    (hBase : ∀ x : Site, x ∈ (aO (List.replicate j Digit.two)).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (j : ℤ) + 3)) :
    (overlapGraph (goodPart (evenLPieces S pO pE aO aE w false elong))).Connected := by
  have hW : W1Odd w = false := by
    rw [← W1Odd_strip_three w, hst]; simp [W1Odd, phase, List.count_replicate]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = true := by rw [hst]; simp
  have h1 : (regsAt (stripTrailing Digit.three w)).1 = some (List.replicate j Digit.two) := by
    rw [hst]; exact ConnectedAltL.regs_pre_fst _ _ (by decide)
  have hpw : parentsAt w = ⟨(parentsAt ((List.replicate j Digit.two) ++ [Digit.two])).odd, ⟨(parentsAt ((List.replicate j Digit.two) ++ [Digit.two])).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.two])).odd.num,
      (parentsAt ((List.replicate j Digit.two) ++ [Digit.two])).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt ((List.replicate j Digit.two) ++ [Digit.two])).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three w, hst]
    exact JointRot.parents_append_threes _ _
  have hdb : (!(stripTrailing Digit.three w).isEmpty &&
      (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = true := by rw [hst]; simp
  have hc : (!W1Odd w && !false) = true := by rw [hW]; rfl
  have hd : 2 * ((stripTrailing Digit.three w).length : ℤ) + 1 = (2 * (j : ℤ) + 3) := by rw [hst]; simp; ring
  have hlen := eL_length S pO pE aO aE w false elong
  rw [hdb, hc] at hlen
  simp only [Bool.true_and, ↓reduceIte] at hlen
  refine connected_of_parent _ (by omega) (fun m hm hpos => ?_)
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 1) with h1' | h1'
  · obtain ⟨j', rfl⟩ : ∃ j', m = j' + 1 := ⟨m - 1, by omega⟩
    refine ⟨j', by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong j' (by omega) (by omega)
    obtain ⟨o2, f2, e2⟩ := eL_stem S pO pE aO aE w false elong (j' + 1) (by omega) hm
    rw [h1] at o1 o2
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ((List.replicate j Digit.two) ++ [Digit.two]) + vP2 ((List.replicate j Digit.two) ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (vP2 ((List.replicate j Digit.two) ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) o1 o2 f1 f2 hS.cD hS.cY1i (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨hEn, hHd⟩ := eL_dbl01 S pO pE aO aE w false elong hdb hc
  rcases Nat.lt_or_ge m (trailingCount Digit.three w + 2) with h2' | h2'
  · obtain rfl : m = trailingCount Digit.three w + 1 := by omega
    refine ⟨trailingCount Digit.three w, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := eL_stem S pO pE aO aE w false elong (trailingCount Digit.three w) le_rfl (by omega)
    obtain ⟨o2, f2, e2⟩ := hEn hm
    rw [h1] at o1
    exact adj_fields _ _ _ _ _ (by omega) _ _ _ _ (vP1 ((List.replicate j Digit.two) ++ [Digit.two]) + vP2 ((List.replicate j Digit.two) ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (((0 : ℤ), (0 : ℤ))) o1 o2 f1 f2 hS.cD (by simp [JointFamily.enlOdo, tileShape]) (by eLb_id)
      (by rw [e1]; simp) (by rw [e2]; simp)
  obtain ⟨i, rfl⟩ : ∃ i, m = trailingCount Digit.three w + 2 + i := ⟨m - (trailingCount Digit.three w + 2), by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨trailingCount Digit.three w + 1, by omega, ?_⟩
    obtain ⟨o1, f1, e1⟩ := hEn (by omega)
    obtain ⟨o2, f2, -, x2⟩ := hHd 0 hm
    rw [h1] at o2
    have he : evenLInitOff w false + altOff (stripTrailing Digit.three w)
        ((trailingCount Digit.three w : ℤ) • (evenKCoeff (W1Odd w) false
          (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).1 +
        (evenKCoeff (W1Odd w) false (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).2.1) +
        ((1 : ℤ), (1 : ℤ)) + (((1 : ℤ), (-1 : ℤ))) = eHeadPos w false 0 + (((1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (3 : ℤ) * (2 * (j : ℤ) + 3) + (-4 : ℤ))) := by eLb_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((1 : ℤ), (-1 : ℤ))) (((1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (3 : ℤ) * (2 * (j : ℤ) + 3) + (-4 : ℤ))) o1 o2 f1 f2 (by simp [JointFamily.enlOdo, tileShape]) ((hBase _).2 (by base_mem)) he
      (by rw [e1]; simp) (fun hx => ?_)
    have hA := x2 _ hx
    rw [he, add_sub_cancel_left, hd] at hA
    simp only [paperNearStairAltA, Set.mem_union, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at hA
    omega
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨trailingCount Digit.three w + 2 + i', by omega, ?_⟩
    obtain ⟨o1, f1, e1', x1⟩ := hHd i' (by omega)
    obtain ⟨o2, f2, e2, -⟩ := hHd (i' + 1) hm
    rw [h1] at o1 o2
    have he : eHeadPos w false i' + (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) = eHeadPos w false (i' + 1) + (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) := by eLb_id
    refine adj_fields _ _ _ _ _ (by omega) _ _ _ _ (((0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ), (0 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) (((0 : ℤ) * (2 * (j : ℤ) + 3) + (-1 : ℤ), (1 : ℤ) * (2 * (j : ℤ) + 3) + (0 : ℤ))) o1 o2 f1 f2 ((hBase _).2 (by base_mem)) ((hBase _).2 (by base_mem)) he ?_
      (by rw [e2 (by omega)]; simp)
    rcases Nat.eq_zero_or_pos i' with rfl | hi'
    · intro hx
      have hA := x1 _ hx
      rw [add_sub_cancel_left, hd] at hA
      simp only [paperNearStairAltA, Set.mem_union, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at hA
      omega
    · rw [e1' hi']; simp

/-! ### The facts from the family -/

open FLatticePaper.Tiles.JointRot (below_of_lt stdCorners_reg)
open FLatticePaper.Tiles.JointGlue (mem_pieceUnion)

/-- At a base word the alternate tile odometers of the family satisfy the paper base condition. -/
theorem base_alt_cond (D : JointData) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) (f : Word → JSlice) (u : Word)
    (hJu : IsJointSlice D f u) (hb : Standard.IsBase u) : SurgicalAlt.PaperAltBaseCond u (f u).aOdd (f u).aEven := by
  obtain ⟨-, hWA, hTP, -⟩ := hJu
  rw [(hTP.1 hb).2.2.1, (hTP.1 hb).2.2.2]
  have h := hWA.2.2.1 hb
  rw [hA] at h
  exact h

/-- The standard pieces of the decomposition of the even alternate tile odometer of a word that is not a base word. -/
theorem altE_sub (D : JointData) (f : Word → JSlice) (w1 : Word) (hb : ¬ Standard.IsBase w1) (hJ : IsJointSlice D f w1) :
    (∀ x ∈ (regOdo D.S (fun u => (below f w1 u).tOdd) (fun u => (below f w1 u).tEven) (regsAt w1).2 false).dom,
      altOff w1 (altQ0Coeff (W1Odd w1) .dsQ1Plus) + (altShifts (W1Odd w1) (vP2 w1) (vQ1 w1)).2 + x ∈ (f w1).aEven.dom) ∧
    (∀ x ∈ (regOdo D.S (fun u => (below f w1 u).tOdd) (fun u => (below f w1 u).tEven) (regsAt w1).2 false).dom,
      altOff w1 (altQ0Coeff (W1Odd w1) .dsQ1Minus) + x ∈ (f w1).aEven.dom) ∧
    (∀ x ∈ (regOdo D.S (fun u => (below f w1 u).tOdd) (fun u => (below f w1 u).tEven) (regsAt w1).1 true).dom,
      altOff w1 (altQ0Coeff (W1Odd w1) .p1Plus) + x ∈ (f w1).aEven.dom) ∧
    (∀ x ∈ (regOdo D.S (fun u => (below f w1 u).tOdd) (fun u => (below f w1 u).tEven) (regsAt w1).1 true).dom,
      altOff w1 (altQ0Coeff (W1Odd w1) .p1Minus) + x ∈ (f w1).aEven.dom) := by
  have hR := (hJ.2.2.1.2.1 hb).2.2.2
  rw [hR.1]
  refine ⟨fun x hx => ConnectedAltL.mem_pieceUnion_of (p := stdPiece (regOdo D.S (fun u => (below f w1 u).tOdd)
      (fun u => (below f w1 u).tEven) (regsAt w1).2 false) (altOff w1 (altQ0Coeff (W1Odd w1) .dsQ1Plus) +
      (altShifts (W1Odd w1) (vP2 w1) (vQ1 w1)).2) (altAff w1 (altQ0Coeff (W1Odd w1) .dsQ1Plus) + aP2 w1))
      (by unfold tileAltEvenPieces; simp) (by simp only [stdPiece, add_sub_cancel_left]; exact hx),
    fun x hx => ConnectedAltL.mem_pieceUnion_of (p := stdPiece (regOdo D.S (fun u => (below f w1 u).tOdd)
      (fun u => (below f w1 u).tEven) (regsAt w1).2 false) (altOff w1 (altQ0Coeff (W1Odd w1) .dsQ1Minus))
      (altAff w1 (altQ0Coeff (W1Odd w1) .dsQ1Minus)))
      (by unfold tileAltEvenPieces; simp) (by simp only [stdPiece, add_sub_cancel_left]; exact hx),
    fun x hx => ConnectedAltL.mem_pieceUnion_of (p := stdPiece (regOdo D.S (fun u => (below f w1 u).tOdd)
      (fun u => (below f w1 u).tEven) (regsAt w1).1 true) (altOff w1 (altQ0Coeff (W1Odd w1) .p1Plus))
      (altAff w1 (altQ0Coeff (W1Odd w1) .p1Plus)))
      (by unfold tileAltEvenPieces; simp) (by simp only [stdPiece, add_sub_cancel_left]; exact hx),
    fun x hx => ConnectedAltL.mem_pieceUnion_of (p := stdPiece (regOdo D.S (fun u => (below f w1 u).tOdd)
      (fun u => (below f w1 u).tEven) (regsAt w1).1 true) (altOff w1 (altQ0Coeff (W1Odd w1) .p1Minus))
      (altAff w1 (altQ0Coeff (W1Odd w1) .p1Minus)))
      (by unfold tileAltEvenPieces; simp) (by simp only [stdPiece, add_sub_cancel_left]; exact hx)⟩

/-- The standard pieces of the decomposition of the odd alternate tile odometer of a word that is not a base word. -/
theorem altO_sub (D : JointData) (f : Word → JSlice) (w1 : Word) (hb : ¬ Standard.IsBase w1) (hJ : IsJointSlice D f w1) :
    (∀ x ∈ (regOdo D.S (fun u => (below f w1 u).tOdd) (fun u => (below f w1 u).tEven) (regsAt w1).1 true).dom,
      altOff w1 (altP0Coeff (W1Odd w1) .dsP1Plus) + x ∈ (f w1).aOdd.dom) ∧
    (∀ x ∈ (regOdo D.S (fun u => (below f w1 u).tOdd) (fun u => (below f w1 u).tEven) (regsAt w1).1 true).dom,
      altOff w1 (altP0Coeff (W1Odd w1) .dsP1Minus) + (altShifts (W1Odd w1) (vP2 w1) (vQ1 w1)).1 + x ∈ (f w1).aOdd.dom) ∧
    (∀ x ∈ (regOdo D.S (fun u => (below f w1 u).tOdd) (fun u => (below f w1 u).tEven) (regsAt w1).2 false).dom,
      altOff w1 (altP0Coeff (W1Odd w1) .q1Plus) + x ∈ (f w1).aOdd.dom) ∧
    (∀ x ∈ (regOdo D.S (fun u => (below f w1 u).tOdd) (fun u => (below f w1 u).tEven) (regsAt w1).2 false).dom,
      altOff w1 (altP0Coeff (W1Odd w1) .q1Minus) + x ∈ (f w1).aOdd.dom) := by
  have hR := (hJ.2.2.1.2.1 hb).2.2.1
  rw [hR.1]
  refine ⟨fun x hx => ConnectedAltL.mem_pieceUnion_of (p := stdPiece (regOdo D.S (fun u => (below f w1 u).tOdd)
      (fun u => (below f w1 u).tEven) (regsAt w1).1 true) (altOff w1 (altP0Coeff (W1Odd w1) .dsP1Plus))
      (altAff w1 (altP0Coeff (W1Odd w1) .dsP1Plus)))
      (by unfold tileAltOddPieces; simp) (by simp only [stdPiece, add_sub_cancel_left]; exact hx),
    fun x hx => ConnectedAltL.mem_pieceUnion_of (p := stdPiece (regOdo D.S (fun u => (below f w1 u).tOdd)
      (fun u => (below f w1 u).tEven) (regsAt w1).1 true) (altOff w1 (altP0Coeff (W1Odd w1) .dsP1Minus) +
      (altShifts (W1Odd w1) (vP2 w1) (vQ1 w1)).1) (altAff w1 (altP0Coeff (W1Odd w1) .dsP1Minus) + aP2 w1))
      (by unfold tileAltOddPieces; simp) (by simp only [stdPiece, add_sub_cancel_left]; exact hx),
    fun x hx => ConnectedAltL.mem_pieceUnion_of (p := stdPiece (regOdo D.S (fun u => (below f w1 u).tOdd)
      (fun u => (below f w1 u).tEven) (regsAt w1).2 false) (altOff w1 (altP0Coeff (W1Odd w1) .q1Plus))
      (altAff w1 (altP0Coeff (W1Odd w1) .q1Plus)))
      (by unfold tileAltOddPieces; simp) (by simp only [stdPiece, add_sub_cancel_left]; exact hx),
    fun x hx => ConnectedAltL.mem_pieceUnion_of (p := stdPiece (regOdo D.S (fun u => (below f w1 u).tOdd)
      (fun u => (below f w1 u).tEven) (regsAt w1).2 false) (altOff w1 (altP0Coeff (W1Odd w1) .q1Minus))
      (altAff w1 (altP0Coeff (W1Odd w1) .q1Minus)))
      (by unfold tileAltOddPieces; simp) (by simp only [stdPiece, add_sub_cancel_left]; exact hx)⟩

/-- **The overlap graphs of the odd L-corrections are connected**, for the paper data, from the family below the word. -/
theorem connOddL_of (D : JointData) (hS0 : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hJ : ∀ u : Word, u.length < w.length → IsJointSlice D f u)
    (hT : ∀ u : Word, u.length < w.length → TileProps u (f u).tOdd (f u).tEven (f u).aOdd (f u).aEven)
    (plus elong : Bool) (hdef : OddLDefined w) :
    (overlapGraph (goodPart (oddLPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
      (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) w plus elong))).Connected := by
  obtain ⟨w1, s, k, hs, hw⟩ := hdef
  have hst : stripTrailing Digit.two w = w1 ++ [s] := by rw [hw]; exact JointRot.strip_of_defined _ _ hs _ _
  have hlt : w1.length < w.length := by rw [hw]; simp
  have hbel : below f w w1 = f w1 := below_of_lt f w w1 hlt
  have hJ1 := hJ w1 hlt
  have hT1 := hT w1 hlt
  have hJ1' : ∀ u : Word, u.length < w1.length → IsJointSlice D f u := fun u hu => hJ u (by omega)
  have h2 : (regsAt (w1 ++ [s])).2 = some w1 := ConnectedAltL.regs_pre_snd w1 s hs
  have hSt : StdCorners ((fun u => (below f w u).tEven) w1) (vQ1 (w1 ++ [s])) (vQ2 (w1 ++ [s])) := by
    have h := ConnectedAltL.stdCorners_snd' D f (below f w) (w1 ++ [s]) w1 h2 hbel hJ1
    rw [h2] at h; exact h
  have hH : ∀ a ∈ tileShape ZTile.one, a ∈ ((fun u => (below f w u).aEven) w1).dom ∧
      altD w1 false - a ∈ ((fun u => (below f w u).aEven) w1).dom := by
    simp only [hbel]; exact ConnectedAltL.altHalfTurn_pts _ _ _ hT1.2.2.2.2.2
  have hbc : Standard.IsBase w1 → SurgicalAlt.PaperAltBaseCond w1 (f w1).aOdd (f w1).aEven :=
    base_alt_cond D hA f w1 hJ1
  have hZ : ∀ x ∈ tileShape ZTile.zero, x ∈ D.S.zeroO.dom := by
    rw [hS0]; intro x hx; exact (SpecialCells.mem_zeroTile_iff x).2 hx
  cases s
  · have hBr : StdCorners (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (regsAt (w1 ++ [Digit.one])).1 true) (vP1 (w1 ++ [Digit.one])) (vP2 (w1 ++ [Digit.one])) :=
      ConnectedAltL.stdCorners_fst' D f (below f w) _ w1 (ConnectedAltL.regs_pre_fst w1 _ (by decide)) hbel hJ1
    have htr : (!(w1 ++ [Digit.one]).isEmpty && (w1 ++ [Digit.one]).all (fun d => decide (d = Digit.three))) = false := by
      simp
    by_cases hb1 : Standard.IsBase w1
    · by_cases he : w1 = []
      · subst he
        have hB : ∀ x : Site, x ∈ ((fun u => (below f w u).aEven) []).dom ↔ x ∈ paperStairAltTile 3 := by
          simp only [hbel]; exact ((hbc hb1).1 rfl).2.2.1
        cases plus
        · exact oddL_conn_base_empty_one_false _ _ _ _ _ w elong hst htr hSt hBr hB
        · exact oddL_conn_base_empty_one_true _ _ _ _ _ w elong hst htr hSt hBr hB
      · have hj : 1 ≤ w1.length := List.length_pos_of_ne_nil he
        rcases hb1 with h0 | h3 | h2'
        · exact absurd h0 he
        · obtain ⟨j, rfl⟩ : ∃ j, w1 = List.replicate j Digit.three := ⟨w1.length, List.eq_replicate_iff.mpr ⟨rfl, h3⟩⟩
          simp only [List.length_replicate] at hj
          have hB : ∀ x : Site, x ∈ ((fun u => (below f w u).aEven) (List.replicate j Digit.three)).dom ↔
              x ∈ paperStairAltTile (2 * (j : ℤ) + 3) := by
            simp only [hbel]; exact ((hbc (Or.inr (Or.inl h3))).2.1 j hj rfl).2.2.1
          cases plus
          · exact oddL_conn_base_threes_one_false _ _ _ _ _ w j hj elong hst htr hSt hBr hB
          · exact oddL_conn_base_threes_one_true _ _ _ _ _ w j hj elong hst htr hSt hBr hB
        · obtain ⟨j, rfl⟩ : ∃ j, w1 = List.replicate j Digit.two := ⟨w1.length, List.eq_replicate_iff.mpr ⟨rfl, h2'⟩⟩
          simp only [List.length_replicate] at hj
          have hB : ∀ x : Site, x ∈ ((fun u => (below f w u).aEven) (List.replicate j Digit.two)).dom ↔
              x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (j : ℤ) + 2) := by
            simp only [hbel]; exact ((hbc (Or.inr (Or.inr h2'))).2.2 j hj rfl).2.2.1
          cases plus
          · exact oddL_conn_base_twos_one_false _ _ _ _ _ w j hj elong hst htr hSt hBr hB
          · exact oddL_conn_base_twos_one_true _ _ _ _ _ w j hj elong hst htr hSt hBr hB
    · obtain ⟨hP', hQ'⟩ := stdCorners_reg D f w1 hb1 hJ1'
      have sE := altE_sub D f w1 hb1 hJ1
      cases hW1 : W1Odd w1
      · rw [hW1] at sE
        cases plus
        · exact oddL_conn_one_false_false _ _ _ _ _ w w1 elong hst hW1 htr hSt hBr hH (by simp only [hbel]; exact (sE.2.2.2 _ hP'.cY1i))
        · exact oddL_conn_one_false_true _ _ _ _ _ w w1 elong hst hW1 htr hSt hBr hH (by simp only [hbel]; exact (sE.2.2.1 _ hP'.cX))
      · rw [hW1] at sE
        cases plus
        · exact oddL_conn_one_true_false _ _ _ _ _ w w1 elong hst hW1 htr hSt hBr (by simp only [hbel]; exact ⟨(sE.1 _ hQ'.cY1), (sE.2.1 _ hQ'.c0), (sE.1 _ hQ'.c0)⟩)
        · exact oddL_conn_one_true_true _ _ _ _ _ w w1 elong hst hW1 htr hSt hBr (by simp only [hbel]; exact ⟨(sE.2.1 _ hQ'.cX), (sE.1 _ hQ'.c0), (sE.2.1 _ hQ'.c0)⟩)
  · exact absurd rfl hs
  · by_cases hb1 : Standard.IsBase w1
    · by_cases hall : ∀ d ∈ w1, d = Digit.three
      · -- the prefix `3^(j+1)`
        obtain ⟨j, rfl⟩ : ∃ j, w1 = List.replicate j Digit.three := ⟨w1.length, List.eq_replicate_iff.mpr ⟨rfl, hall⟩⟩
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · have hB : ∀ x : Site, x ∈ ((fun u => (below f w u).aEven) (List.replicate 0 Digit.three)).dom ↔
              x ∈ paperStairAltTile 3 := by
            simp only [hbel]; exact ((hbc (Or.inl rfl)).1 rfl).2.2.1
          cases plus
          · exact oddL_conn_special_empty_false _ _ _ _ _ w elong hst hSt hZ hB
          · exact oddL_conn_special_empty_true _ _ _ _ _ w elong hst hSt hZ hB
        · have hB : ∀ x : Site, x ∈ ((fun u => (below f w u).aEven) (List.replicate j Digit.three)).dom ↔
              x ∈ paperStairAltTile (2 * (j : ℤ) + 3) := by
            simp only [hbel]; exact ((hbc (Or.inr (Or.inl hall))).2.1 j hj rfl).2.2.1
          cases plus
          · exact oddL_conn_special_threes_false _ _ _ _ _ w j hj elong hst hSt hZ hB
          · exact oddL_conn_special_threes_true _ _ _ _ _ w j hj elong hst hSt hZ hB
      · -- `2^j`, `j ≥ 1`
        have h2' : ∀ d ∈ w1, d = Digit.two := by
          rcases hb1 with h0 | h3 | h2'
          · subst h0; simp at hall
          · exact absurd h3 hall
          · exact h2'
        obtain ⟨j, rfl⟩ : ∃ j, w1 = List.replicate j Digit.two := ⟨w1.length, List.eq_replicate_iff.mpr ⟨rfl, h2'⟩⟩
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
          rcases j with _ | j'
          · simp at hall
          · exact ⟨j', rfl⟩
        have htr : (!(List.replicate (j' + 1) Digit.two ++ [Digit.three]).isEmpty &&
            (List.replicate (j' + 1) Digit.two ++ [Digit.three]).all (fun d => decide (d = Digit.three))) = false := by
          simp [List.replicate_succ]
        have hBr : StdCorners (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
            (regsAt (List.replicate (j' + 1) Digit.two ++ [Digit.three])).1 true)
            (vP1 (List.replicate (j' + 1) Digit.two ++ [Digit.three])) (vP2 (List.replicate (j' + 1) Digit.two ++ [Digit.three])) :=
          ConnectedAltL.stdCorners_fst' D f (below f w) _ (List.replicate j' Digit.two)
            (by rw [JointRot.regsAt_append_singleton]; exact SpecialCells.regs_twos_fst' j')
            (below_of_lt f w _ (by rw [hw]; simp; omega)) (hJ _ (by rw [hw]; simp; omega))
        have hB : ∀ x : Site, x ∈ ((fun u => (below f w u).aEven) (List.replicate (j' + 1) Digit.two)).dom ↔
            x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * ((j' + 1 : ℕ) : ℤ) + 2) := by
          simp only [hbel]; exact ((hbc (Or.inr (Or.inr h2'))).2.2 (j' + 1) (by omega) rfl).2.2.1
        cases plus
        · exact oddL_conn_base_twos_three_false _ _ _ _ _ w (j' + 1) (by omega) elong hst htr hSt hBr hB
        · exact oddL_conn_base_twos_three_true _ _ _ _ _ w (j' + 1) (by omega) elong hst htr hSt hBr hB
    · obtain ⟨hP', hQ'⟩ := stdCorners_reg D f w1 hb1 hJ1'
      have sE := altE_sub D f w1 hb1 hJ1
      obtain ⟨u, hu⟩ := (JointRot.regs_some w1 hb1).1
      have hul := JointInduction.regsAt_lt w1 u (Or.inl hu)
      have hBr : StdCorners (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
          (regsAt (w1 ++ [Digit.three])).1 true) (vP1 (w1 ++ [Digit.three])) (vP2 (w1 ++ [Digit.three])) :=
        ConnectedAltL.stdCorners_fst' D f (below f w) _ u (by rw [JointRot.regsAt_append_singleton]; exact hu)
          (below_of_lt f w u (by omega)) (hJ u (by omega))
      have htr : (!(w1 ++ [Digit.three]).isEmpty && (w1 ++ [Digit.three]).all (fun d => decide (d = Digit.three))) = false := by
        rw [Bool.eq_false_iff]; intro h
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
        exact hb1 (Or.inr (Or.inl (fun d hd => h.2 d (List.mem_append_left _ hd))))
      cases hW1 : W1Odd w1
      · rw [hW1] at sE
        cases plus
        · exact oddL_conn_three_false_false _ _ _ _ _ w w1 elong hst hW1 htr hSt hBr hH (by simp only [hbel]; exact (sE.2.2.1 _ hP'.cX))
        · exact oddL_conn_three_false_true _ _ _ _ _ w w1 elong hst hW1 htr hSt hBr hH (by simp only [hbel]; exact (sE.2.2.2 _ hP'.cY1i))
      · rw [hW1] at sE
        cases plus
        · exact oddL_conn_three_true_false _ _ _ _ _ w w1 elong hst hW1 htr hSt hBr hH (by simp only [hbel]; exact ⟨(sE.1 _ hQ'.c0), (sE.2.1 _ hQ'.c0)⟩)
        · exact oddL_conn_three_true_true _ _ _ _ _ w w1 elong hst hW1 htr hSt hBr hH (by simp only [hbel]; exact ⟨(sE.2.1 _ hQ'.c0), (sE.1 _ hQ'.c0)⟩)

/-- **The overlap graphs of the even L-corrections are connected**, for the paper data, from the family below the word. -/
theorem connEvenL_of (D : JointData) (hS0 : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hJ : ∀ u : Word, u.length < w.length → IsJointSlice D f u)
    (hT : ∀ u : Word, u.length < w.length → TileProps u (f u).tOdd (f u).tEven (f u).aOdd (f u).aEven)
    (plus elong : Bool) (hdef : EvenLDefined w) :
    (overlapGraph (goodPart (evenLPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
      (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) w plus elong))).Connected := by
  obtain ⟨w1, s, k, hs, hw⟩ := hdef
  have hst : stripTrailing Digit.three w = w1 ++ [s] := by rw [hw]; exact JointRot.strip_of_defined _ _ hs _ _
  have hlt : w1.length < w.length := by rw [hw]; simp
  have hbel : below f w w1 = f w1 := below_of_lt f w w1 hlt
  have hJ1 := hJ w1 hlt
  have hT1 := hT w1 hlt
  have hJ1' : ∀ u : Word, u.length < w1.length → IsJointSlice D f u := fun u hu => hJ u (by omega)
  have h1 : (regsAt (w1 ++ [s])).1 = some w1 := ConnectedAltL.regs_pre_fst w1 s hs
  have hSt : StdCorners ((fun u => (below f w u).tOdd) w1) (vP1 (w1 ++ [s])) (vP2 (w1 ++ [s])) := by
    have h := ConnectedAltL.stdCorners_fst' D f (below f w) (w1 ++ [s]) w1 h1 hbel hJ1
    rw [h1] at h; exact h
  have hH : ∀ a ∈ tileShape ZTile.one, a ∈ ((fun u => (below f w u).aOdd) w1).dom ∧
      altD w1 true - a ∈ ((fun u => (below f w u).aOdd) w1).dom := by
    simp only [hbel]; exact ConnectedAltL.altHalfTurn_pts _ _ _ hT1.2.2.2.2.1
  have hbc : Standard.IsBase w1 → SurgicalAlt.PaperAltBaseCond w1 (f w1).aOdd (f w1).aEven :=
    base_alt_cond D hA f w1 hJ1
  have hOne : ∀ x ∈ tileShape ZTile.one, x ∈ D.S.oneO.dom := by
    rw [hS0]; intro x hx; exact (SpecialCells.mem_oneTile_iff x).2 hx
  cases s
  · have hBr : StdCorners (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (regsAt (w1 ++ [Digit.one])).2 false) (vQ1 (w1 ++ [Digit.one])) (vQ2 (w1 ++ [Digit.one])) :=
      ConnectedAltL.stdCorners_snd' D f (below f w) _ w1 (ConnectedAltL.regs_pre_snd w1 _ (by decide)) hbel hJ1
    have hdb : (!(w1 ++ [Digit.one]).isEmpty && (w1 ++ [Digit.one]).all (fun d => decide (d = Digit.two))) = false := by
      simp
    by_cases hb1 : Standard.IsBase w1
    · by_cases he : w1 = []
      · subst he
        have hB : ∀ x : Site, x ∈ ((fun u => (below f w u).aOdd) []).dom ↔
            x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile 3 := by
          simp only [hbel]; exact ((hbc hb1).1 rfl).1
        cases plus
        · exact evenL_conn_base_empty_one_false _ _ _ _ _ w elong hst hdb hSt hBr hB
        · exact evenL_conn_base_empty_one_true _ _ _ _ _ w elong hst hdb hSt hBr hB
      · have hj : 1 ≤ w1.length := List.length_pos_of_ne_nil he
        rcases hb1 with h0 | h3 | h2'
        · exact absurd h0 he
        · obtain ⟨j, rfl⟩ : ∃ j, w1 = List.replicate j Digit.three := ⟨w1.length, List.eq_replicate_iff.mpr ⟨rfl, h3⟩⟩
          simp only [List.length_replicate] at hj
          have hB : ∀ x : Site, x ∈ ((fun u => (below f w u).aOdd) (List.replicate j Digit.three)).dom ↔
              x - ((1 : ℤ), (1 : ℤ)) ∈ paperLadderAltTile (2 * (j : ℤ) + 2) := by
            simp only [hbel]; exact ((hbc (Or.inr (Or.inl h3))).2.1 j hj rfl).1
          cases plus
          · exact evenL_conn_base_threes_one_false _ _ _ _ _ w j hj elong hst hdb hSt hBr hB
          · exact evenL_conn_base_threes_one_true _ _ _ _ _ w j hj elong hst hdb hSt hBr hB
        · obtain ⟨j, rfl⟩ : ∃ j, w1 = List.replicate j Digit.two := ⟨w1.length, List.eq_replicate_iff.mpr ⟨rfl, h2'⟩⟩
          simp only [List.length_replicate] at hj
          have hB : ∀ x : Site, x ∈ ((fun u => (below f w u).aOdd) (List.replicate j Digit.two)).dom ↔
              x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (j : ℤ) + 3) := by
            simp only [hbel]; exact ((hbc (Or.inr (Or.inr h2'))).2.2 j hj rfl).1
          cases plus
          · exact evenL_conn_base_twos_one_false _ _ _ _ _ w j hj elong hst hdb hSt hBr hB
          · exact evenL_conn_base_twos_one_true _ _ _ _ _ w j hj elong hst hdb hSt hBr hB
    · obtain ⟨hP', hQ'⟩ := stdCorners_reg D f w1 hb1 hJ1'
      have sO := altO_sub D f w1 hb1 hJ1
      cases hW1 : W1Odd w1
      · rw [hW1] at sO
        cases plus
        · exact evenL_conn_one_false_false _ _ _ _ _ w w1 elong hst hdb hSt hBr hW1 (by simp only [hbel]; exact ⟨(sO.2.1 _ hP'.cX), (sO.1 _ hP'.c0), (sO.2.1 _ hP'.c0)⟩)
        · exact evenL_conn_one_false_true _ _ _ _ _ w w1 elong hst hdb hSt hBr hW1 (by simp only [hbel]; exact ⟨(sO.1 _ hP'.cY1), (sO.2.1 _ hP'.c0), (sO.1 _ hP'.c0)⟩)
      · rw [hW1] at sO
        cases plus
        · exact evenL_conn_one_true_false _ _ _ _ _ w w1 elong hst hdb hSt hBr hW1 hH (by simp only [hbel]; exact (sO.2.1 _ hP'.c0))
        · exact evenL_conn_one_true_true _ _ _ _ _ w w1 elong hst hdb hSt hBr hW1 hH (by simp only [hbel]; exact (sO.1 _ hP'.cD))
  · by_cases hb1 : Standard.IsBase w1
    · by_cases hall : ∀ d ∈ w1, d = Digit.two
      · -- the prefix `2^(j+1)`
        obtain ⟨j, rfl⟩ : ∃ j, w1 = List.replicate j Digit.two := ⟨w1.length, List.eq_replicate_iff.mpr ⟨rfl, hall⟩⟩
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · have hB : ∀ x : Site, x ∈ ((fun u => (below f w u).aOdd) (List.replicate 0 Digit.two)).dom ↔
              x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile 3 := by
            simp only [hbel]; exact ((hbc (Or.inl rfl)).1 rfl).1
          cases plus
          · exact evenL_conn_special_empty_false _ _ _ _ _ w elong hst hSt hB
          · exact evenL_conn_special_empty_true _ _ _ _ _ w elong hst hSt hOne hB
        · have hB : ∀ x : Site, x ∈ ((fun u => (below f w u).aOdd) (List.replicate j Digit.two)).dom ↔
              x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (j : ℤ) + 3) := by
            simp only [hbel]; exact ((hbc (Or.inr (Or.inr hall))).2.2 j hj rfl).1
          cases plus
          · exact evenL_conn_special_twos_false _ _ _ _ _ w j hj elong hst hSt hB
          · exact evenL_conn_special_twos_true _ _ _ _ _ w j hj elong hst hSt hOne hB
      · -- `3^j`, `j ≥ 1`
        have h3 : ∀ d ∈ w1, d = Digit.three := by
          rcases hb1 with h0 | h3 | h2'
          · subst h0; simp at hall
          · exact h3
          · exact absurd h2' hall
        obtain ⟨j, rfl⟩ : ∃ j, w1 = List.replicate j Digit.three := ⟨w1.length, List.eq_replicate_iff.mpr ⟨rfl, h3⟩⟩
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
          rcases j with _ | j'
          · simp at hall
          · exact ⟨j', rfl⟩
        have hdb : (!(List.replicate (j' + 1) Digit.three ++ [Digit.two]).isEmpty &&
            (List.replicate (j' + 1) Digit.three ++ [Digit.two]).all (fun d => decide (d = Digit.two))) = false := by
          simp [List.replicate_succ]
        have hBr : StdCorners (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
            (regsAt (List.replicate (j' + 1) Digit.three ++ [Digit.two])).2 false)
            (vQ1 (List.replicate (j' + 1) Digit.three ++ [Digit.two])) (vQ2 (List.replicate (j' + 1) Digit.three ++ [Digit.two])) :=
          ConnectedAltL.stdCorners_snd' D f (below f w) _ (List.replicate j' Digit.three)
            (by rw [JointRot.regsAt_append_singleton]; exact SpecialCells.regs_threes_snd' j')
            (below_of_lt f w _ (by rw [hw]; simp; omega)) (hJ _ (by rw [hw]; simp; omega))
        have hB : ∀ x : Site, x ∈ ((fun u => (below f w u).aOdd) (List.replicate (j' + 1) Digit.three)).dom ↔
            x - ((1 : ℤ), (1 : ℤ)) ∈ paperLadderAltTile (2 * ((j' + 1 : ℕ) : ℤ) + 2) := by
          simp only [hbel]; exact ((hbc (Or.inr (Or.inl h3))).2.1 (j' + 1) (by omega) rfl).1
        cases plus
        · exact evenL_conn_base_threes_two_false _ _ _ _ _ w (j' + 1) (by omega) elong hst hdb hSt hBr hB
        · exact evenL_conn_base_threes_two_true _ _ _ _ _ w (j' + 1) (by omega) elong hst hdb hSt hBr hB
    · obtain ⟨hP', hQ'⟩ := stdCorners_reg D f w1 hb1 hJ1'
      have sO := altO_sub D f w1 hb1 hJ1
      obtain ⟨u, hu⟩ := (JointRot.regs_some w1 hb1).2
      have hul := JointInduction.regsAt_lt w1 u (Or.inr hu)
      have hBr : StdCorners (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
          (regsAt (w1 ++ [Digit.two])).2 false) (vQ1 (w1 ++ [Digit.two])) (vQ2 (w1 ++ [Digit.two])) :=
        ConnectedAltL.stdCorners_snd' D f (below f w) _ u (by rw [JointRot.regsAt_append_singleton]; exact hu)
          (below_of_lt f w u (by omega)) (hJ u (by omega))
      have hdb : (!(w1 ++ [Digit.two]).isEmpty && (w1 ++ [Digit.two]).all (fun d => decide (d = Digit.two))) = false := by
        rw [Bool.eq_false_iff]; intro h
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
        exact hb1 (Or.inr (Or.inr (fun d hd => h.2 d (List.mem_append_left _ hd))))
      cases hW1 : W1Odd w1
      · rw [hW1] at sO
        cases plus
        · exact evenL_conn_two_false_false _ _ _ _ _ w w1 elong hst hdb hSt hBr hW1 hH (by simp only [hbel]; exact ⟨(sO.1 _ hP'.c0), (sO.2.1 _ hP'.c0)⟩)
        · exact evenL_conn_two_false_true _ _ _ _ _ w w1 elong hst hdb hSt hBr hW1 hH (by simp only [hbel]; exact ⟨(sO.2.1 _ hP'.c0), (sO.1 _ hP'.c0)⟩)
      · rw [hW1] at sO
        cases plus
        · exact evenL_conn_two_true_false _ _ _ _ _ w w1 elong hst hdb hSt hBr hW1 hH (by simp only [hbel]; exact ⟨(sO.2.2.2 _ hQ'.cY1), (sO.2.1 _ hP'.c0)⟩)
        · exact evenL_conn_two_true_true _ _ _ _ _ w w1 elong hst hdb hSt hBr hW1 hH (by simp only [hbel]; exact ⟨(sO.2.2.1 _ hQ'.cXi), (sO.1 _ hP'.cD)⟩)
  · exact absurd rfl hs

/-- **`ConnectedL`** for the paper data, from the family below the word. -/
theorem connectedL_of (D : JointData) (hS0 : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hJ : ∀ u : Word, u.length < w.length → IsJointSlice D f u)
    (hT : ∀ u : Word, u.length < w.length → TileProps u (f u).tOdd (f u).tEven (f u).aOdd (f u).aEven) :
    JointRot.ConnectedL D (below f w) w :=
  ⟨fun plus elong hdef => connOddL_of D hS0 hA f w hJ hT plus elong hdef,
    fun plus elong hdef => connEvenL_of D hS0 hA f w hJ hT plus elong hdef⟩

/-- **The rotation step of the joint induction for the paper data**, from the base rotations alone: the connectivity of the
alternate and L decompositions is `ConnectedAltL.connectedAlt_of` and `connectedL_of`, the special prefixes are
`SpecialCells.specialCells_paper`. -/
theorem rotStepInput_paper_of_base (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) (hlS : D.lSides = paperLSides) (hBR : JointRot.BaseRot D) :
    JointInduction.RotStepInput D :=
  SpecialCells.rotStepInput_paper D hS hA hlS hBR
    (fun f n hL w hw hb => ConnectedAltL.connectedAlt_of D hlS f w hb (fun u hu => (hL.1 u (by omega)).1)
      (fun u hu => (hL.1 u (by omega)).2.2.1))
    (fun f n hL w hw => connectedL_of D hS hA f w (fun u hu => (hL.1 u (by omega)).1)
      (fun u hu => (hL.1 u (by omega)).2.2.1))

/-- **The rotation step of the joint induction for the paper data**, with no named input: the base rotations are
`BaseTileProps.base_rotProps`. -/
theorem rotStepInput_paper_full (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) (hlS : D.lSides = paperLSides) : JointInduction.RotStepInput D :=
  rotStepInput_paper_of_base D hS hA hlS (fun w hw x r h1 h2 h3 h4 => by
    rw [hS] at h1 h3
    rw [hA] at h2 h4
    exact BaseTileProps.base_rotProps w hw x r ⟨h1, h2⟩ ⟨h3, h4⟩)

end FLatticePaper.Tiles.ConnectedL
