import FLatticePaper.Tiles.SpecialCells

/-!
# The connectivity of the alternate and L decompositions

The overlap graphs of the decompositions of the alternate tile odometers (`tileAltOddPieces`, `tileAltEvenPieces`) and of the
L-corrected odometers (`oddLPieces`, `evenLPieces`) are connected (`JointRot.ConnectedAlt`, `JointRot.ConnectedL`): spanning
trees of overlaps, each witnessed by a point of both pieces. The witnesses are corner points of the standard copies
(`JointRot.StdCorners`), the first tile and its half-turn image for the alternate copies (`AltHalfTurn`), points of the kept sides
of the L-corrected copies, and points of the pieces of the decompositions of the copies themselves.
-/

namespace FLatticePaper.Tiles.ConnectedAltL

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

/-! ### Generic tools -/

theorem adj_std (ps : List Piece) (i j : Fin ps.length) (hij : i.1 ≠ j.1) (a b : Site)
    (ha : a ∈ (ps.get i).odo.dom) (hb : b ∈ (ps.get j).odo.dom) (he : (ps.get i).off + a = (ps.get j).off + b)
    (hei : (ps.get i).exc = ∅) (hej : (ps.get j).exc = ∅) : (overlapGraph (goodPart ps)).Adj i j := by
  refine adj_of_mem ps i j hij ((ps.get i).off + a) ?_ ?_ ?_ ?_
  · rw [mem_placed, add_sub_cancel_left]; exact ha
  · rw [mem_placed, he, add_sub_cancel_left]; exact hb
  · rw [hei]; simp
  · rw [hej]; simp

theorem W1Odd_snoc_one (u : Word) : W1Odd (u ++ [Digit.one]) = !W1Odd u := by
  unfold W1Odd phase
  rw [List.count_append]
  rcases Nat.mod_two_eq_zero_or_one (u.count Digit.one) with h | h <;> simp [Nat.add_mod, h]

theorem W1Odd_snoc_two (u : Word) : W1Odd (u ++ [Digit.two]) = W1Odd u := by
  unfold W1Odd phase; simp

theorem W1Odd_snoc_three (u : Word) : W1Odd (u ++ [Digit.three]) = W1Odd u := by
  unfold W1Odd phase; simp

/-! ### The alternate decompositions with the alternate parent -/

/-- The odd alternate decomposition when the alternate parent is kept (no L-corrected copy). -/
def altOddL7 (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (c7 : AltCoeff) : List Piece :=
  let P := regOdo S pO pE (regsAt w).1 true
  let Q := regOdo S pO pE (regsAt w).2 false
  let Sp := (altShifts (W1Odd w) (vP2 w) (vQ1 w)).1
  let cP := altP0Coeff (W1Odd w) .dsP1Plus
  let cM := altP0Coeff (W1Odd w) .dsP1Minus
  let c1 := altP0Coeff (W1Odd w) .q1Plus
  let c2 := altP0Coeff (W1Odd w) .q1Minus
  [stdPiece P (altOff w cP) (altAff w cP), stdPiece P (altOff w cP + Sp) (altAff w cP + aP2 w),
    stdPiece P (altOff w cM) (altAff w cM), stdPiece P (altOff w cM + Sp) (altAff w cM + aP2 w),
    stdPiece Q (altOff w c1) (altAff w c1), stdPiece Q (altOff w c2) (altAff w c2),
    stdPiece (regOdo S aO aE (regsAt w).2 false) (altOff w c7) (altAff w c7)]

/-- The even alternate decomposition when the alternate parent is kept. -/
def altEvenL7 (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (c7 : AltCoeff) : List Piece :=
  let P := regOdo S pO pE (regsAt w).1 true
  let Q := regOdo S pO pE (regsAt w).2 false
  let Sq := (altShifts (W1Odd w) (vP2 w) (vQ1 w)).2
  let cP := altQ0Coeff (W1Odd w) .dsQ1Plus
  let cM := altQ0Coeff (W1Odd w) .dsQ1Minus
  let c1 := altQ0Coeff (W1Odd w) .p1Plus
  let c2 := altQ0Coeff (W1Odd w) .p1Minus
  [stdPiece Q (altOff w cP) (altAff w cP), stdPiece Q (altOff w cP + Sq) (altAff w cP + aP2 w),
    stdPiece Q (altOff w cM) (altAff w cM), stdPiece Q (altOff w cM + Sq) (altAff w cM + aP2 w),
    stdPiece P (altOff w c1) (altAff w c1), stdPiece P (altOff w c2) (altAff w c2),
    stdPiece (regOdo S aO aE (regsAt w).1 true) (altOff w c7) (altAff w c7)]

theorem altOdd_eq7 (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer)
    (wd : Word) (d : Digit) (c7 : AltCoeff) (hd : d ≠ Digit.two) (hc : altQ1Coeff (W1Odd (wd ++ [d])) d = some c7) :
    tileAltOddPieces S pO pE aO aE lO (wd ++ [d]) = altOddL7 S pO pE aO aE (wd ++ [d]) c7 := by
  have hl : (wd ++ [d]).getLast? = some d := by simp
  unfold tileAltOddPieces altOddL7
  simp only [hl, altTypeOf, Option.bind_some, hc, Option.some.injEq, hd, decide_false, Bool.false_eq_true, ↓reduceIte,
    List.cons_append, List.nil_append]

theorem altEven_eq7 (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (wd : Word) (d : Digit) (c7 : AltCoeff) (hd : d ≠ Digit.three) (hc : altP1Coeff (W1Odd (wd ++ [d])) d = some c7) :
    tileAltEvenPieces S pO pE aO aE lE (wd ++ [d]) = altEvenL7 S pO pE aO aE (wd ++ [d]) c7 := by
  have hl : (wd ++ [d]).getLast? = some d := by simp
  unfold tileAltEvenPieces altEvenL7
  simp only [hl, altTypeOf, Option.bind_some, hc, Option.some.injEq, hd, decide_false, Bool.false_eq_true, ↓reduceIte,
    List.cons_append, List.nil_append]

set_option hygiene false in
macro "l7_odo" : tactic => `(tactic| (
  simp only [altOddL7, altEvenL7, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero, stdPiece]))

set_option hygiene false in
macro "l7_id" : tactic => `(tactic| (
  simp only [altOddL7, altEvenL7, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero, stdPiece, altOff,
    coeffOff, altP0Coeff, altQ0Coeff, altShifts, altD, hW, hWd, ↓reduceIte, Bool.false_eq_true, beq_self_eq_true,
    Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.not_false, beq_false, beq_true, vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even,
    texV2, parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine]
  refine Prod.ext ?_ ?_ <;> simp <;> omega))

theorem altOdd_conn_one (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer) (wd : Word)
    (hP : StdCorners (regOdo S pO pE (regsAt (wd ++ [Digit.one])).1 true) (vP1 (wd ++ [Digit.one])) (vP2 (wd ++ [Digit.one])))
    (hQ : StdCorners (regOdo S pO pE (regsAt (wd ++ [Digit.one])).2 false) (vQ1 (wd ++ [Digit.one])) (vQ2 (wd ++ [Digit.one])))
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (regOdo S aO aE (regsAt (wd ++ [Digit.one])).2 false).dom ∧
      altD wd false - a ∈ (regOdo S aO aE (regsAt (wd ++ [Digit.one])).2 false).dom) :
    (overlapGraph (goodPart (tileAltOddPieces S pO pE aO aE lO (wd ++ [Digit.one])))).Connected := by
  cases hWd : W1Odd wd
  · have hW : W1Odd (wd ++ [Digit.one]) = true := by simp [W1Odd_snoc_one, hWd]
    rw [altOdd_eq7 S pO pE aO aE lO wd Digit.one (1, 1, -1, 0) (by decide) (by rw [hW]; rfl)]
    refine connected_of_reach _ (by simp [altOddL7]) (fun k => ?_)
    have a04 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.one]) (1, 1, -1, 0)))).Adj ⟨0, by simp [altOddL7]⟩ ⟨4, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.one])) (((0 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.cX) (by l7_odo; exact hQ.c0) (by l7_id) rfl rfl
    have a15 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.one]) (1, 1, -1, 0)))).Adj ⟨1, by simp [altOddL7]⟩ ⟨5, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP2 (wd ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.cY1) (by l7_odo; exact hQ.c1) (by l7_id) rfl rfl
    have a16 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.one]) (1, 1, -1, 0)))).Adj ⟨1, by simp [altOddL7]⟩ ⟨6, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.one])) (((0 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.cX) (by l7_odo; exact (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).1) (by l7_id) rfl rfl
    have a24 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.one]) (1, 1, -1, 0)))).Adj ⟨2, by simp [altOddL7]⟩ ⟨4, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) (vQ1 (wd ++ [Digit.one]) + vQ2 (wd ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (by l7_odo; exact hP.cXi) (by l7_odo; exact hQ.cD1) (by l7_id) rfl rfl
    have a26 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.one]) (1, 1, -1, 0)))).Adj ⟨2, by simp [altOddL7]⟩ ⟨6, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP2 (wd ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (altD wd false - ((0 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.cY1i) (by l7_odo; exact (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).2) (by l7_id) rfl rfl
    have a35 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.one]) (1, 1, -1, 0)))).Adj ⟨3, by simp [altOddL7]⟩ ⟨5, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP2 (wd ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vQ1 (wd ++ [Digit.one]) + vQ2 (wd ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (by l7_odo; exact hP.cY1i) (by l7_odo; exact hQ.cD) (by l7_id) rfl rfl
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | _ | kv
    · exact (SimpleGraph.Reachable.refl _)
    · exact (((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a26).reachable).trans (a16.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
    · exact (((((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a26).reachable).trans (a16.symm).reachable).trans (a15).reachable).trans (a35.symm).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
    · exact ((((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a26).reachable).trans (a16.symm).reachable).trans (a15).reachable)
    · exact ((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a26).reachable)
    · simp [altOddL7] at hk; omega
  · have hW : W1Odd (wd ++ [Digit.one]) = false := by simp [W1Odd_snoc_one, hWd]
    rw [altOdd_eq7 S pO pE aO aE lO wd Digit.one (0, 1, 1, 0) (by decide) (by rw [hW]; rfl)]
    refine connected_of_reach _ (by simp [altOddL7]) (fun k => ?_)
    have a04 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.one]) (0, 1, 1, 0)))).Adj ⟨0, by simp [altOddL7]⟩ ⟨4, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (((0 : ℤ), (0 : ℤ))) (vQ1 (wd ++ [Digit.one])) (by l7_odo; exact hP.c0) (by l7_odo; exact hQ.cX) (by l7_id) rfl rfl
    have a06 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.one]) (0, 1, 1, 0)))).Adj ⟨0, by simp [altOddL7]⟩ ⟨6, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP2 (wd ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.cY1) (by l7_odo; exact (hH ((1 : ℤ), (0 : ℤ)) (by simp [tileShape])).1) (by l7_id) rfl rfl
    have a15 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.one]) (0, 1, 1, 0)))).Adj ⟨1, by simp [altOddL7]⟩ ⟨5, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.one]) + vP2 (wd ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (vQ1 (wd ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) (by l7_odo; exact hP.cD1) (by l7_odo; exact hQ.cXi) (by l7_id) rfl rfl
    have a24 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.one]) (0, 1, 1, 0)))).Adj ⟨2, by simp [altOddL7]⟩ ⟨4, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (((1 : ℤ), (0 : ℤ))) (vQ2 (wd ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.c1) (by l7_odo; exact hQ.cY1) (by l7_id) rfl rfl
    have a35 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.one]) (0, 1, 1, 0)))).Adj ⟨3, by simp [altOddL7]⟩ ⟨5, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.one]) + vP2 (wd ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vQ2 (wd ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (by l7_odo; exact hP.cD) (by l7_odo; exact hQ.cY1i) (by l7_id) rfl rfl
    have a36 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.one]) (0, 1, 1, 0)))).Adj ⟨3, by simp [altOddL7]⟩ ⟨6, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) (altD wd false - ((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.cXi) (by l7_odo; exact (hH ((1 : ℤ), (0 : ℤ)) (by simp [tileShape])).2) (by l7_id) rfl rfl
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | _ | kv
    · exact (SimpleGraph.Reachable.refl _)
    · exact (((((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a36.symm).reachable).trans (a35).reachable).trans (a15.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a36.symm).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
    · exact ((((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a36.symm).reachable).trans (a35).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a06).reachable)
    · simp [altOddL7] at hk; omega

theorem altOdd_conn_three (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer) (wd : Word)
    (hP : StdCorners (regOdo S pO pE (regsAt (wd ++ [Digit.three])).1 true) (vP1 (wd ++ [Digit.three])) (vP2 (wd ++ [Digit.three])))
    (hQ : StdCorners (regOdo S pO pE (regsAt (wd ++ [Digit.three])).2 false) (vQ1 (wd ++ [Digit.three])) (vQ2 (wd ++ [Digit.three])))
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (regOdo S aO aE (regsAt (wd ++ [Digit.three])).2 false).dom ∧
      altD wd false - a ∈ (regOdo S aO aE (regsAt (wd ++ [Digit.three])).2 false).dom) :
    (overlapGraph (goodPart (tileAltOddPieces S pO pE aO aE lO (wd ++ [Digit.three])))).Connected := by
  cases hWd : W1Odd wd
  · have hW : W1Odd (wd ++ [Digit.three]) = false := by simp [W1Odd_snoc_three, hWd]
    rw [altOdd_eq7 S pO pE aO aE lO wd Digit.three (0, 1, 1, 0) (by decide) (by rw [hW]; rfl)]
    refine connected_of_reach _ (by simp [altOddL7]) (fun k => ?_)
    have a04 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.three]) (0, 1, 1, 0)))).Adj ⟨0, by simp [altOddL7]⟩ ⟨4, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (((0 : ℤ), (0 : ℤ))) (vQ1 (wd ++ [Digit.three])) (by l7_odo; exact hP.c0) (by l7_odo; exact hQ.cX) (by l7_id) rfl rfl
    have a06 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.three]) (0, 1, 1, 0)))).Adj ⟨0, by simp [altOddL7]⟩ ⟨6, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP2 (wd ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.cY1) (by l7_odo; exact (hH ((1 : ℤ), (0 : ℤ)) (by simp [tileShape])).1) (by l7_id) rfl rfl
    have a15 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.three]) (0, 1, 1, 0)))).Adj ⟨1, by simp [altOddL7]⟩ ⟨5, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.three]) + vP2 (wd ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) (vQ1 (wd ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) (by l7_odo; exact hP.cD1) (by l7_odo; exact hQ.cXi) (by l7_id) rfl rfl
    have a24 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.three]) (0, 1, 1, 0)))).Adj ⟨2, by simp [altOddL7]⟩ ⟨4, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (((1 : ℤ), (0 : ℤ))) (vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.c1) (by l7_odo; exact hQ.cY1) (by l7_id) rfl rfl
    have a35 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.three]) (0, 1, 1, 0)))).Adj ⟨3, by simp [altOddL7]⟩ ⟨5, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.three]) + vP2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (by l7_odo; exact hP.cD) (by l7_odo; exact hQ.cY1i) (by l7_id) rfl rfl
    have a36 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.three]) (0, 1, 1, 0)))).Adj ⟨3, by simp [altOddL7]⟩ ⟨6, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) (altD wd false - ((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.cXi) (by l7_odo; exact (hH ((1 : ℤ), (0 : ℤ)) (by simp [tileShape])).2) (by l7_id) rfl rfl
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | _ | kv
    · exact (SimpleGraph.Reachable.refl _)
    · exact (((((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a36.symm).reachable).trans (a35).reachable).trans (a15.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a36.symm).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
    · exact ((((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a36.symm).reachable).trans (a35).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a06).reachable)
    · simp [altOddL7] at hk; omega
  · have hW : W1Odd (wd ++ [Digit.three]) = true := by simp [W1Odd_snoc_three, hWd]
    rw [altOdd_eq7 S pO pE aO aE lO wd Digit.three (1, 1, -1, 0) (by decide) (by rw [hW]; rfl)]
    refine connected_of_reach _ (by simp [altOddL7]) (fun k => ?_)
    have a04 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.three]) (1, 1, -1, 0)))).Adj ⟨0, by simp [altOddL7]⟩ ⟨4, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.three])) (((0 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.cX) (by l7_odo; exact hQ.c0) (by l7_id) rfl rfl
    have a15 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.three]) (1, 1, -1, 0)))).Adj ⟨1, by simp [altOddL7]⟩ ⟨5, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP2 (wd ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.cY1) (by l7_odo; exact hQ.c1) (by l7_id) rfl rfl
    have a16 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.three]) (1, 1, -1, 0)))).Adj ⟨1, by simp [altOddL7]⟩ ⟨6, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.three])) (((0 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.cX) (by l7_odo; exact (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).1) (by l7_id) rfl rfl
    have a24 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.three]) (1, 1, -1, 0)))).Adj ⟨2, by simp [altOddL7]⟩ ⟨4, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) (vQ1 (wd ++ [Digit.three]) + vQ2 (wd ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) (by l7_odo; exact hP.cXi) (by l7_odo; exact hQ.cD1) (by l7_id) rfl rfl
    have a26 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.three]) (1, 1, -1, 0)))).Adj ⟨2, by simp [altOddL7]⟩ ⟨6, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (altD wd false - ((0 : ℤ), (0 : ℤ))) (by l7_odo; exact hP.cY1i) (by l7_odo; exact (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).2) (by l7_id) rfl rfl
    have a35 : (overlapGraph (goodPart (altOddL7 S pO pE aO aE (wd ++ [Digit.three]) (1, 1, -1, 0)))).Adj ⟨3, by simp [altOddL7]⟩ ⟨5, by simp [altOddL7]⟩ :=
      adj_std _ _ _ (by simp) (vP2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (vQ1 (wd ++ [Digit.three]) + vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (by l7_odo; exact hP.cY1i) (by l7_odo; exact hQ.cD) (by l7_id) rfl rfl
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | _ | kv
    · exact (SimpleGraph.Reachable.refl _)
    · exact (((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a26).reachable).trans (a16.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
    · exact (((((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a26).reachable).trans (a16.symm).reachable).trans (a15).reachable).trans (a35.symm).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
    · exact ((((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a26).reachable).trans (a16.symm).reachable).trans (a15).reachable)
    · exact ((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a26).reachable)
    · simp [altOddL7] at hk; omega

theorem altEven_conn_one (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer) (wd : Word)
    (hP : StdCorners (regOdo S pO pE (regsAt (wd ++ [Digit.one])).1 true) (vP1 (wd ++ [Digit.one])) (vP2 (wd ++ [Digit.one])))
    (hQ : StdCorners (regOdo S pO pE (regsAt (wd ++ [Digit.one])).2 false) (vQ1 (wd ++ [Digit.one])) (vQ2 (wd ++ [Digit.one])))
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (regOdo S aO aE (regsAt (wd ++ [Digit.one])).1 true).dom ∧
      altD wd true - a ∈ (regOdo S aO aE (regsAt (wd ++ [Digit.one])).1 true).dom)
    (hsub : W1Odd wd = true → (altOff wd (altP0Coeff true .dsP1Plus) + (vP1 wd + vP2 wd + ((1 : ℤ), (-1 : ℤ)))) ∈ (regOdo S aO aE (regsAt (wd ++ [Digit.one])).1 true).dom ∧ (altOff wd (altP0Coeff true .q1Minus) + (vQ2 wd + ((1 : ℤ), (-1 : ℤ)))) ∈ (regOdo S aO aE (regsAt (wd ++ [Digit.one])).1 true).dom) :
    (overlapGraph (goodPart (tileAltEvenPieces S pO pE aO aE lO (wd ++ [Digit.one])))).Connected := by
  cases hWd : W1Odd wd
  · have hW : W1Odd (wd ++ [Digit.one]) = true := by simp [W1Odd_snoc_one, hWd]
    rw [altEven_eq7 S pO pE aO aE lO wd Digit.one (0, 1, 1, 0) (by decide) (by rw [hW]; rfl)]
    refine connected_of_reach _ (by simp [altEvenL7]) (fun k => ?_)
    have a04 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.one]) (0, 1, 1, 0)))).Adj ⟨0, by simp [altEvenL7]⟩ ⟨4, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (((0 : ℤ), (0 : ℤ))) (vP1 (wd ++ [Digit.one])) (by l7_odo; exact hQ.c0) (by l7_odo; exact hP.cX) (by l7_id) rfl rfl
    have a15 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.one]) (0, 1, 1, 0)))).Adj ⟨1, by simp [altEvenL7]⟩ ⟨5, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.one]) + vQ2 (wd ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (vP1 (wd ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) (by l7_odo; exact hQ.cD1) (by l7_odo; exact hP.cXi) (by l7_id) rfl rfl
    have a16 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.one]) (0, 1, 1, 0)))).Adj ⟨1, by simp [altEvenL7]⟩ ⟨6, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ2 (wd ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (altD wd true - ((0 : ℤ), (0 : ℤ))) (by l7_odo; exact hQ.cY1i) (by l7_odo; exact (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).2) (by l7_id) rfl rfl
    have a24 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.one]) (0, 1, 1, 0)))).Adj ⟨2, by simp [altEvenL7]⟩ ⟨4, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (((1 : ℤ), (0 : ℤ))) (vP2 (wd ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hQ.c1) (by l7_odo; exact hP.cY1) (by l7_id) rfl rfl
    have a26 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.one]) (0, 1, 1, 0)))).Adj ⟨2, by simp [altEvenL7]⟩ ⟨6, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.one])) (((0 : ℤ), (0 : ℤ))) (by l7_odo; exact hQ.cX) (by l7_odo; exact (hH ((0 : ℤ), (0 : ℤ)) (by simp [tileShape])).1) (by l7_id) rfl rfl
    have a35 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.one]) (0, 1, 1, 0)))).Adj ⟨3, by simp [altEvenL7]⟩ ⟨5, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.one]) + vQ2 (wd ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vP2 (wd ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (by l7_odo; exact hQ.cD) (by l7_odo; exact hP.cY1i) (by l7_id) rfl rfl
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | _ | kv
    · exact (SimpleGraph.Reachable.refl _)
    · exact (((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a26).reachable).trans (a16.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
    · exact (((((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a26).reachable).trans (a16.symm).reachable).trans (a15).reachable).trans (a35.symm).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
    · exact ((((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a26).reachable).trans (a16.symm).reachable).trans (a15).reachable)
    · exact ((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a26).reachable)
    · simp [altEvenL7] at hk; omega
  · have hW : W1Odd (wd ++ [Digit.one]) = false := by simp [W1Odd_snoc_one, hWd]
    have hs := hsub hWd
    rw [altEven_eq7 S pO pE aO aE lO wd Digit.one (1, 1, -1, 0) (by decide) (by rw [hW]; rfl)]
    refine connected_of_reach _ (by simp [altEvenL7]) (fun k => ?_)
    have a04 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.one]) (1, 1, -1, 0)))).Adj ⟨0, by simp [altEvenL7]⟩ ⟨4, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.one])) (((0 : ℤ), (0 : ℤ))) (by l7_odo; exact hQ.cX) (by l7_odo; exact hP.c0) (by l7_id) rfl rfl
    have a15 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.one]) (1, 1, -1, 0)))).Adj ⟨1, by simp [altEvenL7]⟩ ⟨5, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ2 (wd ++ [Digit.one]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hQ.cY1) (by l7_odo; exact hP.c1) (by l7_id) rfl rfl
    have a24 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.one]) (1, 1, -1, 0)))).Adj ⟨2, by simp [altEvenL7]⟩ ⟨4, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.one]) - ((0 : ℤ), (1 : ℤ))) (vP1 (wd ++ [Digit.one]) + vP2 (wd ++ [Digit.one]) + ((0 : ℤ), (-1 : ℤ))) (by l7_odo; exact hQ.cXi) (by l7_odo; exact hP.cD1) (by l7_id) rfl rfl
    have a35 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.one]) (1, 1, -1, 0)))).Adj ⟨3, by simp [altEvenL7]⟩ ⟨5, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ2 (wd ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (vP1 (wd ++ [Digit.one]) + vP2 (wd ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (by l7_odo; exact hQ.cY1i) (by l7_odo; exact hP.cD) (by l7_id) rfl rfl
    have a06 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.one]) (1, 1, -1, 0)))).Adj ⟨0, by simp [altEvenL7]⟩ ⟨6, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.one]) + vQ2 (wd ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (altOff wd (altP0Coeff true .dsP1Plus) + (vP1 wd + vP2 wd + ((1 : ℤ), (-1 : ℤ)))) (by l7_odo; exact hQ.cD) (by l7_odo; exact hs.1) (by l7_id) rfl rfl
    have a16 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.one]) (1, 1, -1, 0)))).Adj ⟨1, by simp [altEvenL7]⟩ ⟨6, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.one]) + vQ2 (wd ++ [Digit.one]) + ((1 : ℤ), (-1 : ℤ))) (altOff wd (altP0Coeff true .q1Minus) + (vQ2 wd + ((1 : ℤ), (-1 : ℤ)))) (by l7_odo; exact hQ.cD) (by l7_odo; exact hs.2) (by l7_id) rfl rfl
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | _ | kv
    · exact (SimpleGraph.Reachable.refl _)
    · exact (((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a16.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
    · exact (((((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a16.symm).reachable).trans (a15).reachable).trans (a35.symm).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
    · exact ((((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a16.symm).reachable).trans (a15).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a06).reachable)
    · simp [altEvenL7] at hk; omega

theorem altEven_conn_two (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer) (wd : Word)
    (hP : StdCorners (regOdo S pO pE (regsAt (wd ++ [Digit.two])).1 true) (vP1 (wd ++ [Digit.two])) (vP2 (wd ++ [Digit.two])))
    (hQ : StdCorners (regOdo S pO pE (regsAt (wd ++ [Digit.two])).2 false) (vQ1 (wd ++ [Digit.two])) (vQ2 (wd ++ [Digit.two])))
    (hH : ∀ a ∈ tileShape ZTile.one, a ∈ (regOdo S aO aE (regsAt (wd ++ [Digit.two])).1 true).dom ∧
      altD wd true - a ∈ (regOdo S aO aE (regsAt (wd ++ [Digit.two])).1 true).dom)
    (hsub : W1Odd wd = true → (altOff wd (altP0Coeff true .q1Plus) + (vQ1 wd - ((0 : ℤ), (1 : ℤ)))) ∈ (regOdo S aO aE (regsAt (wd ++ [Digit.two])).1 true).dom ∧ (altOff wd (altP0Coeff true .q1Minus) + (vQ2 wd + ((1 : ℤ), (0 : ℤ)))) ∈ (regOdo S aO aE (regsAt (wd ++ [Digit.two])).1 true).dom) :
    (overlapGraph (goodPart (tileAltEvenPieces S pO pE aO aE lO (wd ++ [Digit.two])))).Connected := by
  cases hWd : W1Odd wd
  · have hW : W1Odd (wd ++ [Digit.two]) = false := by simp [W1Odd_snoc_two, hWd]
    rw [altEven_eq7 S pO pE aO aE lO wd Digit.two (0, 0, 0, 1) (by decide) (by rw [hW]; rfl)]
    refine connected_of_reach _ (by simp [altEvenL7]) (fun k => ?_)
    have a04 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.two]) (0, 0, 0, 1)))).Adj ⟨0, by simp [altEvenL7]⟩ ⟨4, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.two])) (((0 : ℤ), (0 : ℤ))) (by l7_odo; exact hQ.cX) (by l7_odo; exact hP.c0) (by l7_id) rfl rfl
    have a06 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.two]) (0, 0, 0, 1)))).Adj ⟨0, by simp [altEvenL7]⟩ ⟨6, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ2 (wd ++ [Digit.two]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hQ.cY1) (by l7_odo; exact (hH ((1 : ℤ), (0 : ℤ)) (by simp [tileShape])).1) (by l7_id) rfl rfl
    have a15 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.two]) (0, 0, 0, 1)))).Adj ⟨1, by simp [altEvenL7]⟩ ⟨5, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ2 (wd ++ [Digit.two]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hQ.cY1) (by l7_odo; exact hP.c1) (by l7_id) rfl rfl
    have a24 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.two]) (0, 0, 0, 1)))).Adj ⟨2, by simp [altEvenL7]⟩ ⟨4, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.two]) - ((0 : ℤ), (1 : ℤ))) (vP1 (wd ++ [Digit.two]) + vP2 (wd ++ [Digit.two]) + ((0 : ℤ), (-1 : ℤ))) (by l7_odo; exact hQ.cXi) (by l7_odo; exact hP.cD1) (by l7_id) rfl rfl
    have a35 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.two]) (0, 0, 0, 1)))).Adj ⟨3, by simp [altEvenL7]⟩ ⟨5, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (vP1 (wd ++ [Digit.two]) + vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (by l7_odo; exact hQ.cY1i) (by l7_odo; exact hP.cD) (by l7_id) rfl rfl
    have a36 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.two]) (0, 0, 0, 1)))).Adj ⟨3, by simp [altEvenL7]⟩ ⟨6, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.two]) - ((0 : ℤ), (1 : ℤ))) (altD wd true - ((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hQ.cXi) (by l7_odo; exact (hH ((1 : ℤ), (0 : ℤ)) (by simp [tileShape])).2) (by l7_id) rfl rfl
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | _ | kv
    · exact (SimpleGraph.Reachable.refl _)
    · exact (((((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a36.symm).reachable).trans (a35).reachable).trans (a15.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a36.symm).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
    · exact ((((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a36.symm).reachable).trans (a35).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a06).reachable)
    · simp [altEvenL7] at hk; omega
  · have hW : W1Odd (wd ++ [Digit.two]) = true := by simp [W1Odd_snoc_two, hWd]
    have hs := hsub hWd
    rw [altEven_eq7 S pO pE aO aE lO wd Digit.two (0, 0, 2, 1) (by decide) (by rw [hW]; rfl)]
    refine connected_of_reach _ (by simp [altEvenL7]) (fun k => ?_)
    have a04 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.two]) (0, 0, 2, 1)))).Adj ⟨0, by simp [altEvenL7]⟩ ⟨4, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (((0 : ℤ), (0 : ℤ))) (vP1 (wd ++ [Digit.two])) (by l7_odo; exact hQ.c0) (by l7_odo; exact hP.cX) (by l7_id) rfl rfl
    have a15 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.two]) (0, 0, 2, 1)))).Adj ⟨1, by simp [altEvenL7]⟩ ⟨5, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.two]) + vQ2 (wd ++ [Digit.two]) + ((0 : ℤ), (-1 : ℤ))) (vP1 (wd ++ [Digit.two]) - ((0 : ℤ), (1 : ℤ))) (by l7_odo; exact hQ.cD1) (by l7_odo; exact hP.cXi) (by l7_id) rfl rfl
    have a24 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.two]) (0, 0, 2, 1)))).Adj ⟨2, by simp [altEvenL7]⟩ ⟨4, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (((1 : ℤ), (0 : ℤ))) (vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (0 : ℤ))) (by l7_odo; exact hQ.c1) (by l7_odo; exact hP.cY1) (by l7_id) rfl rfl
    have a35 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.two]) (0, 0, 2, 1)))).Adj ⟨3, by simp [altEvenL7]⟩ ⟨5, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.two]) + vQ2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (by l7_odo; exact hQ.cD) (by l7_odo; exact hP.cY1i) (by l7_id) rfl rfl
    have a06 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.two]) (0, 0, 2, 1)))).Adj ⟨0, by simp [altEvenL7]⟩ ⟨6, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.two]) + vQ2 (wd ++ [Digit.two]) + ((0 : ℤ), (-1 : ℤ))) (altOff wd (altP0Coeff true .q1Plus) + (vQ1 wd - ((0 : ℤ), (1 : ℤ)))) (by l7_odo; exact hQ.cD1) (by l7_odo; exact hs.1) (by l7_id) rfl rfl
    have a36 : (overlapGraph (goodPart (altEvenL7 S pO pE aO aE (wd ++ [Digit.two]) (0, 0, 2, 1)))).Adj ⟨3, by simp [altEvenL7]⟩ ⟨6, by simp [altEvenL7]⟩ :=
      adj_std _ _ _ (by simp) (((1 : ℤ), (0 : ℤ))) (altOff wd (altP0Coeff true .q1Minus) + (vQ2 wd + ((1 : ℤ), (0 : ℤ)))) (by l7_odo; exact hQ.c1) (by l7_odo; exact hs.2) (by l7_id) rfl rfl
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | _ | kv
    · exact (SimpleGraph.Reachable.refl _)
    · exact (((((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a36.symm).reachable).trans (a35).reachable).trans (a15.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a36.symm).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
    · exact ((((SimpleGraph.Reachable.refl _).trans (a06).reachable).trans (a36.symm).reachable).trans (a35).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a06).reachable)
    · simp [altEvenL7] at hk; omega

/-! ### The corrected alternate decompositions (two L-corrected copies, no alternate parent) -/

/-- The position of the stem `j` of the odd L-correction of `w` (`oddLPieces`). -/
def oStemPos (w : Word) (plus : Bool) (j : ℕ) : Site :=
  oddLInitOff w plus + altOff (stripTrailing Digit.two w) ((j : ℤ) • (oddKCoeff (W1Odd w) plus).1)

/-- The position of the head `i` of the odd L-correction of `w`. -/
def oHeadPos (w : Word) (plus : Bool) (i : ℕ) : Site :=
  let K := oddKCoeff (W1Odd w) plus
  oddLInitOff w plus + altOff (stripTrailing Digit.two w)
    ((trailingCount Digit.two w : ℤ) • K.1 + K.2.1 + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2)

/-- The position of the stem `j` of the even L-correction of `w` (`evenLPieces`). -/
def eStemPos (w : Word) (plus : Bool) (j : ℕ) : Site :=
  evenLInitOff w plus + altOff (stripTrailing Digit.three w) ((j : ℤ) •
    (evenKCoeff (W1Odd w) plus (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).1)

/-- The position of the head `i` of the even L-correction of `w`. -/
def eHeadPos (w : Word) (plus : Bool) (i : ℕ) : Site :=
  let K := evenKCoeff (W1Odd w) plus (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))
  evenLInitOff w plus + altOff (stripTrailing Digit.three w)
    ((trailingCount Digit.three w : ℤ) • K.1 + K.2.1 + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2)

/-- The odd alternate decomposition after a `2`. -/
def altOddC6 (S : WeakData) (pO pE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer) (wd : Word) :
    List Piece :=
  let w := wd ++ [Digit.two]
  let P := regOdo S pO pE (regsAt w).1 true
  let Q := regOdo S pO pE (regsAt w).2 false
  let Sp := (altShifts (W1Odd w) (vP2 w) (vQ1 w)).1
  let cP := altP0Coeff (W1Odd w) .dsP1Plus
  let cM := altP0Coeff (W1Odd w) .dsP1Minus
  let c1 := altP0Coeff (W1Odd w) .q1Plus
  let c2 := altP0Coeff (W1Odd w) .q1Minus
  [stdPiece P (altOff w cP) (altAff w cP), stdPiece (lO wd false true) (altOff w cP + Sp) (altAff w cP + aP2 w),
    stdPiece (lO wd true true) (altOff w cM) (altAff w cM), stdPiece P (altOff w cM + Sp) (altAff w cM + aP2 w),
    stdPiece Q (altOff w c1) (altAff w c1), stdPiece Q (altOff w c2) (altAff w c2)]

/-- The even alternate decomposition after a `3`. -/
def altEvenC6 (S : WeakData) (pO pE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer) (wd : Word) :
    List Piece :=
  let w := wd ++ [Digit.three]
  let P := regOdo S pO pE (regsAt w).1 true
  let Q := regOdo S pO pE (regsAt w).2 false
  let Sq := (altShifts (W1Odd w) (vP2 w) (vQ1 w)).2
  let cP := altQ0Coeff (W1Odd w) .dsQ1Plus
  let cM := altQ0Coeff (W1Odd w) .dsQ1Minus
  let c1 := altQ0Coeff (W1Odd w) .p1Plus
  let c2 := altQ0Coeff (W1Odd w) .p1Minus
  [stdPiece (lE wd true true) (altOff w cP) (altAff w cP), stdPiece Q (altOff w cP + Sq) (altAff w cP + aP2 w),
    stdPiece Q (altOff w cM) (altAff w cM), stdPiece (lE wd false true) (altOff w cM + Sq) (altAff w cM + aP2 w),
    stdPiece P (altOff w c1) (altAff w c1), stdPiece P (altOff w c2) (altAff w c2)]

theorem altOdd_eqC6 (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer)
    (wd : Word) : tileAltOddPieces S pO pE aO aE lO (wd ++ [Digit.two]) = altOddC6 S pO pE lO wd := by
  have hl : (wd ++ [Digit.two]).getLast? = some Digit.two := by simp
  unfold tileAltOddPieces altOddC6
  simp [hl, altTypeOf, altQ1Coeff]

theorem altEven_eqC6 (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (wd : Word) : tileAltEvenPieces S pO pE aO aE lE (wd ++ [Digit.three]) = altEvenC6 S pO pE lE wd := by
  have hl : (wd ++ [Digit.three]).getLast? = some Digit.three := by simp
  unfold tileAltEvenPieces altEvenC6
  cases h : W1Odd (wd ++ [Digit.three]) <;> simp [hl, altTypeOf, altP1Coeff, h]

set_option hygiene false in
macro "c6_odo" : tactic => `(tactic| (
  simp only [altOddC6, altEvenC6, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero, stdPiece]))

set_option hygiene false in
macro "c6_id" : tactic => `(tactic| (
  simp only [altOddC6, altEvenC6, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero, stdPiece, altOff,
    coeffOff, altP0Coeff, altQ0Coeff, altShifts, oStemPos, oHeadPos, eStemPos, eHeadPos, oddLInitOff, evenLInitOff, p0Off,
    q0Off, SurgicalDict.offsetP0, SurgicalDict.offsetQ0, oddKCoeff, evenKCoeff, hW, hWd, ↓reduceIte, Bool.false_eq_true,
    vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2, parentsAt_append_singleton, Parents.step, Parents.current,
    Parents.combine, hpw, Prod.smul_mk, smul_eq_mul]
  refine Prod.ext ?_ ?_ <;> simp <;> push_cast <;> ring))

set_option hygiene false in
macro "c6_idE" : tactic => `(tactic| ((try simp only [eStemPos, eHeadPos]); (try simp only [hs2]); c6_id))

theorem altOdd_conn_two (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer) (wd : Word)
    (hP : StdCorners (regOdo S pO pE (regsAt (wd ++ [Digit.two])).1 true) (vP1 (wd ++ [Digit.two])) (vP2 (wd ++ [Digit.two])))
    (hQ : StdCorners (regOdo S pO pE (regsAt (wd ++ [Digit.two])).2 false) (vQ1 (wd ++ [Digit.two])) (vQ2 (wd ++ [Digit.two])))
    (hLF : W1Odd wd = false → (((1 : ℤ), (0 : ℤ))) ∈ (lO wd true true).dom ∧ (oStemPos wd false 0 + (vQ1 (stripTrailing Digit.two wd) + vQ2 (stripTrailing Digit.two wd) + ((0 : ℤ), (-1 : ℤ)))) ∈ (lO wd false true).dom ∧ (((0 : ℤ), (0 : ℤ))) ∈ (lO wd false true).dom ∧ (oHeadPos wd true 1 + ((0 : ℤ), (0 : ℤ))) ∈ (lO wd true true).dom)
    (hLT : W1Odd wd = true → (vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (0 : ℤ))) ∈ (lO wd false true).dom ∧ (vP1 (wd ++ [Digit.two]) - ((0 : ℤ), (1 : ℤ))) ∈ (lO wd true true).dom ∧ (oHeadPos wd false 1 + ((0 : ℤ), (0 : ℤ))) ∈ (lO wd false true).dom ∧ (oHeadPos wd true (2 * trailingCount Digit.two wd + 1) + ((0 : ℤ), (0 : ℤ))) ∈ (lO wd true true).dom) :
    (overlapGraph (goodPart (tileAltOddPieces S pO pE aO aE lO (wd ++ [Digit.two])))).Connected := by
  rw [altOdd_eqC6]
  refine connected_of_reach _ (by simp [altOddC6]) (fun k => ?_)
  have hpw : parentsAt wd = ⟨⟨(parentsAt (stripTrailing Digit.two wd)).odd.num +
      (trailingCount Digit.two wd : ℕ) * (parentsAt (stripTrailing Digit.two wd)).even.num,
      (parentsAt (stripTrailing Digit.two wd)).odd.den +
      (trailingCount Digit.two wd : ℕ) * (parentsAt (stripTrailing Digit.two wd)).even.den⟩,
      (parentsAt (stripTrailing Digit.two wd)).even⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.two wd]
    exact JointRot.parents_append_twos _ _
  cases hWd : W1Odd wd
  · have hW : W1Odd (wd ++ [Digit.two]) = false := by simp [W1Odd_snoc_two, hWd]
    have hl := hLF hWd
    have a04 : (overlapGraph (goodPart (altOddC6 S pO pE lO wd))).Adj ⟨0, by simp [altOddC6]⟩ ⟨4, by simp [altOddC6]⟩ :=
      adj_std _ _ _ (by simp) (((0 : ℤ), (0 : ℤ))) (vQ1 (wd ++ [Digit.two])) (by c6_odo; exact hP.c0) (by c6_odo; exact hQ.cX) (by c6_id) rfl rfl
    have a24 : (overlapGraph (goodPart (altOddC6 S pO pE lO wd))).Adj ⟨2, by simp [altOddC6]⟩ ⟨4, by simp [altOddC6]⟩ :=
      adj_std _ _ _ (by simp) (((1 : ℤ), (0 : ℤ))) (vQ2 (wd ++ [Digit.two]) + ((1 : ℤ), (0 : ℤ))) (by c6_odo; exact hl.1) (by c6_odo; exact hQ.cY1) (by c6_id) rfl rfl
    have a35 : (overlapGraph (goodPart (altOddC6 S pO pE lO wd))).Adj ⟨3, by simp [altOddC6]⟩ ⟨5, by simp [altOddC6]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.two]) + vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (vQ2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (by c6_odo; exact hP.cD) (by c6_odo; exact hQ.cY1i) (by c6_id) rfl rfl
    have a15 : (overlapGraph (goodPart (altOddC6 S pO pE lO wd))).Adj ⟨1, by simp [altOddC6]⟩ ⟨5, by simp [altOddC6]⟩ :=
      adj_std _ _ _ (by simp) (oStemPos wd false 0 + (vQ1 (stripTrailing Digit.two wd) + vQ2 (stripTrailing Digit.two wd) + ((0 : ℤ), (-1 : ℤ)))) (vQ1 (wd ++ [Digit.two]) - ((0 : ℤ), (1 : ℤ))) (by c6_odo; exact hl.2.1) (by c6_odo; exact hQ.cXi) (by c6_id) rfl rfl
    have a12 : (overlapGraph (goodPart (altOddC6 S pO pE lO wd))).Adj ⟨1, by simp [altOddC6]⟩ ⟨2, by simp [altOddC6]⟩ :=
      adj_std _ _ _ (by simp) (((0 : ℤ), (0 : ℤ))) (oHeadPos wd true 1 + ((0 : ℤ), (0 : ℤ))) (by c6_odo; exact hl.2.2.1) (by c6_odo; exact hl.2.2.2) (by c6_id) rfl rfl
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | kv
    · exact (SimpleGraph.Reachable.refl _)
    · exact ((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a12.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
    · exact ((((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a12.symm).reachable).trans (a15).reachable).trans (a35.symm).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
    · exact (((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a12.symm).reachable).trans (a15).reachable)
    · simp [altOddC6] at hk; omega
  · have hW : W1Odd (wd ++ [Digit.two]) = true := by simp [W1Odd_snoc_two, hWd]
    have hl := hLT hWd
    have a04 : (overlapGraph (goodPart (altOddC6 S pO pE lO wd))).Adj ⟨0, by simp [altOddC6]⟩ ⟨4, by simp [altOddC6]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.two])) (((0 : ℤ), (0 : ℤ))) (by c6_odo; exact hP.cX) (by c6_odo; exact hQ.c0) (by c6_id) rfl rfl
    have a15 : (overlapGraph (goodPart (altOddC6 S pO pE lO wd))).Adj ⟨1, by simp [altOddC6]⟩ ⟨5, by simp [altOddC6]⟩ :=
      adj_std _ _ _ (by simp) (vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) (by c6_odo; exact hl.1) (by c6_odo; exact hQ.c1) (by c6_id) rfl rfl
    have a24 : (overlapGraph (goodPart (altOddC6 S pO pE lO wd))).Adj ⟨2, by simp [altOddC6]⟩ ⟨4, by simp [altOddC6]⟩ :=
      adj_std _ _ _ (by simp) (vP1 (wd ++ [Digit.two]) - ((0 : ℤ), (1 : ℤ))) (vQ1 (wd ++ [Digit.two]) + vQ2 (wd ++ [Digit.two]) + ((0 : ℤ), (-1 : ℤ))) (by c6_odo; exact hl.2.1) (by c6_odo; exact hQ.cD1) (by c6_id) rfl rfl
    have a35 : (overlapGraph (goodPart (altOddC6 S pO pE lO wd))).Adj ⟨3, by simp [altOddC6]⟩ ⟨5, by simp [altOddC6]⟩ :=
      adj_std _ _ _ (by simp) (vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (vQ1 (wd ++ [Digit.two]) + vQ2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ))) (by c6_odo; exact hP.cY1i) (by c6_odo; exact hQ.cD) (by c6_id) rfl rfl
    have a12 : (overlapGraph (goodPart (altOddC6 S pO pE lO wd))).Adj ⟨1, by simp [altOddC6]⟩ ⟨2, by simp [altOddC6]⟩ :=
      adj_std _ _ _ (by simp) (oHeadPos wd false 1 + ((0 : ℤ), (0 : ℤ))) (oHeadPos wd true (2 * trailingCount Digit.two wd + 1) + ((0 : ℤ), (0 : ℤ))) (by c6_odo; exact hl.2.2.1) (by c6_odo; exact hl.2.2.2) (by c6_id) rfl rfl
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | kv
    · exact (SimpleGraph.Reachable.refl _)
    · exact ((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a12.symm).reachable)
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
    · exact ((((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a12.symm).reachable).trans (a15).reachable).trans (a35.symm).reachable)
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
    · exact (((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a12.symm).reachable).trans (a15).reachable)
    · simp [altOddC6] at hk; omega

theorem altEven_conn_three (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer) (wd : Word)
    (hP : StdCorners (regOdo S pO pE (regsAt (wd ++ [Digit.three])).1 true) (vP1 (wd ++ [Digit.three])) (vP2 (wd ++ [Digit.three])))
    (hQ : StdCorners (regOdo S pO pE (regsAt (wd ++ [Digit.three])).2 false) (vQ1 (wd ++ [Digit.three])) (vQ2 (wd ++ [Digit.three])))
    (hLF : W1Odd wd = false → (vQ1 (wd ++ [Digit.three])) ∈ (lO wd true true).dom ∧ (vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) ∈ (lO wd false true).dom ∧ (eHeadPos wd true 1 + ((0 : ℤ), (0 : ℤ))) ∈ (lO wd true true).dom ∧ (eHeadPos wd false (2 * trailingCount Digit.three wd + 1) + ((0 : ℤ), (0 : ℤ))) ∈ (lO wd false true).dom)
    (hLT : W1Odd wd = true → (((0 : ℤ), (0 : ℤ))) ∈ (lO wd true true).dom ∧ (eStemPos wd false 0 + (vP1 (stripTrailing Digit.three wd) + vP2 (stripTrailing Digit.three wd) + ((1 : ℤ), (-1 : ℤ)))) ∈ (lO wd false true).dom ∧ (eHeadPos wd true 1 + ((0 : ℤ), (0 : ℤ))) ∈ (lO wd true true).dom ∧ (eHeadPos wd false (2 * trailingCount Digit.three wd + 1) + ((0 : ℤ), (0 : ℤ))) ∈ (lO wd false true).dom) :
    (overlapGraph (goodPart (tileAltEvenPieces S pO pE aO aE lO (wd ++ [Digit.three])))).Connected := by
  rw [altEven_eqC6]
  refine connected_of_reach _ (by simp [altEvenC6]) (fun k => ?_)
  have hpw : parentsAt wd = ⟨(parentsAt (stripTrailing Digit.three wd)).odd,
      ⟨(parentsAt (stripTrailing Digit.three wd)).even.num +
        2 * (trailingCount Digit.three wd : ℕ) * (parentsAt (stripTrailing Digit.three wd)).odd.num,
      (parentsAt (stripTrailing Digit.three wd)).even.den +
        2 * (trailingCount Digit.three wd : ℕ) * (parentsAt (stripTrailing Digit.three wd)).odd.den⟩⟩ := by
    conv_lhs => rw [← JointRot.strip_append_replicate Digit.three wd]
    exact JointRot.parents_append_threes _ _
  cases hWd : W1Odd wd
  · have hW : W1Odd (wd ++ [Digit.three]) = false := by simp [W1Odd_snoc_three, hWd]
    have hl := hLF hWd
    cases hs2 : decide ((stripTrailing Digit.three wd).getLast? = some Digit.two)
    · have a04 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨0, by simp [altEvenC6]⟩ ⟨4, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.three])) (((0 : ℤ), (0 : ℤ))) (by c6_odo; exact hl.1) (by c6_odo; exact hP.c0) (by c6_idE) rfl rfl
      have a15 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨1, by simp [altEvenC6]⟩ ⟨5, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) (by c6_odo; exact hQ.cY1) (by c6_odo; exact hP.c1) (by c6_idE) rfl rfl
      have a24 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨2, by simp [altEvenC6]⟩ ⟨4, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) (vP1 (wd ++ [Digit.three]) + vP2 (wd ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) (by c6_odo; exact hQ.cXi) (by c6_odo; exact hP.cD1) (by c6_idE) rfl rfl
      have a35 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨3, by simp [altEvenC6]⟩ ⟨5, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (vP1 (wd ++ [Digit.three]) + vP2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (by c6_odo; exact hl.2.1) (by c6_odo; exact hP.cD) (by c6_idE) rfl rfl
      have a03 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨0, by simp [altEvenC6]⟩ ⟨3, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (eHeadPos wd true 1 + ((0 : ℤ), (0 : ℤ))) (eHeadPos wd false (2 * trailingCount Digit.three wd + 1) + ((0 : ℤ), (0 : ℤ))) (by c6_odo; exact hl.2.2.1) (by c6_odo; exact hl.2.2.2) (by c6_idE) rfl rfl
      obtain ⟨kv, hk⟩ := k
      rcases kv with _ | _ | _ | _ | _ | _ | kv
      · exact (SimpleGraph.Reachable.refl _)
      · exact ((((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a35).reachable).trans (a15.symm).reachable)
      · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
      · exact ((SimpleGraph.Reachable.refl _).trans (a03).reachable)
      · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
      · exact (((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a35).reachable)
      · simp [altEvenC6] at hk; omega
    · have a04 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨0, by simp [altEvenC6]⟩ ⟨4, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.three])) (((0 : ℤ), (0 : ℤ))) (by c6_odo; exact hl.1) (by c6_odo; exact hP.c0) (by c6_idE) rfl rfl
      have a15 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨1, by simp [altEvenC6]⟩ ⟨5, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) (((1 : ℤ), (0 : ℤ))) (by c6_odo; exact hQ.cY1) (by c6_odo; exact hP.c1) (by c6_idE) rfl rfl
      have a24 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨2, by simp [altEvenC6]⟩ ⟨4, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) (vP1 (wd ++ [Digit.three]) + vP2 (wd ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) (by c6_odo; exact hQ.cXi) (by c6_odo; exact hP.cD1) (by c6_idE) rfl rfl
      have a35 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨3, by simp [altEvenC6]⟩ ⟨5, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (vP1 (wd ++ [Digit.three]) + vP2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (by c6_odo; exact hl.2.1) (by c6_odo; exact hP.cD) (by c6_idE) rfl rfl
      have a03 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨0, by simp [altEvenC6]⟩ ⟨3, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (eHeadPos wd true 1 + ((0 : ℤ), (0 : ℤ))) (eHeadPos wd false (2 * trailingCount Digit.three wd + 1) + ((0 : ℤ), (0 : ℤ))) (by c6_odo; exact hl.2.2.1) (by c6_odo; exact hl.2.2.2) (by c6_idE) rfl rfl
      obtain ⟨kv, hk⟩ := k
      rcases kv with _ | _ | _ | _ | _ | _ | kv
      · exact (SimpleGraph.Reachable.refl _)
      · exact ((((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a35).reachable).trans (a15.symm).reachable)
      · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
      · exact ((SimpleGraph.Reachable.refl _).trans (a03).reachable)
      · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
      · exact (((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a35).reachable)
      · simp [altEvenC6] at hk; omega
  · have hW : W1Odd (wd ++ [Digit.three]) = true := by simp [W1Odd_snoc_three, hWd]
    have hl := hLT hWd
    cases hs2 : decide ((stripTrailing Digit.three wd).getLast? = some Digit.two)
    · have a04 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨0, by simp [altEvenC6]⟩ ⟨4, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (((0 : ℤ), (0 : ℤ))) (vP1 (wd ++ [Digit.three])) (by c6_odo; exact hl.1) (by c6_odo; exact hP.cX) (by c6_idE) rfl rfl
      have a15 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨1, by simp [altEvenC6]⟩ ⟨5, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.three]) + vQ2 (wd ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) (vP1 (wd ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) (by c6_odo; exact hQ.cD1) (by c6_odo; exact hP.cXi) (by c6_idE) rfl rfl
      have a24 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨2, by simp [altEvenC6]⟩ ⟨4, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (((1 : ℤ), (0 : ℤ))) (vP2 (wd ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) (by c6_odo; exact hQ.c1) (by c6_odo; exact hP.cY1) (by c6_idE) rfl rfl
      have a35 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨3, by simp [altEvenC6]⟩ ⟨5, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (eStemPos wd false 0 + (vP1 (stripTrailing Digit.three wd) + vP2 (stripTrailing Digit.three wd) + ((1 : ℤ), (-1 : ℤ)))) (vP2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (by c6_odo; exact hl.2.1) (by c6_odo; exact hP.cY1i) (by c6_idE) rfl rfl
      have a03 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨0, by simp [altEvenC6]⟩ ⟨3, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (eHeadPos wd true 1 + ((0 : ℤ), (0 : ℤ))) (eHeadPos wd false (2 * trailingCount Digit.three wd + 1) + ((0 : ℤ), (0 : ℤ))) (by c6_odo; exact hl.2.2.1) (by c6_odo; exact hl.2.2.2) (by c6_idE) rfl rfl
      obtain ⟨kv, hk⟩ := k
      rcases kv with _ | _ | _ | _ | _ | _ | kv
      · exact (SimpleGraph.Reachable.refl _)
      · exact ((((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a35).reachable).trans (a15.symm).reachable)
      · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
      · exact ((SimpleGraph.Reachable.refl _).trans (a03).reachable)
      · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
      · exact (((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a35).reachable)
      · simp [altEvenC6] at hk; omega
    · have a04 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨0, by simp [altEvenC6]⟩ ⟨4, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (((0 : ℤ), (0 : ℤ))) (vP1 (wd ++ [Digit.three])) (by c6_odo; exact hl.1) (by c6_odo; exact hP.cX) (by c6_idE) rfl rfl
      have a15 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨1, by simp [altEvenC6]⟩ ⟨5, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (vQ1 (wd ++ [Digit.three]) + vQ2 (wd ++ [Digit.three]) + ((0 : ℤ), (-1 : ℤ))) (vP1 (wd ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ))) (by c6_odo; exact hQ.cD1) (by c6_odo; exact hP.cXi) (by c6_idE) rfl rfl
      have a24 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨2, by simp [altEvenC6]⟩ ⟨4, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (((1 : ℤ), (0 : ℤ))) (vP2 (wd ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ))) (by c6_odo; exact hQ.c1) (by c6_odo; exact hP.cY1) (by c6_idE) rfl rfl
      have a35 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨3, by simp [altEvenC6]⟩ ⟨5, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (eStemPos wd false 0 + (vP1 (stripTrailing Digit.three wd) + vP2 (stripTrailing Digit.three wd) + ((1 : ℤ), (-1 : ℤ)))) (vP2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ))) (by c6_odo; exact hl.2.1) (by c6_odo; exact hP.cY1i) (by c6_idE) rfl rfl
      have a03 : (overlapGraph (goodPart (altEvenC6 S pO pE lO wd))).Adj ⟨0, by simp [altEvenC6]⟩ ⟨3, by simp [altEvenC6]⟩ :=
        adj_std _ _ _ (by simp) (eHeadPos wd true 1 + ((0 : ℤ), (0 : ℤ))) (eHeadPos wd false (2 * trailingCount Digit.three wd + 1) + ((0 : ℤ), (0 : ℤ))) (by c6_odo; exact hl.2.2.1) (by c6_odo; exact hl.2.2.2) (by c6_idE) rfl rfl
      obtain ⟨kv, hk⟩ := k
      rcases kv with _ | _ | _ | _ | _ | _ | kv
      · exact (SimpleGraph.Reachable.refl _)
      · exact ((((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a35).reachable).trans (a15.symm).reachable)
      · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable)
      · exact ((SimpleGraph.Reachable.refl _).trans (a03).reachable)
      · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable)
      · exact (((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a35).reachable)
      · simp [altEvenC6] at hk; omega

/-! ### The witnesses from the family -/

open FLatticePaper.Tiles.JointRot (stdCorners_reg below_of_lt)
open FLatticePaper.Tiles.JointGlue (mem_pieceUnion)

theorem regs_snoc_one (wd : Word) : regsAt (wd ++ [Digit.one]) = (some wd, some wd) := by
  rw [JointRot.regsAt_append_singleton]; rfl

theorem regs_snoc_two (wd : Word) : (regsAt (wd ++ [Digit.two])).1 = some wd := by
  rw [JointRot.regsAt_append_singleton]; rfl

theorem regs_snoc_three (wd : Word) : (regsAt (wd ++ [Digit.three])).2 = some wd := by
  rw [JointRot.regsAt_append_singleton]; rfl

/-- The first tile and its half-turn image lie in an odometer with the alternate half-turn property. -/
theorem altHalfTurn_pts (o : PartialOdometer) (Dh E : Site) (h : AltHalfTurn o Dh E) :
    ∀ a ∈ tileShape ZTile.one, a ∈ o.dom ∧ Dh - a ∈ o.dom := by
  obtain ⟨α, β, hF, hH⟩ := h
  intro a ha
  exact ⟨(hF a ha).1, (hH a (hF a ha).1).1⟩

theorem not_base_of_W1Odd (u : Word) (h : W1Odd u = true) : ¬ Standard.IsBase u := by
  have h1 : Digit.one ∈ u := by
    by_contra hn
    have : u.count Digit.one = 0 := List.count_eq_zero.mpr hn
    simp [W1Odd, phase, this] at h
  rintro (rfl | h3 | h2)
  · simp at h1
  · exact absurd (h3 _ h1) (by decide)
  · exact absurd (h2 _ h1) (by decide)

theorem mem_pieceUnion_of {ps : List Piece} {p : Piece} (hp : p ∈ ps) {x : Site} (hx : x - p.off ∈ p.odo.dom) :
    x ∈ pieceUnion ps :=
  mem_pieceUnion.mpr ⟨p, hp, mem_placed.mpr hx⟩

/-- The odd alternate decomposition after a `1` or a `3` (the alternate parent is kept). -/
theorem connAltOdd_kept (D : JointData) (f : Word → JSlice) (wd : Word) (d : Digit) (hd : d ≠ Digit.two)
    (hb : ¬ Standard.IsBase (wd ++ [d])) (hJ : ∀ u : Word, u.length < (wd ++ [d]).length → IsJointSlice D f u)
    (hT : TileProps wd (f wd).tOdd (f wd).tEven (f wd).aOdd (f wd).aEven) :
    (overlapGraph (goodPart (tileAltOddPieces D.S (fun u => (below f (wd ++ [d]) u).tOdd)
      (fun u => (below f (wd ++ [d]) u).tEven) (fun u => (below f (wd ++ [d]) u).aOdd)
      (fun u => (below f (wd ++ [d]) u).aEven) (fun u => (below f (wd ++ [d]) u).lOdd) (wd ++ [d])))).Connected := by
  obtain ⟨hP, hQ⟩ := stdCorners_reg D f _ hb hJ
  have hH := altHalfTurn_pts _ _ _ hT.2.2.2.2.2
  have hbel : below f (wd ++ [d]) wd = f wd := below_of_lt f _ wd (by simp)
  cases d
  · refine altOdd_conn_one _ _ _ _ _ _ wd hP hQ ?_
    rw [regs_snoc_one wd]
    show ∀ a ∈ tileShape ZTile.one, a ∈ (below f (wd ++ [Digit.one]) wd).aEven.dom ∧
      altD wd false - a ∈ (below f (wd ++ [Digit.one]) wd).aEven.dom
    rw [hbel]; exact hH
  · exact absurd rfl hd
  · refine altOdd_conn_three _ _ _ _ _ _ wd hP hQ ?_
    rw [regs_snoc_three wd]
    show ∀ a ∈ tileShape ZTile.one, a ∈ (below f (wd ++ [Digit.three]) wd).aEven.dom ∧
      altD wd false - a ∈ (below f (wd ++ [Digit.three]) wd).aEven.dom
    rw [hbel]; exact hH

/-- The even alternate decomposition after a `1` or a `2` (the alternate parent is kept). -/
theorem connAltEven_kept (D : JointData) (f : Word → JSlice) (wd : Word) (d : Digit) (hd : d ≠ Digit.three)
    (hb : ¬ Standard.IsBase (wd ++ [d])) (hJ : ∀ u : Word, u.length < (wd ++ [d]).length → IsJointSlice D f u)
    (hT : TileProps wd (f wd).tOdd (f wd).tEven (f wd).aOdd (f wd).aEven) :
    (overlapGraph (goodPart (tileAltEvenPieces D.S (fun u => (below f (wd ++ [d]) u).tOdd)
      (fun u => (below f (wd ++ [d]) u).tEven) (fun u => (below f (wd ++ [d]) u).aOdd)
      (fun u => (below f (wd ++ [d]) u).aEven) (fun u => (below f (wd ++ [d]) u).lEven) (wd ++ [d])))).Connected := by
  obtain ⟨hP, hQ⟩ := stdCorners_reg D f _ hb hJ
  have hH := altHalfTurn_pts _ _ _ hT.2.2.2.2.1
  have hlt : wd.length < (wd ++ [d]).length := by simp
  have hbel : below f (wd ++ [d]) wd = f wd := below_of_lt f _ wd hlt
  -- the pieces of the parent alternate when `W_1(wd)` is odd
  have hpar : W1Odd wd = true →
      (∀ x : Site, x ∈ (regOdo D.S (fun u => (below f wd u).tOdd) (fun u => (below f wd u).tEven) (regsAt wd).1 true).dom →
        altOff wd (altP0Coeff true .dsP1Plus) + x ∈ (f wd).aOdd.dom) ∧
      (∀ x : Site, x ∈ (regOdo D.S (fun u => (below f wd u).tOdd) (fun u => (below f wd u).tEven) (regsAt wd).2 false).dom →
        altOff wd (altP0Coeff true .q1Plus) + x ∈ (f wd).aOdd.dom ∧ altOff wd (altP0Coeff true .q1Minus) + x ∈ (f wd).aOdd.dom) := by
    intro hWd
    have hbwd := not_base_of_W1Odd wd hWd
    have hR := ((hJ wd hlt).2.2.1.2.1 hbwd).2.2.1
    rw [hR.1]
    have mem : ∀ c : SurgicalDict.AltP0Piece, c ≠ .dsP1Plus → c ≠ .dsP1Minus →
        stdPiece (regOdo D.S (fun u => (below f wd u).tOdd) (fun u => (below f wd u).tEven) (regsAt wd).2 false)
          (altOff wd (altP0Coeff (W1Odd wd) c)) (altAff wd (altP0Coeff (W1Odd wd) c)) ∈
        tileAltOddPieces D.S (fun u => (below f wd u).tOdd) (fun u => (below f wd u).tEven) (fun u => (below f wd u).aOdd)
          (fun u => (below f wd u).aEven) (fun u => (below f wd u).lOdd) wd := by
      intro c h1 h2
      unfold tileAltOddPieces
      cases c <;> simp_all
    refine ⟨fun x hx => mem_pieceUnion_of (p := stdPiece (regOdo D.S (fun u => (below f wd u).tOdd)
      (fun u => (below f wd u).tEven) (regsAt wd).1 true) (altOff wd (altP0Coeff (W1Odd wd) .dsP1Plus))
      (altAff wd (altP0Coeff (W1Odd wd) .dsP1Plus))) (by unfold tileAltOddPieces; simp) ?_,
      fun x hx => ⟨mem_pieceUnion_of (mem .q1Plus (by decide) (by decide)) ?_,
        mem_pieceUnion_of (mem .q1Minus (by decide) (by decide)) ?_⟩⟩
    all_goals simp only [stdPiece, hWd, add_sub_cancel_left]; exact hx
  have hcw : ∀ u : Word, u.length < wd.length → IsJointSlice D f u := fun u hu => hJ u (by simp; omega)
  cases d
  · refine altEven_conn_one _ _ _ _ _ _ wd hP hQ ?_ ?_
    · rw [regs_snoc_one wd]
      show ∀ a ∈ tileShape ZTile.one, a ∈ (below f (wd ++ [Digit.one]) wd).aOdd.dom ∧
        altD wd true - a ∈ (below f (wd ++ [Digit.one]) wd).aOdd.dom
      rw [hbel]; exact hH
    · intro hWd
      obtain ⟨hP', hQ'⟩ := stdCorners_reg D f wd (not_base_of_W1Odd wd hWd) hcw
      rw [regs_snoc_one wd]
      show _ ∈ (below f (wd ++ [Digit.one]) wd).aOdd.dom ∧ _ ∈ (below f (wd ++ [Digit.one]) wd).aOdd.dom
      rw [hbel]
      exact ⟨(hpar hWd).1 _ hP'.cD, ((hpar hWd).2 _ hQ'.cY1i).2⟩
  · refine altEven_conn_two _ _ _ _ _ _ wd hP hQ ?_ ?_
    · rw [regs_snoc_two wd]
      show ∀ a ∈ tileShape ZTile.one, a ∈ (below f (wd ++ [Digit.two]) wd).aOdd.dom ∧
        altD wd true - a ∈ (below f (wd ++ [Digit.two]) wd).aOdd.dom
      rw [hbel]; exact hH
    · intro hWd
      obtain ⟨hP', hQ'⟩ := stdCorners_reg D f wd (not_base_of_W1Odd wd hWd) hcw
      rw [regs_snoc_two wd]
      show _ ∈ (below f (wd ++ [Digit.two]) wd).aOdd.dom ∧ _ ∈ (below f (wd ++ [Digit.two]) wd).aOdd.dom
      rw [hbel]
      exact ⟨((hpar hWd).2 _ hQ'.cXi).1, ((hpar hWd).2 _ hQ'.cY1).2⟩
  · exact absurd rfl hd

/-! ### Points of the elongated L-corrected copies -/

/-- The standard tile odometer of the second register of `w` has its eight corner points, over any family that agrees with `f`
there. -/
theorem stdCorners_snd' (D : JointData) (f g : Word → JSlice) (w u : Word) (h2 : (regsAt w).2 = some u) (hg : g u = f u)
    (hJu : IsJointSlice D f u) :
    StdCorners (regOdo D.S (fun v => (g v).tOdd) (fun v => (g v).tEven) (regsAt w).2 false) (vQ1 w) (vQ2 w) := by
  rw [h2]
  show StdCorners (g u).tEven _ _
  rw [hg]
  obtain ⟨α, β, -, hV⟩ := TileTranslationStd.stdCorners_even u (f u).tEven hJu.2.2.1.2.2.2.2.2.1
  have h := JointRot.stdCorners_of_values _ _ _ _ _ _ hV
  rw [(JointRot.parents_of_regs w).2 u h2] at h
  exact h

theorem stdCorners_fst' (D : JointData) (f g : Word → JSlice) (w u : Word) (h1 : (regsAt w).1 = some u) (hg : g u = f u)
    (hJu : IsJointSlice D f u) :
    StdCorners (regOdo D.S (fun v => (g v).tOdd) (fun v => (g v).tEven) (regsAt w).1 true) (vP1 w) (vP2 w) := by
  rw [h1]
  show StdCorners (g u).tOdd _ _
  rw [hg]
  obtain ⟨α, β, -, hV⟩ := TileTranslationStd.stdCorners_odd u (f u).tOdd hJu.2.2.1.2.2.2.2.1
  have h := JointRot.stdCorners_of_values _ _ _ _ _ _ hV
  rw [(JointRot.parents_of_regs w).1 u h1] at h
  exact h

theorem regs_pre_snd (v : Word) (s : Digit) (hs : s ≠ Digit.two) : (regsAt (v ++ [s])).2 = some v := by
  rw [JointRot.regsAt_append_singleton]; cases s <;> simp_all [SurgicalWeak.regStep]

theorem regs_pre_fst (v : Word) (s : Digit) (hs : s ≠ Digit.three) : (regsAt (v ++ [s])).1 = some v := by
  rw [JointRot.regsAt_append_singleton]; cases s <;> simp_all [SurgicalWeak.regStep]

theorem fracOdd_snoc_two (wd : Word) : texV1Odd (StandardClause.fracOdd wd) = vP1 (wd ++ [Digit.two]) ∧
    texV2 (StandardClause.fracOdd wd) = vP2 (wd ++ [Digit.two]) := by
  unfold vP1 vP2 StandardClause.fracOdd
  rw [parentsAt_append_singleton]
  exact ⟨rfl, rfl⟩

theorem fracEven_snoc_three (wd : Word) : texV1Even (StandardClause.fracEven wd) = vQ1 (wd ++ [Digit.three]) ∧
    texV2 (StandardClause.fracEven wd) = vQ2 (wd ++ [Digit.three]) := by
  unfold vQ1 vQ2 StandardClause.fracEven
  rw [parentsAt_append_singleton]
  exact ⟨rfl, rfl⟩

/-- The corner points of the four sides of the odd child of `wd` (on the side strings at the standard anchors). -/
theorem odd_side_corners (wd : Word) :
    ((0 : ℤ), (0 : ℤ)) ∈ placedSites (sideString (hWordOf wd false) (vWordOf wd false) 0 .hPlus) ∧
    vP1 (wd ++ [Digit.two]) ∈ placedSites (sideString (hWordOf wd false) (vWordOf wd false) 0 .hPlus) ∧
    vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ)) ∈ placedSites (sideString (hWordOf wd false) (vWordOf wd false) 0 .hMinus) ∧
    ((1 : ℤ), (0 : ℤ)) ∈ placedSites (sideString (hWordOf wd false) (vWordOf wd false) 0 .vMinus) ∧
    vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (0 : ℤ)) ∈ placedSites (sideString (hWordOf wd false) (vWordOf wd false) 0 .vMinus) ∧
    vP1 (wd ++ [Digit.two]) - ((0 : ℤ), (1 : ℤ)) ∈ placedSites (sideString (hWordOf wd false) (vWordOf wd false) 0 .vPlus) := by
  obtain ⟨hX, hY⟩ := fracOdd_snoc_two wd
  have hP := JointRot.side_hPlus (hWordOf wd false) (texV1Odd (StandardClause.fracOdd wd))
    (hWordOf_head_last wd false).1 (hWordOf_head_last wd false).2 (StdCornerAnchors.stdAnchorX_odd wd)
  have hM := JointRot.side_hMinus (hWordOf wd false).reverse (by
      intro h; rw [List.reverse_eq_nil_iff] at h; have := (hWordOf_head_last wd false).1; rw [h] at this; simp at this)
    (lastPosOf (vRevStringAt (vWordOf wd false).reverse 0))
  have hV := JointRot.side_vMinus (vWordOf wd false) (texV2 (StandardClause.fracOdd wd))
    (StringCorners.vertWord_head_last wd).1 (StringCorners.vertWord_head_last wd).2 (StdCornerAnchors.stdAnchorY_odd wd)
  have hVp := JointRot.side_vPlus (vWordOf wd false) (by
      intro h; have := (StringCorners.vertWord_head_last wd).1
      change (vWordOf wd false).head? = some Letter.p at this
      rw [h] at this; simp at this)
    (lastPosOf (hStringAt (hWordOf wd false) 0))
  rw [hX] at hP
  rw [hY] at hV
  refine ⟨hP.1, hP.2, ?_, hV.1, hV.2, ?_⟩
  · have e : lastPosOf (vRevStringAt (vWordOf wd false).reverse 0) + ((0 : ℤ), (1 : ℤ)) =
        vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ)) := by
      rw [StdCornerAnchors.stdAnchorY_odd wd, hY]; refine Prod.ext ?_ ?_ <;> (simp only [Prod.fst_add, Prod.snd_add]; omega)
    rw [e] at hM; exact hM
  · have e : lastPosOf (hStringAt (hWordOf wd false) 0) + ((1 : ℤ), (0 : ℤ)) = vP1 (wd ++ [Digit.two]) - ((0 : ℤ), (1 : ℤ)) := by
      rw [show (0 : GInt) = ((0 : ℤ), (0 : ℤ)) from rfl, StdCornerAnchors.stdAnchorX_odd wd, hX]
      refine Prod.ext ?_ ?_ <;> (simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
    rw [e] at hVp; exact hVp

/-- The corner points of the horizontal sides of the even child of `wd`. -/
theorem even_side_corners (wd : Word) :
    ((0 : ℤ), (0 : ℤ)) ∈ placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 .hPlus) ∧
    vQ1 (wd ++ [Digit.three]) ∈ placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 .hPlus) ∧
    vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ)) ∈ placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 .hMinus) := by
  obtain ⟨hX, hY⟩ := fracEven_snoc_three wd
  have hP := JointRot.side_hPlus (hWordOf wd true) (texV1Even (StandardClause.fracEven wd))
    (hWordOf_head_last wd true).1 (hWordOf_head_last wd true).2 (StdCornerAnchors.stdAnchorX_even wd)
  have hM := JointRot.side_hMinus (hWordOf wd true).reverse (by
      intro h; rw [List.reverse_eq_nil_iff] at h; have := (hWordOf_head_last wd true).1; rw [h] at this; simp at this)
    (lastPosOf (vRevStringAt (vWordOf wd true).reverse 0))
  rw [hX] at hP
  refine ⟨hP.1, hP.2, ?_⟩
  have e : lastPosOf (vRevStringAt (vWordOf wd true).reverse 0) + ((0 : ℤ), (1 : ℤ)) =
      vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ)) := by
    rw [StdCornerAnchors.stdAnchorY_even wd, hY]; refine Prod.ext ?_ ?_ <;> (simp only [Prod.fst_add, Prod.snd_add]; omega)
  rw [e] at hM; exact hM

/-- Points of the elongated odd L-corrected odometer of `wd`: the corners of its kept sides, the first stem and the heads. -/
theorem lPts_odd (D : JointData) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (wd : Word)
    (hJw : IsJointSlice D f wd) (hJ : ∀ u : Word, u.length < wd.length → IsJointSlice D f u)
    (hT : ∀ u : Word, u.length < wd.length → TileProps u (f u).tOdd (f u).tEven (f u).aOdd (f u).aEven)
    (hdef : OddLDefined wd) (plus : Bool) :
    (plus = false → ((0 : ℤ), (0 : ℤ)) ∈ ((f wd).lOdd plus true).dom ∧ vP1 (wd ++ [Digit.two]) ∈ ((f wd).lOdd plus true).dom) ∧
    (plus = true → vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ)) ∈ ((f wd).lOdd plus true).dom) ∧
    ((W1Odd wd == plus) = false → ((1 : ℤ), (0 : ℤ)) ∈ ((f wd).lOdd plus true).dom ∧
      vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (0 : ℤ)) ∈ ((f wd).lOdd plus true).dom) ∧
    ((W1Odd wd == plus) = true → vP1 (wd ++ [Digit.two]) - ((0 : ℤ), (1 : ℤ)) ∈ ((f wd).lOdd plus true).dom) ∧
    (∀ x ∈ (regOdo D.S (fun u => (below f wd u).tOdd) (fun u => (below f wd u).tEven)
        (regsAt (stripTrailing Digit.two wd)).2 false).dom, oStemPos wd plus 0 + x ∈ ((f wd).lOdd plus true).dom) ∧
    StdCorners (regOdo D.S (fun u => (below f wd u).tOdd) (fun u => (below f wd u).tEven)
      (regsAt (stripTrailing Digit.two wd)).2 false) (vQ1 (stripTrailing Digit.two wd)) (vQ2 (stripTrailing Digit.two wd)) ∧
    (∀ i < 2 * (trailingCount Digit.two wd + 1), ∀ a ∈ tileShape ZTile.one,
      oHeadPos wd plus i + a ∈ ((f wd).lOdd plus true).dom) := by
  obtain ⟨hR, -, c, hc⟩ := hJw.2.2.2.1 plus true hdef
  rw [hlS] at hc
  obtain ⟨s0, sX, sM, sV1, sVY, sVp⟩ := odd_side_corners wd
  obtain ⟨w1, s, k, hs, hw⟩ := hdef
  have hpre : stripTrailing Digit.two wd = w1 ++ [s] := by rw [hw]; exact JointRot.strip_of_defined _ _ hs _ _
  have h2 := regs_pre_snd w1 s hs
  rw [← hpre] at h2
  have hlw1 : w1.length < wd.length := by rw [hw]; simp
  have hbel : below f wd w1 = f w1 := below_of_lt f _ _ hlw1
  refine ⟨fun hp => ⟨(hc .hPlus (by simp [paperLSides, hp]) _ s0).1, (hc .hPlus (by simp [paperLSides, hp]) _ sX).1⟩,
    fun hp => (hc .hMinus (by simp [paperLSides, hp]) _ sM).1,
    fun ho => ⟨(hc .vMinus (by simp [paperLSides, ho]) _ sV1).1, (hc .vMinus (by simp [paperLSides, ho]) _ sVY).1⟩,
    fun ho => (hc .vPlus (by simp [paperLSides, ho]) _ sVp).1, fun x hx => ?_,
    stdCorners_snd' D f (below f wd) _ w1 h2 hbel (hJ w1 hlw1), fun i hi a ha => ?_⟩
  · rw [hR.1]
    refine mem_pieceUnion_of (p := stdPiece (regOdo D.S (fun u => (below f wd u).tOdd) (fun u => (below f wd u).tEven)
      (regsAt (stripTrailing Digit.two wd)).2 false) (oStemPos wd plus 0)
      (oddLInitAff wd plus + altAff (stripTrailing Digit.two wd) (((0 : ℕ) : ℤ) • (oddKCoeff (W1Odd wd) plus).1))) ?_ ?_
    · unfold oddLPieces
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨0, by simp, rfl⟩))
    · simp only [stdPiece, add_sub_cancel_left]; exact hx
  · rw [hR.1]
    unfold oddLPieces
    refine JointGlue.mem_pieceUnion.mpr ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩), ?_⟩
    · rw [mem_placed]
      show oHeadPos wd plus i + a - oHeadPos wd plus i ∈ _
      rw [add_sub_cancel_left, h2]
      show a ∈ (below f wd w1).aEven.dom
      rw [hbel]
      exact (altHalfTurn_pts _ _ _ (hT w1 hlw1).2.2.2.2.2 a ha).1

/-- Points of the elongated even L-corrected odometer of `wd`: the corners of its horizontal kept side, the first stem and the
heads. -/
theorem lPts_even (D : JointData) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (wd : Word)
    (hJw : IsJointSlice D f wd) (hJ : ∀ u : Word, u.length < wd.length → IsJointSlice D f u)
    (hT : ∀ u : Word, u.length < wd.length → TileProps u (f u).tOdd (f u).tEven (f u).aOdd (f u).aEven)
    (hdef : EvenLDefined wd) (plus : Bool) :
    (plus = true → ((0 : ℤ), (0 : ℤ)) ∈ ((f wd).lEven plus true).dom ∧ vQ1 (wd ++ [Digit.three]) ∈ ((f wd).lEven plus true).dom) ∧
    (plus = false → vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ)) ∈ ((f wd).lEven plus true).dom) ∧
    (∀ x ∈ (regOdo D.S (fun u => (below f wd u).tOdd) (fun u => (below f wd u).tEven)
        (regsAt (stripTrailing Digit.three wd)).1 true).dom, eStemPos wd plus 0 + x ∈ ((f wd).lEven plus true).dom) ∧
    StdCorners (regOdo D.S (fun u => (below f wd u).tOdd) (fun u => (below f wd u).tEven)
      (regsAt (stripTrailing Digit.three wd)).1 true) (vP1 (stripTrailing Digit.three wd)) (vP2 (stripTrailing Digit.three wd)) ∧
    (∀ i < 2 * (trailingCount Digit.three wd + 1), ∀ a ∈ tileShape ZTile.one,
      eHeadPos wd plus i + a ∈ ((f wd).lEven plus true).dom) := by
  obtain ⟨hR, -, c, hc⟩ := hJw.2.2.2.2 plus true hdef
  rw [hlS] at hc
  obtain ⟨s0, sX, sM⟩ := even_side_corners wd
  obtain ⟨w1, s, k, hs, hw⟩ := hdef
  have hpre : stripTrailing Digit.three wd = w1 ++ [s] := by rw [hw]; exact JointRot.strip_of_defined _ _ hs _ _
  have h1 := regs_pre_fst w1 s hs
  rw [← hpre] at h1
  have hlw1 : w1.length < wd.length := by rw [hw]; simp
  have hbel : below f wd w1 = f w1 := below_of_lt f _ _ hlw1
  refine ⟨fun hp => ⟨(hc .hPlus (by cases h : W1Odd wd <;> simp [paperLSides, printedEvenSides, hp]) _ s0).1,
      (hc .hPlus (by cases h : W1Odd wd <;> simp [paperLSides, printedEvenSides, hp]) _ sX).1⟩,
    fun hp => (hc .hMinus (by cases h : W1Odd wd <;> simp [paperLSides, printedEvenSides, hp]) _ sM).1,
    fun x hx => ?_, stdCorners_fst' D f (below f wd) _ w1 h1 hbel (hJ w1 hlw1), fun i hi a ha => ?_⟩
  · rw [hR.1]
    refine mem_pieceUnion_of (p := stdPiece (regOdo D.S (fun u => (below f wd u).tOdd) (fun u => (below f wd u).tEven)
      (regsAt (stripTrailing Digit.three wd)).1 true) (eStemPos wd plus 0)
      (evenLInitAff wd plus + altAff (stripTrailing Digit.three wd) (((0 : ℕ) : ℤ) • (evenKCoeff (W1Odd wd) plus
        (decide ((stripTrailing Digit.three wd).getLast? = some Digit.two))).1))) ?_ ?_
    · unfold evenLPieces
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨0, by simp, rfl⟩)))
    · simp only [stdPiece, add_sub_cancel_left]; exact hx
  · rw [hR.1]
    unfold evenLPieces
    refine JointGlue.mem_pieceUnion.mpr ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩), ?_⟩
    · rw [mem_placed]
      show eHeadPos wd plus i + a - eHeadPos wd plus i ∈ _
      rw [add_sub_cancel_left, h1]
      show a ∈ (below f wd w1).aOdd.dom
      rw [hbel]
      exact (altHalfTurn_pts _ _ _ (hT w1 hlw1).2.2.2.2.1 a ha).1

/-- The odd alternate decomposition after a `2`: two L-corrected copies. -/
theorem connAltOdd_corr (D : JointData) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (wd : Word)
    (hb : ¬ Standard.IsBase (wd ++ [Digit.two])) (hJ : ∀ u : Word, u.length < (wd ++ [Digit.two]).length → IsJointSlice D f u)
    (hT : ∀ u : Word, u.length < (wd ++ [Digit.two]).length → TileProps u (f u).tOdd (f u).tEven (f u).aOdd (f u).aEven) :
    (overlapGraph (goodPart (tileAltOddPieces D.S (fun u => (below f (wd ++ [Digit.two]) u).tOdd)
      (fun u => (below f (wd ++ [Digit.two]) u).tEven) (fun u => (below f (wd ++ [Digit.two]) u).aOdd)
      (fun u => (below f (wd ++ [Digit.two]) u).aEven) (fun u => (below f (wd ++ [Digit.two]) u).lOdd) (wd ++ [Digit.two])))).Connected := by
  obtain ⟨hP, hQ⟩ := stdCorners_reg D f _ hb hJ
  have hlt : wd.length < (wd ++ [Digit.two]).length := by simp
  have hbel : below f (wd ++ [Digit.two]) wd = f wd := below_of_lt f _ wd hlt
  have hdef := JointRot.oddLDefined_dropLast hb (by simp)
  simp only [List.dropLast_concat] at hdef
  have lpF := lPts_odd D hlS f wd (hJ wd hlt) (fun u hu => hJ u (by simp; omega)) (fun u hu => hT u (by simp; omega)) hdef false
  have lpT := lPts_odd D hlS f wd (hJ wd hlt) (fun u hu => hJ u (by simp; omega)) (fun u hu => hT u (by simp; omega)) hdef true
  refine altOdd_conn_two _ _ _ _ _ _ wd hP hQ (fun hWd => ?_) (fun hWd => ?_)
  · simp only [hbel]
    exact ⟨((lpT).2.2.1 (by rw [hWd]; rfl)).1, (lpF).2.2.2.2.1 _ (lpF).2.2.2.2.2.1.cD1, ((lpF).1 rfl).1, (lpT).2.2.2.2.2.2 1 (by omega) _ (by simp [tileShape])⟩
  · simp only [hbel]
    exact ⟨((lpF).2.2.1 (by rw [hWd]; rfl)).2, (lpT).2.2.2.1 (by rw [hWd]; rfl), (lpF).2.2.2.2.2.2 1 (by omega) _ (by simp [tileShape]), (lpT).2.2.2.2.2.2 (2 * trailingCount Digit.two wd + 1) (by omega) _ (by simp [tileShape])⟩

/-- The even alternate decomposition after a `3`: two L-corrected copies. -/
theorem connAltEven_corr (D : JointData) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (wd : Word)
    (hb : ¬ Standard.IsBase (wd ++ [Digit.three])) (hJ : ∀ u : Word, u.length < (wd ++ [Digit.three]).length → IsJointSlice D f u)
    (hT : ∀ u : Word, u.length < (wd ++ [Digit.three]).length → TileProps u (f u).tOdd (f u).tEven (f u).aOdd (f u).aEven) :
    (overlapGraph (goodPart (tileAltEvenPieces D.S (fun u => (below f (wd ++ [Digit.three]) u).tOdd)
      (fun u => (below f (wd ++ [Digit.three]) u).tEven) (fun u => (below f (wd ++ [Digit.three]) u).aOdd)
      (fun u => (below f (wd ++ [Digit.three]) u).aEven) (fun u => (below f (wd ++ [Digit.three]) u).lEven) (wd ++ [Digit.three])))).Connected := by
  obtain ⟨hP, hQ⟩ := stdCorners_reg D f _ hb hJ
  have hlt : wd.length < (wd ++ [Digit.three]).length := by simp
  have hbel : below f (wd ++ [Digit.three]) wd = f wd := below_of_lt f _ wd hlt
  have hdef := JointRot.evenLDefined_dropLast hb (by simp)
  simp only [List.dropLast_concat] at hdef
  have lpF := lPts_even D hlS f wd (hJ wd hlt) (fun u hu => hJ u (by simp; omega)) (fun u hu => hT u (by simp; omega)) hdef false
  have lpT := lPts_even D hlS f wd (hJ wd hlt) (fun u hu => hJ u (by simp; omega)) (fun u hu => hT u (by simp; omega)) hdef true
  refine altEven_conn_three _ _ _ _ _ _ wd hP hQ (fun hWd => ?_) (fun hWd => ?_)
  · simp only [hbel]
    exact ⟨((lpT).1 rfl).2, (lpF).2.1 rfl, (lpT).2.2.2.2 1 (by omega) _ (by simp [tileShape]), (lpF).2.2.2.2 (2 * trailingCount Digit.three wd + 1) (by omega) _ (by simp [tileShape])⟩
  · simp only [hbel]
    exact ⟨((lpT).1 rfl).1, (lpF).2.2.1 _ (lpF).2.2.2.1.cD, (lpT).2.2.2.2 1 (by omega) _ (by simp [tileShape]), (lpF).2.2.2.2 (2 * trailingCount Digit.three wd + 1) (by omega) _ (by simp [tileShape])⟩

/-- **`ConnectedAlt`** for a word that is not a base word, from the family below it (paper sides of the L-corrections). -/
theorem connectedAlt_of (D : JointData) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (w : Word)
    (hb : ¬ Standard.IsBase w) (hJ : ∀ u : Word, u.length < w.length → IsJointSlice D f u)
    (hT : ∀ u : Word, u.length < w.length → TileProps u (f u).tOdd (f u).tEven (f u).aOdd (f u).aEven) :
    JointRot.ConnectedAlt D (below f w) w := by
  rcases w.eq_nil_or_concat with rfl | ⟨wd, d, h⟩
  · exact absurd (Or.inl rfl) hb
  rw [List.concat_eq_append] at h
  subst h
  have hlt : wd.length < (wd ++ [d]).length := by simp
  cases d
  · exact ⟨connAltOdd_kept D f wd _ (by decide) hb hJ (hT wd hlt), connAltEven_kept D f wd _ (by decide) hb hJ (hT wd hlt)⟩
  · exact ⟨connAltOdd_corr D hlS f wd hb hJ hT, connAltEven_kept D f wd _ (by decide) hb hJ (hT wd hlt)⟩
  · exact ⟨connAltOdd_kept D f wd _ (by decide) hb hJ (hT wd hlt), connAltEven_corr D hlS f wd hb hJ hT⟩

end FLatticePaper.Tiles.ConnectedAltL
