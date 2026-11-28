import FLatticePaper.Tiles.CorrectedRegularRotation

/-! Rotation of the two complete corrected piece lists and the induced child-domain equalities. -/

namespace FLatticePaper.Tiles.CorrectedChildRotation

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard SurgicalDict SurgicalWeak SurgicalAlt JointFamily JointGlue JointRot LCorrecProps
open CorrectedEvenPlacement CorrectedPlacementFrames CorrectedCellRotation CorrectedChildColumns

private def member (ps : List Piece) (i : ℕ) (z : Site) := ∃ p, ps[i]?=some p ∧ z∈p.placed
private def Row (ps qs : List Piece) (i j : ℕ) (c : Site) := ∀ z, member qs i z ↔ member ps j (mulI z+c)

private theorem row_of_get {ps qs : List Piece} {i j : ℕ} {c : Site} (cr : Site)
    (hi : i<qs.length) (hj : j<ps.length)
    (T : CellsRot ps[j].odo.dom qs[i].odo.dom cr) (off : mulI qs[i].off=ps[j].off+cr-c) : Row ps qs i j c := by
  intro z
  simpa [member,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using placed T off z

private theorem all_members (ps : List Piece) (x : Site) :
    x∈pieceUnion ps ↔ ∃ i : ℕ, i<ps.length ∧ member ps i x := by
  rw [mem_pieceUnion]
  constructor
  · rintro ⟨p,hp,hx⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hp
    exact ⟨i,hi,_,List.getElem?_eq_getElem hi,hx⟩
  · rintro ⟨_,_,p,hp,hx⟩
    exact ⟨p,List.mem_of_getElem? hp,hx⟩

private theorem all_six (ps qs : List Piece) (c : Site) (perm : ℕ → ℕ)
    (lp : ps.length=6) (lq : qs.length=6) (bound : ∀ i, i<6 → perm i<6)
    (onto : ∀ j, j<6 → ∃ i, i<6 ∧ perm i=j)
    (rows : ∀ i, i<6 → Row ps qs i (perm i) c) : CellsRot (pieceUnion ps) (pieceUnion qs) c := by
  intro z
  rw [all_members,all_members,lp,lq]
  constructor
  · rintro ⟨i,hi,hit⟩
    exact ⟨perm i,bound i hi,(rows i hi z).mp hit⟩
  · rintro ⟨j,hj,hit⟩
    obtain ⟨i,hi,rfl⟩ := onto j hj
    exact ⟨i,hi,(rows i hi z).mpr hit⟩
private def stdIndex (o : Bool) (i : ℕ) : ℕ :=
  (if o then [3,2,5,4,1,0] else [5,4,3,2,0,1])[i]?.getD i

private def altIndex (o : Bool) (i : ℕ) : ℕ :=
  (if o then [1,0,3,2,5,4] else [2,3,0,1,4,5])[i]?.getD i

private abbrev C (w : Word) := texV1Odd ((parentsAt w).current .odd) - ((0 : ℤ),(1 : ℤ))

section
variable (S : WeakData) (pO pE aO aE : Word → PartialOdometer)
variable (lE lO : Word → Bool → Bool → PartialOdometer) (w : Word)
variable (hl : w.getLast? = some Digit.three)
variable (hP : CellsRot (regOdo S pO pE (regsAt w).1 true).dom (regOdo S pO pE (regsAt (swapW w)).2 false).dom
  (vP1 w - ((0 : ℤ),(1 : ℤ))))
variable (hQ : CellsRot (regOdo S pO pE (regsAt w).2 false).dom (regOdo S pO pE (regsAt (swapW w)).1 true).dom
  (vQ1 w - ((0 : ℤ),(1 : ℤ))))
variable (hL : ∀ elong : Bool, w.getLast? = some Digit.three → ∀ plus : Bool,
  CellsRot (lE w.dropLast plus elong).dom (lO (swapW w.dropLast) (plus != W1Odd w) elong).dom (vQ1 w - ((0 : ℤ),(1 : ℤ))))

set_option hygiene false in
local macro "std_parent" : tactic => `(tactic| (
  simp only [tileOddPieces, tileEvenPieces, List.getElem_cons_succ, List.getElem_cons_zero, stdPiece,
    corr_swapW_two, corr_swapW_three, W1Odd_swapW, dropLast_swapW, hl, hWo, reduceCtorEq,
    decide_true, decide_false, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
    Bool.false_eq_true, if_true, if_false]
  first | exact hP | exact hQ | exact lp | exact lm))

set_option hygiene false in
local macro "alt_parent" : tactic => `(tactic| (alt_lists; first | exact hP | exact hQ | exact lp | exact lm))

include hl hP hQ hL
set_option maxHeartbeats 400000 in
private theorem standard_rows (i : ℕ) (hi : i < 6) :
    Row (tileOddPieces S pO pE lE w) (tileEvenPieces S pO pE lO (swapW w)) i (stdIndex (W1Odd w) i) (C w) := by
  have lp := hL false hl true
  have lm := hL false hl false
  obtain ⟨e1,e2,e3,e4,e5,e6⟩ := vecs_swapW w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := (parentsAt_valid w).odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := (parentsAt_valid w).even_parity
  have hh : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  cases hWo : W1Odd w <;> rcases hh with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [hWo] at lp lm
  all_goals norm_num [stdIndex, C]
  all_goals
    first
    | (apply row_of_get (vQ1 w - ((0 : ℤ),(1 : ℤ))) (by simp [tileEvenPieces]) (by simp [tileOddPieces]) <;>
       first | std_parent | rot_id)
    | (apply row_of_get (vP1 w - ((0 : ℤ),(1 : ℤ))) (by simp [tileEvenPieces]) (by simp [tileOddPieces]) <;>
       first | std_parent | rot_id)
set_option maxHeartbeats 400000 in
private theorem alternate_rows (i : ℕ) (hi : i < 6) :
    Row (tileAltEvenPieces S pO pE aO aE lE w) (tileAltOddPieces S pO pE aO aE lO (swapW w)) i
      (altIndex (W1Odd w) i) (altCf w false).1 := by
  have lp := hL true hl true
  have lm := hL true hl false
  obtain ⟨e1,e2,e3,e4,e5,e6⟩ := vecs_swapW w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := (parentsAt_valid w).odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := (parentsAt_valid w).even_parity
  have hh : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  cases hWo : W1Odd w <;> rcases hh with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [hWo] at lp lm
  all_goals norm_num [altIndex]
  all_goals
    first
    | (apply row_of_get (vQ1 w - ((0 : ℤ),(1 : ℤ))) (by alt_lists; simp) (by alt_lists; simp) <;>
       first | alt_parent | rot_id_alt)
    | (apply row_of_get (vP1 w - ((0 : ℤ),(1 : ℤ))) (by alt_lists; simp) (by alt_lists; simp) <;>
       first | alt_parent | rot_id_alt)

omit hl hP hQ hL

private theorem finite_maps (o alt : Bool) :
    let f := if alt then altIndex o else stdIndex o
    (∀ i, i<6 → f i<6) ∧ (∀ j, j<6 → ∃ i, i<6 ∧ f i=j) := by
  intro f
  have first (i : ℕ) (hi : i<6) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  constructor
  · intro i hi; rcases first i hi with rfl|rfl|rfl|rfl|rfl|rfl <;> cases o <;> cases alt <;> decide
  · intro j hj
    have witness : ∃ i : Fin 6, f i.val=j := by
      rcases first j hj with rfl|rfl|rfl|rfl|rfl|rfl <;> cases o <;> cases alt <;> decide
    obtain ⟨i,hi⟩ := witness
    exact ⟨i.val,i.isLt,hi⟩


include hl hP hQ hL in
theorem standard : CellsRot (pieceUnion (tileOddPieces S pO pE lE w))
    (pieceUnion (tileEvenPieces S pO pE lO (swapW w))) (texV1Odd ((parentsAt w).current .odd)-((0,1):Site)) := by
  obtain ⟨bounds,onto⟩ := finite_maps (W1Odd w) false
  exact all_six _ _ _ _ (by simp [tileOddPieces]) (by simp [tileEvenPieces]) bounds onto
    (standard_rows S pO pE lE lO w hl hP hQ hL)

include hl hP hQ hL in
theorem alternate : CellsRot (pieceUnion (tileAltEvenPieces S pO pE aO aE lE w))
    (pieceUnion (tileAltOddPieces S pO pE aO aE lO (swapW w))) (altCf w false).1 := by
  obtain ⟨bounds,onto⟩ := finite_maps (W1Odd w) true
  apply all_six _ _ _ (altIndex (W1Odd w)) _ _ bounds onto (alternate_rows S pO pE aO aE lE lO w hl hP hQ hL)
  all_goals cases hWo : W1Odd w <;> alt_lists

end

end FLatticePaper.Tiles.CorrectedChildRotation
