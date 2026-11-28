import FLatticePaper.Tiles.CorrectedMixedSources

/-! Axes and the actual alternate register at the first exit from either positive pure run. -/

namespace FLatticePaper.Tiles.CorrectedMixedBasePlacement

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard SurgicalWeak SurgicalAlt SurgicalAltTiles SurgicalDict
open JointFamily LCorrecProps AltRotStep PaperAltBase
open CorrectedEvenPlacement CorrectedPlacementFrames CorrectedMixedSources

def pureWord (three : Bool) (k : ℕ) : Word := List.replicate (k+1) (if three then .three else .two)
def child (three one : Bool) (k : ℕ) : Word := pureWord three k++[exit one]
def size (three : Bool) (k : ℕ) : ℤ := 2*((k:ℤ)+1)+(if three then 2 else 3)

def axisA (three : Bool) (d : ℤ) : Site := if three then (2*d,2) else (d+1,d-1)
def axisB (three : Bool) (d : ℤ) : Site := if three then (1-d,d+1) else (-1,d)
def axisU (three one : Bool) (d : ℤ) : Site := if three then (d+(if one then 1 else -1),1) else (d,d-2)
def axisV (three one : Bool) (d : ℤ) : Site := if three then
  (1-(d+(if one then 1 else -1)),1+(d+(if one then 1 else -1))) else (-2,2*d-2)

theorem nonbase (three one : Bool) (k : ℕ) (different : (three || one)=true) : ¬IsBase (child three one k) := by
  cases three <;> cases one
  all_goals first | contradiction | skip
  all_goals unfold child pureWord exit; simp only [Bool.false_eq_true,if_true,if_false]
  all_goals rintro (nil|two|three)
  all_goals first | simp at nil | skip
  all_goals first
    | exact Digit.noConfusion (two _ (List.mem_append_right _ (List.mem_cons_self)))
    | exact Digit.noConfusion (three _ (List.mem_append_right _ (List.mem_cons_self)))
    | exact Digit.noConfusion (three _ (List.mem_append_left _ (List.mem_replicate.mpr ⟨by omega,rfl⟩)))

theorem previous (three : Bool) (k : ℕ) :
    -(parentsAt (pureWord three k)).odd.det (parentsAt (pureWord three k)).even=1 := by
  cases three <;> simp [pureWord,BaseTileProps.parents_two,BaseTileProps.parents_three,Fraction.det]

theorem axes (three one : Bool) (k : ℕ) (different : (three || one)=true) :
    let t := child three one k
    let d := size three k
    vP1 t=axisA three d ∧ vP2 t=axisB three d ∧ vQ1 t=axisU three one d ∧ vQ2 t=axisV three one d := by
  cases three <;> cases one
  all_goals first | contradiction | skip
  all_goals dsimp only; refine ⟨?_,?_,?_,?_⟩
  all_goals ext <;> simp [child,pureWord,exit,size,axisA,axisB,axisU,axisV,vP1,vP2,vQ1,vQ2,
    parentsAt_append_singleton,Parents.step,Parents.current,Parents.combine,BaseTileProps.parents_three,
    BaseTileProps.parents_two,texV1Odd,texV1Even,texV2] <;> ring

def extra (three one even : Bool) (d : ℤ) : Tile :=
  let b := axisB three d
  let u := axisU three one d
  let v := axisV three one d
  let a := axisA three d
  if even then
    shift (if three then shift (ladderAltF d) (1,1) else shift (nearStairAltF d) (0,-1))
      (if one then b+u else v)
  else if one then
    shift (if three then stairAltF (d+1) else shift (nearLadderAltF (d-1)) (0,-1)) (b+a-u)
  else ∅

set_option maxHeartbeats 400000 in
/-- At a base predecessor the remaining alternate copy has the raw stair or ladder boundary
of that base and its prescribed translation; it is empty on an odd two exit. -/
theorem remainder (three one even : Bool) (k : ℕ) (different : (three || one)=true) :
    rest (child three one k) one even=extra three one even (size three k) := by
  have ph : W1Odd (child three one k)=one := by
    cases three <;> cases one <;> simp [child,pureWord,W1Odd,phase,List.count_append,List.count_replicate,exit]
  have ⟨A,Bb,U,V⟩ := axes three one k different
  have co (c) : coeffOff (texV1Odd (parentsAt (child three one k)).odd) (texV2 (parentsAt (child three one k)).odd)
      (texV1Even (parentsAt (child three one k)).even) (texV2 (parentsAt (child three one k)).even) c =
      coeffOff (axisA three (size three k)) (axisB three (size three k))
        (axisU three one (size three k)) (axisV three one (size three k)) c := by
    change coeffOff (vP1 _) (vP2 _) (vQ1 _) (vQ2 _) _=_
    rw [A,Bb,U,V]
  have base : IsBase (pureWord three k) := by
    cases three
    · exact isBase_replicate_two _
    · exact isBase_replicate_three _
  have oldP : (altRegs B (child three one k)).1=(B (pureWord three k)).1 := by
    rw [←altOddTile_of_base B base,child,altRegs_snoc]; cases one <;> rfl
  have oldQ (o : one=true) : (altRegs B (child three one k)).2=(B (pureWord three k)).2 := by
    subst one
    rw [←altEvenTile_of_base B base,child,altRegs_snoc]; rfl
  unfold rest
  rw [ph]
  cases three <;> cases one <;> cases even
  all_goals first | contradiction | skip
  all_goals simp only [Bool.false_eq_true,if_false,if_true,extra,exit,altP1Part,altQ1Part,altP1Coeff,
    altQ1Coeff,co,reduceCtorEq]
  all_goals simp only [oldP,oldQ]; simp [pureWord,B_three _ (Nat.succ_pos _),B_two _ (Nat.succ_pos _),
    coeffOff,size,axisA,axisB,axisU,axisV,Prod.mk_add_mk,Prod.mk_sub_mk]
  all_goals congr 1; first | rfl | (congr 1 <;> ring)

/-- The physical diagram in the primitive axes of the base exit. -/
def entry (three one even : Bool) (d : ℤ) :=
  CorrectedMixedPlacement.layout (axisA three d) (axisB three d) (axisU three one d) (axisV three one d) one 1 even

/-- Assembly at one physical site, with the raw alternate register at its actual offset. -/
theorem at_site (three one even : Bool) (k : ℕ) (different : (three || one)=true) (z : Site)
    (comparison : let d := size three k
      let P := fun i => (entry three one even d i).mem z
      (six P ∨ z∈extra three one even d) ↔ P 0 ∨ P 9) :
    let t := child three one k
    let e := -(parentsAt t).odd.det (parentsAt t).even
    let A := vP1 t+vQ1 t
    let Bb := vP2 t+vQ2 t
    z∈(if even then altEvenT t else altOddT t) ↔ CorrectedCellsBands.Band A Bb 0 0 z ∨
      CorrectedCellsBands.Band A Bb 0 0 (z-(vP2 t+(if even then -e else e) • vQ1 t)) := by
  intro t e A Bb
  have ⟨p,q,u,v⟩ := axes three one k different
  have src := printed (pureWord three k) one even (nonbase three one k different) z
  change _ ↔ six (fun i => (CorrectedMixedPlacement.layout (vP1 t) (vP2 t) (vQ1 t) (vQ2 t) one
    (-(parentsAt (pureWord three k)).odd.det (parentsAt (pureWord three k)).even) even i).mem z) ∨ z∈rest t one even at src
  change vP1 t=_ at p
  change vP2 t=_ at q
  change vQ1 t=_ at u
  change vQ2 t=_ at v
  have ex : rest t one even=extra three one even (size three k) := remainder three one even k different
  rw [p,q,u,v,previous,ex] at src
  have dt : e=CorrectedRegisterDiagram.orientation one 1 := by
    dsimp only [e,t,child]; rw [parentsAt_append_singleton,←previous three k]
    cases one
    · exact CorrectedRegisterLattice.next_sign _ false
    · exact CorrectedRegisterLattice.next_sign _ true
  refine src.trans (comparison.trans ?_)
  dsimp only [A,Bb]
  rw [p,q,u,v,dt]
  simp [entry,CorrectedMixedPlacement.layout,CorrectedPlacedDiagram.Block.mem]

end FLatticePaper.Tiles.CorrectedMixedBasePlacement
