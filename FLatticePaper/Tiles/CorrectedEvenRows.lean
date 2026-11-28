import FLatticePaper.Tiles.CorrectedChildColumns

/-! The full even-register copies, completed stem rows, bridges and single head column of the
two children corrected after a three. -/

namespace FLatticePaper.Tiles.CorrectedEvenRows

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily LCorrecProps LCorrecRecursion SurgicalWeak SurgicalAlt SurgicalDict
open CorrectedColumnRuns CorrectedHeadColumn CorrectedChildColumns

private abbrev O (w : Word) := domOdo (oddTile w)
private abbrev E (w : Word) := domOdo (evenTile w)
private abbrev AO (w : Word) := domOdo (altOddT w)
private abbrev AE (w : Word) := domOdo (altEvenT w)
private abbrev pre (v : Word) := stripTrailing Digit.three v
private abbrev run (v : Word) := trailingCount Digit.three v
private abbrev eHead := JointRot.eHead cellData O E AO AE

/-- Offset of the full odd-register entry that is adjacent to the first stem. -/
def start (v : Word) (plus long : Bool) : Site :=
  let w := v++[Digit.three]
  if long then altOff w (altQ0Coeff (W1Odd w) (if plus then .p1Plus else .p1Minus))
  else p0Off w (if plus then .p1Plus else .p1Minus)

/-- Offset of the full even-register entry in one of the two doubled copies. -/
def full (v : Word) (plus long : Bool) : Site :=
  let w := v++[Digit.three]
  let o := W1Odd w
  if long then
    if plus then altOff w (altQ0Coeff o .dsQ1Plus)+(altShifts o (vP2 w) (vQ1 w)).2
    else altOff w (altQ0Coeff o .dsQ1Minus)
  else if plus then p0Off w .q1DPlus + (if o then vQ1 w else 0)
    else p0Off w .q1DMinus + (if o then 0 else vQ1 w)

def step (v : Word) (plus : Bool) : Site := altOff (pre v) (JointRot.eK v plus).1

private theorem first (v : Word) (plus long : Bool) :
    evenLInitOff v plus + evenOff v plus long = start v plus long + step v plus := by
  let k := run v
  have ev : pre v++List.replicate k .three = v := JointRot.strip_append_replicate _ _
  obtain ⟨a,b,c,d⟩ := ev ▸ three_periods (pre v) k
  have ew : pre v++List.replicate (k+1) .three = v++[.three] := by rw [List.replicate_succ',←List.append_assoc,ev]
  obtain ⟨a',b',c',d'⟩ := ew ▸ three_periods (pre v) (k+1)
  have hw : W1Odd (v++[.three])=W1Odd v := JointRot.phase_snoc_three v
  cases h : W1Odd v <;> cases plus <;> cases long
  all_goals apply Prod.ext
  all_goals simp [evenLInitOff,evenOff,start,step,JointRot.eK,evenKCoeff,hw,h,
    q0Off,p0Off,offsetQ0,offsetP0,altQ0Coeff,altShifts,altOff,coeffOff,b,c,d,a',b',c',d',pre,k]
  all_goals ring

private theorem stem_run (v : Word) : stemE (v++[.three]) = stemE (pre v) := by
  have reg (u : Word) (k : ℕ) : (regsAt (u++List.replicate k .three)).1 = (regsAt u).1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ',←List.append_assoc,WeakStepPaper.regsAt_snoc]
      exact ih
  have ev := JointRot.strip_append_replicate Digit.three v
  have hh := reg (pre v) (run v)
  rw [show pre v++List.replicate (run v) Digit.three = v from ev] at hh
  unfold stemE
  rw [WeakStepPaper.regsAt_snoc]
  change (regOdo cellData O E (regsAt v).1 true).dom = _
  rw [hh]

private theorem append_union (ps qs : List Piece) :
    pieceUnion (ps++qs) = pieceUnion ps ∪ pieceUnion qs := by
  ext z
  simp only [JointGlue.mem_pieceUnion,List.mem_append,Finset.mem_union]
  aesop

private theorem cons_union (p : Piece) (ps : List Piece) : pieceUnion (p::ps) = p.placed ∪ pieceUnion ps := rfl
private theorem placed (o : PartialOdometer) (u a : Site) : (stdPiece o u a).placed = shift o.dom u := rfl

/-- All the actual middle pieces on one side, including the enlarged small tile at a pure-two prefix. -/
def middle (v : Word) (plus long : Bool) : Tile :=
  shift (pieceUnion (JointRot.eMid cellData O E v plus)) (evenOff v plus long)

private theorem front (T : Tile) (a b : Site) (k : ℕ) :
    shift T a ∪ shift (column T b k) (a+b) = shift (column T b (k+1)) a := by
  ext z
  simp only [Finset.mem_union,mem_shift,mem_column]
  constructor
  · rintro (h|⟨i,hi,h⟩)
    · exact ⟨0,by omega,by simpa using h⟩
    · refine ⟨i+1,by omega,?_⟩
      convert h using 1; push_cast; rw [add_smul,one_smul]; abel
  · rintro ⟨i,hi,h⟩
    cases i with
    | zero => exact Or.inl (by simpa using h)
    | succ i =>
      right; refine ⟨i,by omega,?_⟩
      convert h using 1; push_cast; rw [add_smul,one_smul]; abel

private theorem foot_row (v : Word) (plus long : Bool) :
    shift (stemE (pre v)) (start v plus long) ∪ shift (evenFoot v plus) (evenOff v plus long) =
      shift (column (stemE (pre v)) (step v plus) (run v+1)) (start v plus long) ∪ middle v plus long := by
  let stem := JointRot.eStem cellData O E v plus
  let rows := (List.range (run v+1)).map stem
  have rr : shift (pieceUnion rows) (evenOff v plus long) =
      shift (column (stemE (pre v)) (step v plus) (run v)) (start v plus long+step v plus) := by
    rw [←first]
    ext z
    simp only [mem_shift,JointGlue.mem_pieceUnion,rows,List.mem_map,List.mem_range,mem_column]
    have pos (i : ℕ) : z-evenOff v plus long ∈ (stem i).placed ↔
        z-(evenLInitOff v plus+evenOff v plus long)-(i : ℤ) • step v plus ∈ stemE (pre v) := by
      change z-evenOff v plus long ∈ shift (stemE (pre v)) (evenLInitOff v plus+
        altOff (pre v) ((i : ℤ) • (JointRot.eK v plus).1)) ↔ _
      rw [mem_shift,altOff_smul]
      unfold step
      abel
    constructor
    · rintro ⟨_,⟨i,hi,rfl⟩,hi'⟩; exact ⟨i,by omega,(pos i).mp hi'⟩
    · rintro ⟨i,hi,h⟩; exact ⟨stem i,⟨i,by omega,rfl⟩,(pos i).mpr h⟩
  unfold evenFoot
  rw [append_union,shift_union]
  change _ ∪ (shift (pieceUnion rows) _ ∪ middle v plus long) = _
  rw [rr,←Finset.union_assoc,front]

private theorem feet (v : Word) (long : Bool) :
    evenChild (fun u p _ => evenFoot u p) v long =
      (shift (evenTile v) (full v true long) ∪ shift (evenTile v) (full v false long)) ∪
      ((shift (stemE (pre v)) (start v true long) ∪ shift (evenFoot v true) (evenOff v true long)) ∪
       (shift (stemE (pre v)) (start v false long) ∪ shift (evenFoot v false) (evenOff v false long))) := by
  let w := v++[Digit.three]
  have last : w.getLast? = some Digit.three := by simp [w]
  have drop : w.dropLast = v := by simp [w]
  have p : (regOdo cellData O E (regsAt w).1 true).dom = stemE (pre v) := stem_run v
  have q : (regOdo cellData O E (regsAt w).2 false).dom = evenTile v := by
    simp only [w,WeakStepPaper.regsAt_snoc,regStep,regOdo,E,domOdo]
  cases long <;> cases h : W1Odd w
  all_goals simp only [evenChild,tileOddPieces,tileAltEvenPieces,evenOff,full,start,←show w = v++[Digit.three] from rfl,
    last,drop,altTypeOf,altP1Coeff,reduceCtorEq,Option.bind_some,if_true,Bool.false_eq_true,if_false,decide_true,h,
    Bool.not_true,Bool.not_false,Bool.true_and,cons_union,placed,List.append_nil,p,q,domOdo,add_zero,
    show pieceUnion [] = ∅ from rfl,Finset.union_empty]
  all_goals ac_rfl

/-- The six rows of standard pieces and the joined head column, for either corrected child after a three. -/
theorem after_three (v : Word) (long : Bool) :
    let k := run v
    let m := 2*(k+1) - if long then 0 else 1
    evenChild evenLCells v long =
      ((shift (evenTile v) (full v true long) ∪ shift (evenTile v) (full v false long)) ∪
        ((shift (column (stemE (pre v)) (step v true) (k+1)) (start v true long) ∪ middle v true long) ∪
         (shift (column (stemE (pre v)) (step v false) (k+1)) (start v false long) ∪ middle v false long))) ∪
      shift (column (headE (pre v)) (vP2 (pre v)) m) ((eHead v true 0).off+evenOff v true long) := by
  dsimp only
  rw [even_child,feet,foot_row,foot_row]

end FLatticePaper.Tiles.CorrectedEvenRows
