import FLatticePaper.Tiles.CorrectedHeadColumn

/-! The standard and alternate corrected child lists as a single column of alternate parents
together with their full standard entries, stems, and bridges. -/

namespace FLatticePaper.Tiles.CorrectedChildColumns

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily LCorrecProps LCorrecRecursion SurgicalWeak SurgicalAlt SurgicalDict
open CorrectedHeadColumn CorrectedColumnRuns

private abbrev O (w : Word) := domOdo (oddTile w)
private abbrev E (w : Word) := domOdo (evenTile w)
private abbrev AO (w : Word) := domOdo (altOddT w)
private abbrev AE (w : Word) := domOdo (altEvenT w)

private theorem append_union (p q : List Piece) : pieceUnion (p++q) = pieceUnion p ∪ pieceUnion q := by
  ext z
  simp only [JointGlue.mem_pieceUnion,List.mem_append,Finset.mem_union]
  aesop

private theorem cons_union (p : Piece) (ps : List Piece) : pieceUnion (p::ps) = p.placed ∪ pieceUnion ps := rfl

private theorem placed (o : PartialOdometer) (v a : Site) : (stdPiece o v a).placed = shift o.dom v := rfl

private theorem regroup (t a b c d : Tile) :
    t ∪ ((a ∪ b) ∪ (c ∪ d)) = (t ∪ (a ∪ c)) ∪ (b ∪ d) := by ac_rfl

private abbrev count (k : ℕ) (long : Bool) := 2*(k+1) - if long then 0 else 1

/-- All stems and the complete bridge of the even L, at their original placements. -/
def evenFoot (v : Word) (plus : Bool) : Tile :=
  pieceUnion ((List.range (trailingCount .three v+1)).map (JointRot.eStem cellData O E v plus) ++ JointRot.eMid cellData O E v plus)

private abbrev eHead := JointRot.eHead cellData O E AO AE
private abbrev eHeads (v : Word) (plus long : Bool) :=
  pieceUnion ((List.range (count (trailingCount .three v) long)).map (eHead v plus))

private theorem e_split (v : Word) (plus long : Bool) :
    evenLCells v plus long = evenFoot v plus ∪ eHeads v plus long := by
  rw [evenLCells,JointRot.evenLPieces_split,append_union]
  rfl

/-- The corrected child with any prescribed family of even L domains in the two indicated entries. -/
def evenChild (F : Word → Bool → Bool → Tile) (v : Word) (long : Bool) : Tile :=
  let w := v++[Digit.three]
  let G := fun u p l => domOdo (F u p l)
  if long then pieceUnion (tileAltEvenPieces cellData O E AO AE G w)
  else pieceUnion (tileOddPieces cellData O E G w)

private theorem e_slots (F : Word → Bool → Bool → Tile) (v : Word) (long : Bool) :
    evenChild F v long = evenChild (fun _ _ _ => ∅) v long ∪
      (shift (F v true long) (evenOff v true long) ∪ shift (F v false long) (evenOff v false long)) := by
  let w := v++[Digit.three]
  have last : w.getLast? = some Digit.three := by simp [w]
  have drop : w.dropLast = v := by simp [w]
  cases long <;> cases h : W1Odd w
  all_goals simp only [evenChild,evenOff,tileOddPieces,tileAltEvenPieces,
    ←show w = v++[Digit.three] from rfl,h,last,drop,decide_true,if_true,Bool.false_eq_true,if_false,
    Bool.not_true,Bool.not_false,Bool.true_and,List.cons_append,List.nil_append,cons_union,placed,domOdo,
    show pieceUnion [] = ∅ from rfl,AltRotStep.shift_empty,Finset.union_empty,Finset.empty_union,add_zero]
  all_goals ac_rfl

/-- Combining the actual even L slots leaves one complete alternate-parent column at its positive initial
head. The other entries of the child and both feet retain their placements. -/
theorem even_child (v : Word) (long : Bool) :
    let pre := stripTrailing Digit.three v
    let m := count (trailingCount .three v) long
    evenChild evenLCells v long = evenChild (fun u p _ => evenFoot u p) v long ∪
      shift (column (headE pre) (vP2 pre) m) ((eHead v true 0).off+evenOff v true long) := by
  dsimp only
  rw [e_slots evenLCells,e_slots (fun u p _ => evenFoot u p),←even_heads,
    e_split,e_split,shift_union,shift_union]
  exact regroup _ _ _ _ _

/-- All stems and the complete bridge of the odd L, at their original placements. -/
def oddFoot (v : Word) (plus : Bool) : Tile :=
  pieceUnion ((List.range (trailingCount .two v+1)).map (JointRot.oStem cellData O E v plus) ++ [JointRot.oBridge cellData O E v plus])

private abbrev oHead := JointRot.oHead cellData O E AO AE
private abbrev oHeads (v : Word) (plus long : Bool) :=
  pieceUnion ((List.range (count (trailingCount .two v) long)).map (oHead v plus))

private theorem o_split (v : Word) (plus long : Bool) :
    oddLCells v plus long = oddFoot v plus ∪ oHeads v plus long := by
  rw [oddLCells,JointRot.oddLPieces_split,append_union]
  rfl

/-- The corrected child with any prescribed family of odd L domains in the two indicated entries. -/
def oddChild (F : Word → Bool → Bool → Tile) (v : Word) (long : Bool) : Tile :=
  let w := v++[Digit.two]
  let G := fun u p l => domOdo (F u p l)
  if long then pieceUnion (tileAltOddPieces cellData O E AO AE G w)
  else pieceUnion (tileEvenPieces cellData O E G w)

private theorem o_slots (F : Word → Bool → Bool → Tile) (v : Word) (long : Bool) :
    oddChild F v long = oddChild (fun _ _ _ => ∅) v long ∪
      (shift (F v true long) (oddOff v true long) ∪ shift (F v false long) (oddOff v false long)) := by
  let w := v++[Digit.two]
  have last : w.getLast? = some Digit.two := by simp [w]
  have drop : w.dropLast = v := by simp [w]
  cases long <;> cases h : W1Odd w
  all_goals simp only [oddChild,oddOff,tileEvenPieces,tileAltOddPieces,
    ←show w = v++[Digit.two] from rfl,h,last,drop,decide_true,if_true,Bool.false_eq_true,if_false,
    List.cons_append,List.nil_append,cons_union,placed,domOdo,
    show pieceUnion [] = ∅ from rfl,AltRotStep.shift_empty,Finset.union_empty,Finset.empty_union]
  all_goals ac_rfl

/-- Combining the actual odd L slots leaves one complete alternate-parent column at its positive initial
head. The other entries of the child and both feet retain their placements. -/
theorem odd_child (v : Word) (long : Bool) :
    let pre := stripTrailing Digit.two v
    let m := count (trailingCount .two v) long
    oddChild oddLCells v long = oddChild (fun u p _ => oddFoot u p) v long ∪
      shift (column (headO pre) ((if W1Odd v then -vQ1 pre else vQ1 pre)) m) ((oHead v true 0).off+oddOff v true long) := by
  dsimp only
  rw [o_slots oddLCells,o_slots (fun u p _ => oddFoot u p),←odd_heads,
    o_split,o_split,shift_union,shift_union]
  exact regroup _ _ _ _ _

end FLatticePaper.Tiles.CorrectedChildColumns
