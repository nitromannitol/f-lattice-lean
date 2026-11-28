import FLatticePaper.Tiles.CorrectedEvenRows

/-! The placed pieces after a run of threes in one common physical coordinate frame. -/

namespace FLatticePaper.Tiles.CorrectedEvenPlacement

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily LCorrecProps LCorrecRecursion SurgicalWeak SurgicalAlt SurgicalDict
open CorrectedColumnRuns CorrectedHeadColumn CorrectedChildColumns CorrectedEvenRows

abbrev stemPrefix (v : Word) := stripTrailing Digit.three v
abbrev length (v : Word) := trailingCount Digit.three v+1

/-- Old period vectors and the displacement of the doubled register after the run. -/
structure Periods where
  a : Site
  b : Site
  u : Site
  v : Site
  runA : Site
  fullU : Site
  fullV : Site

def periods (v : Word) : Periods :=
  let p := stemPrefix v
  let k : ℤ := length v
  let A := vP1 p
  let B := vP2 p
  ⟨A,B,vQ1 p,vQ2 p,k • A,vQ1 p+k • A,vQ2 p+(2*k) • B⟩

def Periods.origin (g : Periods) (odd long : Bool) : Site :=
  if odd then -g.runA else if long then 0 else -g.fullU

def Periods.center (g : Periods) (odd long : Bool) : Site :=
  g.a+g.b+g.fullV+(if odd then g.u+g.u else 0)+(if long then g.b else 0)

def Periods.full (g : Periods) (odd plus long : Bool) : Site :=
  if plus then (if odd then g.a+g.u else -g.fullU)+(if long then g.b else 0)
  else if odd then g.b-g.runA else g.a+g.b

def Periods.row (g : Periods) (odd plus long : Bool) : Site :=
  let c := if odd then -g.runA else g.u
  if plus then c else g.center odd long-g.a-g.b-c-g.runA

def Periods.bridge (g : Periods) (odd plus long : Bool) : Site :=
  let c := if odd then g.a else 0
  if plus then c else g.center odd long-g.u-g.v-c

def Periods.head (g : Periods) (odd two : Bool) : Site :=
  if odd then (if two then g.u+g.u+g.v else g.b+g.u)
  else if two then g.v else g.a+g.b-g.u

private abbrev O (w : Word) := domOdo (oddTile w)
private abbrev E (w : Word) := domOdo (evenTile w)
private abbrev AO (w : Word) := domOdo (altOddT w)
private abbrev AE (w : Word) := domOdo (altEvenT w)
private abbrev head := JointRot.eHead cellData O E AO AE

/-- Position of the bridge in the child before the common translation. -/
def bridgeOffset (v : Word) (plus long : Bool) : Site :=
  let k : ℤ := trailingCount .three v
  let K := JointRot.eK v plus
  evenLInitOff v plus+altOff (stemPrefix v) (k • K.1+K.2.1)+evenOff v plus long

private theorem before (v : Word) :
    let p := stemPrefix v
    let k : ℤ := trailingCount .three v
    vP1 v=vP1 p ∧ vP2 v=vP2 p ∧ vQ1 v=vQ1 p+k • vP1 p ∧ vQ2 v=vQ2 p+(2*k) • vP2 p := by
  have h : stemPrefix v++List.replicate (trailingCount .three v) .three=v := JointRot.strip_append_replicate _ _
  have q := three_periods (stemPrefix v) (trailingCount .three v)
  dsimp only at q
  rw [h] at q
  exact q

private theorem after_run (v : Word) :
    let w := v++[Digit.three]
    let p := stemPrefix v
    let k : ℤ := length v
    vP1 w=vP1 p ∧ vP2 w=vP2 p ∧ vQ1 w=vQ1 p+k • vP1 p ∧ vQ2 w=vQ2 p+(2*k) • vP2 p := by
  have h : stemPrefix v++List.replicate (trailingCount .three v) .three=v := JointRot.strip_append_replicate _ _
  have h' : stemPrefix v++List.replicate (length v) .three=v++[.three] := by
    rw [length,List.replicate_succ',←List.append_assoc,h]
  exact h' ▸ three_periods (stemPrefix v) (length v)

local macro "calculate_offsets " v:ident plus:ident long:ident : tactic =>
  `(tactic| (
    obtain ⟨a,b,c,d⟩ := before $v
    obtain ⟨a',b',c',d'⟩ := after_run $v
    have phase : W1Odd ($v++[Digit.three]) = W1Odd $v := JointRot.phase_snoc_three $v
    cases sign : W1Odd $v <;> cases ($plus) <;> cases ($long)
    all_goals apply Prod.ext
    all_goals simp [Periods.origin,Periods.center,Periods.full,Periods.row,Periods.bridge,periods,
      CorrectedEvenRows.full,CorrectedEvenRows.start,CorrectedEvenRows.step,bridgeOffset,
      JointRot.eK,evenKCoeff,evenLInitOff,evenOff,phase,sign,altQ0Coeff,altShifts,p0Off,q0Off,
      offsetP0,offsetQ0,altOff_add,altOff_smul,altOff,coeffOff,b,c,d,a',b',c',d',length,stemPrefix]
    all_goals ring))

/-- The two full copies at their common offsets. -/
theorem full_offset (v : Word) (plus long : Bool) :
    CorrectedEvenRows.full v plus long+(periods v).origin (W1Odd v) long =
      (periods v).full (W1Odd v) plus long := by calculate_offsets v plus long

private def backwards (v : Word) (plus : Bool) : Bool := W1Odd v != plus

theorem step_offset (v : Word) (plus : Bool) :
    step v plus = (if backwards v plus then -(periods v).a else (periods v).a) := by
  cases h : W1Odd v <;> cases plus <;> ext <;> simp [step,backwards,periods,JointRot.eK,evenKCoeff,h,altOff,coeffOff]

/-- The first offset of each completed row when both are read in the positive horizontal direction. -/
theorem row_offset (v : Word) (plus long : Bool) :
    start v plus long+(periods v).origin (W1Odd v) long+
      (if backwards v plus then -(periods v).runA else 0) = (periods v).row (W1Odd v) plus long := by
  unfold backwards
  calculate_offsets v plus long

/-- The bridge and its opposite in the same frame as the two full copies. -/
theorem bridge_offset (v : Word) (plus long : Bool) :
    bridgeOffset v plus long+(periods v).origin (W1Odd v) long =
      (periods v).bridge (W1Odd v) plus long := by calculate_offsets v plus long

/-- The positive initial head of the joined column. Its offset is independent of elongation. -/
theorem head_offset (v : Word) (long : Bool) :
    (head v true 0).off+evenOff v true long+(periods v).origin (W1Odd v) long =
      (periods v).head (W1Odd v) (decide ((stemPrefix v).getLast?=some Digit.two)) := by
  obtain ⟨_,_,c,_⟩ := before v
  obtain ⟨a',b',c',d'⟩ := after_run v
  have phase : W1Odd (v++[Digit.three])=W1Odd v := JointRot.phase_snoc_three v
  cases sign : W1Odd v <;> cases long <;> cases two : decide ((stemPrefix v).getLast?=some Digit.two)
  all_goals apply Prod.ext
  all_goals simp [head,JointRot.eHead,Periods.head,Periods.origin,periods,JointRot.eK,evenKCoeff,evenOff,
    evenLInitOff,phase,sign,two,altQ0Coeff,p0Off,q0Off,offsetP0,offsetQ0,
    altOff,coeffOff,c,a',b',c',d',length,stemPrefix]
  all_goals ring

/-- Reading a consecutive column in the positive direction from its far endpoint. -/
theorem reverse_column (T : Tile) (a c : Site) (N : ℕ) :
    shift (column T (-a) N) c = shift (column T a N) (c-(N : ℤ) • a) := by
  ext z
  simp only [mem_shift,mem_column]
  constructor <;> rintro ⟨j,hj,h⟩ <;> refine ⟨N-j,by omega,?_⟩
  all_goals
    convert h using 1
    apply Prod.ext <;> simp [Nat.cast_sub hj,sub_mul] <;> ring

private theorem row_placed (v : Word) (plus long : Bool) :
    let g := periods v
    let o := W1Odd v
    shift (shift (column (stemE (stemPrefix v)) (step v plus) (length v)) (start v plus long)) (g.origin o long) =
      shift (column (stemE (stemPrefix v)) g.a (length v)) (g.row o plus long) := by
  dsimp only
  rw [shift_shift,step_offset]
  have h := row_offset v plus long
  cases e : backwards v plus
  · simpa only [e,Bool.false_eq_true,if_false,add_zero] using congrArg (shift (column (stemE (stemPrefix v)) (periods v).a (length v))) h
  · simp only [e,if_true] at h ⊢
    rw [reverse_column]
    change start v plus long+(periods v).origin (W1Odd v) long+-((length v : ℤ) • (periods v).a)=_ at h
    exact congrArg (shift _) (by simpa only [sub_eq_add_neg] using h)

/-- The enlarged one-tile contributes precisely at a nonempty all-two prefix. -/
def enlarged (v : Word) : Bool :=
  !(stemPrefix v).isEmpty && (stemPrefix v).all (fun d => decide (d=Digit.two))

/-- The bridge and the possible enlarged one-tile in the common frame. -/
def bridgePieces (v : Word) (plus long : Bool) : Tile :=
  let o := W1Odd v
  let b := (periods v).bridge o plus long
  (if enlarged v && (!o && !plus) then ∅ else shift (bridgeE (stemPrefix v)) b) ∪
  (if enlarged v then shift enlOdo.dom (b+((1,1):Site)) else ∅)

private theorem middle_placed (v : Word) (plus long : Bool) :
    shift (middle v plus long) ((periods v).origin (W1Odd v) long) = bridgePieces v plus long := by
  have eq := bridge_offset v plus long
  simp only [bridgePieces]
  rw [←eq]
  unfold middle JointRot.eMid
  change shift (shift (pieceUnion ((if enlarged v && (!W1Odd v && !plus) then [] else [_]) ++
    (if enlarged v then [_] else []))) _) _ = _
  cases d : enlarged v <;> cases c : (!W1Odd v && !plus)
  all_goals simp only [Bool.false_and,Bool.true_and,Bool.false_eq_true,if_false,if_true,
    List.nil_append,List.append_nil,List.cons_append,pieceUnion,List.foldr_nil,List.foldr_cons,
    Finset.union_empty,Finset.empty_union,shift_union,shift_shift]
  all_goals simp only [Piece.placed,stdPiece,show ∀ (t : Tile) (x : Site), t.image (·+x)=shift t x from fun _ _ => rfl,
    shift_shift,bridgeOffset,stemPrefix]
  all_goals first
    | rfl
    | congr 1 <;> abel
  all_goals rfl

/-- The two full tiles, both positively read stem rows, the two bridges and the
entire head column with the offsets of the common physical diagram. -/
theorem after_three (v : Word) (long : Bool) :
    let g := periods v
    let o := W1Odd v
    let pre := stemPrefix v
    let m := 2*length v-if long then 0 else 1
    shift (evenChild evenLCells v long) (g.origin o long) =
      ((shift (evenTile v) (g.full o true long) ∪ shift (evenTile v) (g.full o false long)) ∪
        ((shift (column (stemE pre) g.a (length v)) (g.row o true long) ∪ bridgePieces v true long) ∪
         (shift (column (stemE pre) g.a (length v)) (g.row o false long) ∪ bridgePieces v false long))) ∪
      shift (column (headE pre) g.b m) (g.head o (decide (pre.getLast?=some Digit.two))) := by
  dsimp only
  rw [CorrectedEvenRows.after_three]
  simp only [shift_union]
  rw [row_placed v true long,row_placed v false long,middle_placed v true long,middle_placed v false long]
  simp only [shift_shift,full_offset,head_offset]
  rfl

end FLatticePaper.Tiles.CorrectedEvenPlacement
