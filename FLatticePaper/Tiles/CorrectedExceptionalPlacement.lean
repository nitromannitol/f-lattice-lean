import FLatticePaper.Tiles.CorrectedExceptionalBridge
import FLatticePaper.Tiles.CorrectedOuterRotation

/-! Placement of the last stem, first head, and both bridges when the stripped prefix consists of twos. -/

namespace FLatticePaper.Tiles.CorrectedExceptionalPlacement

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily LCorrecProps SurgicalWeak SurgicalAlt SurgicalAltTiles SurgicalDict JointRot
open CorrectedEvenPlacement LCorrecRecursion CorrectedExceptionalBridge

abbrev O (w : Word) := domOdo (oddTile w)
abbrev E (w : Word) := domOdo (evenTile w)
abbrev AO (w : Word) := domOdo (altOddT w)
abbrev AE (w : Word) := domOdo (altEvenT w)

def base (w : Word) (plus : Bool) : Site :=
  evenLInitOff w plus+altOff (stemPrefix w) ((trailingCount .three w:ℤ) • (eK w plus).1+(eK w plus).2.1)

theorem phase (w : Word) (j : ℕ) (hp : stemPrefix w=List.replicate (j+1) .two) : W1Odd w=false := calc
  _ = W1Odd (stemPrefix w++List.replicate (trailingCount .three w) .three) :=
    congrArg W1Odd (strip_append_replicate .three w).symm
  _ = W1Odd (stemPrefix w) := W1Odd_append_replicate _ _ _ (by decide)
  _ = false := by rw [hp,W1Odd,AltRotStep.phase_replicate_two]; rfl

theorem registers (j : ℕ) :
    regsAt (List.replicate (j+1) .two)=(some (List.replicate j .two),none) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ',WeakStepPaper.regsAt_snoc,ih]; rfl

private theorem first_parent (j : ℕ) :
    altOddT (List.replicate j .two)=shift (PaperAltBase.nearStairAltF (2*(j:ℤ)+3)) (0,-1) := by
  change SurgicalAltTiles.altOddTile AltRotStep.B _=_
  rw [AltRotStep.altOddTile_of_base AltRotStep.B (AltRotStep.isBase_replicate_two j)]
  cases j with
  | zero => rw [List.replicate_zero,AltRotStep.B_nil]; rfl
  | succ j => rw [AltRotStep.B_two _ (Nat.succ_pos _) ]

theorem incident (w : Word) (j : ℕ) (plus : Bool) (hp : stemPrefix w=List.replicate (j+1) .two) :
    let k := trailingCount .three w
    let d := 2*(j:ℤ)+3
    (eStem cellData O E w plus k).placed=shift (stem d plus) (base w plus) ∧
    (eHead cellData O E AO AE w plus 0).placed=shift (CorrectedExceptionalBridge.head d plus) (base w plus) := by
  intro k d
  have ph := phase w j hp
  have raw : stripTrailing .three w=List.replicate (j+1) .two := hp
  have last : (stripTrailing .three w).getLast?=some .two := by rw [raw,List.replicate_succ']; simp
  have s : stemE (stemPrefix w)=nstairN d := by
    rw [hp]; simp only [stemE,registers,regOdo,domOdo]; exact SiteBase.oddTile_rep_two _
  have h : headE (stemPrefix w)=shift (PaperAltBase.nearStairAltF d) (0,-1) := by
    rw [hp]; simp only [headE,registers,regOdo,domOdo]; exact first_parent _
  have so : (eStem cellData O E w plus k).off=stemOffset d plus+base w plus := by
    unfold eStem stdPiece base
    rw [altOff_add]
    cases plus <;> ext <;> simp [eK,ph,evenKCoeff,stemOffset,altOff,coeffOff,vP1,vP2,vQ1,vQ2,hp,
      BaseTileProps.parents_two,texV1Odd,texV1Even,texV2,k,d] <;> ring
  have ho : (eHead cellData O E AO AE w plus 0).off=headOffset d plus+base w plus := by
    unfold eHead base
    simp only [altOff_add,Int.natCast_zero,zero_add,one_smul,eK,ph,last,decide_true]
    cases plus <;> ext <;> simp [evenKCoeff,headOffset,altOff,coeffOff,vP1,vP2,vQ1,vQ2,hp,
      BaseTileProps.parents_two,texV1Odd,texV1Even,texV2,d] <;> ring
  change shift (stemE (stemPrefix w)) _=_ ∧ shift (headE (stemPrefix w)) _=_
  rw [s,h,so,ho,stem,CorrectedExceptionalBridge.head]
  simp only [shift_shift,add_assoc,and_self]

theorem middle_placed (w : Word) (j : ℕ) (plus : Bool) (hp : stemPrefix w=List.replicate (j+1) .two) :
    pieceUnion (eMid cellData O E w plus)=shift (middle plus) (base w plus) := by
  have ph := phase w j hp
  have dbl : (!(stemPrefix w).isEmpty && (stemPrefix w).all (fun d => decide (d=Digit.two)))=true := by
    simp [hp,List.replicate_succ]
  have b : (regOdo cellData O E (regsAt (stemPrefix w)).2 false).dom=oneTile := by
    rw [hp]; simp [registers,regOdo,cellData,domOdo]
  have full : oneTile ∪ shift enlOdo.dom (1,1)=CorrectedPureBridges.grid := by decide
  unfold eMid
  simp only [dbl,ph,Bool.not_false,Bool.true_and]
  cases plus
  · change shift enlOdo.dom (base w false+(1,1)) ∪ ∅=_
    rw [Finset.union_empty,middle,if_neg (by decide),shift_shift,add_comm]
  · change (shift (regOdo cellData O E (regsAt (stemPrefix w)).2 false).dom (base w true) ∪
      (shift enlOdo.dom (base w true+(1,1)) ∪ ∅))=_
    rw [Finset.union_empty,b,middle,if_pos (by decide),←full,shift_union,shift_shift,add_comm]

theorem rotated_offset (w : Word) (j : ℕ) (plus : Bool) (hp : stemPrefix w=List.replicate (j+1) .two) :
    mulI (oBridge cellData O E (swapW w) (plus != W1Odd w)).off+
      (texV1Even ((parentsAt w).current .even)-((0,1):Site)) =
      (if plus then ((2,0):Site) else (2,1))+base w plus := by
  have ph := phase w j hp
  have swph := W1Odd_swapW w
  obtain ⟨sp,sk⟩ := swapW_strip_three w
  have raw : stripTrailing .three w=List.replicate (j+1) .two := hp
  have last : (stripTrailing .three w).getLast?=some .two := by rw [raw,List.replicate_succ']; simp
  have pw := parents_append_threes (stemPrefix w) (trailingCount .three w)
  rw [strip_append_replicate] at pw
  have ps := parents_append_twos (swapW (stemPrefix w)) (trailingCount .three w)
  have rep : swapW (stemPrefix w)++List.replicate (trailingCount .three w) .two=swapW w := by
    conv_rhs => rw [←strip_append_replicate .three w,swapW_append,swapW_replicate]
    rfl
  rw [rep] at ps
  unfold oBridge base
  simp only [sp,sk,swph,ph,eK,oK,last,decide_true,Bool.bne_false]
  simp only [stemPrefix,raw,swapW_replicate,Digit.swapTwoThree,BaseTileProps.parents_two,BaseTileProps.parents_three] at pw ps
  cases plus <;> ext <;> simp [oddKCoeff,evenKCoeff,oddLInitOff,
    evenLInitOff,LCorrections.oddBridgeShift,stdPiece,p0Off,q0Off,offsetP0,offsetQ0,
    altOff,coeffOff,vP1,vP2,vQ1,vQ2,ps,pw,raw,swapW_replicate,Digit.swapTwoThree,BaseTileProps.parents_two,BaseTileProps.parents_three,swph,ph,
    Parents.current,Parents.combine,texV1Even,texV1Odd,texV2,mulI] <;> ring

end FLatticePaper.Tiles.CorrectedExceptionalPlacement
