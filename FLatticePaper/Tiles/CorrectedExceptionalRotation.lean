import FLatticePaper.Tiles.CorrectedExceptionalPlacement

/-! Rotation of the two corrected columns with the enlarged bridge at a positive pure-two exit. -/

namespace FLatticePaper.Tiles.CorrectedExceptionalRotation

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily LCorrecProps SurgicalWeak JointRot CorrectedEvenPlacement
open CorrectedCellRotation CorrectedExceptionalBridge CorrectedExceptionalPlacement

private theorem split_union (a m h : List Piece) :
    pieceUnion (a++m++h)=pieceUnion (a++h) ∪ pieceUnion m := by
  ext x
  simp only [Finset.mem_union,JointGlue.mem_pieceUnion,List.mem_append]
  aesop

private theorem bridge_rotation (w : Word) (j : ℕ) (plus : Bool)
    (hp : stemPrefix w=List.replicate (j+1) .two) :
    CellsRot (shift (rotated plus) (base w plus))
      (oBridge cellData O E (swapW w) (plus != W1Odd w)).placed
      (texV1Even ((parentsAt w).current .even)-((0,1):Site)) := by
  let q := oBridge cellData O E (swapW w) (plus != W1Odd w)
  let c := texV1Even ((parentsAt w).current .even)-((0,1):Site)
  obtain ⟨sp,-⟩ := swapW_strip_three w
  have raw : stripTrailing .three w=List.replicate (j+1) .two := hp
  have reg : (regsAt (stripTrailing .two (swapW w))).1=none := by
    rw [sp,regsAt_swapW,raw,registers]; rfl
  have b : q.odo.dom=zeroTile := by simp [q,oBridge,stdPiece,reg,regOdo,cellData,domOdo]
  have off : mulI q.off+c=(if plus then ((2,0):Site) else (2,1))+base w plus :=
    rotated_offset w j plus hp
  intro z
  change z∈q.placed ↔ mulI z+c∈_
  rw [mem_placed,b,rotated,shift_shift,←off,mem_shift,mem_rot]
  have v : mulI z+c-(mulI q.off+c)=mulI (z-q.off) := by ext <;> dsimp [mulI] <;> ring
  rw [v]
  simp [mulI]
  rfl

private theorem incident_subset (w : Word) (j : ℕ) (plus long : Bool)
    (hp : stemPrefix w=List.replicate (j+1) .two) :
    shift (stem (2*(j:ℤ)+3) plus ∪ CorrectedExceptionalBridge.head (2*(j:ℤ)+3) plus) (base w plus) ⊆
      pieceUnion (CorrectedOuterRotation.outer w plus long) := by
  obtain ⟨S,H⟩ := incident w j plus hp
  rw [shift_union,←S,←H]
  intro z hz
  apply JointGlue.mem_pieceUnion.mpr
  rcases Finset.mem_union.mp hz with s|h
  · refine ⟨_,List.mem_append_left _ (List.mem_map.mpr ⟨_,List.mem_range.mpr (Nat.lt_succ_self _),rfl⟩),s⟩
  · have pos : 0<2*(trailingCount .three w+1)-(if long then 0 else 1) := by cases long <;> simp; omega
    refine ⟨_,List.mem_append_right _ (List.mem_map.mpr ⟨0,List.mem_range.mpr pos,rfl⟩),h⟩

/-- The entire L-correction rotates, including both shifted small bridges and the incident end tiles. -/
theorem cells (w : Word) (j : ℕ) (plus long : Bool) (hp : stemPrefix w=List.replicate (j+1) .two) :
    CellsRot (evenLCells w plus long) (oddLCells (swapW w) (plus != W1Odd w) long)
      (texV1Even ((parentsAt w).current .even)-((0,1):Site)) := by
  let d := 2*(j:ℤ)+3
  let rim := pieceUnion (CorrectedOuterRotation.outer w plus long)
  let b := base w plus
  have pre : stemPrefix w=List.replicate j .two++[CorrectedPlacementFrames.exit false] := by
    rw [hp,List.replicate_succ']; rfl
  have R := CorrectedOuterRotation.at_exit w (List.replicate j .two) false plus long pre
  have B := bridge_rotation w j plus hp
  have inc := incident_subset w j plus long hp
  have same := congrArg (fun T => shift T b) (union_eq d (by dsimp [d]; omega) plus)
  simp only [shift_union] at same
  have whole : rim ∪ shift (middle plus) b = rim ∪ shift (rotated plus) b := by
    have sub : shift (stem d plus) b ∪ shift (CorrectedExceptionalBridge.head d plus) b ⊆ rim := by
      rw [←shift_union]; exact inc
    have eq : rim ∪ (shift (stem d plus) b ∪ shift (CorrectedExceptionalBridge.head d plus) b)=rim :=
      Finset.union_eq_left.mpr sub
    calc
      _ = (rim ∪ (shift (stem d plus) b ∪ shift (CorrectedExceptionalBridge.head d plus) b)) ∪ shift (middle plus) b := by rw [eq]
      _ = (rim ∪ (shift (stem d plus) b ∪ shift (CorrectedExceptionalBridge.head d plus) b)) ∪ shift (rotated plus) b := by
        rw [Finset.union_assoc,same,←Finset.union_assoc]
      _ = _ := by rw [eq]
  unfold evenLCells oddLCells
  rw [evenLPieces_split,oddLPieces_split,split_union,split_union,middle_placed w j plus hp]
  intro z
  change z∈pieceUnion (CorrectedOuterRotation.swapped (swapW w) (plus != W1Odd w) long) ∪
      pieceUnion [oBridge cellData O E (swapW w) (plus != W1Odd w)] ↔ _∈rim ∪ shift (middle plus) b
  rw [whole]
  simp only [Finset.mem_union,pieceUnion,List.foldr_cons,List.foldr_nil,Finset.union_empty]
  exact or_congr (R z) (B z)

end FLatticePaper.Tiles.CorrectedExceptionalRotation
