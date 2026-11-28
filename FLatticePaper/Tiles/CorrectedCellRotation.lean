import FLatticePaper.Tiles.CorrectedAlternateRotation

/-! Exact point-set rotation of the printed parent tiles and of placed piece unions. -/

namespace FLatticePaper.Tiles.CorrectedCellRotation

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open JointFamily LCorrecProps

/-- The whole tile in the swapped coordinates at its prescribed rotation offset. -/
def CellsRot (A B : Tile) (c : Site) := ∀ z, z∈B ↔ mulI z+c∈A

private theorem mem_turn (t : Tile) (z : Site) : mulI z∈rot t ↔ z∈t := by
  rw [mem_rot]; simp [mulI]

private theorem of_rot {A B : Tile} {c : Site} (eq : rot B=shift A (-c)) : CellsRot A B c := by
  intro z
  rw [←mem_turn B z,eq,mem_shift,sub_neg_eq_add]

private theorem of_shift_rot {A B : Tile} {c : Site} (eq : shift (rot B) c=A) : CellsRot A B c := by
  intro z
  rw [←eq,mem_shift,add_sub_cancel_right,mem_turn]

theorem odd (w : Word) : CellsRot (oddTile w) (evenTile (swapW w)) (texV1Odd ((parentsAt w).current .odd)-((0,1):Site)) := by
  have eq := (rot_standard_tiles (swapW w)).2
  rw [JointRot.swapW_swapW',parentsAt_swapW,←(parentsAt_valid w).rotate_current_odd,
    Fraction.rotate_of_odd (parentsAt_valid w).current_odd_parity] at eq
  apply of_rot
  rw [eq]
  congr 1
  ext <;> dsimp [tF,tV,texV1Odd] <;> ring

theorem even (w : Word) : CellsRot (evenTile w) (oddTile (swapW w)) (texV1Even ((parentsAt w).current .even)-((0,1):Site)) := by
  let q := (parentsAt w).current .even
  have par : (q.num+q.den)%2=0 := (parentsAt_valid w).current_even_parity
  have eq := (rot_standard_tiles (swapW w)).1
  rw [JointRot.swapW_swapW',parentsAt_swapW,←(parentsAt_valid w).rotate_current_even,
    Fraction.rotate_of_even (parentsAt_valid w).current_even_parity] at eq
  apply of_rot
  rw [eq]
  congr 1
  change tV ((q.den-q.num)/2) ((q.den+q.num)/2) = -(texV1Even q-((0,1):Site))
  ext <;> dsimp [tV,texV1Even] <;> omega

private theorem alt_offset (w : Word) (odd : Bool) :
    (if odd then AltRotStep.tauE (swapW w) else AltRotStep.tauO (swapW w))=(altCf w odd).1 := by
  obtain ⟨_,_,_,_,p,q⟩ := JointRot.vecs_swapW w
  have par : ((parentsAt w).even.num+(parentsAt w).even.den)%2=0 := (parentsAt_valid w).even_parity
  have o : (phase w==1)=W1Odd w := rfl
  cases odd <;> cases hp : W1Odd w
  all_goals simp only [AltRotStep.tauE,AltRotStep.tauO,AltRotStep.tauEven,AltRotStep.tauOdd,
    phase_swapW,o,hp,Bool.false_eq_true,if_true,if_false,altCf,p,q]
  all_goals ext <;> dsimp [AltRotStep.tauShort,AltRotStep.tauLong,Parents.current,Parents.combine,
    vP1,vP2,vQ1,texV1Odd,texV1Even,texV2,mulI] <;> omega

theorem alt_odd (w : Word) : CellsRot (altOddT w) (altEvenT (swapW w)) (altCf w true).1 := by
  have h := (AltRotStep.altRot (swapW w)).2
  rw [JointRot.swapW_swapW',show AltRotStep.tauE (swapW w)=_ from alt_offset w true] at h
  exact of_shift_rot h

theorem alt_even (w : Word) : CellsRot (altEvenT w) (altOddT (swapW w)) (altCf w false).1 := by
  have h := (AltRotStep.altRot (swapW w)).1
  rw [JointRot.swapW_swapW',show AltRotStep.tauO (swapW w)=_ from alt_offset w false] at h
  exact of_shift_rot h

/-- Placing a pair of tiles at offsets with the given difference preserves the pointwise rotation identity. -/
theorem placed {p q : Piece} {c u : Site} (T : CellsRot p.odo.dom q.odo.dom u)
    (off : mulI q.off=p.off+u-c) : CellsRot p.placed q.placed c := by
  intro z
  rw [JointRot.mem_placed,JointRot.mem_placed,T]
  have add : mulI (z-q.off)=mulI z-mulI q.off := by
    ext <;> dsimp [mulI]
    all_goals ring
  have eq : mulI (z-q.off)+u=mulI z+c-p.off := by rw [add,off]; abel
  rw [eq]

/-- All sites of both unions are transported when the pieces pair in their listed order. -/
theorem union {ps qs : List Piece} {c : Site}
    (matchPieces : List.Forall₂ (fun p q : Piece => CellsRot p.placed q.placed c) ps qs) :
    CellsRot (pieceUnion ps) (pieceUnion qs) c := by
  induction matchPieces with
  | nil => intro z; simp [pieceUnion]
  | cons h _ ih =>
    intro z; simp only [pieceUnion,List.foldr_cons,Finset.mem_union]
    exact or_congr (h z) (ih z)

end FLatticePaper.Tiles.CorrectedCellRotation
