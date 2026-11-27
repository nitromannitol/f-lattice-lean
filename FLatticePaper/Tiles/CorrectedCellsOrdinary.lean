import FLatticePaper.Tiles.LCorrecProps
import FLatticePaper.Tiles.WeakStepPaper
import FLatticePaper.Tiles.AltRotStep

/-! The four domain identities at children whose decomposition uses full copies of both
parents. These are the uncorrected branches of `LCorrecProps.CorrectedCells`. -/

namespace FLatticePaper.Tiles.CorrectedCellsOrdinary

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SurgicalWeak FLatticePaper.Tiles.SurgicalDict
open FLatticePaper.Tiles.SurgicalAlt FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.LCorrecProps
open FLatticePaper.Tiles.PaperAltBase (paperAltBaseTiles)

private abbrev oddO (w : Word) := domOdo (oddTile w)
private abbrev evenO (w : Word) := domOdo (evenTile w)
private abbrev altO (w : Word) := domOdo (altOddT w)
private abbrev altE (w : Word) := domOdo (altEvenT w)

private theorem standard_regs (w : Word) :
    (regOdo cellData oddO evenO (regsAt w).1 true).dom = (stateAt w).tOdd ∧
      (regOdo cellData oddO evenO (regsAt w).2 false).dom = (stateAt w).tEven := by
  obtain ⟨hs, h0, ht, h1⟩ := WeakStepPaper.regsAt_tiles w
  constructor
  · cases h : (regsAt w).1 with
    | none => exact (h0 h).symm
    | some u => exact (hs u h).symm
  · cases h : (regsAt w).2 with
    | none => exact (h1 h).symm
    | some u => exact (ht u h).symm

private theorem alternate_regs (w : Word) :
    (regOdo cellData altO altE (regsAt w).1 true).dom = (SurgicalAltTiles.altRegs paperAltBaseTiles w).1 ∧
      (regOdo cellData altO altE (regsAt w).2 false).dom = (SurgicalAltTiles.altRegs paperAltBaseTiles w).2 := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton v d ih =>
    rw [WeakStepPaper.regsAt_snoc, AltRotStep.altRegs_snoc]
    cases d
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, ih.2⟩
    · exact ⟨ih.1, rfl⟩

private theorem placed_std (o : PartialOdometer) (v a : Site) :
    (stdPiece o v a).placed = shift o.dom v := rfl

private theorem shift_origin (T : Tile) : shift T 0 = T := by
  ext x
  simp [mem_shift]

private theorem piece_cons (p : Piece) (ps : List Piece) :
    pieceUnion (p :: ps) = p.placed ∪ pieceUnion ps := rfl

private theorem shift_double (T : Tile) (s v : Site) :
    shift (doubled T s) v = shift T v ∪ shift T (v + s) := by
  rw [doubled, shift_union, shift_shift, add_comm s v]

/-- The odd standard domain clause at every non-base word ending in one or two. -/
theorem odd_domain (w : Word) (hw : ¬ IsBase w) (hc : w.getLast? ≠ some .three) :
    pieceUnion (tileOddPieces cellData oddO evenO (fun u s e => domOdo (evenLCells u s e)) w) = oddTile w := by
  have hT : oddTile w = oddChildB (W1Odd w) (stateAt w).tOdd (stateAt w).tEven
      (parentsAt w).odd (parentsAt w).even := by
    unfold oddTile
    rw [SiteInduction.childTiles_nonbase w hw, stateAt_par]
    rfl
  rw [hT]
  cases ho : W1Odd w <;>
    simp [tileOddPieces, hc, ho, p0Off, offsetP0, vP1, vP2, vQ1, vQ2, oddChildB,
      piece_cons, show pieceUnion [] = ∅ from rfl, placed_std, (standard_regs w).1,
      (standard_regs w).2, shift_origin, Finset.union_comm, Finset.union_left_comm, Finset.union_assoc]

/-- The even standard domain clause at every non-base word ending in one or three. -/
theorem even_domain (w : Word) (hw : ¬ IsBase w) (hc : w.getLast? ≠ some .two) :
    pieceUnion (tileEvenPieces cellData oddO evenO (fun u s e => domOdo (oddLCells u s e)) w) = evenTile w := by
  have hT : evenTile w = evenChildB (W1Odd w) (stateAt w).tOdd (stateAt w).tEven
      (parentsAt w).odd (parentsAt w).even := by
    unfold evenTile
    rw [SiteInduction.childTiles_nonbase w hw, stateAt_par]
    rfl
  rw [hT]
  cases ho : W1Odd w <;>
    simp [tileEvenPieces, hc, ho, q0Off, offsetQ0, vP1, vP2, vQ1, vQ2, evenChildB,
      piece_cons, show pieceUnion [] = ∅ from rfl, placed_std, (standard_regs w).1,
      (standard_regs w).2, shift_origin, add_assoc, Finset.union_comm, Finset.union_left_comm]

/-- The odd alternate domain clause when the doubled odd parent is uncorrected. -/
theorem alt_odd_domain (w : Word) (hw : ¬ IsBase w) (hc : w.getLast? ≠ some .two) :
    pieceUnion (tileAltOddPieces cellData oddO evenO altO altE
      (fun u s e => domOdo (oddLCells u s e)) w) = altOddT w := by
  unfold altOddT
  rw [AltRotStep.altOddTile_of_not_base _ hw]
  simp only [tileAltOddPieces, hc, decide_false, Bool.false_eq_true, if_false, List.cons_append,
    List.nil_append, piece_cons, placed_std, (standard_regs w).1, (standard_regs w).2]
  simp only [SurgicalAltTiles.altOddPieces, shift_double, W1Odd, altOff, vP1, vP2, vQ1, vQ2]
  cases h : altTypeOf w with
  | none =>
    simp only [Option.bind_none, show pieceUnion [] = ∅ from rfl, Finset.union_empty]
    ac_rfl
  | some t =>
    simp only [Option.bind_some]
    cases hk : altQ1Coeff (phase w == 1) t <;>
      simp only [piece_cons, placed_std, show pieceUnion [] = ∅ from rfl, Finset.union_empty, (alternate_regs w).2] <;>
      ac_rfl

/-- The even alternate domain clause when the doubled even parent is uncorrected. -/
theorem alt_even_domain (w : Word) (hw : ¬ IsBase w) (hc : w.getLast? ≠ some .three) :
    pieceUnion (tileAltEvenPieces cellData oddO evenO altO altE
      (fun u s e => domOdo (evenLCells u s e)) w) = altEvenT w := by
  unfold altEvenT
  rw [AltRotStep.altEvenTile_of_not_base _ hw]
  simp only [tileAltEvenPieces, hc, decide_false, Bool.false_eq_true, if_false, List.cons_append,
    List.nil_append, piece_cons, placed_std, (standard_regs w).1, (standard_regs w).2]
  simp only [SurgicalAltTiles.altEvenPieces, shift_double, W1Odd, altOff, vP1, vP2, vQ1, vQ2]
  cases h : altTypeOf w with
  | none =>
    simp only [Option.bind_none, show pieceUnion [] = ∅ from rfl, Finset.union_empty]
    ac_rfl
  | some t =>
    simp only [Option.bind_some]
    cases hk : altP1Coeff (phase w == 1) t <;>
      simp only [piece_cons, placed_std, show pieceUnion [] = ∅ from rfl, Finset.union_empty, (alternate_regs w).1] <;>
      ac_rfl

end FLatticePaper.Tiles.CorrectedCellsOrdinary
