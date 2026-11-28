import FLatticePaper.Tiles.CorrectedChildRotation

/-! Transfer both corrected domain equalities to a two-ending child. -/

namespace FLatticePaper.Tiles.CorrectedSwappedDomains

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard SurgicalWeak JointFamily JointRot LCorrecProps
open CorrectedEvenPlacement CorrectedPlacementFrames CorrectedCellRotation CorrectedChildColumns

private abbrev O (w : Word) := domOdo (oddTile w)
private abbrev E (w : Word) := domOdo (evenTile w)
private abbrev AO (w : Word) := domOdo (altOddT w)
private abbrev AE (w : Word) := domOdo (altEvenT w)
private abbrev LE (w : Word) (p l : Bool) := domOdo (evenLCells w p l)
private abbrev LO (w : Word) (p l : Bool) := domOdo (oddLCells w p l)

private theorem registers (w : Word) (hn : ¬IsBase w) :
    CellsRot (regOdo cellData O E (regsAt w).1 true).dom
       (regOdo cellData O E (regsAt (swapW w)).2 false).dom (vP1 w-((0,1):Site)) ∧
    CellsRot (regOdo cellData O E (regsAt w).2 false).dom
       (regOdo cellData O E (regsAt (swapW w)).1 true).dom (vQ1 w-((0,1):Site)) := by
  obtain ⟨⟨x,xh⟩,⟨y,yh⟩⟩ := regs_some w hn
  obtain ⟨p,q⟩ := parents_of_regs w
  rw [regsAt_swapW,xh,yh]
  simp only [Option.map_some,regOdo,O,E,domOdo,vP1,vQ1,←p x xh,←q y yh]
  exact ⟨CorrectedCellRotation.odd x,CorrectedCellRotation.even y⟩

/-- Exact domains on the three-ending side imply the two native domain equalities on the
rotated two-ending side, once the two L components have their prescribed rotations. -/
theorem transfer (v : Word) (hn : ¬IsBase (v++[.three]))
    (columns : ∀ p l, CellsRot (evenLCells v p l) (oddLCells (swapW v) (p != W1Odd v) l)
      (texV1Even ((parentsAt v).current .even)-((0,1):Site)))
    (ordinary : evenChild evenLCells v false=oddTile (v++[.three]))
    (elongated : evenChild evenLCells v true=altEvenT (v++[.three])) :
    oddChild oddLCells (swapW v) false=evenTile (swapW v++[.two]) ∧
    oddChild oddLCells (swapW v) true=altOddT (swapW v++[.two]) := by
  let w := v++[Digit.three]
  have sw : swapW w=swapW v++[.two] := by rw [show w=v++[.three] from rfl,swapW_append]; rfl
  have last : w.getLast?=some Digit.three := by simp [w]
  have drop : w.dropLast=v := by simp [w]
  have Q : vQ1 w=texV1Even ((parentsAt v).current .even) := by dsimp [w,vQ1]; rw [parentsAt_append_singleton]; rfl
  have sign : W1Odd w=W1Odd v := phase_snoc_three v
  have cs (l : Bool) (_ : w.getLast?=some Digit.three) (p : Bool) :
      CellsRot (LE w.dropLast p l).dom (LO (swapW w.dropLast) (p != W1Odd w) l).dom (vQ1 w-((0,1):Site)) := by
    rw [drop,sign,Q]
    exact columns p l
  obtain ⟨hp,hq⟩ := registers w hn
  have S := CorrectedChildRotation.standard cellData O E LE LO w last hp hq cs
  have A := CorrectedChildRotation.alternate cellData O E AO AE LE LO w last hp hq cs
  have P := CorrectedCellRotation.odd w
  have T := CorrectedCellRotation.alt_even w
  rw [sw] at S A P T
  change pieceUnion (tileOddPieces cellData O E LE w)=oddTile w at ordinary
  change pieceUnion (tileAltEvenPieces cellData O E AO AE LE w)=altEvenT w at elongated
  rw [ordinary] at S
  rw [elongated] at A
  constructor
  · ext z; exact (S z).trans (P z).symm
  · ext z; exact (A z).trans (T z).symm

/-- Every non-base exit supplies the L rotations used in the transfer. -/
theorem at_exit (v u : Word) (one : Bool) (pre : stemPrefix v=u++[exit one])
    (hn : ¬IsBase (v++[.three])) (original : ¬IsBase (stemPrefix v))
    (ordinary : evenChild evenLCells v false=oddTile (v++[.three]))
    (elongated : evenChild evenLCells v true=altEvenT (v++[.three])) :
    oddChild oddLCells (swapW v) false=evenTile (swapW v++[.two]) ∧
    oddChild oddLCells (swapW v) true=altOddT (swapW v++[.two]) :=
  transfer v hn (fun p l => CorrectedRegularRotation.at_exit v u one p l pre original) ordinary elongated

end FLatticePaper.Tiles.CorrectedSwappedDomains
