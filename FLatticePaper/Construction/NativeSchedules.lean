import FLatticePaper.Construction.CorrectionSchedule

namespace FLatticePaper.Construction

open Farey

structure TileParents where
  odd : NonemptyTile
  even : NonemptyTile
  alternateOdd : NonemptyTile
  alternateEven : NonemptyTile

def TileRegisters.parentsFor (registers : TileRegisters) (digit : Digit) : TileParents :=
  let tiles := registers.llCenter
  ⟨if digit = .three then tiles.standard.retainedOdd else tiles.standard.currentOdd,
    if digit = .two then tiles.standard.retainedEven else tiles.standard.currentEven,
    if digit = .three then tiles.alternate.retainedOdd else tiles.alternate.currentOdd,
    if digit = .two then tiles.alternate.retainedEven else tiles.alternate.currentEven⟩

def afterFirstStandard : Parity → List (Fin 6)
  | .odd => [1, 4, 5, 2, 3]
  | .even => [2, 3, 1, 4, 5]

private def afterSeventhAlternate : Parity → List (Fin 6)
  | .odd => [2, 3, 1, 4, 5]
  | .even => [1, 4, 2, 3, 5]

def standardSources (parents : TileParents) : Parity → Fin 6 → NonemptyTile
  | .odd => ![parents.even, parents.even, parents.even, parents.even, parents.odd, parents.odd]
  | .even => ![parents.even, parents.even, parents.odd, parents.odd, parents.odd, parents.odd]

def placedBySlot (jets : Fin 6 → TileJet) (donor : Fin 6 → NonemptyTile) :
    Fin 6 → NonemptyTile :=
  fun slot => (jets slot).place (donor slot)

def ordinaryStandardSchedule (parents : TileParents) (word : Word) (parity : Parity) :
    PlacedSchedule :=
  let placed := placedBySlot (standardJets word parity) (standardSources parents parity)
  ⟨placed 0, (afterFirstStandard parity).map placed⟩

def ordinaryAlternateSchedule (parents : TileParents) (beforePush : Word) (digit : Digit)
    (parity : Parity) : PlacedSchedule :=
  let word := beforePush ++ [digit]
  let placed := placedBySlot (alternateJets word parity) (standardSources parents parity.flip)
  let oldAlt := match parity with
    | .odd => restoreAlternate word .even parents.alternateEven
    | .even => restoreAlternate word .odd parents.alternateOdd
  let seventh := (seventhAlternateJet beforePush digit parity).place oldAlt
  ⟨placed 0, seventh :: (afterSeventhAlternate parity).map placed⟩

structure CorrectionPair where
  left : NonemptyTile
  right : NonemptyTile

private def upperRight (tile : NonemptyTile) : Site := tile.val.upperRight tile.property

private def alignCorrections (parents : TileParents) (helpers : CorrectionPair)
    (beforePush : Word) (digit : Digit) (standardParity : Parity) : CorrectionPair :=
  let target := upperRight (match standardParity with | .odd => parents.even | .even => parents.odd)
  if digit ≠ .three ∧ phase (beforePush ++ [digit]) = 1 then
    ⟨helpers.left, helpers.right.place (target - upperRight helpers.right) 0⟩
  else
    ⟨helpers.left.place (target - upperRight helpers.left) 0, helpers.right⟩

def correctedStandardSchedule (parents : TileParents) (helpers : CorrectionPair)
    (beforePush : Word) (digit : Digit) (parity : Parity) : PlacedSchedule :=
  let word := beforePush ++ [digit]
  let helpers := alignCorrections parents helpers beforePush digit parity
  let donor : Fin 6 → NonemptyTile := match parity with
    | .odd =>
      if phase word = 0 then
        ![parents.even, helpers.right, helpers.left, parents.even, parents.odd, parents.odd]
      else
        ![helpers.right, parents.even, parents.even, helpers.left, parents.odd, parents.odd]
    | .even => ![parents.even, parents.even, parents.odd, helpers.left, helpers.right, parents.odd]
  let placed := placedBySlot (standardJets word parity) donor
  ⟨placed 0, (afterFirstStandard parity).map placed⟩

def correctedAlternateSchedule (parents : TileParents) (helpers : CorrectionPair)
    (beforePush : Word) (digit : Digit) (parity : Parity) : PlacedSchedule :=
  let word := beforePush ++ [digit]
  let helpers := alignCorrections parents helpers beforePush digit parity.flip
  let donor : Fin 6 → NonemptyTile := match parity with
    | .odd => ![parents.even, parents.even, parents.odd, helpers.left, helpers.right, parents.odd]
    | .even => ![helpers.right, parents.even, parents.even, helpers.left, parents.odd, parents.odd]
  let placed := placedBySlot (alternateJets word parity) donor
  ⟨placed 0, [2, 3, 4, 5, 1].map placed⟩

end FLatticePaper.Construction
