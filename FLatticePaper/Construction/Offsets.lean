import FLatticePaper.Farey.Lineage
import FLatticePaper.Graph
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fin.VecNotation

namespace FLatticePaper.Construction

open Farey

/-- A spatial translation and the slope added at the destination. -/
abbrev TileJet := Site × Site

def kernelJet (fraction : Fraction) : TileJet :=
  ((fraction.den, fraction.num), 0)

def transverseJet (fraction : Fraction) : TileJet :=
  ((fraction.num - fraction.den, fraction.num + fraction.den), (fraction.num, -fraction.den))

def doubleFirst (first second third fourth step : TileJet) : Fin 6 → TileJet :=
  ![first, first + step, second, second + step, third, fourth]

def doubleLast (first second third fourth step : TileJet) : Fin 6 → TileJet :=
  ![first, second, third, third + step, fourth, fourth + step]

/-- The six standard placements from the two retained fraction registers. -/
def standardJets (word : Word) (parity : Parity) : Fin 6 → TileJet :=
  let parents := parentsAt word
  let oddKernel := kernelJet parents.odd
  let oddTrans := transverseJet parents.odd
  let evenKernel := kernelJet parents.even
  let evenTrans := transverseJet parents.even
  match parity with
  | .odd =>
    if phase word = 0 then
      doubleFirst 0 (2 • oddKernel + oddTrans) (2 • evenKernel) evenTrans evenKernel
    else
      doubleFirst (2 • oddKernel) oddTrans 0 (2 • evenKernel + evenTrans) evenKernel
  | .even =>
    if phase word = 0 then
      doubleLast 0 (2 • oddKernel + 2 • oddTrans) evenKernel evenTrans oddTrans
    else
      doubleLast (2 • oddKernel) (2 • oddTrans) 0 (evenTrans + evenKernel) oddTrans

/-- The six ordinary source slots of an alternate, before inserting its
seventh source or replacing slots by the corrections. -/
def alternateJets (word : Word) (parity : Parity) : Fin 6 → TileJet :=
  let parents := parentsAt word
  let oddKernel := kernelJet parents.odd
  let oddTrans := transverseJet parents.odd
  let evenKernel := kernelJet parents.even
  let evenTrans := transverseJet parents.even
  match parity with
  | .odd =>
    if phase word = 0 then
      doubleLast 0 (2 • oddKernel + 2 • oddTrans + evenKernel) evenKernel evenTrans
        (evenKernel + oddTrans)
    else
      doubleLast (2 • oddKernel) (2 • oddTrans - evenKernel) 0 (evenKernel + evenTrans)
        (-evenKernel + oddTrans)
  | .even =>
    if phase word = 0 then
      doubleFirst 0 (2 • oddKernel + oddTrans) evenKernel (oddTrans - evenKernel + evenTrans)
        (-evenKernel + oddTrans)
    else
      doubleFirst (2 • oddKernel) oddTrans 0 (oddTrans + evenTrans + 2 • evenKernel)
        (evenKernel + oddTrans)

/-- The last digit and the resulting word are kept together for the seventh slot. -/
def seventhAlternateJet (beforePush : Word) (digit : Digit) (parity : Parity) : TileJet :=
  let word := beforePush ++ [digit]
  let parents := parentsAt word
  let oddKernel := kernelJet parents.odd
  let oddTrans := transverseJet parents.odd
  let evenKernel := kernelJet parents.even
  let evenTrans := transverseJet parents.even
  match parity, decide (phase word = 0) with
  | .odd, true => evenKernel + oddTrans
  | .odd, false =>
    match digit with
    | .two => oddTrans
    | .one | .three => oddTrans + 2 • oddKernel - evenKernel
  | .even, true =>
    match digit with
    | .one => oddTrans + (2 • oddKernel - evenKernel)
    | .two => evenTrans
    | .three => oddTrans + evenKernel - 2 • (evenKernel - 2 • oddKernel)
  | .even, false =>
    match digit with
    | .two => 2 • evenKernel + evenTrans
    | .one | .three => evenKernel + oddTrans

/-- Restore the retained alternate to the corner selected at its own birth. -/
def alternateRestoration (word : Word) (parity : Parity) : Site :=
  match retainedBirth? word parity with
  | none => 0
  | some birth =>
    let parents := parentsAt birth.1
    let offset := (kernelJet parents.even).1 - (transverseJet parents.odd).1
    if 0 ≤ offset.2 then
      match parity with
      | .odd => if phase birth.1 = 1 then -offset else 0
      | .even =>
        if phase birth.1 = 0 then
          -(offset + if birth.1.all (fun digit => decide (digit = .three)) then (0, 1) else 0)
        else 0
    else 0

structure CorrectionJets where
  scan : TileJet
  bridge : TileJet
  headStart : TileJet
  headStep : TileJet

/-- The four increments of the L construction, using the saved ancestor's
registers and phase, not those of the consuming word. -/
def correctionJets (beforeLast : Word) (last : Digit) (parity : Parity) (flip : Bool) :
    CorrectionJets :=
  let word := beforeLast ++ [last]
  let parents := parentsAt word
  let oddKernel := kernelJet parents.odd
  let oddTrans := transverseJet parents.odd
  let evenKernel := kernelJet parents.even
  let evenTrans := transverseJet parents.even
  let twiceOdd := 2 • oddKernel
  match parity, decide (phase word = 1), flip with
  | .odd, true, false =>
    ⟨evenTrans, evenTrans + (evenKernel - twiceOdd),
      (-evenTrans + oddTrans) + (twiceOdd - evenKernel), -evenKernel⟩
  | .odd, false, false => ⟨evenTrans, evenTrans, -evenTrans + oddTrans, evenKernel⟩
  | .odd, true, true => ⟨-evenTrans, -oddTrans, twiceOdd - evenKernel, evenKernel⟩
  | .odd, false, true =>
    ⟨-evenTrans, -oddTrans - (twiceOdd - evenKernel), 0, -evenKernel⟩
  | .even, true, false =>
    ⟨twiceOdd, twiceOdd,
      if last = .two then evenKernel - twiceOdd + evenTrans - oddTrans + evenKernel
      else evenKernel - twiceOdd, oddTrans⟩
  | .even, false, false =>
    ⟨-twiceOdd, -evenKernel,
      if last = .two then evenTrans - oddTrans else twiceOdd - evenKernel, oddTrans⟩
  | .even, true, true =>
    ⟨-twiceOdd, -evenKernel + oddTrans - evenTrans,
      if last = .two then evenTrans - oddTrans + evenKernel else 0, -oddTrans⟩
  | .even, false, true =>
    ⟨twiceOdd, twiceOdd + oddTrans - evenTrans,
      if last = .two then evenTrans - oddTrans - twiceOdd + evenKernel else 0, -oddTrans⟩

end FLatticePaper.Construction
