import FLatticePaper.Construction.Offsets
import FLatticePaper.Construction.PlacedSchedule

namespace FLatticePaper.Construction

open Farey

def TileJet.place (jet : TileJet) (tile : NonemptyTile) : NonemptyTile :=
  tile.place jet.1 jet.2

def restoreAlternate (word : Word) (parity : Parity) (tile : NonemptyTile) : NonemptyTile :=
  tile.place (alternateRestoration word parity) 0

private def advancedCopies (tile : NonemptyTile) (increment : TileJet) :
    TileJet → ℕ → List NonemptyTile
  | _, 0 => []
  | jet, count + 1 =>
    let next := jet + increment
    next.place tile :: advancedCopies tile increment next count

private theorem length_advancedCopies (tile : NonemptyTile) (increment start : TileJet) (count : ℕ) :
    (advancedCopies tile increment start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [advancedCopies, ih]

def correctionHeadCount (scanLength : ℕ) (elongated : Bool) : ℕ :=
  2 * (scanLength + 1) - if elongated then 0 else 1

/-- A right or flipped-left correction before trim and max-zero. The bridge
nudge is a second, unpriced translation after its affine placement. -/
def correctionPieces (saved : TileRegisters) (ancestorPrefix : Word) (last : Digit)
    (beforePush : Word) (parity : Parity) (flip elongated : Bool) (scanLength : ℕ) :
    PlacedSchedule :=
  let ancestor := ancestorPrefix ++ [last]
  let sources := saved.llCenter
  let (stem, cross, head) := match parity with
    | .odd => (sources.standard.retainedEven, sources.standard.retainedOdd,
        restoreAlternate beforePush .even sources.alternate.retainedEven)
    | .even => (sources.standard.retainedOdd, sources.standard.retainedEven,
        restoreAlternate beforePush .odd sources.alternate.retainedOdd)
  let increments := correctionJets ancestorPrefix last parity flip
  let start : TileJet :=
    if flip then standardJets beforePush parity (match parity with | .odd => 3 | .even => 5)
    else 0
  let bridgeJet := start + scanLength • increments.scan + increments.bridge
  let bridge := bridgeJet.place cross
  let bridge := match parity with
    | .odd =>
      if ancestor.all (fun digit => decide (digit = .three)) then
        bridge.place (if flip then (1, -1) else (0, -1)) 0
      else bridge
    | .even =>
      if flip && ancestor.all (fun digit => decide (digit = .two)) then bridge.place (1, 1) 0
      else bridge
  ⟨start.place stem,
    advancedCopies stem increments.scan start scanLength ++
      bridge :: advancedCopies head increments.headStep (bridgeJet + increments.headStart)
        (correctionHeadCount scanLength elongated)⟩

theorem correctionPieces_rest_length (saved : TileRegisters) (ancestorPrefix : Word) (last : Digit)
    (beforePush : Word) (parity : Parity) (flip elongated : Bool) (scanLength : ℕ) :
    (correctionPieces saved ancestorPrefix last beforePush parity flip elongated scanLength).rest.length =
      scanLength + 1 + correctionHeadCount scanLength elongated := by
  cases parity <;> simp [correctionPieces, length_advancedCopies] <;> omega

/-- Take the helper from a nonempty saved word with the exact pure suffix.
It is evaluated before the new letter is appended. -/
def correctionSchedule (saved : TileRegisters) (ancestor beforePush : Word)
    (parity : Parity) (flip elongated : Bool) : Except String PlacedSchedule := do
  let some last := ancestor.getLast? | throw "empty saved correction ancestor"
  let scanLength := beforePush.length - ancestor.length
  let suffixDigit : Digit := match parity with | .odd => .two | .even => .three
  if beforePush ≠ ancestor ++ List.replicate scanLength suffixDigit then
    throw "saved correction ancestor has the wrong suffix"
  else
    pure (correctionPieces saved ancestor.dropLast last beforePush parity flip elongated scanLength)

end FLatticePaper.Construction
