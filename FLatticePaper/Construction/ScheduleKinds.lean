import FLatticePaper.Construction.Native

/-! # The constructor's schedule choice against the digit table of `lemma:global_odometers` (task 36)

`paper/global_recurrence.tex` (lines 56-75) gives, for the last digit `d` of a word and each of the four outputs (standard odd,
standard even, alternate odd, alternate even), the schedule used: ordinary, a short `L`-correction, or a long (elongated)
`L`-correction:

| last digit | standard odd | standard even | alternate odd | alternate even |
|---|---|---|---|---|
| 1 | ordinary | ordinary | ordinary | ordinary |
| 2 | ordinary | short L | long L | ordinary |
| 3 | short L | ordinary | ordinary | long L |

`tableKind` is that table. `tableRegisters state d` is the evaluator's step `NativeState.nextRegisters state d` written with
each output chosen by `tableKind`. The theorem `nextRegisters_eq_tableRegisters` says the evaluator's step is this one for
every digit; it is a case analysis on the last digit, closed by reduction. The shape lemmas give the number of copies of each
schedule for every word (the evaluator's definitions, not the geometry). -/

namespace FLatticePaper.Construction

open Farey

/-- The schedule of one output: ordinary, short `L`-correction, or long (elongated) `L`-correction. -/
inductive ScheduleKind where
  | ordinary
  | shortL
  | longL
  deriving DecidableEq

/-- The four outputs of a step. -/
inductive OutputKind where
  | standardOdd
  | standardEven
  | alternateOdd
  | alternateEven
  deriving DecidableEq

/-- The table of `lemma:global_odometers` (global_recurrence.tex 56-75), by the last digit and the output. -/
def tableKind : Digit → OutputKind → ScheduleKind
  | .one, _ => .ordinary
  | .two, .standardOdd => .ordinary
  | .two, .standardEven => .shortL
  | .two, .alternateOdd => .longL
  | .two, .alternateEven => .ordinary
  | .three, .standardOdd => .shortL
  | .three, .standardEven => .ordinary
  | .three, .alternateOdd => .ordinary
  | .three, .alternateEven => .longL

/-- Choose the alternative named by a schedule kind. -/
def chooseKind {α : Type} (kind : ScheduleKind) (ordinary shortL longL : α) : α :=
  match kind with
  | .ordinary => ordinary
  | .shortL => shortL
  | .longL => longL

/-- The correction pair of the saved registers, as `correctionPair` of `Native.lean` builds it. -/
def correctionPairOf (saved : SavedRegisters) (beforePush : Word) (parity : Parity) (elongated : Bool) :
    Except String CorrectionPair := do
  let left ← correctionSchedule saved.tiles saved.word beforePush parity true elongated
  let left ← left.eval .correction "left L"
  let right ← correctionSchedule saved.tiles saved.word beforePush parity false elongated
  let right ← right.eval .correction "right L"
  return ⟨left.llCenter, right.llCenter⟩

def ordinaryStandardTile (parents : TileParents) (word : Word) (parity : Parity) : Except String NonemptyTile :=
  (ordinaryStandardSchedule parents word parity).eval .tile "standard"

def ordinaryAlternateTile (parents : TileParents) (beforePush : Word) (digit : Digit) (parity : Parity) :
    Except String NonemptyTile :=
  (ordinaryAlternateSchedule parents beforePush digit parity).eval .tile "alternate"

def correctedStandardTile (parents : TileParents) (pair : CorrectionPair) (beforePush : Word) (digit : Digit)
    (parity : Parity) : Except String NonemptyTile :=
  (correctedStandardSchedule parents pair beforePush digit parity).eval .tile "corrected standard"

def correctedAlternateTile (parents : TileParents) (pair : CorrectionPair) (beforePush : Word) (digit : Digit)
    (parity : Parity) : Except String NonemptyTile :=
  (correctedAlternateSchedule parents pair beforePush digit parity).eval .tile "corrected alternate"

/-- The evaluator's step, with each output chosen by `tableKind` (the table of `lemma:global_odometers`).
For the digit `1` no correction is built, as in the evaluator; all outputs are ordinary by the table. -/
def tableRegisters (state : NativeState) : Digit → Except String TileRegisters
  | .one => do
    let beforePush := state.current.word
    let word := beforePush ++ [.one]
    let parents := state.current.tiles.parentsFor .one
    let oddTile ← ordinaryStandardTile parents word .odd
    let evenTile ← ordinaryStandardTile parents word .even
    let altOdd ← ordinaryAlternateTile parents beforePush .one .odd
    let altEven ← ordinaryAlternateTile parents beforePush .one .even
    return ⟨⟨oddTile, evenTile, parents.odd, parents.even⟩,
      ⟨altOdd, altEven, parents.alternateOdd, parents.alternateEven⟩⟩
  | .two => do
    let beforePush := state.current.word
    let word := beforePush ++ [.two]
    let parents := state.current.tiles.parentsFor .two
    let short ← correctionPairOf state.savedTwo beforePush .odd false
    let long ← correctionPairOf state.savedTwo beforePush .odd true
    let oddTile ← chooseKind (tableKind .two .standardOdd) (ordinaryStandardTile parents word .odd)
      (correctedStandardTile parents short beforePush .two .odd)
      (correctedStandardTile parents long beforePush .two .odd)
    let evenTile ← chooseKind (tableKind .two .standardEven) (ordinaryStandardTile parents word .even)
      (correctedStandardTile parents short beforePush .two .even)
      (correctedStandardTile parents long beforePush .two .even)
    let altOdd ← chooseKind (tableKind .two .alternateOdd) (ordinaryAlternateTile parents beforePush .two .odd)
      (correctedAlternateTile parents short beforePush .two .odd)
      (correctedAlternateTile parents long beforePush .two .odd)
    let altEven ← chooseKind (tableKind .two .alternateEven) (ordinaryAlternateTile parents beforePush .two .even)
      (correctedAlternateTile parents short beforePush .two .even)
      (correctedAlternateTile parents long beforePush .two .even)
    return ⟨⟨oddTile, evenTile, parents.odd, parents.even⟩,
      ⟨altOdd, altEven, parents.alternateOdd, parents.alternateEven⟩⟩
  | .three => do
    let beforePush := state.current.word
    let word := beforePush ++ [.three]
    let parents := state.current.tiles.parentsFor .three
    let short ← correctionPairOf state.savedThree beforePush .even false
    let long ← correctionPairOf state.savedThree beforePush .even true
    let oddTile ← chooseKind (tableKind .three .standardOdd) (ordinaryStandardTile parents word .odd)
      (correctedStandardTile parents short beforePush .three .odd)
      (correctedStandardTile parents long beforePush .three .odd)
    let evenTile ← chooseKind (tableKind .three .standardEven) (ordinaryStandardTile parents word .even)
      (correctedStandardTile parents short beforePush .three .even)
      (correctedStandardTile parents long beforePush .three .even)
    let altOdd ← chooseKind (tableKind .three .alternateOdd) (ordinaryAlternateTile parents beforePush .three .odd)
      (correctedAlternateTile parents short beforePush .three .odd)
      (correctedAlternateTile parents long beforePush .three .odd)
    let altEven ← chooseKind (tableKind .three .alternateEven) (ordinaryAlternateTile parents beforePush .three .even)
      (correctedAlternateTile parents short beforePush .three .even)
      (correctedAlternateTile parents long beforePush .three .even)
    return ⟨⟨oddTile, evenTile, parents.odd, parents.even⟩,
      ⟨altOdd, altEven, parents.alternateOdd, parents.alternateEven⟩⟩

/-- The evaluator's step is the table-driven step, for every state and every last digit. -/
theorem nextRegisters_eq_tableRegisters (state : NativeState) (digit : Digit) :
    state.nextRegisters digit = tableRegisters state digit := by
  cases digit <;> rfl

/-- The table has ordinary schedules for every output of the digit `1`. -/
theorem tableKind_one (output : OutputKind) : tableKind .one output = .ordinary := rfl

/-- Shape of the ordinary standard schedule: six copies (the first and five more), for both parities and every word. -/
theorem ordinaryStandardSchedule_rest_length (parents : TileParents) (word : Word) (parity : Parity) :
    (ordinaryStandardSchedule parents word parity).rest.length = 5 := by
  cases parity <;> rfl

/-- Shape of the ordinary alternate schedule: seven copies (the first, five slots, and the earlier alternate). -/
theorem ordinaryAlternateSchedule_rest_length (parents : TileParents) (beforePush : Word) (digit : Digit)
    (parity : Parity) :
    (ordinaryAlternateSchedule parents beforePush digit parity).rest.length = 6 := by
  cases parity <;> rfl

/-- Shape of the corrected standard schedule: six copies, of which two are the helper corrections. -/
theorem correctedStandardSchedule_rest_length (parents : TileParents) (pair : CorrectionPair) (beforePush : Word)
    (digit : Digit) (parity : Parity) :
    (correctedStandardSchedule parents pair beforePush digit parity).rest.length = 5 := by
  cases parity <;> rfl

/-- Shape of the corrected alternate schedule: six copies, of which two are the helper corrections. -/
theorem correctedAlternateSchedule_rest_length (parents : TileParents) (pair : CorrectionPair) (beforePush : Word)
    (digit : Digit) (parity : Parity) :
    (correctedAlternateSchedule parents pair beforePush digit parity).rest.length = 5 := by
  cases parity <;> rfl

end FLatticePaper.Construction
