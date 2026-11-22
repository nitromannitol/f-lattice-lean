import FLatticePaper.Construction.ScheduleKinds
import Mathlib.Data.Finset.Sort

/-! Task 37, part 1: the schedules of the constructor, for the words of length at most three, with the absolute cells of every
placed copy in insertion order (the first copy, then `rest`). For each state `x` (a word of length at most two, evaluated by
`evaluateNativeState`) and each digit `d` (the step `x ++ [d]`, skipping the pure runs that are base runs of `splitInitial`),
the program prints the ordinary standard and alternate schedules and, for the digits 2 and 3, the corrected standard and
alternate schedules with both corrections, and the correction schedules themselves.

Lines: `H <word> <schedule> <count>` opens a schedule with `count` copies; `Q <index> <cells>` gives copy `index`
(`0` is the first copy), with cells `x,y;x,y;...` (absolute). `E ...` is an evaluator error (none expected).
Output file: `/tmp/w2_overlap.txt` on the sandbox; the line `done` ends the run. -/

namespace FLatticePaper.Construction.OverlapNativeCheck

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction

def OFF : ℤ := 1000
def MUL : ℤ := 10000

def encode (x : Site) : ℕ := ((x.1 + OFF) * MUL + (x.2 + OFF)).toNat

def decode (n : ℕ) : Site :=
  (((n : ℤ) / MUL) - OFF, ((n : ℤ) % MUL) - OFF)

def digitChar : Digit → Char
  | .one => '1'
  | .two => '2'
  | .three => '3'

def wordString (w : Word) : String := String.ofList (w.map digitChar)

def cellsStr (s : Finset Site) : String :=
  let codes : List ℕ := (Finset.image encode s).sort (· ≤ ·)
  String.intercalate ";" (codes.map fun n => s!"{(decode n).1},{(decode n).2}")

def outFile : System.FilePath := "/tmp/w2_overlap.txt"

def emit (h : IO.FS.Handle) (line : String) : IO Unit := do
  h.putStrLn line
  h.flush

def emitRest (h : IO.FS.Handle) : Nat → List NonemptyTile → IO Unit
  | _, [] => pure ()
  | i, t :: ts => do
    emit h s!"Q {i} {cellsStr t.val.sites}"
    emitRest h (i + 1) ts

def emitSchedule (h : IO.FS.Handle) (label : String) (s : PlacedSchedule) : IO Unit := do
  emit h s!"H {label} {1 + s.rest.length}"
  emit h s!"Q 0 {cellsStr s.first.val.sites}"
  emitRest h 1 s.rest

def allDigit (x : Word) (d : Digit) : Bool := x.all (fun y => decide (y = d))

def states : List Word :=
  [[], [.one], [.two], [.three], [.one, .one], [.one, .two], [.one, .three], [.two, .one], [.two, .two], [.two, .three],
    [.three, .one], [.three, .two], [.three, .three]]

def emitState (h : IO.FS.Handle) (x : Word) : IO Unit := do
  match evaluateNativeState x with
  | .error e => emit h s!"E state {wordString x} {e}"
  | .ok st =>
    for d in [Digit.one, Digit.two, Digit.three] do
      if (d == .two && allDigit x .two) || (d == .three && allDigit x .three) then
        pure ()
      else
        let word := x ++ [d]
        let parents := st.current.tiles.parentsFor d
        emitSchedule h s!"{wordString word} ordStdOdd" (ordinaryStandardSchedule parents word .odd)
        emitSchedule h s!"{wordString word} ordStdEven" (ordinaryStandardSchedule parents word .even)
        emitSchedule h s!"{wordString word} ordAltOdd" (ordinaryAlternateSchedule parents x d .odd)
        emitSchedule h s!"{wordString word} ordAltEven" (ordinaryAlternateSchedule parents x d .even)
        match d with
        | .one => pure ()
        | _ =>
          let saved := if d == .two then st.savedTwo else st.savedThree
          let parity : Parity := if d == .two then .odd else .even
          for elong in [false, true] do
            let tag := if elong then "long" else "short"
            match correctionPairOf saved x parity elong with
            | .error e => emit h s!"E pair {wordString word} {tag} {e}"
            | .ok pair =>
              emitSchedule h s!"{wordString word} corrStd{tag}Odd" (correctedStandardSchedule parents pair x d .odd)
              emitSchedule h s!"{wordString word} corrStd{tag}Even" (correctedStandardSchedule parents pair x d .even)
              emitSchedule h s!"{wordString word} corrAlt{tag}Odd" (correctedAlternateSchedule parents pair x d .odd)
              emitSchedule h s!"{wordString word} corrAlt{tag}Even" (correctedAlternateSchedule parents pair x d .even)
          for flip in [true, false] do
            for elong in [false, true] do
              let side := if flip then "L" else "R"
              let tag := if elong then "long" else "short"
              match correctionSchedule saved.tiles saved.word x parity flip elong with
              | .error e => emit h s!"E sched {wordString word} {side} {tag} {e}"
              | .ok sched => emitSchedule h s!"{wordString word} piece{side}{tag}" sched

def main : IO Unit := do
  let h ← IO.FS.Handle.mk outFile .write
  emit h "start"
  for x in states do
    emitState h x
  emit h "done"

#eval main

end FLatticePaper.Construction.OverlapNativeCheck
