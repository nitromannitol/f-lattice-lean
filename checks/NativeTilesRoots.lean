import FLatticePaper.Construction.Native
import Mathlib.Data.Finset.Sort

/-! Task 34, part 2: the constructor's tiles for the words beginning with `2` or `3` (length at most 4).

The evaluator starts a word from its leading run of twos (or threes) as a base run (`splitInitial`), so a word beginning with
`2^k` or `3^k` is evaluated from the base state of that run, and its remaining letters are stepped from there. The roots are
therefore the runs `2`, `22`, `222`, `3`, `33`, `333` (the states `evaluateNativeState` gives for them), and the continuations
start with a letter different from the run digit (a further run digit would extend the run). Output: `/tmp/w2_roots.txt`,
the same line format as `checks/NativeTiles.lean`; the line `done` ends the run. -/

namespace FLatticePaper.Construction.NativeTilesRootsCheck

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

def wordString (w : Word) : String := String.mk (w.map digitChar)

def cellsOf (t : NonemptyTile) : String :=
  let codes : List ℕ := (Finset.image encode t.val.sites).sort (· ≤ ·)
  String.intercalate ";" (codes.map fun n => s!"{(decode n).1},{(decode n).2}")

def outFile : System.FilePath := "/tmp/w2_roots.txt"

def emit (h : IO.FS.Handle) (line : String) : IO Unit := do
  h.putStrLn line
  h.flush

def emitTiles (h : IO.FS.Handle) (w : Word) (state : NativeState) : IO Unit := do
  let s := wordString w
  let regs := state.current.tiles.llCenter
  emit h s!"T {s} stdOdd {cellsOf regs.standard.currentOdd}"
  emit h s!"T {s} stdEven {cellsOf regs.standard.currentEven}"
  emit h s!"T {s} altOdd {cellsOf regs.alternate.currentOdd}"
  emit h s!"T {s} altEven {cellsOf regs.alternate.currentEven}"

/-- The continuations of a run root: letters after the run, the first one different from the run digit. -/
partial def extend (h : IO.FS.Handle) (runDigit : Digit) (w : Word) (state : NativeState) (remaining : Nat)
    (first : Bool) : IO Unit := do
  if remaining = 0 then return
  for d in [Digit.one, Digit.two, Digit.three] do
    if first && d = runDigit then
      continue
    let w' := w ++ [d]
    match state.advance d with
    | .ok next =>
      emitTiles h w' next
      extend h runDigit w' next (remaining - 1) false
    | .error e => emit h s!"E {wordString w'} {e}"

def runRoot (h : IO.FS.Handle) (runDigit : Digit) (root : Word) : IO Unit := do
  match evaluateNativeState root with
  | .ok state =>
    emitTiles h root state
    extend h runDigit root state (3 - root.length) true
  | .error e => emit h s!"E {wordString root} {e}"

def main : IO Unit := do
  let h ← IO.FS.Handle.mk outFile .write
  emit h "start"
  runRoot h .two [.two]
  runRoot h .two [.two, .two]
  runRoot h .two [.two, .two, .two]
  runRoot h .three [.three]
  runRoot h .three [.three, .three]
  runRoot h .three [.three, .three, .three]
  emit h "done"

#eval main

end FLatticePaper.Construction.NativeTilesRootsCheck
