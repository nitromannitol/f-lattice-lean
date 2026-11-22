import FLatticePaper.Construction.Native
import Mathlib.Data.Finset.Sort

/-! Task 34: the constructor's output tiles, printed as cell sets for every word of length at most 4.

The words are generated breadth first by length: the evaluator is stepped once per letter (`NativeState.advance`, the step
of `evaluateNativeState`), starting from the empty base run; all words of length `k` are emitted before those of length
`k + 1`. Each word `w` prints the four tiles of `(state w).current.tiles.llCenter` (the output of `evaluateNative w`):
`T <word> <tile> <x,y;x,y;...>` (all cells), or `E <word> <error>`.
This run is valid for the words beginning with `1`. A word beginning with `2` or `3` starts with a base run, which the
evaluator takes from `splitInitial` and not by stepping from the empty word, so stepping from the empty base run gives
`E` lines for `2` and `3` and for their extensions; those words are computed from their base runs in
`checks/NativeTilesRoots.lean`.
The tiles are `stdOdd/stdEven` (`standard.currentOdd/currentEven`, the children of the word) and `altOdd/altEven`.
Cells are encoded as natural numbers `(x + OFF) * MUL + (y + OFF)` so that the finite set can be sorted (computable).
The output file is `/tmp/w2_bfs.txt` on the sandbox; the line `done` ends the run. -/

namespace FLatticePaper.Construction.NativeTilesCheck

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

def cellsOf (t : NonemptyTile) : String :=
  let codes : List ℕ := (Finset.image encode t.val.sites).sort (· ≤ ·)
  String.intercalate ";" (codes.map fun n => s!"{(decode n).1},{(decode n).2}")

def outFile : System.FilePath := "/tmp/w2_bfs.txt"

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

/-- One level: the words one letter longer than those of `level`, with their states. -/
def nextLevel (h : IO.FS.Handle) (level : List (Word × NativeState)) : IO (List (Word × NativeState)) := do
  let mut out : List (Word × NativeState) := []
  for (w, state) in level do
    for d in [Digit.one, Digit.two, Digit.three] do
      let w' := w ++ [d]
      match state.advance d with
      | .ok next =>
        emitTiles h w' next
        out := out ++ [(w', next)]
      | .error e => emit h s!"E {wordString w'} {e}"
  return out

def main : IO Unit := do
  let h ← IO.FS.Handle.mk outFile .write
  emit h "start"
  let start := NativeState.init (splitInitial []).1
  emitTiles h [] start
  let mut level : List (Word × NativeState) := [([], start)]
  for _ in [0:4] do
    level ← nextLevel h level
  emit h "done"

#eval main

end FLatticePaper.Construction.NativeTilesCheck
