import FLatticePaper.Construction.Native
import Mathlib.Data.Finset.Sort

/-! Task 35, part 1: the constructor's L-correction outputs, for the words of length at most three.

For each nonempty ancestor word `u` of length at most two, the program prints
* `P <u> <tile> <cells>`: the retained tiles of the saved registers of `u` (`llCenter`, as the constructor uses them):
  `stdRetOdd` = T(p_2), `stdRetEven` = T(q_2) (the parent pair of `u`), `altRetOdd`, `altRetEven` = the alternate parent tiles;
* `C <parity> <x> <side> <length> <cells>` or `E ...`: the correction `correctionSchedule` evaluates (`.correction` mode, as
  `correctionPair` does) for the word `x`, where `x = u ++ 2^k` for the odd parity (`u` ends in 1 or 3) and `x = u ++ 3^k`
  for the even parity (`u` ends in 1 or 2), with `|x| ≤ 3`. `side` is `L` (flip) or `R`; `length` is `long` (elongated) or
  `short`. The saved registers are those of `u`, which are the `savedTwo` (resp. `savedThree`) registers of `x`.
Output file: `w2_lcorr.txt`; the line `done` ends the run. -/

namespace FLatticePaper.Construction.LCorrectionsNativeCheck

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

def outFile : System.FilePath := "w2_lcorr.txt"

def emit (h : IO.FS.Handle) (line : String) : IO Unit := do
  h.putStrLn line
  h.flush

def endsIn (u : Word) (ds : List Digit) : Bool :=
  match u.getLast? with
  | some d => decide (d ∈ ds)
  | none => false

def emitRegisters (h : IO.FS.Handle) (u : Word) (tiles : TileRegisters) : IO Unit := do
  let s := wordString u
  let r := tiles.llCenter
  emit h s!"P {s} stdRetOdd {cellsOf r.standard.retainedOdd}"
  emit h s!"P {s} stdRetEven {cellsOf r.standard.retainedEven}"
  emit h s!"P {s} altRetOdd {cellsOf r.alternate.retainedOdd}"
  emit h s!"P {s} altRetEven {cellsOf r.alternate.retainedEven}"

def emitCorrections (h : IO.FS.Handle) (parity : Parity) (x : Word) (saved : SavedRegisters) : IO Unit := do
  let pname := match parity with
    | .odd => "odd"
    | .even => "even"
  for flip in [true, false] do
    for elong in [false, true] do
      let side := if flip then "L" else "R"
      let len := if elong then "long" else "short"
      match correctionSchedule saved.tiles saved.word x parity flip elong with
      | .error e => emit h s!"E {pname} {wordString x} {side} {len} {e}"
      | .ok sched =>
        match sched.eval .correction "L-correction" with
        | .error e => emit h s!"E {pname} {wordString x} {side} {len} {e}"
        | .ok tile => emit h s!"C {pname} {wordString x} {side} {len} {cellsOf tile.llCenter}"

def ancestors : List Word :=
  [[.one], [.two], [.three],
    [.one, .one], [.one, .two], [.one, .three],
    [.two, .one], [.two, .two], [.two, .three],
    [.three, .one], [.three, .two], [.three, .three]]

def main : IO Unit := do
  let h ← IO.FS.Handle.mk outFile .write
  emit h "start"
  for u in ancestors do
    match evaluateNativeState u with
    | .error e => emit h s!"E {wordString u} {e}"
    | .ok state =>
      let saved := state.current
      emitRegisters h u saved.tiles
      if endsIn u [.one, .three] then
        for k in [0:4 - u.length] do
          emitCorrections h .odd (u ++ List.replicate k .two) saved
      if endsIn u [.one, .two] then
        for k in [0:4 - u.length] do
          emitCorrections h .even (u ++ List.replicate k .three) saved
  emit h "done"

#eval main

end FLatticePaper.Construction.LCorrectionsNativeCheck
