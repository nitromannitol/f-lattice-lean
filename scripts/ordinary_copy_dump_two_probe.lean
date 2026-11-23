import FLatticePaper.Construction.RawOrigin

/-! Variant of `ordinary_copy_dump_probe.lean` (task 48): the even copies of the words ending in digit two, which the original
probe does not emit (its `ordinaryParities .two` is `[.odd]`). Only words ending in two are dumped. -/

/-! Probe for task 44: dump the six placed copies of each ordinary standard schedule (words of length at most three,
without all threes), with their sites and heights. The parents are those of the native step, as in
`ordinary_origin_probe.lean`. Output: `COPY <word> <parity> <slot>` then `S <x> <y> <h>` for each site (row-first). -/

open FLatticePaper.Farey FLatticePaper.Construction HeightTile FLatticePaper

namespace CopyDump

instance : DecidableEq FLatticePaper.Site := inferInstanceAs (DecidableEq (ℤ × ℤ))

def gen : ℕ → List Word
  | 0 => [[]]
  | n + 1 => [Digit.one, Digit.two, Digit.three].flatMap fun d => (gen n).map (d :: ·)

def lexKey (p : ℤ × ℤ) : Lex (ℤ × ℤ) := toLex (p.2, p.1)

def sortedKeys : ℕ → Finset (Lex (ℤ × ℤ)) → List (Lex (ℤ × ℤ))
  | 0, _ => []
  | n + 1, s => if h : s.Nonempty then s.min' h :: sortedKeys n (s.erase (s.min' h)) else []

def splitLast : Word → Option (Word × Digit)
  | [] => none
  | [d] => some ([], d)
  | d :: rest => (splitLast rest).map (fun p => (d :: p.1, p.2))

def ordinaryParities : Digit → List Parity
  | .one => [.odd, .even]
  | .two => [.odd, .even]
  | .three => [.even]

def copyLines (t : NonemptyTile) : List String :=
  let s := t.val.sites
  let keys := sortedKeys s.card (s.image lexKey)
  keys.map fun k =>
    let p : ℤ × ℤ := ((ofLex k).2, (ofLex k).1)
    let h : Int := if hp : p ∈ s then t.val.height ⟨p, hp⟩ else 0
    s!"S {p.1} {p.2} {h}"

def tileLines (w : Word) : List String :=
  match splitLast w with
  | none => []
  | some (pre, d) =>
    match evaluateNativeState pre with
    | .error e => [s!"ERR {repr w} {e}"]
    | .ok st =>
      let parents := st.current.tiles.parentsFor d
      (ordinaryParities d).flatMap fun parity =>
        (List.finRange 6).flatMap fun slot =>
          s!"COPY {repr w} {repr parity} {slot.val}" :: copyLines (ordinaryStandardCopy parents w parity slot)

def allOut : String :=
  String.intercalate "\n"
    ((gen 1 ++ gen 2 ++ gen 3).filter (fun w => w.any (· ≠ Digit.three) && decide (w.getLast? = some Digit.two)) |>.flatMap tileLines)

#eval IO.println allOut

end CopyDump
