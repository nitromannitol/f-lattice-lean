import FLatticePaper.Construction.Native

/-! Probe for task 43: the absolute raw sites of the ordinary standard schedules and their lower-left site `Q`.

For each word of length at most three (excluding all threes) and each parity the native constructor uses as ordinary,
the parents are those of the native step (the tiles in the state before the last digit). The raw assembly of the
schedule has sites equal to the union of the first tile and the copies (insertion never translates sites), so its
lower-left site (least in row-first order) is `Q`. Output: `TILE <word> <parity> Q <x> <y> SIZE <n>`, then the raw sites
in row-first order as `S <x> <y>`. -/

open FLatticePaper.Farey FLatticePaper.Construction HeightTile FLatticePaper

namespace OriginProbe

instance : DecidableEq FLatticePaper.Site := inferInstanceAs (DecidableEq (ℤ × ℤ))

def gen : ℕ → List Word
  | 0 => [[]]
  | n + 1 => [Digit.one, Digit.two, Digit.three].flatMap fun d => (gen n).map (d :: ·)

def lexKey (p : ℤ × ℤ) : Lex (ℤ × ℤ) := toLex (p.2, p.1)

/-- The least site in row-first order (lowest row, then leftmost), computed without proofs. -/
def lexMin (U : Finset (ℤ × ℤ)) : ℤ × ℤ :=
  if h : (U.image lexKey).Nonempty then
    let k := (U.image lexKey).min' h
    ((ofLex k).2, (ofLex k).1)
  else (0, 0)

def sortedKeys : ℕ → Finset (Lex (ℤ × ℤ)) → List (Lex (ℤ × ℤ))
  | 0, _ => []
  | n + 1, s => if h : s.Nonempty then s.min' h :: sortedKeys n (s.erase (s.min' h)) else []

/-- The raw sites: the first tile and the copies, with sites unchanged by insertion. -/
def rawSites (s : PlacedSchedule) : Finset (ℤ × ℤ) :=
  s.copies.foldl (fun acc c => acc ∪ c.sites) s.first.val.sites

def splitLast : Word → Option (Word × Digit)
  | [] => none
  | [d] => some ([], d)
  | d :: rest => (splitLast rest).map (fun p => (d :: p.1, p.2))

def ordinaryParities : Digit → List Parity
  | .one => [.odd, .even]
  | .two => [.odd]
  | .three => [.even]

def tileLines (w : Word) : List String :=
  match splitLast w with
  | none => []
  | some (pre, d) =>
    match evaluateNativeState pre with
    | .error e => [s!"ERR {repr w} {e}"]
    | .ok st =>
      let parents := st.current.tiles.parentsFor d
      (ordinaryParities d).flatMap fun parity =>
        let U := rawSites (ordinaryStandardSchedule parents w parity)
        let q := lexMin U
        let sites := (sortedKeys U.card (U.image lexKey)).map (fun k => ((ofLex k).2, (ofLex k).1))
        [s!"TILE {repr w} {repr parity} Q {q.1} {q.2} SIZE {U.card}"] ++
          sites.map (fun p => s!"S {p.1} {p.2}")

def allOut : String :=
  String.intercalate "\n"
    ((gen 1 ++ gen 2 ++ gen 3).filter (fun w => w.any (· ≠ Digit.three)) |>.flatMap tileLines)

#eval IO.println allOut

end OriginProbe
