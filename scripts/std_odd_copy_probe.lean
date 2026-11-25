import FLatticePaper.Construction.NativeSchedules
import FLatticePaper.Construction.OrdinaryStandardCover

/-! Probe for task 46 (the odd alternate copies against the standard odd copies): for each word of length at most three ending in
1 or 3, dump the six copies `ordinaryStandardCopy parents word .odd k` (k = 0..5), with their sites and heights, in raw coordinates.
Tags `std0` .. `std5`. Run with `lake env lean scripts/std_odd_copy_probe.lean`; the output is in the build log. -/

open FLatticePaper.Farey FLatticePaper.Construction HeightTile FLatticePaper

namespace StdOddCopies

instance : DecidableEq FLatticePaper.Site := inferInstanceAs (DecidableEq (ℤ × ℤ))

def gen : ℕ → List Word
  | 0 => [[]]
  | n + 1 => [Digit.one, Digit.two, Digit.three].flatMap fun d => (gen n).map (d :: ·)

def sortedSites : ℕ → Finset (Lex (ℤ × ℤ)) → List (Lex (ℤ × ℤ))
  | 0, _ => []
  | n + 1, s =>
    if h : s.Nonempty then s.min' h :: sortedSites n (s.erase (s.min' h)) else []

def dumpTile (tag : String) (t : HeightTile FLatticePaper.Site) : String :=
  let ls := sortedSites t.sites.card (t.sites.map toLex.toEmbedding)
  let body := ls.map (fun l =>
    let x : FLatticePaper.Site := ofLex l
    if h : x ∈ t.sites then s!"S {x.1} {x.2} {t.height ⟨x, h⟩}" else "BAD")
  s!"T {tag} {t.sites.card}\n" ++ String.intercalate "\n" body

def endsOneOrThree (w : Word) : Bool :=
  match w.getLast? with
  | some Digit.one => true
  | some Digit.three => true
  | _ => false

def dumpStd (w : Word) : String :=
  match w.getLast? with
  | none => "ERR 0 empty"
  | some d =>
    match evaluateNative w.dropLast with
    | .error e => s!"ERR {w.length} {e}"
    | .ok regs =>
      let parents := regs.parentsFor d
      s!"W {w.length} {repr w}\n" ++
        String.intercalate "\n" ((List.finRange 6).map fun k =>
          dumpTile s!"std{k.val}" (ordinaryStandardCopy parents w .odd k).val)

def allOut : String :=
  String.intercalate "\n" ((gen 1 ++ gen 2 ++ gen 3).filter endsOneOrThree |>.map dumpStd)

#eval IO.println allOut

end StdOddCopies
