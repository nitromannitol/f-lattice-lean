import FLatticePaper.Construction.Native

/-! Probe for task 42: dump the native output tiles `standard.currentOdd` and `standard.currentEven` after each word
of length at most three, with their sites in sorted order and their heights. Run with `flb w3 env lean` from the
repository; the output is in the sandbox log. -/

open FLatticePaper.Farey FLatticePaper.Construction HeightTile FLatticePaper

namespace TileDump

instance : DecidableEq FLatticePaper.Site := inferInstanceAs (DecidableEq (ℤ × ℤ))

def gen : ℕ → List Word
  | 0 => [[]]
  | n + 1 => [Digit.one, Digit.two, Digit.three].flatMap fun d => (gen n).map (d :: ·)

/-- The sites of a finite set in lexicographic order, by repeatedly taking the minimum (computable). -/
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

def dumpWord (w : Word) : String :=
  match evaluateNative w with
  | .error e => s!"ERR {w.length} {e}"
  | .ok regs =>
    s!"W {w.length} {repr w}\n" ++
      dumpTile "odd" regs.standard.currentOdd.val ++ "\n" ++
      dumpTile "even" regs.standard.currentEven.val

def allOut : String :=
  String.intercalate "\n" ((gen 1 ++ gen 2 ++ gen 3).filter (fun w => w.any (· ≠ Digit.three)) |>.map dumpWord)

#eval IO.println allOut

end TileDump
