import FLatticePaper.Construction.Native

/-! Probe for task 46 (the seven copies of the ordinary even alternate): for each word `w` of length at most three that ends in
digit `1` or `2`, dump the first copy and the six copies of `ordinaryAlternateSchedule (parents of the prefix) prefix digit .even`
with their sites and heights. The tags are `first` (the placed standard donor in slot 0), `seventh` (the restored alternate
piece) and `slotS` (the placed standard donor in slot `S`, in the order of `afterSeventhAlternate .even`). Run with
`flb w2 env lean scripts/alt_copy_probe.lean`; the output is in the sandbox log. -/

open FLatticePaper.Farey FLatticePaper.Construction HeightTile FLatticePaper

namespace CopyDump

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

def endsOneOrTwo (w : Word) : Bool :=
  match w.getLast? with
  | some Digit.one => true
  | some Digit.two => true
  | _ => false

def copyTags : List String := "seventh" :: (afterSeventhAlternate .even).map fun s => s!"slot{s}"

def dumpCopies (w : Word) : String :=
  match w.getLast? with
  | none => s!"ERR 0 empty"
  | some d =>
    match evaluateNative w.dropLast with
    | .error e => s!"ERR {w.length} {e}"
    | .ok regs =>
      let sched := ordinaryAlternateSchedule (regs.parentsFor d) w.dropLast d .even
      let tags := "first" :: copyTags
      let tiles := sched.first.val :: sched.copies
      s!"W {w.length} {repr w}\n" ++
        String.intercalate "\n" ((tags.zip tiles).map fun (tag, t) => dumpTile tag t)

def allOut : String :=
  String.intercalate "\n" ((gen 1 ++ gen 2 ++ gen 3).filter endsOneOrTwo |>.map dumpCopies)

#eval IO.println allOut

end CopyDump
