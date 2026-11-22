import FLatticePaper.Construction.Native

open FLatticePaper.Farey FLatticePaper.Construction HeightTile FLatticePaper

instance : DecidableEq FLatticePaper.Site := inferInstanceAs (DecidableEq (ℤ × ℤ))

namespace CopyDump

def gen : ℕ → List Word
  | 0 => [[]]
  | n + 1 => [Digit.one, Digit.two, Digit.three].flatMap fun d => (gen n).map (d :: ·)

/-- The height of a tile at a site, with value `0` off its domain (only used on its own domain). -/
def valAt (t : HeightTile FLatticePaper.Site) (x : FLatticePaper.Site) : ℤ :=
  if h : x ∈ t.sites then t.height ⟨x, h⟩ else 0

/-- One insertion: the contact, the constancy of the increment on the overlap, the overlap size and the number of
new sites. The accumulated values are those of the earlier copies, so `f` is only compared on the overlap. -/
def stepCheck (S : Finset FLatticePaper.Site) (f : FLatticePaper.Site → ℤ) (c : HeightTile FLatticePaper.Site) : Bool × Bool × ℕ × ℕ :=
  let O := S ∩ c.sites
  (decide O.Nonempty, decide (∀ x ∈ O, ∀ y ∈ O, valAt c x - f x = valAt c y - f y),
    O.card, (c.sites \ S).card)

/-- The minimum of `g` over a finite set (the Lean insertion shift, `contactShift`). -/
def overlapMin (O : Finset FLatticePaper.Site) (g : FLatticePaper.Site → ℤ) : ℤ :=
  O.fold min 1000000000 g

/-- The chain with the Lean normalization: each new copy is shifted by the minimum of its increment over the overlap,
and the new sites take the shifted values. Returns (contact, constant increment on the overlap, overlap size,
new size, shift). -/
def chainNorm (S : Finset FLatticePaper.Site) (f : FLatticePaper.Site → ℤ) :
    List (HeightTile FLatticePaper.Site) → List (Bool × Bool × ℕ × ℕ × ℤ)
  | [] => []
  | c :: rest =>
    let O := S ∩ c.sites
    let d : FLatticePaper.Site → ℤ := fun x => valAt c x - f x
    let m := overlapMin O d
    (decide O.Nonempty, decide (∀ x ∈ O, ∀ y ∈ O, d x = d y), O.card, (c.sites \ S).card, m) ::
      chainNorm (S ∪ c.sites) (fun x => if x ∈ S then f x else valAt c x - m) rest

/-- Pairwise: for copies `i < j` of one schedule, the overlap size and whether the increment `j − i` is constant on it. -/
def pairChecks (cs : List (HeightTile FLatticePaper.Site)) : List (ℕ × ℕ × ℕ × Bool) :=
  let idx := List.range cs.length
  (idx.flatMap fun i => idx.filterMap fun j =>
    if i < j then
      match cs[i]?, cs[j]? with
      | some a, some b =>
        let O := a.sites ∩ b.sites
        let d : FLatticePaper.Site → ℤ := fun x => valAt b x - valAt a x
        some (i, j, O.card, decide (∀ x ∈ O, ∀ y ∈ O, d x = d y))
      | _, _ => none
    else none)

def copiesOf (w : Word) (parity : Parity) (sch : PlacedSchedule) : List (HeightTile FLatticePaper.Site) :=
  sch.first.val :: sch.copies

def reportWord (w : Word) : String :=
  match w.getLast? with
  | none => "empty"
  | some digit =>
    match evaluateNativeState w.dropLast with
    | .error e => s!"ERR {e}"
    | .ok st =>
      let parents := st.current.tiles.parentsFor digit
      let oddSch := ordinaryStandardSchedule parents w .odd
      let evenSch := ordinaryStandardSchedule parents w .even
      let oddCopies := copiesOf w .odd oddSch
      let evenCopies := copiesOf w .even evenSch
      let showCs (cs : List (HeightTile FLatticePaper.Site)) : String :=
        match cs with
        | [] => "[]"
        | c :: rest => toString (chainNorm c.sites (valAt c) rest)
      s!"odd {oddCopies.length} {showCs oddCopies} | even {evenCopies.length} {showCs evenCopies}"

def allLines : String :=
  String.intercalate "\n" ((gen 1 ++ gen 2 ++ gen 3).filter (fun w => w.any (· ≠ Digit.three)) |>.map
    (fun w => s!"{repr w} {reportWord w}"))

def pairLines : String :=
  String.intercalate "\n" ((gen 1 ++ gen 2 ++ gen 3).filter (fun w => w.any (· ≠ Digit.three)) |>.map
    (fun w => match w.getLast? with
      | none => "empty"
      | some digit =>
        match evaluateNativeState w.dropLast with
        | .error e => s!"ERR {e}"
        | .ok st =>
          let parents := st.current.tiles.parentsFor digit
          let oddCs := copiesOf w .odd (ordinaryStandardSchedule parents w .odd)
          let evenCs := copiesOf w .even (ordinaryStandardSchedule parents w .even)
          s!"PAIRS {repr w} odd {pairChecks oddCs} even {pairChecks evenCs}"))

#eval IO.println pairLines

end CopyDump
