import FLatticePaper.Tiles.StackLocal

/-! A finite Boolean summary of the top of the local union, and its transition.

The window: rows `dy ∈ [-4, 3]` relative to the last plus position, columns `c ∈ [-2, 3]`. For each row: whether it is
nonempty, and which window columns it meets; for each pair of rows `dy, dy+1` with `dy ∈ [-4, 2]`: whether they share a
column. The transition `trans` computes the summary of the union after one more plus tile (and its shadow) from the summary
and the new letter. `okS` is the Boolean check that the new rows are convex and the pairs are linked; `reachList` is the
set of summaries reachable from the summaries of the words of length two, found by a bounded search and checked by
`decide`. -/

namespace FLatticePaper.Tiles

/-- The summary of a local union. Lists are indexed by rows `i ↦ dy = i - 4` (`i < 8`), columns `j ↦ c = j - 2`
(`j < 6`), and pairs `k ↦ (dy, dy+1)` with `dy = k - 4` (`k < 7`). -/
structure WS where
  lastL : Letter
  secondL : Letter
  ne : List Bool
  bits : List (List Bool)
  sh : List Bool
  deriving DecidableEq, Repr

/-- The row index of `dy`, when it lies in the window. -/
def rowIdx (dy : ℤ) : Option ℕ := if -4 ≤ dy ∧ dy ≤ 3 then some (dy + 4).toNat else none

/-- The column index of `c`, when it lies in the window. -/
def colIdx (c : ℤ) : Option ℕ := if -2 ≤ c ∧ c ≤ 3 then some (c + 2).toNat else none

/-- The pair index of `dy`, when `(dy, dy+1)` lies in the window. -/
def pairIdx (dy : ℤ) : Option ℕ := if -4 ≤ dy ∧ dy ≤ 2 then some (dy + 4).toNat else none

/-- The relative cells of a new plus tile and its shadow, relative to the new anchor. -/
def relCells (o : Orientation) (a : Letter) (ep : Bool) : List Site :=
  tileSitesOf a ep ++ (tileSitesOf a ep).map (fun c => c + shadowO o a)

/-- Whether the new tile is enlarged (horizontal, one-tile after one-tile). -/
def enlargeNew (o : Orientation) (s : WS) (a : Letter) : Bool :=
  decide (o = Orientation.horizontal) && decide (s.lastL = Letter.q) && decide (a = Letter.q)

/-- The new nonempty flag of row `i`. -/
def newNe (o : Orientation) (s : WS) (a : Letter) (i : ℕ) : Bool :=
  let sy := (plusStepO o a).2
  let dy2 : ℤ := (i : ℤ) - 4
  let oldNe : Bool := match rowIdx (dy2 + sy) with
    | some k => s.ne.getD k false
    | none => false
  let nN : Bool := (relCells o a (enlargeNew o s a)).any (fun c => decide (c.2 = dy2))
  oldNe || nN

/-- The new window bit of row `i`, column `j`. -/
def newBit (o : Orientation) (s : WS) (a : Letter) (i j : ℕ) : Bool :=
  let sx := (plusStepO o a).1
  let sy := (plusStepO o a).2
  let dy2 : ℤ := (i : ℤ) - 4
  let c : ℤ := (j : ℤ) - 2
  let oldB : Bool := match rowIdx (dy2 + sy), colIdx (c + sx) with
    | some k, some l => (s.bits.getD k []).getD l false
    | _, _ => false
  oldB || (relCells o a (enlargeNew o s a)).any (fun p => decide (p = (c, dy2)))

/-- The new window bits of row `i`. -/
def newRowBits (o : Orientation) (s : WS) (a : Letter) (i : ℕ) : List Bool :=
  (List.range 6).map (fun j => newBit o s a i j)

/-- The new share flag of the pair with index `k`. -/
def newSh (o : Orientation) (s : WS) (a : Letter) (k : ℕ) : Bool :=
  let sy := (plusStepO o a).2
  let dy : ℤ := (k : ℤ) - 4
  let oldS : Bool := match pairIdx (dy + sy) with
    | some q => s.sh.getD q false
    | none => false
  oldS || (List.range 6).any (fun j => newBit o s a k j && newBit o s a (k + 1) j)

/-- The transition of the summary by one letter. -/
def transWS (o : Orientation) (s : WS) (a : Letter) : WS :=
  { lastL := a
    secondL := s.secondL
    ne := (List.range 8).map (fun i => newNe o s a i)
    bits := (List.range 8).map (fun i => newRowBits o s a i)
    sh := (List.range 7).map (fun k => newSh o s a k) }

/-- No gap in a window row: the true columns form an interval. -/
def gapFree (l : List Bool) : Bool :=
  (List.range 6).all fun j1 => (List.range 6).all fun j2 => (List.range 6).all fun j3 =>
    !(decide (j1 < j2) && decide (j2 < j3) && l.getD j1 false && l.getD j3 false && !(l.getD j2 false))

/-- The old row (before the step) has window cells. -/
def oldRowHasBits (o : Orientation) (s : WS) (a : Letter) (i : ℕ) : Bool :=
  let sy := (plusStepO o a).2
  let dy2 : ℤ := (i : ℤ) - 4
  match rowIdx (dy2 + sy) with
  | some k => (s.bits.getD k []).any id
  | none => false

/-- The check of a new row: a far-only old row cannot receive new cells, and the window cells form an interval. -/
def rowOk (o : Orientation) (s : WS) (a : Letter) (i : ℕ) : Bool :=
  let sy := (plusStepO o a).2
  let dy2 : ℤ := (i : ℤ) - 4
  let oldNe : Bool := match rowIdx (dy2 + sy) with
    | some k => s.ne.getD k false
    | none => false
  let nN : Bool := (relCells o a (enlargeNew o s a)).any (fun c => decide (c.2 = dy2))
  !(oldNe && !(oldRowHasBits o s a i) && nN) && gapFree (newRowBits o s a i)

/-- The check of a pair: if both rows are nonempty, they share a column. -/
def pairOk (o : Orientation) (s : WS) (a : Letter) (k : ℕ) : Bool :=
  let nk := newNe o s a k
  let nk1 := newNe o s a (k + 1)
  !(nk && nk1) || newSh o s a k

/-- All checks for one step. -/
def okS (o : Orientation) (s : WS) (a : Letter) : Bool :=
  (List.range 8).all (fun i => rowOk o s a i) && (List.range 7).all (fun k => pairOk o s a k)

/-- The summary of the union of the first `m` letters (`m ≥ 2`), with anchor `posO (m-1)`. -/
def stateOf (o : Orientation) (ℓ : ℕ → Letter) (m : ℕ) : WS :=
  { lastL := ℓ (m - 1)
    secondL := ℓ 1
    ne := (List.range 8).map (fun i => decide
      ((lamO o ℓ m).filter (fun p => p.2 = (posO o ℓ (m - 1)).2 + ((i : ℤ) - 4))).Nonempty)
    bits := (List.range 8).map (fun i => (List.range 6).map (fun j => decide
      (((posO o ℓ (m - 1)).1 + ((j : ℤ) - 2), (posO o ℓ (m - 1)).2 + ((i : ℤ) - 4)) ∈ lamO o ℓ m)))
    sh := (List.range 7).map (fun k => decide
      (((lamO o ℓ m).image Prod.fst).filter (fun x =>
        (x, (posO o ℓ (m - 1)).2 + ((k : ℤ) - 4)) ∈ lamO o ℓ m ∧
        (x, (posO o ℓ (m - 1)).2 + ((k : ℤ) - 4) + 1) ∈ lamO o ℓ m)).Nonempty) }

/-- The letter sequence with first letters `a b` (only the first two letters matter for the summary of length two). -/
def ell2 (a b : Letter) : ℕ → Letter := fun k => if k = 0 then a else b

/-- Breadth-first closure of the summaries under `transWS`, with a fuel bound. -/
def bfs (o : Orientation) : ℕ → List WS → List WS → List WS
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | n + 1, seen, s :: rest =>
    let nexts := ([transWS o s Letter.p, transWS o s Letter.q].filter (fun t => !seen.contains t)).eraseDups
    bfs o n (seen ++ nexts) (rest ++ nexts)

/-- The summaries of the words of length two. -/
def baseWS (o : Orientation) : List WS :=
  ([(Letter.p, Letter.p), (Letter.p, Letter.q), (Letter.q, Letter.p), (Letter.q, Letter.q)].map
    (fun ab => stateOf o (ell2 ab.1 ab.2) 2)).eraseDups

/-- The reachable summaries. -/
def reachList (o : Orientation) : List WS := bfs o 200 (baseWS o) (baseWS o)

set_option maxHeartbeats 400000 in
theorem reach_base_h : ∀ a ∈ [Letter.p, Letter.q], ∀ b ∈ [Letter.p, Letter.q], stateOf .horizontal (ell2 a b) 2 ∈ reachList .horizontal := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem reach_closed_h : ∀ s ∈ reachList .horizontal, ∀ a ∈ [Letter.p, Letter.q],
    okS .horizontal s a = true ∧ transWS .horizontal s a ∈ reachList .horizontal := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem reach_base_v : ∀ a ∈ [Letter.p, Letter.q], ∀ b ∈ [Letter.p, Letter.q], stateOf .vertical (ell2 a b) 2 ∈ reachList .vertical := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem reach_closed_v : ∀ s ∈ reachList .vertical, ∀ a ∈ [Letter.p, Letter.q],
    okS .vertical s a = true ∧ transWS .vertical s a ∈ reachList .vertical := by
  decide +kernel

end FLatticePaper.Tiles
