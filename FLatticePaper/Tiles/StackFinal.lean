import FLatticePaper.Tiles.StackGap

/-! The final union of an almost palindrome: the local union `lamO o ℓ (n - 1)` of its first `n - 1` letters together with
the last plus tile and the final minus tile. Its summary check is decided over the reachable summaries whose two end
letters mirror (`lastL = secondL`), which is exactly the almost-palindrome condition on the first and last interior
letters (numerically: the unrestricted check fails, the mirrored one holds for all words of length at most 14). -/

namespace FLatticePaper.Tiles

/-- The letter of the last plus tile: `p` horizontally, `q` vertically. -/
def lastLetter : Orientation → Letter
  | .horizontal => .p
  | .vertical => .q

/-- The relative cells of the final pieces (the last plus tile and the final minus tile), relative to the last anchor.
The flag of the final minus tile is the second letter (horizontal). -/
def finRel (o : Orientation) (l1 : Letter) : List Site :=
  match o with
  | .horizontal => tileSitesOf .p false ++ (tileSitesOf .q (decide (l1 = Letter.q))).map (fun c => c + ((1 : ℤ), (-1 : ℤ)))
  | .vertical => tileSitesOf .q false ++ (tileSitesOf .p false).map (fun c => c + ((1 : ℤ), (0 : ℤ)))

/-- The row-nonempty flag of the final union. -/
def newNeF (o : Orientation) (s : WS) (a : Letter) (i : ℕ) : Bool :=
  let sy := (plusStepO o a).2
  let dy2 : ℤ := (i : ℤ) - 4
  let oldNe : Bool := match rowIdx (dy2 + sy) with
    | some k => s.ne.getD k false
    | none => false
  let nN : Bool := (finRel o s.secondL).any (fun c => decide (c.2 = dy2))
  oldNe || nN

/-- The window bit of the final union. -/
def newBitF (o : Orientation) (s : WS) (a : Letter) (i j : ℕ) : Bool :=
  oldBitAt o s a i j || (finRel o s.secondL).any
    (fun p => decide (p = (((j : ℤ) - 2), ((i : ℤ) - 4))))

def newRowBitsF (o : Orientation) (s : WS) (a : Letter) (i : ℕ) : List Bool :=
  (List.range 6).map (fun j => newBitF o s a i j)

/-- The pair-share flag of the final union. -/
def newShF (o : Orientation) (s : WS) (a : Letter) (k : ℕ) : Bool :=
  let sy := (plusStepO o a).2
  let dy : ℤ := (k : ℤ) - 4
  let oldS : Bool := match pairIdx (dy + sy) with
    | some q => s.sh.getD q false
    | none => false
  oldS || (List.range 6).any (fun j => newBitF o s a k j && newBitF o s a (k + 1) j)

/-- The gap check of the final union. -/
def gapOkF (o : Orientation) (s : WS) (a : Letter) (i : ℕ) : Bool :=
  let sy := (plusStepO o a).2
  let dy2 : ℤ := (i : ℤ) - 4
  let oldNe : Bool := match rowIdx (dy2 + sy) with
    | some k => s.ne.getD k false
    | none => false
  let nN : Bool := (finRel o s.secondL).any (fun c => decide (c.2 = dy2))
  !(oldNe && nN) || oldRowIn o s a i

def rowOkF (o : Orientation) (s : WS) (a : Letter) (i : ℕ) : Bool :=
  gapOkF o s a i && gapFree (newRowBitsF o s a i)

def pairOkF (o : Orientation) (s : WS) (a : Letter) (k : ℕ) : Bool :=
  let nk := newNeF o s a k
  let nk1 := newNeF o s a (k + 1)
  !(nk && nk1) || newShF o s a k

/-- All checks of the final union. -/
def okF (o : Orientation) (s : WS) : Bool :=
  (List.range 8).all (fun i => rowOkF o s (lastLetter o) i) &&
    (List.range 7).all (fun k => pairOkF o s (lastLetter o) k)

set_option maxHeartbeats 400000 in
theorem okF_h : ∀ s ∈ reachList .horizontal, s.lastL = s.secondL → okF .horizontal s = true := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem okF_v : ∀ s ∈ reachList .vertical, s.lastL = s.secondL → okF .vertical s = true := by
  decide +kernel

end FLatticePaper.Tiles
