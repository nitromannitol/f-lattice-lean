import FLatticePaper.Tiles.StackWindow

/-! The row check that makes the summary sufficient for row convexity.

A row of the new union that already has cells of the old union and receives new cells must already have an old cell
inside the new window: otherwise the old cells and the new window cells could be separated by a gap. `gapOk` is this
check on the summary. It is decided on all reachable summaries, and `okS2` strengthens `okS` with it. -/

namespace FLatticePaper.Tiles

/-- The old window bit at the new window position `(i, j)`: whether the old union has a cell there. -/
def oldBitAt (o : Orientation) (s : WS) (a : Letter) (i j : ℕ) : Bool :=
  let sx := (plusStepO o a).1
  let sy := (plusStepO o a).2
  let dy2 : ℤ := (i : ℤ) - 4
  let c : ℤ := (j : ℤ) - 2
  match rowIdx (dy2 + sy), colIdx (c + sx) with
  | some k, some l => (s.bits.getD k []).getD l false
  | _, _ => false

/-- Whether the old union has a cell inside the new window in row `i`. -/
def oldRowIn (o : Orientation) (s : WS) (a : Letter) (i : ℕ) : Bool :=
  (List.range 6).any (fun j => oldBitAt o s a i j)

/-- The gap check of row `i`: an old row that is nonempty and receives new cells has an old cell in the new window. -/
def gapOk (o : Orientation) (s : WS) (a : Letter) (i : ℕ) : Bool :=
  let sy := (plusStepO o a).2
  let dy2 : ℤ := (i : ℤ) - 4
  let oldNe : Bool := match rowIdx (dy2 + sy) with
    | some k => s.ne.getD k false
    | none => false
  let nN : Bool := (relCells o a (enlargeNew o s a)).any (fun c => decide (c.2 = dy2))
  !(oldNe && nN) || oldRowIn o s a i

/-- The row checks of one step, strengthened by the gap check. -/
def rowOk2 (o : Orientation) (s : WS) (a : Letter) (i : ℕ) : Bool :=
  gapOk o s a i && gapFree (newRowBits o s a i)

/-- All checks for one step, with the gap check. -/
def okS2 (o : Orientation) (s : WS) (a : Letter) : Bool :=
  (List.range 8).all (fun i => rowOk2 o s a i) && (List.range 7).all (fun k => pairOk o s a k)

set_option maxHeartbeats 400000 in
theorem okS2_h : ∀ s ∈ reachList .horizontal, ∀ a ∈ [Letter.p, Letter.q], okS2 .horizontal s a = true := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem okS2_v : ∀ s ∈ reachList .vertical, ∀ a ∈ [Letter.p, Letter.q], okS2 .vertical s a = true := by
  decide +kernel

end FLatticePaper.Tiles
