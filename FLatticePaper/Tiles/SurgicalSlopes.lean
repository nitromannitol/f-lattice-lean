import FLatticePaper.Tiles.ZeroOneOdometers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # The slope table of the surgical text, beside the old table

`ZeroOneOdometers.slopeDiff` is the table used by the earlier proofs (`respectsB`, `deltaOf`). On horizontal strings it is the
table of a *reversed* horizontal string: `(p,q) ↦ -1/2`, `(q,p) ↦ 1/2`. The surgical text (lines 1563-1570, operator fix E05)
gives the forward horizontal table `pq ↦ 1/2`, `qp ↦ -1/2`, and says the signs of `pq` and `qp` are exchanged for a reversed
horizontal string (line 1582). The vertical tables agree.

`surgicalSlopeDiff` is the surgical table. The old table is not changed. -/

namespace FLatticePaper.Tiles

/-- The slope change `s(o_{i+1}) - s(o_i)` of consecutive zero-one odometers of the surgical text, for the letters `(a, b)` of
the string of orientation `o`, reversed when `rev` (eq:zero-one-odometer_slopes-horizontal, -vert, lines 1563-1582). -/
def surgicalSlopeDiff (o : Orientation) (rev : Bool) (a b : Letter) : ℚ × ℚ :=
  match o, rev, a, b with
  | .horizontal, false, .p, .q => (1 / 2, 0)
  | .horizontal, false, .q, .p => (-1 / 2, 0)
  | .horizontal, true, .p, .q => (-1 / 2, 0)
  | .horizontal, true, .q, .p => (1 / 2, 0)
  | .horizontal, _, .p, .p => (0, 0)
  | .horizontal, _, .q, .q => (0, 0)
  | .vertical, _, .p, .p => (0, -1)
  | .vertical, _, .q, .q => (1, -1)
  | .vertical, _, .p, .q => (1 / 2, -1)
  | .vertical, _, .q, .p => (1 / 2, -1)

/-- The old table is the surgical table of a reversed horizontal string (on horizontal letters). -/
theorem slopeDiff_eq_reversed_horizontal (a b : Letter) :
    slopeDiff .horizontal a b = surgicalSlopeDiff .horizontal true a b := by
  cases a <;> cases b <;> rfl

/-- The old table is the surgical table of a vertical string (on all letters). -/
theorem slopeDiff_eq_vertical (rev : Bool) (a b : Letter) :
    slopeDiff .vertical a b = surgicalSlopeDiff .vertical rev a b := by
  cases rev <;> cases a <;> cases b <;> rfl

/-- The forward horizontal table differs from the old one on `(p,q)` and `(q,p)`: the old table is the reversed one. -/
theorem slopeDiff_ne_forward_horizontal :
    slopeDiff .horizontal .p .q ≠ surgicalSlopeDiff .horizontal false .p .q := by
  intro h
  have h1 := congrArg Prod.fst h
  simp only [slopeDiff, surgicalSlopeDiff] at h1
  linarith

end FLatticePaper.Tiles
