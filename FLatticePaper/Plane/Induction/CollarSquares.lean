import FLatticePaper.Plane.Induction.W1Phase

/-! Task 72 (hcollar, collar squares): the child squares of the collar sides, written from the root `r = zTurn (c − l_v)`.

With `x = c.1 − l_v.1` and `y = c.2 − l_v.2` the root is `r = (−y, x − 1)`, and the three core squares of `W1Phase` give
the child squares `squareCorners` of the physical centre `c`:

* bottom (upper-left square of `c`): parent square `squareCorners (−y − 1) (x − 2)`, child square `squareCorners (c.1 − 1) c.2`;
* aligned V side with `ε = +1` (upper-right square of `c`): parent `squareCorners (−y − 1) (x − 1)`, child `squareCorners c.1 c.2`;
* aligned V side with `ε = −1` (lower-left square of `c`): parent `squareCorners (−y) (x − 2)`, child `squareCorners (c.1 − 1) (c.2 − 1)`.

The non-aligned V side uses the same three rules at the pricing point `y₀ = c − W·U` (`W·U` is the sheet shift of §2); the
root of `y₀` is `zTurn (y₀ − l_v)`. This file proves the membership of the root in the parent square and the child-square
identities, which are the arithmetic part of `sheet_private_square`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper FLatticePaper.AndOrRank

/-- The bottom root lies in its parent square `squareCorners (−y − 1) (x − 2)`, as its upper-right corner. -/
theorem bottom_root_mem (lv c : Site) :
    zTurn (c - lv) ∈ squareCorners (-(c.2 - lv.2) - 1) (c.1 - lv.1 - 2) := by
  have h : zTurn (c - lv) = ((-(c.2 - lv.2) - 1) + 1, (c.1 - lv.1 - 2) + 1) :=
    Prod.ext (by simp [zTurn]) (by simp [zTurn]; ring)
  rw [h]
  simp [squareCorners]

/-- The V-side (`ε = +1`) root lies in its parent square `squareCorners (−y − 1) (x − 1)`, as its right corner. -/
theorem vPlus_root_mem (lv c : Site) :
    zTurn (c - lv) ∈ squareCorners (-(c.2 - lv.2) - 1) (c.1 - lv.1 - 1) := by
  have h : zTurn (c - lv) = ((-(c.2 - lv.2) - 1) + 1, c.1 - lv.1 - 1) := by
    refine Prod.ext ?_ ?_ <;> simp [zTurn]
  rw [h]
  simp [squareCorners]

/-- The V-side (`ε = −1`) root lies in its parent square `squareCorners (−y) (x − 2)`, as its upper corner. -/
theorem vMinus_root_mem (lv c : Site) :
    zTurn (c - lv) ∈ squareCorners (-(c.2 - lv.2)) (c.1 - lv.1 - 2) := by
  have h : zTurn (c - lv) = (-(c.2 - lv.2), (c.1 - lv.1 - 2) + 1) :=
    Prod.ext (by simp [zTurn]) (by simp [zTurn]; ring)
  rw [h]
  simp [squareCorners]

/-- The child base of the bottom square: the sheet image of `squareCorners (−y − 1) (x − 2)` is `squareCorners (c.1 − 1) c.2`. -/
theorem bottom_child_base (lv c : Site) :
    ((c.1 - lv.1 - 2) + 1 + lv.1, -(-(c.2 - lv.2) - 1) - 1 + lv.2) = (c.1 - 1, c.2) := by
  ext <;> dsimp only <;> ring

/-- The child base of the V-side (`ε = +1`) square: the sheet image of `squareCorners (−y − 1) (x − 1)` is `squareCorners c.1 c.2`. -/
theorem vPlus_child_base (lv c : Site) :
    ((c.1 - lv.1 - 1) + 1 + lv.1, -(-(c.2 - lv.2) - 1) - 1 + lv.2) = (c.1, c.2) := by
  ext <;> dsimp only <;> ring

/-- The child base of the V-side (`ε = −1`) square: the sheet image of `squareCorners (−y) (x − 2)` is `squareCorners (c.1 − 1) (c.2 − 1)`. -/
theorem vMinus_child_base (lv c : Site) :
    ((c.1 - lv.1 - 2) + 1 + lv.1, -(-(c.2 - lv.2)) - 1 + lv.2) = (c.1 - 1, c.2 - 1) := by
  ext <;> dsimp only <;> ring

/-- The centre is the upper-right corner of the bottom child square `squareCorners (c.1 − 1) c.2`. -/
theorem bottom_centre_mem (c : Site) : c ∈ squareCorners (c.1 - 1) c.2 := by
  obtain ⟨x, y⟩ := c
  simp [squareCorners]

/-- The centre is the lower-left corner of the V-side (`ε = +1`) child square `squareCorners c.1 c.2`. -/
theorem vPlus_centre_mem (c : Site) : c ∈ squareCorners c.1 c.2 := by
  obtain ⟨x, y⟩ := c
  simp [squareCorners]

/-- The centre is the upper-right corner of the V-side (`ε = −1`) child square `squareCorners (c.1 − 1) (c.2 − 1)`. -/
theorem vMinus_centre_mem (c : Site) : c ∈ squareCorners (c.1 - 1) (c.2 - 1) := by
  obtain ⟨x, y⟩ := c
  simp [squareCorners]

/-- The centre is the upper-left corner of the lower-right (top-arc) square `squareCorners c.1 (c.2 − 1)`. -/
theorem top_centre_mem (c : Site) : c ∈ squareCorners c.1 (c.2 - 1) := by
  obtain ⟨x, y⟩ := c
  simp [squareCorners]

end FLatticePaper.Induction
