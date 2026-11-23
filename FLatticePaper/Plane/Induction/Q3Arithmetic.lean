import FLatticePaper.Plane.Induction.ParentCoordinates
import Mathlib.Tactic.FieldSimp

/-! Task 59, step 2 (first Q3 piece): the arithmetic of fix Q3.md, paragraphs 4 and 9–10.

* `sGrade_parentPeriod`: the parent's V period `U_p = 2(D, N)` has child grade `s(U_p) = 2C`, the scalar `B_0` of the
  common-chart argument.
* `vBlock_floor_gap`: `(d−n)l/d − (D−N)l/D = ε l/(D d)` (rational identity behind the V-block floors).
* `index_mem_zero_one_of_spectrum`: if `l ≤ s ≤ h`, `h − l < B`, and `l − s ≤ i·B ≤ B + h − s`, then `i ∈ {0, 1}`
  (the spectrum inequality that forces the index `i`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem index_mem_zero_one_of_spectrum (i B l s h : ℤ) (hB : 0 < B) (hwidth : h - l < B)
    (hl : l ≤ s) (hh : s ≤ h) (hlo : l - s ≤ i * B) (hhi : i * B ≤ B + h - s) :
    i = 0 ∨ i = 1 := by
  by_contra hne
  rcases (show i ≤ -1 ∨ 2 ≤ i by omega) with h1 | h1
  · have hiB : i * B ≤ -B := by nlinarith
    linarith
  · have hiB : 2 * B ≤ i * B := by nlinarith
    linarith

namespace ChildFrame
variable (frame : ChildFrame)

/-- The parent's V period `U_p = 2(D, N)` has child grade `s(U_p) = 2C`. -/
theorem sGrade_parentPeriod :
    frame.sGrade (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) = 2 * frame.parentC := by
  unfold sGrade parentC
  dsimp only
  ring

/-- The V-block floor identity `(d−n)l/d − (D−N)l/D = ε l/(D d)` as rationals. -/
theorem vBlock_floor_gap (l : ℚ) (hd : (frame.child.den : ℚ) ≠ 0) (hD : (frame.parents.odd.den : ℚ) ≠ 0) :
    ((frame.child.den : ℚ) - frame.child.num) * l / frame.child.den -
        ((frame.parents.odd.den : ℚ) - frame.parents.odd.num) * l / frame.parents.odd.den =
      (frame.eps : ℚ) * l / (frame.parents.odd.den * frame.child.den) := by
  rw [frame.eps_eq]
  push_cast
  field_simp
  ring

end ChildFrame

end FLatticePaper.Induction
