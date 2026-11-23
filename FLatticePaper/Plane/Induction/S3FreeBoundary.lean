import FLatticePaper.Plane.Induction.S3Canonical

/-! Task 58, step 1: the free H/V boundary of a child frame and its prescribed directions (fix Q1, paragraph 3).

The sites are the representatives on the closed polygon `E` of the frame, with `L = d + n`.

* `hSpectrum`, `vSpectrum`: the H trace grades `t` (even `2, …, L-2`, odd `n, …, d`) and the V cut grades `s`
  (even `0, …, 2n`, and even `2-d+n, …, L-2`). Both parts are parity classes, since `n` and `d` are odd.
* `freeH`: the bottom boundary of `E` with `t` in the H spectrum; ordered by `x` it is `H_0, …, H_{d-1}`.
* `freeV`: the left boundary of `E` with `s` in the V spectrum; ordered by `y` it is `V_0, …, V_{L-1}`.
* The four special sites: `H_0 = (1,0)`, `H_{d-1} = (d, n-1)`, `V_0 = (0,0)`, `V_{L-1} = (n-d+1, n+d-1)`.
  They are the values checked on all words of length at most 4 by `scripts/s3_free_check.py`.
* `prescribedH η z`, `prescribedV η z`: the prescribed kept direction (the kept input is `z + prescribed`),
  for the horizontal sign minus and the vertical sign `η`. `EvenSite` is the site parity.

Only representatives in `E` are described. Deck translates are not included; the numerics check `η = 1` only. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- `H_0 = (1,0)`. -/
def hFirst : Site := (1, 0)

/-- `V_0 = (0,0)`. -/
def vFirst : Site := (0, 0)

namespace ChildFrame
variable (frame : ChildFrame)

/-- The H spectrum: `t` even in `[2, L-2]`, or `t` odd in `[n, d]`. -/
def hSpectrum (t : ℤ) : Prop :=
  (t % 2 = 0 ∧ 2 ≤ t ∧ t ≤ frame.child.den + frame.child.num - 2) ∨
    (t % 2 = 1 ∧ frame.child.num ≤ t ∧ t ≤ frame.child.den)

/-- The V spectrum: `s` even in `[0, 2n]`, or `s` even in `[2-d+n, L-2]`. -/
def vSpectrum (s : ℤ) : Prop :=
  s % 2 = 0 ∧
    ((0 ≤ s ∧ s ≤ 2 * frame.child.num) ∨
      (2 - frame.child.den + frame.child.num ≤ s ∧ s ≤ frame.child.den + frame.child.num - 2))

/-- The free H trace: the bottom boundary of `E` with `t` in the H spectrum. -/
def freeH : Set Site :=
  {z | z ∈ frame.closedPolygon ∧ (z.1, z.2 - 1) ∉ frame.closedPolygon ∧ frame.hSpectrum (frame.tGrade z)}

/-- The free V cut: the left boundary of `E` with `s` in the V spectrum. -/
def freeV : Set Site :=
  {z | z ∈ frame.closedPolygon ∧ (z.1 - 1, z.2) ∉ frame.closedPolygon ∧ frame.vSpectrum (frame.sGrade z)}

/-- `H_{d-1} = (d, n-1)`. -/
def hLast : Site := (frame.child.den, frame.child.num - 1)

/-- `V_{L-1} = V + (1,-1)` with `V = (n-d, n+d)`. -/
def vLast : Site := (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1)

/-- The prescribed direction on a free H site: `-η` north at `H_0`, north at `H_{d-1}`, east at even internal sites,
north at odd internal sites. -/
def prescribedH (η : ℤ) (z : Site) : Site :=
  if z = hFirst then (0, -η)
  else if z = frame.hLast then (0, 1)
  else if EvenSite z then (1, 0) else (0, 1)

/-- The prescribed direction on a free V site: east at `V_0`, `η` east at `V_{L-1}`, `η` east at even internal sites,
`-η` north at odd internal sites. -/
def prescribedV (η : ℤ) (z : Site) : Site :=
  if z = vFirst then (1, 0)
  else if z = frame.vLast then (η, 0)
  else if EvenSite z then (η, 0) else (0, -η)

theorem prescribedH_hFirst (η : ℤ) : frame.prescribedH η hFirst = (0, -η) := by
  simp [prescribedH]

theorem prescribedV_vFirst (η : ℤ) : frame.prescribedV η vFirst = (1, 0) := by
  simp [prescribedV]

theorem prescribedH_unit (η : ℤ) (hη : η = 1 ∨ η = -1) (z : Site) :
    frame.prescribedH η z = (1, 0) ∨ frame.prescribedH η z = (-1, 0) ∨
      frame.prescribedH η z = (0, 1) ∨ frame.prescribedH η z = (0, -1) := by
  unfold prescribedH
  split_ifs <;> rcases hη with rfl | rfl <;> simp

theorem prescribedV_unit (η : ℤ) (hη : η = 1 ∨ η = -1) (z : Site) :
    frame.prescribedV η z = (1, 0) ∨ frame.prescribedV η z = (-1, 0) ∨
      frame.prescribedV η z = (0, 1) ∨ frame.prescribedV η z = (0, -1) := by
  unfold prescribedV
  split_ifs <;> rcases hη with rfl | rfl <;> simp

end ChildFrame

end FLatticePaper.Induction
