import FLatticePaper.Plane.Induction.SquareClauses
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.ParentCoordinates

/-! Task 45: the W1 constructor (archive `W1_CONSTRUCTOR.md`, §1 and the statement of W1Forced).

For a child with `n < d`, `L = d + n`, `T = d² + 2dn − n²` (the period denominator), the archive's §1 gives:
* the H spectrum `[a, b]`: `[2, L−2]` at even sites and `[n, d]` at odd sites;
* the V spectrum `[c, h]`: `[0, 2n]` at even sites and `[2−d+n, L−2]` at odd sites;
* the strict interior `E°`: `b − T < t < a` and `h < s < T + c`, with `t = n x − d y` and `s = L x + (d − n) y`.

The closed rectangle `closedRect` is the grade rectangle of `ChildFrame.closedPolygon` (E's extremes `a − T`, `b`, `c`, `T + h`). -/

namespace FLatticePaper.W1

open Farey FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.Induction

/-- The period denominator `T = d² + 2dn − n²`. -/
def w1T (n d : ℤ) : ℤ := d ^ 2 + 2 * d * n - n ^ 2

/-- `t(x, y) = n x − d y`. -/
def w1t (n d : ℤ) (z : Site) : ℤ := n * z.1 - d * z.2

/-- `s(x, y) = (d + n) x + (d − n) y`. -/
def w1s (n d : ℤ) (z : Site) : ℤ := (d + n) * z.1 + (d - n) * z.2

/-- The low H spectrum `a`: `2` at even sites, `n` at odd sites. -/
def w1a (n : ℤ) (z : Site) : ℤ := if EvenSite z then 2 else n

/-- The high H spectrum `b`: `L − 2` at even sites, `d` at odd sites. -/
def w1b (n d : ℤ) (z : Site) : ℤ := if EvenSite z then d + n - 2 else d

/-- The low V spectrum `c`: `0` at even sites, `2 − d + n` at odd sites. -/
def w1c (n d : ℤ) (z : Site) : ℤ := if EvenSite z then 0 else 2 - d + n

/-- The high V spectrum `h`: `2n` at even sites, `L − 2` at odd sites. -/
def w1h (n d : ℤ) (z : Site) : ℤ := if EvenSite z then 2 * n else d + n - 2

/-- **The strict interior `E°` of §1**: the open parity-resolved rectangle `b − T < t < a`, `h < s < T + c`. -/
def StrictInterior (n d : ℤ) (z : Site) : Prop :=
  w1b n d z - w1T n d < w1t n d z ∧ w1t n d z < w1a n z ∧
    w1h n d z < w1s n d z ∧ w1s n d z < w1T n d + w1c n d z

/-- The closed grade rectangle of `ChildFrame.closedPolygon` (with `T` the period denominator). -/
def closedRect (n d : ℤ) (z : Site) : Prop :=
  if EvenSite z then
    2 - w1T n d ≤ w1t n d z ∧ w1t n d z ≤ d + n - 2 ∧ 0 ≤ w1s n d z ∧ w1s n d z ≤ w1T n d + 2 * n
  else
    n - w1T n d ≤ w1t n d z ∧ w1t n d z ≤ d ∧ 2 - d + n ≤ w1s n d z ∧ w1s n d z ≤ w1T n d + d + n - 2

/-- A unit square whose corners are all strictly interior, with the derivation of `ForcedEdge` (unit rule) inside `R`. -/
inductive ForcedEdgeIn (F : Field) (R : Site → Prop) (seed : Site → Site → Prop) : Site → Site → Prop
  | seed {c i : Site} : seed c i → ForcedEdgeIn F R seed c i
  | unit {a b : ℤ} {c o : Site} (inside : Site → Site) (hR : ∀ c' ∈ squareCorners a b, R c')
      (hc : c ∈ squareCorners a b) (hw : laplacian F c = 0)
      (ho : o = incomingNeg c ∨ o = incomingPos c) (hout : o ∉ squareCorners a b)
      (hin : ∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1 ∨
        (laplacian F c' = 0 ∧ inside c' ∈ squareCorners a b ∧
          (inside c' = incomingNeg c' ∨ inside c' = incomingPos c')))
      (hforced : ∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = 0 →
        ForcedEdgeIn F R seed c' (inside c')) :
      ForcedEdgeIn F R seed c o

/-- A derivation whose squares lie in `R` is a derivation of `ForcedEdge`. -/
theorem forcedEdgeIn_forced {F : Field} {R : Site → Prop} {seed : Site → Site → Prop} {c i : Site}
    (h : ForcedEdgeIn F R seed c i) : ForcedEdge F seed c i := by
  induction h with
  | seed hs => exact ForcedEdge.seed hs
  | @unit a b c o inside _ hc hw ho hout hin _ ih =>
    exact ForcedEdge.unit inside hc hw ho hout hin (fun c' hc' hne h0 => ih c' hc' hne h0)

/-- **W1Forced (the statement of the W1 implication).** Every white of the strict interior is forced by unit propagation from no
seeds, by a derivation whose unit squares lie in the strict interior. -/
def W1Forced (n d : ℤ) (F : Field) : Prop :=
  ∀ z : Site, StrictInterior n d z → laplacian F z = 0 →
    ∃ o : Site, ForcedEdgeIn F (StrictInterior n d) (fun _ _ => False) z o

/-- The strict interior lies in the closed grade rectangle (`E°` inside `closedPolygon`), for a child with `1 ≤ n`, `n + 2 ≤ d`. -/
theorem strictInterior_closedRect {n d : ℤ} (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (z : Site)
    (h : StrictInterior n d z) : closedRect n d z := by
  simp only [StrictInterior, closedRect, w1b, w1a, w1h, w1c, w1T, w1t, w1s] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  split_ifs at h1 h2 h3 h4 ⊢
  · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The grade rectangle of a child frame is the closed rectangle of its numerator and denominator. -/
theorem closedPolygon_eq_closedRect (frame : ChildFrame) :
    frame.closedPolygon = {z | closedRect frame.child.num frame.child.den z} := by
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  ext z
  simp only [ChildFrame.closedPolygon, closedRect, ChildFrame.tGrade, ChildFrame.sGrade, w1t, w1s, w1T, Set.mem_setOf_eq,
    hT]

/-! Bridge to the child frame. The parent coordinate transform of §1 is w3's `ChildFrame` identities in
`Plane/Induction/ParentCoordinates.lean` (`periodDenominator_parentTGrade`, `periodDenominator_parentSGrade`, `parentC_mul_num`,
`parentC_mul_den`, `parentC_mul_L`); here they are restated in the integer grades `w1t`, `w1s`, `w1T` of this file. -/

theorem frame_tGrade_eq (frame : ChildFrame) (z : Site) :
    frame.tGrade z = w1t frame.child.num frame.child.den z := rfl

theorem frame_sGrade_eq (frame : ChildFrame) (z : Site) :
    frame.sGrade z = w1s frame.child.num frame.child.den z := rfl

theorem frame_periodDenominator_eq (frame : ChildFrame) :
    frame.child.periodDenominator = w1T frame.child.num frame.child.den :=
  (frame.child_facts).2.2.2.2

/-- **The parent H grade in the child grades (archive §1):** `T · t_p = C t + ε s`, with `t_p = N x − D y`. -/
theorem parent_transform_t (frame : ChildFrame) (z : Site) :
    w1T frame.child.num frame.child.den * frame.parentTGrade z =
      frame.parentC * w1t frame.child.num frame.child.den z + frame.eps * w1s frame.child.num frame.child.den z := by
  have h := frame.periodDenominator_parentTGrade z
  rw [frame_periodDenominator_eq, frame_tGrade_eq, frame_sGrade_eq] at h
  exact h

/-- **The parent V grade in the child grades (archive §1):** `T · s_p = C s + 2 ε t`, with `s_p = (D + N) x + (D − N) y`. -/
theorem parent_transform_s (frame : ChildFrame) (z : Site) :
    w1T frame.child.num frame.child.den * frame.parentSGrade z =
      frame.parentC * w1s frame.child.num frame.child.den z + 2 * frame.eps * w1t frame.child.num frame.child.den z := by
  have h := frame.periodDenominator_parentSGrade z
  rw [frame_periodDenominator_eq, frame_tGrade_eq, frame_sGrade_eq] at h
  exact h

/-- The parent H grade is the exact quotient `(C t + ε s) / T`, for a child with `T > 0`. -/
theorem parent_tGrade_div (frame : ChildFrame) (z : Site) :
    (frame.parentC * w1t frame.child.num frame.child.den z + frame.eps * w1s frame.child.num frame.child.den z) /
        w1T frame.child.num frame.child.den = frame.parentTGrade z := by
  have hT : 0 < w1T frame.child.num frame.child.den := by
    rw [← frame_periodDenominator_eq]
    exact Fraction.periodDenominator_pos (frame.valid.current_interior .even).inUnitInterval
  rw [← parent_transform_t frame z, Int.mul_ediv_cancel_left _ hT.ne']

end FLatticePaper.W1
