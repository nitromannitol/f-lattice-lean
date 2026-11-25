import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! # W4 (Q35): a free V site of the child is not strictly interior

The left V arc `freeV` of a child frame consists of closed-polygon sites whose left neighbour lies outside the polygon, with the V
spectrum (in particular `s` even). `StrictInterior` (W1Constructor) is the open region in the grades `t = n x₁ − d x₂` and
`s = (d + n) x₁ + (d − n) x₂`. A left V site is a boundary site, so it is not strictly interior. This is the boundary contradiction of
Q35's `j > 0` paragraph (`c = v_j` on the left boundary, against `hSI`). -/

namespace FLatticePaper.W4Boundary

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

/-- The even-site core: a strict even site has its left (odd) neighbour inside the rectangle. -/
theorem core_even_left (n d T t s : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hs2 : s % 2 = 0)
    (h1 : d + n - 2 - T < t) (h2 : t < 2) (h3 : 2 * n < s) (h4 : s < T)
    (hout : t - n < n - T ∨ d < t - n ∨ s - (d + n) < 2 - d + n ∨ T + d + n - 2 < s - (d + n)) : False := by
  rcases hout with h | h | h | h <;> omega

/-- The odd-site core: a strict odd site has its left (even) neighbour inside the rectangle. -/
theorem core_odd_left (n d T t s : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hs2 : s % 2 = 0) (hdn : (d + n) % 2 = 0)
    (h1 : d - T < t) (h2 : t < n) (h3 : d + n - 2 < s) (h4 : s < T + (2 - d + n))
    (hout : t - n < 2 - T ∨ d + n - 2 < t - n ∨ s - (d + n) < 0 ∨ T + 2 * n < s - (d + n)) : False := by
  rcases hout with h | h | h | h <;> omega

theorem w1t_left (n d : ℤ) (z : Site) : w1t n d (z.1 - 1, z.2) = w1t n d z - n := by
  unfold w1t; ring

theorem w1s_left (n d : ℤ) (z : Site) : w1s n d (z.1 - 1, z.2) = w1s n d z - (d + n) := by
  unfold w1s; ring

theorem evenSite_left (z : Site) : EvenSite (z.1 - 1, z.2) ↔ ¬ EvenSite z := by
  unfold EvenSite
  simp only
  omega

/-- **A free V site is not strictly interior.** Its left neighbour is outside the closed rectangle. -/
theorem freeV_not_strict (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) :
    ¬ StrictInterior frame.child.num frame.child.den z := by
  obtain ⟨-, hout, hvs⟩ := hz
  have hs2 : w1s frame.child.num frame.child.den z % 2 = 0 := by
    have h := hvs.1
    rw [frame_sGrade_eq] at h
    exact h
  have hT : frame.child.periodDenominator = w1T frame.child.num frame.child.den := frame_periodDenominator_eq frame
  have hn := frame.child_facts
  have hdn : (frame.child.den + frame.child.num) % 2 = 0 := by
    have h : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
    omega
  have hout' : ¬ closedRect frame.child.num frame.child.den (z.1 - 1, z.2) := by
    rw [closedPolygon_eq_closedRect frame] at hout
    exact hout
  intro hSI
  unfold StrictInterior at hSI
  unfold closedRect at hout'
  rw [w1t_left, w1s_left] at hout'
  by_cases he : EvenSite z
  · have hne : ¬ EvenSite (z.1 - 1, z.2) := fun h => (evenSite_left z).mp h he
    rw [if_neg hne] at hout'
    simp only [w1a, w1b, w1c, w1h, if_pos he] at hSI
    exact core_even_left (n := frame.child.num) (d := frame.child.den) (T := w1T frame.child.num frame.child.den) (t := w1t frame.child.num frame.child.den z) (s := w1s frame.child.num frame.child.den z) (by omega) (by omega) hs2 hSI.1 hSI.2.1 hSI.2.2.1 (by simpa using hSI.2.2.2)
      (by simp only [not_and_or, not_le] at hout'; exact hout')
  · have hne : EvenSite (z.1 - 1, z.2) := (evenSite_left z).mpr he
    rw [if_pos hne] at hout'
    simp only [w1a, w1b, w1c, w1h, if_neg he] at hSI
    exact core_odd_left (n := frame.child.num) (d := frame.child.den) (T := w1T frame.child.num frame.child.den) (t := w1t frame.child.num frame.child.den z) (s := w1s frame.child.num frame.child.den z) (by omega) (by omega) hs2 hdn hSI.1 hSI.2.1 hSI.2.2.1 hSI.2.2.2
      (by simp only [not_and_or, not_le] at hout'; exact hout')

/-- **The left boundary in grades.** A site with `s ≤ w1h` (the initial left V arc, `s ∈ [w1c, w1h]`) is not strictly interior. -/
theorem not_strict_of_s_le_h (n d : ℤ) (z : Site) (h : w1s n d z ≤ w1h n d z) : ¬ StrictInterior n d z :=
  fun hS => absurd hS.2.2.1 (not_lt.mpr h)

/-- The grade `s` of the translate `z + (d, n)` is `s(z) + T`, and the parity of `z + (d, n)` is that of `z` (`d + n` even). -/
theorem w1s_add_U (n d : ℤ) (z : Site) : w1s n d (z.1 + d, z.2 + n) = w1s n d z + w1T n d := by
  unfold w1s w1T; ring

theorem evenSite_add_U (n d : ℤ) (hdn : (d + n) % 2 = 0) (z : Site) :
    EvenSite (z.1 + d, z.2 + n) ↔ EvenSite z := by
  unfold EvenSite
  simp only
  omega

/-- **The right boundary in grades.** If `w1c(z) ≤ s(z)` (the initial left V arc), the translate `z + (d, n)` is not strictly interior:
its grade `s` is `s(z) + T` and the bound is `T + w1c`. -/
theorem not_strict_of_shift_U (n d : ℤ) (hdn : (d + n) % 2 = 0) (z : Site) (h : w1c n d z ≤ w1s n d z) :
    ¬ StrictInterior n d (z.1 + d, z.2 + n) := by
  intro hS
  unfold StrictInterior at hS
  have hc : w1c n d (z.1 + d, z.2 + n) = w1c n d z := by
    unfold w1c
    by_cases he : EvenSite z
    · have he' := (evenSite_add_U n d hdn z).mpr he
      simp only [if_pos he, if_pos he']
    · have he' : ¬ EvenSite (z.1 + d, z.2 + n) := fun h' => he ((evenSite_add_U n d hdn z).mp h')
      simp only [if_neg he, if_neg he']
  have hs := hS.2.2.2
  rw [w1s_add_U, hc] at hs
  linarith

end FLatticePaper.W4Boundary
