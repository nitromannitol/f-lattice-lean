import FLatticePaper.Plane.Induction.ConeRoot
import FLatticePaper.Plane.Induction.RotatedCap
import FLatticePaper.Plane.Induction.FanPropagation

/-! # The cone bounds of a fan exit (Q41 section 3, step 3)

A contacting exit `u` of a fan node `q` (the east input of an even node, a vertical input of an odd node) satisfies, at the native site
`Zs u = (−u_2, u_1 − 1)`: the second coordinate is at least `w_2 + 1` (the apex's first coordinate) and the coordinate sum is at least 1,
given the cone bounds of `q` and `w_1 + w_2 ≥ 2` (the apex `b = (w_2 + 1, −w_1)`). -/

namespace FLatticePaper.FanExitBounds

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.CapRay FLatticePaper.RotatedCap

theorem exit_bounds {w : Site} {K : ℕ} (hw12 : 2 ≤ w.1 + w.2) {q u : Site}
    (hq : ConeRoot (w.2 + 1, -w.1) K q)
    (hu : (EvenSite q ∧ u = incomingPos q) ∨ (¬ EvenSite q ∧ (u = incomingNeg q ∨ u = incomingPos q))) :
    w.2 + 1 ≤ (Zs u).2 ∧ 1 ≤ (Zs u).1 + (Zs u).2 := by
  obtain ⟨hc1, -, hev, hodd⟩ := hq
  rcases hu with ⟨he, rfl⟩ | ⟨ho, hu⟩
  · -- even node, east input u = q + (1,0)
    have hp : incomingPos q = (q.1 + 1, q.2) := by
      unfold incomingPos; rw [if_pos he]
    rw [hp]
    have h := hev he
    unfold Zs
    simp only
    constructor <;> omega
  · -- odd node, a vertical input
    rcases hu with rfl | rfl
    · have hn : incomingNeg q = (q.1, q.2 - 1) := by
        unfold incomingNeg; rw [if_neg ho]
      rw [hn]
      have h := hodd ho
      unfold Zs
      simp only
      constructor <;> omega
    · have hp : incomingPos q = (q.1, q.2 + 1) := by
        unfold incomingPos; rw [if_neg ho]
      rw [hp]
      have h := hodd ho
      unfold Zs
      simp only
      constructor <;> omega

end FLatticePaper.FanExitBounds
