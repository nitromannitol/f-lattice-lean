import FLatticePaper.Plane.Induction.HarmI2
import FLatticePaper.Plane.Induction.ZoneI1

/-! # The frame-level harmonic region of I2 (task 49, the wrapper of the harmonic step)

The other sheet is at least `h₀` on the harmonic band `E ∩ {s ≤ 2L − 1}` of the word, for both signs of `ε`, from the strong
estimates of the earlier conjugate. The parent step `f(u) ≤ f(u − U_q)` is a named input in the form of `ParentStepSign`.
-/

namespace FLatticePaper.Induction
open Farey FLatticePaper

namespace HarmWrap

/-- The sheet `A` in coordinates: its shift is `(1 − W) U_q`. -/
theorem sheetA_expr (V : ChildFrame) (Fp : Site → ℤ) (z : Site) :
    V.sheetA Fp z = Fp (z.1 - (1 - V.phaseW) * V.parents.even.den, z.2 - (1 - V.phaseW) * V.parents.even.num) := by
  unfold ChildFrame.sheetA ChildFrame.sheetShift Fraction.unmodifiedDeck
  simp only [smul_eq_mul, Prod.smul_mk]
  rfl

/-- The lower bound `1 − T ≤ t` of the closed polygon. -/
theorem closed_lower (V : ChildFrame) (z : Site) (hz : z ∈ V.closedPolygon) :
    1 - V.child.periodDenominator ≤ V.tGrade z := by
  obtain ⟨hn0, -, -, -, -⟩ := V.child_facts
  have h1n : 1 ≤ V.child.num := by omega
  simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq] at hz
  by_cases he : EvenSite z
  · rw [if_pos he] at hz
    obtain ⟨h1, -⟩ := hz
    linarith
  · rw [if_neg he] at hz
    obtain ⟨h1, -⟩ := hz
    linarith

end HarmWrap

end FLatticePaper.Induction
