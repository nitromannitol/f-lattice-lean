import FLatticePaper.Plane.Induction.HBottom
import FLatticePaper.Plane.Induction.TwosField

/-! Task w3, step D support: the conjugate of a pure word is empty, and the free H arc has a counted enumeration. -/

namespace FLatticePaper.ConjBase

open Farey FLatticePaper FLatticePaper.Induction

/-- The conjugate of `3^k` is the empty word. -/
theorem conjWord_threes (k : ℕ) : conjWord (List.replicate k Digit.three) = [] := by
  unfold conjWord oddBirthPrefix
  simp

/-- The free H arc, enumerated by abscissa with `H 0 = (1,0)` and `H 1 = (2,0)`, counted by `N = d`. -/
theorem freeH_enum_N (frame : ChildFrame) :
    ∃ (H : ℕ → Site) (N : ℕ), 2 ≤ N ∧ (N : ℤ) = frame.child.den ∧
      (∀ j : ℕ, j < N → H j ∈ frame.freeH) ∧ (∀ j : ℕ, j < N → (H j).1 = (j : ℤ) + 1) ∧
      (∀ z ∈ frame.freeH, ∃ j : ℕ, j < N ∧ z = H j) := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  obtain ⟨H, hH, hcov⟩ := freeH_enumeration frame
  refine ⟨H, frame.child.den.toNat, by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj
    exact (hH j (by omega)).1
  · intro j hj
    exact (hH j (by omega)).2
  · intro z hz
    obtain ⟨j, hj, hzj⟩ := hcov z hz
    exact ⟨j, by omega, hzj⟩

end FLatticePaper.ConjBase
