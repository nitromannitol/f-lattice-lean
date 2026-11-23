import FLatticePaper.Plane.Induction.ParentCoordinates

/-! Task 59, step 2 (second Q3 piece): the input changes of the grades and the separation step of fix Q3.md, paragraph 4.

* The unit inputs change the child grades `t`, `s` and the parent grades `t_p`, `s_p` by fixed amounts:
  east `(1,0)`: `t +n`, `s +L`, `t_p +N`, `s_p +(D+N)`; north `(0,1)`: `t −d`, `s +(d−n)`, `t_p −D`, `s_p +(D−N)`.
* A unit input changes `s` by at most `L` (`|s(z+e) − s z| ≤ L`).
* Separation: if `s₁ < lam`, `μ < s₂` and `L ≤ μ − lam`, then `s₂ − s₁ > L`, so a single unit input cannot join them. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem chart_separation (s₁ s₂ lam μ L : ℤ) (h₁ : s₁ < lam) (h₂ : μ < s₂) (hsep : L ≤ μ - lam)
    (hstep : s₂ - s₁ ≤ L) : False := by
  omega

namespace ChildFrame
variable (frame : ChildFrame)

theorem tGrade_add_east (z : Site) : frame.tGrade (z + (1, 0)) = frame.tGrade z + frame.child.num := by
  simp only [tGrade, Prod.fst_add, Prod.snd_add]
  ring

theorem tGrade_add_north (z : Site) : frame.tGrade (z + (0, 1)) = frame.tGrade z - frame.child.den := by
  simp only [tGrade, Prod.fst_add, Prod.snd_add]
  ring

theorem sGrade_add_east (z : Site) :
    frame.sGrade (z + (1, 0)) = frame.sGrade z + (frame.child.den + frame.child.num) := by
  simp only [sGrade, Prod.fst_add, Prod.snd_add]
  ring

theorem sGrade_add_north (z : Site) :
    frame.sGrade (z + (0, 1)) = frame.sGrade z + (frame.child.den - frame.child.num) := by
  simp only [sGrade, Prod.fst_add, Prod.snd_add]
  ring

theorem parentTGrade_add_east (z : Site) :
    frame.parentTGrade (z + (1, 0)) = frame.parentTGrade z + frame.parents.odd.num := by
  simp only [parentTGrade, Prod.fst_add, Prod.snd_add]
  ring

theorem parentTGrade_add_north (z : Site) :
    frame.parentTGrade (z + (0, 1)) = frame.parentTGrade z - frame.parents.odd.den := by
  simp only [parentTGrade, Prod.fst_add, Prod.snd_add]
  ring

theorem parentSGrade_add_east (z : Site) :
    frame.parentSGrade (z + (1, 0)) = frame.parentSGrade z + (frame.parents.odd.den + frame.parents.odd.num) := by
  simp only [parentSGrade, Prod.fst_add, Prod.snd_add]
  ring

theorem parentSGrade_add_north (z : Site) :
    frame.parentSGrade (z + (0, 1)) = frame.parentSGrade z + (frame.parents.odd.den - frame.parents.odd.num) := by
  simp only [parentSGrade, Prod.fst_add, Prod.snd_add]
  ring

/-- A unit input changes `s` by at most `L = d + n`. -/
theorem sGrade_unit_input_bound (z : Site) (a b : ℤ)
    (hstep : (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1))
    (hn : 0 ≤ frame.child.num) (hd : 0 ≤ frame.child.den) :
    |frame.sGrade (z + (a, b)) - frame.sGrade z| ≤ frame.child.den + frame.child.num := by
  have key : frame.sGrade (z + (a, b)) - frame.sGrade z =
      (frame.child.den + frame.child.num) * a + (frame.child.den - frame.child.num) * b := by
    simp only [sGrade, Prod.fst_add, Prod.snd_add]
    ring
  rw [key, abs_le]
  rcases hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> constructor <;> linarith

end ChildFrame

end FLatticePaper.Induction
