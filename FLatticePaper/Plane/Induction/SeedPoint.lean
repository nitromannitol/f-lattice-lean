import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.OddStep
import FLatticePaper.Plane.Induction.PriceDeck

/-!
# The closed-form odd seed site (task w1: hseed0 at every proper word)

For a child frame with odd parent `N/D`, even parent `nq/dq` and `ε = N dq − nq D = ±1`, put `g = (nq + dq)/2`, `h = (dq − nq)/2`.
The even point

  `x = ε (d − 1) (g, h)`

lies on the line `((d − n)/2) x₁ − ((d + n)/2) x₂ = 1 − d` (the line of `SeedFields.odd_zero` for the word) and has even coordinate sum.
Its image `z0 = Z x = (−x₂, x₁ − 1)` is an odd site of the odd seed line `sGrade = 2 − 3d + n`, and the standard field satisfies
`F z0 = harmonicGrid z0` as soon as the quarter-turn zero `quarterTurnField F x = 0` holds at this single point (`seed_check_of_zero`).
-/

namespace FLatticePaper.Induction.SeedPoint

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Seeds

/-- The even point `x = ε(d − 1)(g, h)` of the seed line, with `ε = frame.eps`, `g = (nq + dq)/2`, `h = (dq − nq)/2`. -/
def seedX (frame : ChildFrame) : Site :=
  (frame.eps * (frame.child.den - 1) * ((frame.parents.even.num + frame.parents.even.den) / 2),
    frame.eps * (frame.child.den - 1) * ((frame.parents.even.den - frame.parents.even.num) / 2))

/-- The odd seed site `z0 = Z x = (−x₂, x₁ − 1)`. -/
def seedZ (frame : ChildFrame) : Site := (-(seedX frame).2, (seedX frame).1 - 1)

/-- The algebra of the seed line: with `d = 2D + dq`, `n = 2N + nq`, `dq = g + h`, `nq = g − h` and `ε = N dq − nq D`, `ε² = 1`,
the point `(−ε(d−1)h, ε(d−1)g − 1)` lies on `sGrade = 2 − 3d + n`. -/
theorem seed_alg (N D nq dq g h ε d n : ℤ) (hn : n = 2 * N + nq) (hd : d = 2 * D + dq)
    (hnq : nq = g - h) (hdq : dq = g + h) (hε : ε = N * dq - nq * D) (hε2 : ε * ε = 1) :
    (d + n) * (-(ε * (d - 1) * h)) + (d - n) * (ε * (d - 1) * g - 1) = 2 - 3 * d + n := by
  subst hn hd hnq hdq
  linear_combination (2 * (2 * D + (g + h) - 1) * ε) * hε - (2 * (2 * D + (g + h) - 1)) * hε2

theorem child_num_eq (frame : ChildFrame) : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := by
  simp [ChildFrame.child, Parents.current, Parents.combine]

theorem child_den_eq (frame : ChildFrame) : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := by
  simp [ChildFrame.child, Parents.current, Parents.combine]

theorem eps_eq (frame : ChildFrame) :
    frame.eps = frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den := by
  unfold ChildFrame.eps Fraction.det
  ring

theorem eps_sq' (frame : ChildFrame) : frame.eps * frame.eps = 1 := by
  rcases frame.eps_unit with h | h <;> rw [h] <;> norm_num

/-- The seed site lies on the odd seed line `sGrade = 2 − 3d + n`. -/
theorem seedZ_on_line (frame : ChildFrame) :
    frame.sGrade (seedZ frame) = 2 - 3 * frame.child.den + frame.child.num := by
  have hev : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  have hnq : frame.parents.even.num = (frame.parents.even.num + frame.parents.even.den) / 2 -
      (frame.parents.even.den - frame.parents.even.num) / 2 := by omega
  have hdq : frame.parents.even.den = (frame.parents.even.num + frame.parents.even.den) / 2 +
      (frame.parents.even.den - frame.parents.even.num) / 2 := by omega
  have key := seed_alg frame.parents.odd.num frame.parents.odd.den frame.parents.even.num frame.parents.even.den
    ((frame.parents.even.num + frame.parents.even.den) / 2) ((frame.parents.even.den - frame.parents.even.num) / 2)
    frame.eps frame.child.den frame.child.num (child_num_eq frame) (child_den_eq frame) hnq hdq (eps_eq frame)
    (eps_sq' frame)
  unfold ChildFrame.sGrade seedZ seedX
  linarith [key]

/-- The seed site is odd: the coordinate sum of `x` is even (the factor `d − 1` is even), so `z0 = (−x₂, x₁ − 1)` is odd. -/
theorem seedZ_odd (frame : ChildFrame) (a : ℤ) (ha : frame.child.den = 2 * a + 1) :
    ¬ EvenSite (seedZ frame) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, frame.child.den - 1 = 2 * k := ⟨a, by omega⟩
  have hsum : (seedZ frame).1 + (seedZ frame).2 =
      2 * (frame.eps * k * ((frame.parents.even.num + frame.parents.even.den) / 2 -
        (frame.parents.even.den - frame.parents.even.num) / 2)) - 1 := by
    unfold seedZ seedX
    rw [hk]
    ring
  unfold EvenSite
  generalize frame.eps * k * ((frame.parents.even.num + frame.parents.even.den) / 2 -
    (frame.parents.even.den - frame.parents.even.num) / 2) = Y at hsum
  omega

/-- **The check at the seed point.** The quarter-turn zero `quarterTurnField F x = 0` at the closed-form even point `x` gives
`F (seedZ) = harmonicGrid (seedZ)`. -/
theorem seed_check_of_zero (frame : ChildFrame) (F : Field) (hO : quarterTurnField F (seedX frame) = 0) :
    F (seedZ frame) = harmonicGrid (seedZ frame) := by
  have h := hO
  unfold quarterTurnField at h
  have hZ : QuarterTurn.counterclockwise.mapSite (0, -1) (seedX frame) = seedZ frame := by
    rw [quarterTurn_site]
    rfl
  rw [hZ] at h
  have hH := harmonicGrid_quarter_inv (seedZ frame)
  have hx : ((seedZ frame).2 + 1, -(seedZ frame).1) = seedX frame := by
    unfold seedZ
    ext <;> simp
  rw [hx] at hH
  linarith

end FLatticePaper.Induction.SeedPoint
