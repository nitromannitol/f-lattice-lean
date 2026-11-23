import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.VArcLongitudinal

/-! # Task 75 (odd_zero, field side): the seed `z` and its point `Y = Z z + U` lie in the closed polygon

For a child frame with odd parent `(N, D)` (`num = N`, `den = D`) and even sibling `(r, e)` (`num = r`, `den = e`), the odd-seed point of
the fixer's Q14 is `z = (D + N − 1, D − N + 1) + (1 − W)(e + r, e − r)`, `W = phaseW`. Its image `Y = Z z + U` with `Z(x, y) = (−y, x − 1)` and
`U = (den, num)` (the kernel of the child) is odd, and lies in the closed polygon. The grades of `Y` are
`t(Y) = −K_p − (1−W) K_q + 2d − n` and `s(Y) = T + 2 − 3d + n` (using `Nd − Dn = ε`), with `K_h = (d+n) h₁ + (d−n) h₂`, `T = 2K_p + K_q`.
The inequalities follow from `K_p ≥ 0`, `K_q ≥ 0`, `T ≥ 2d`, and `d ≥ n + 2`. -/

namespace FLatticePaper.W1OddSeedY

open Farey FLatticePaper FLatticePaper.Induction

/-- The odd-seed point `z = (D + N − 1, D − N + 1) + (1 − W)(e + r, e − r)`. -/
def oddSeedPoint (frame : ChildFrame) : Site :=
  (frame.parents.odd.den + frame.parents.odd.num - 1 +
      (1 - frame.phaseW) * (frame.parents.even.den + frame.parents.even.num),
    frame.parents.odd.den - frame.parents.odd.num + 1 +
      (1 - frame.phaseW) * (frame.parents.even.den - frame.parents.even.num))

/-- `Y = Z z + U` with `Z(x, y) = (−y, x − 1)` and `U = (den, num)` the kernel of the child. -/
def oddSeedY (frame : ChildFrame) : Site :=
  (-(oddSeedPoint frame).2 + frame.child.den, (oddSeedPoint frame).1 - 1 + frame.child.num)

/-- The grade `t(Y)` in closed form: `t(Y) = −K_p − (1 − W) K_q + 2d − n` with `K_h = (d+n) h₁ + (d−n) h₂`. -/
theorem tGrade_oddSeedY (frame : ChildFrame) :
    frame.tGrade (oddSeedY frame) =
      -((frame.child.den + frame.child.num) * frame.parents.odd.den +
          (frame.child.den - frame.child.num) * frame.parents.odd.num) -
        (1 - frame.phaseW) * ((frame.child.den + frame.child.num) * frame.parents.even.den +
          (frame.child.den - frame.child.num) * frame.parents.even.num) +
        2 * frame.child.den - frame.child.num := by
  unfold ChildFrame.tGrade oddSeedY oddSeedPoint
  ring

/-- **`Y` lies in the closed polygon** (task 75): the odd branch of `closedPolygon` at the seed image. -/
theorem oddSeed_Y_mem (frame : ChildFrame) : oddSeedY frame ∈ frame.closedPolygon := by
  have hcn := frame.child_num_eq
  have hcd := frame.child_den_eq
  have hpe := ZoneI1.eps_eq frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  obtain ⟨hDpos, hN0, hND⟩ := frame.valid.odd_bounds
  obtain ⟨heD, her0, hreE⟩ := frame.valid.even_bounds
  obtain ⟨hn0, hnd, -, hd3, hTeq⟩ := frame.child_facts
  have hodd : ¬ EvenSite (oddSeedY frame) := by
    unfold EvenSite oddSeedY oddSeedPoint
    rcases frame.eps_unit with hε | hε
    · rw [FLatticePaper.W1Seeds.phaseW_pos frame hε]
      simp only [sub_self, zero_mul, add_zero]
      omega
    · rw [FLatticePaper.W1Seeds.phaseW_neg frame hε]
      simp only [sub_zero, one_mul]
      omega
  have ht := tGrade_oddSeedY frame
  have hsY : frame.sGrade (oddSeedY frame) =
      frame.child.periodDenominator + 2 - 3 * frame.child.den + frame.child.num := by
    rcases frame.eps_unit with hε | hε
    · have hW := FLatticePaper.W1Seeds.phaseW_pos frame hε
      have hrel : frame.parents.odd.num * frame.parents.even.den -
          frame.parents.even.num * frame.parents.odd.den = 1 := by rw [← hpe, hε]
      unfold ChildFrame.sGrade oddSeedY oddSeedPoint
      rw [hW, hTeq, hcd, hcn]
      linear_combination 2 * hrel
    · have hW := FLatticePaper.W1Seeds.phaseW_neg frame hε
      have hrel : frame.parents.odd.num * frame.parents.even.den -
          frame.parents.even.num * frame.parents.odd.den = -1 := by rw [← hpe, hε]
      unfold ChildFrame.sGrade oddSeedY oddSeedPoint
      rw [hW, hTeq, hcd, hcn]
      linear_combination (-2 : ℤ) * hrel
  -- the two parent grades K_p, K_q and the identity T = 2 K_p + K_q
  have hTK : frame.child.periodDenominator =
      2 * ((frame.child.den + frame.child.num) * frame.parents.odd.den +
          (frame.child.den - frame.child.num) * frame.parents.odd.num) +
        ((frame.child.den + frame.child.num) * frame.parents.even.den +
          (frame.child.den - frame.child.num) * frame.parents.even.num) := by
    rw [hTeq, hcd, hcn]
    ring
  have a1 : 0 ≤ frame.child.den + frame.child.num := by omega
  have a2 : 0 ≤ frame.child.den - frame.child.num := by omega
  have hK1 : 0 ≤ (frame.child.den + frame.child.num) * frame.parents.odd.den +
      (frame.child.den - frame.child.num) * frame.parents.odd.num :=
    add_nonneg (mul_nonneg a1 hDpos.le) (mul_nonneg a2 hN0)
  have hK2 : 0 ≤ (frame.child.den + frame.child.num) * frame.parents.even.den +
      (frame.child.den - frame.child.num) * frame.parents.even.num :=
    add_nonneg (mul_nonneg a1 heD.le) (mul_nonneg a2 her0)
  have hK3 : frame.child.den - frame.child.num ≤
      (frame.child.den + frame.child.num) * frame.parents.odd.den +
        (frame.child.den - frame.child.num) * frame.parents.odd.num := by
    have h1 : 0 ≤ (frame.child.den + frame.child.num) * (frame.parents.odd.den - 1) :=
      mul_nonneg a1 (by omega)
    have h2 : 0 ≤ (frame.child.den - frame.child.num) * frame.parents.odd.num := mul_nonneg a2 hN0
    have h3 : (frame.child.den + frame.child.num) * (frame.parents.odd.den - 1) =
        (frame.child.den + frame.child.num) * frame.parents.odd.den - (frame.child.den + frame.child.num) := by ring
    linarith
  have hT2 : 2 * frame.child.den ≤ frame.child.periodDenominator := by
    rw [hTeq]
    have h1 : 0 ≤ frame.child.den * (frame.child.den - frame.child.num - 2) := mul_nonneg (by omega) (by omega)
    have h2 : 0 ≤ frame.child.num * (frame.child.num + 2) := mul_nonneg (by omega) (by omega)
    nlinarith
  unfold ChildFrame.closedPolygon
  rw [Set.mem_setOf_eq, if_neg hodd, ht, hsY]
  rcases frame.eps_unit with hε | hε
  · rw [FLatticePaper.W1Seeds.phaseW_pos frame hε]
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith
  · rw [FLatticePaper.W1Seeds.phaseW_neg frame hε]
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith

end FLatticePaper.W1OddSeedY
