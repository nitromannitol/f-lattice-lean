import FLatticePaper.Plane.Induction.Potentials
import Mathlib.Tactic.LinearCombination

namespace FLatticePaper.Induction
open Farey

namespace ChildFrame
variable (frame : ChildFrame)

/-- The closed fundamental polygon `E`: the parity rectangle in the grades `t`, `s`. -/
def closedPolygon : Set Site :=
  {z | if EvenSite z then
      2 - frame.child.periodDenominator ≤ frame.tGrade z ∧
        frame.tGrade z ≤ frame.child.den + frame.child.num - 2 ∧
        0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num
    else
      frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den ∧
        2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
        frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2}

/-- `W = (1 + ε)/2`. -/
def phaseW : ℤ := (1 + frame.eps) / 2
/-- `lv = (1 − W) U_q`. -/
def sheetShift : Site := (1 - frame.phaseW) • frame.parents.even.unmodifiedDeck.kernel
/-- `e = V_q + ε U_q`. -/
def sheetOffset : Site :=
  frame.parents.even.unmodifiedDeck.transverse + frame.eps • frame.parents.even.unmodifiedDeck.kernel
/-- `a_q·x` with `a_q = (n_q, −d_q)`. -/
def siblingSlope (x : Site) : ℤ := frame.parents.even.num * x.1 - frame.parents.even.den * x.2
/-- `c_e = (T_q − d_q − n_q)/2 + 2W`. -/
def sheetConstant : ℤ :=
  (frame.parents.even.periodDenominator - frame.parents.even.den - frame.parents.even.num) / 2 +
    2 * frame.phaseW

variable (Fp : Field)
/-- The sheet `A(z) = F_p(z − lv)`. -/
def sheetA (z : Site) : ℤ := Fp (z - frame.sheetShift)
/-- The sheet `C(z) = F_p(z − lv − e) + a_q·(z − lv) + c_e`. -/
def sheetC (z : Site) : ℤ :=
  Fp (z - frame.sheetShift - frame.sheetOffset) + frame.siblingSlope (z - frame.sheetShift) +
    frame.sheetConstant
/-- `M = min(A, C)`. -/
def sheetMin (z : Site) : ℤ := min (frame.sheetA Fp z) (frame.sheetC Fp z)

/-- Membership in the closed polygon is decidable: it is a conjunction of integer inequalities
in the parity case given by `EvenSite`. -/
instance closedPolygon_decidable : DecidablePred (· ∈ frame.closedPolygon) := fun z => by
  unfold ChildFrame.closedPolygon
  by_cases h : EvenSite z
  · simp only [Set.mem_setOf_eq, if_pos h]
    infer_instance
  · simp only [Set.mem_setOf_eq, if_neg h]
    infer_instance

end ChildFrame

/-- The modified deck of the even child combines as the unmodified one: `i U + j V` with
`U = (d, n)` and `V = (n − d, n + d)`. -/
theorem ChildFrame.child_modifiedDeck_combine (frame : ChildFrame) (i j : ℤ) :
    frame.child.modifiedDeck.combine i j =
      (i * frame.child.den + j * (frame.child.num - frame.child.den),
        i * frame.child.num + j * (frame.child.num + frame.child.den)) := by
  unfold PeriodDeck.combine
  simp only [ChildFrame.child_modifiedDeck_kernel, ChildFrame.child_modifiedDeck_transverse]

/-- Translating by `i U + j V` shifts the transverse grade by `−j T`. -/
theorem ChildFrame.tGrade_add_combine (frame : ChildFrame) (z : Site) (i j : ℤ) :
    frame.tGrade (z + frame.child.modifiedDeck.combine i j) =
      frame.tGrade z - j * frame.child.periodDenominator := by
  rw [ChildFrame.child_modifiedDeck_combine]
  unfold ChildFrame.tGrade Fraction.periodDenominator
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- Translating by `i U + j V` shifts the longitudinal grade by `i T`. -/
theorem ChildFrame.sGrade_add_combine (frame : ChildFrame) (z : Site) (i j : ℤ) :
    frame.sGrade (z + frame.child.modifiedDeck.combine i j) =
      frame.sGrade z + i * frame.child.periodDenominator := by
  rw [ChildFrame.child_modifiedDeck_combine]
  unfold ChildFrame.sGrade Fraction.periodDenominator
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The even child has even coordinate sum, so the translations `i U + j V` preserve parity. -/
theorem ChildFrame.evenSite_add_combine (frame : ChildFrame) (z : Site) (i j : ℤ) :
    EvenSite (z + frame.child.modifiedDeck.combine i j) ↔ EvenSite z := by
  obtain ⟨m, hm⟩ : ∃ m, frame.child.num + frame.child.den = 2 * m :=
    ⟨(frame.child.num + frame.child.den) / 2, by
      have h := frame.child_even
      unfold Fraction.Even at h
      omega⟩
  rw [ChildFrame.child_modifiedDeck_combine]
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add]
  have key : z.1 + (i * frame.child.den + j * (frame.child.num - frame.child.den)) +
      (z.2 + (i * frame.child.num + j * (frame.child.num + frame.child.den))) =
      (z.1 + z.2) + 2 * (i * m + j * frame.child.num) := by
    linear_combination i * hm
  rw [key, Int.add_mul_emod_self_left]

/-- An integer window: some multiple of `T` moves `x` into `[a − T, a − 1]`. -/
private theorem exists_window (x a T : ℤ) (hT : 0 < T) :
    ∃ j : ℤ, a - T ≤ x + j * T ∧ x + j * T ≤ a - 1 := by
  refine ⟨(a - 1 - x) / T, ?_⟩
  have hdiv := Int.emod_add_ediv_mul (a - 1 - x) T
  have h0 := Int.emod_nonneg (a - 1 - x) hT.ne'
  have h1 := Int.emod_lt_of_pos (a - 1 - x) hT
  constructor <;> linarith

/-- `E` meets every class of the child's deck. -/
theorem ChildFrame.closedPolygon_covers (frame : ChildFrame) (z : Site) :
    ∃ y ∈ frame.closedPolygon, ∃ i j : ℤ, z = y + frame.child.modifiedDeck.combine i j := by
  have hT : 0 < frame.child.periodDenominator :=
    Fraction.periodDenominator_pos (frame.valid.current_interior .even).inUnitInterval
  have hint : frame.child.Interior := frame.valid.current_interior .even
  obtain ⟨hn, hnd⟩ := hint
  by_cases hz : EvenSite z
  · obtain ⟨j, hj1, hj2⟩ := exists_window (frame.tGrade z) 2 frame.child.periodDenominator hT
    obtain ⟨i, hi1, hi2⟩ :=
      exists_window (frame.sGrade z) frame.child.periodDenominator frame.child.periodDenominator hT
    have hpar : EvenSite (z + frame.child.modifiedDeck.combine i (-j)) :=
      (frame.evenSite_add_combine z i (-j)).2 hz
    refine ⟨z + frame.child.modifiedDeck.combine i (-j), ?_, -i, j, ?_⟩
    · unfold ChildFrame.closedPolygon
      rw [Set.mem_setOf_eq, if_pos hpar]
      rw [frame.tGrade_add_combine, frame.sGrade_add_combine]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · simp only [ChildFrame.child_modifiedDeck_combine]
      ext <;> simp <;> ring
  · obtain ⟨j, hj1, hj2⟩ := exists_window (frame.tGrade z) frame.child.num frame.child.periodDenominator hT
    obtain ⟨i, hi1, hi2⟩ := exists_window (frame.sGrade z)
      (2 - frame.child.den + frame.child.num + frame.child.periodDenominator) frame.child.periodDenominator hT
    have hpar : ¬ EvenSite (z + frame.child.modifiedDeck.combine i (-j)) :=
      (frame.evenSite_add_combine z i (-j)).not.mpr hz
    refine ⟨z + frame.child.modifiedDeck.combine i (-j), ?_, -i, j, ?_⟩
    · unfold ChildFrame.closedPolygon
      rw [Set.mem_setOf_eq, if_neg hpar]
      rw [frame.tGrade_add_combine, frame.sGrade_add_combine]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · simp only [ChildFrame.child_modifiedDeck_combine]
      ext <;> simp <;> ring

theorem ChildFrame.phaseW_cases (frame : ChildFrame) :
    (frame.eps = 1 ∧ frame.phaseW = 1) ∨ (frame.eps = -1 ∧ frame.phaseW = 0) := by
  rcases frame.eps_unit with h | h
  · left
    refine ⟨h, ?_⟩
    unfold ChildFrame.phaseW
    rw [h]
    norm_num
  · right
    refine ⟨h, ?_⟩
    unfold ChildFrame.phaseW
    rw [h]
    norm_num

/-- The sibling has even coordinate sum, so `T_q − d_q − n_q` is even. -/
theorem ChildFrame.sheetConstant_exact (frame : ChildFrame) :
    2 * (frame.sheetConstant - 2 * frame.phaseW) =
      frame.parents.even.periodDenominator - frame.parents.even.den - frame.parents.even.num := by
  have hEv : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  obtain ⟨s, hs⟩ : ∃ s, frame.parents.even.num + frame.parents.even.den = 2 * s :=
    ⟨(frame.parents.even.num + frame.parents.even.den) / 2, by omega⟩
  have hdvd : (2 : ℤ) ∣ frame.parents.even.periodDenominator - frame.parents.even.den -
      frame.parents.even.num := by
    refine ⟨frame.parents.even.den * frame.parents.even.num -
      s * (frame.parents.even.num - frame.parents.even.den + 1), ?_⟩
    unfold Fraction.periodDenominator
    linear_combination (-(frame.parents.even.num - frame.parents.even.den + 1)) * hs
  have key := Int.mul_ediv_cancel' hdvd
  unfold ChildFrame.sheetConstant
  linarith

end FLatticePaper.Induction
