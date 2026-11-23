import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.W1ZeroStrip
import FLatticePaper.Plane.Induction.HWeb
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.VArcLongitudinal
import FLatticePaper.Plane.Induction.BaseGeometry
import FLatticePaper.Plane.Induction.Sheets

/-! # Task 72 (1): the bottom arc has `A ≤ C`

On the pure bottom arc `PureBottom E z` of the frame of a proper word `w`, with `F_p = quarterTurnField (standardField (conjWord w))`:

* `A(z) = F_p(z − lv) = 0`. The parent `t`-grade of `z` lies in the free H cut, `0 ≤ t_p(z) ≤ N + D`
  (`parentTGrade_bounds_of_freeH`), and `t_p(z − lv) = t_p(z) + (1 − W)·(−ε)·…` puts `z − lv` in the ordinary `h₀` band
  `[1 − D, N + 2D − 1]` of the conjugate, where the zero strip of the quarter turn gives `F_p = 0` (`zeroStrip_of_strips`).
  The bound `D ≥ 2` needed for the shifted band comes from `N ≤ D`, the parity `N + D` odd, `ε = ±1` and `n ≥ 3`.
* `C(z) ≥ 0`: the zone of I1 (`ZoneI1.I1_of_strong`) applies because `t(z) ≥ 1 − d` on the pure bottom arc (`pureBottom_shape`).

Hence `A(z) = 0 ≤ C(z)` on the pure bottom arc. -/

namespace FLatticePaper.W1ArcBottom

open Farey FLatticePaper FLatticePaper.Induction

/-- The pure bottom arc lies in the free H cut: the south neighbour is outside `E`, and the `t`-grade has the H spectrum. -/
theorem pureBottom_freeH (frame : ChildFrame) {z : Site} (hz : PureBottom frame.closedPolygon z) :
    z ∈ frame.freeH := by
  have hsh := frame.pureBottom_shape hz
  obtain ⟨hnodd, hdodd⟩ := FLatticePaper.W1Exit.child_parity frame
  have hpar : frame.tGrade z % 2 = (z.1 + z.2) % 2 := by
    obtain ⟨a, ha⟩ : ∃ a, frame.child.num = 2 * a + 1 := ⟨frame.child.num / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, frame.child.den = 2 * b + 1 := ⟨frame.child.den / 2, by omega⟩
    have ht : frame.tGrade z = 2 * (a * z.1 - b * z.2) + (z.1 - z.2) := by
      unfold ChildFrame.tGrade
      rw [ha, hb]
      ring
    generalize a * z.1 - b * z.2 = k at ht
    rw [ht]
    omega
  have hmem : z ∈ frame.closedPolygon ∧ z + ((0 : ℤ), (-1 : ℤ)) ∉ frame.closedPolygon := by
    unfold PureBottom OutwardDir at hz
    exact hz.1
  have e : z + ((0 : ℤ), (-1 : ℤ)) = (z.1, z.2 - 1) :=
    Prod.ext (by simp) (by simp [sub_eq_add_neg])
  have hfree : (z.1, z.2 - 1) ∉ frame.closedPolygon := by
    rw [← e]
    exact hmem.2
  have hspec : frame.hSpectrum (frame.tGrade z) := by
    unfold ChildFrame.hSpectrum
    rcases hsh with ⟨hev, h1, h2⟩ | ⟨hod, h1, h2⟩
    · unfold EvenSite at hev
      left
      exact ⟨by omega, by omega, by omega⟩
    · unfold EvenSite at hod
      right
      exact ⟨by omega, by omega, by omega⟩
  exact ⟨hmem.1, hfree, hspec⟩

/-- The parent `t`-grade on the pure bottom arc: `0 ≤ t_p(z) ≤ N + D`. -/
theorem pureBottom_parentT (frame : ChildFrame) {z : Site} (hz : PureBottom frame.closedPolygon z) :
    0 ≤ frame.parentTGrade z ∧ frame.parentTGrade z ≤ frame.parents.odd.num + frame.parents.odd.den :=
  frame.parentTGrade_bounds_of_freeH (pureBottom_freeH frame hz)

/-- The parent grade of the sheet shift: `t_p(lv) = (1 − W)·ε`, since `lv = (1 − W) U_q` and `t_p(U_q) = ε`. -/
theorem parentTGrade_sheetShift (frame : ChildFrame) :
    frame.parentTGrade frame.sheetShift = (1 - frame.phaseW) * frame.eps := by
  unfold ChildFrame.parentTGrade ChildFrame.sheetShift
  rw [ZoneI1.eps_eq frame]
  simp [Fraction.unmodifiedDeck]
  ring

/-- The odd parent has denominator at least `2`, from `n ≥ 3`, `N ≤ D`, `N + D` odd and `ε = ±1`. -/
theorem odd_den_ge_two (frame : ChildFrame) (hn3 : 3 ≤ frame.child.num) :
    2 ≤ frame.parents.odd.den := by
  have hodd : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  obtain ⟨hD, hN0, hND⟩ := frame.valid.odd_bounds
  have hcn := frame.child_num_eq
  have he := ZoneI1.eps_eq frame
  by_contra hlt
  have hD1 : frame.parents.odd.den = 1 := by omega
  have hN : frame.parents.odd.num = 0 := by omega
  rw [hN] at hcn
  rw [hN, hD1] at he
  rcases frame.eps_unit with h | h <;> omega

/-- The shifted parent argument `z − lv` on the pure bottom arc lies in the ordinary `h₀` band `[1 − D, N + 2D − 1]`. -/
theorem parentT_shift_window (frame : ChildFrame) (hD2 : 2 ≤ frame.parents.odd.den) {z : Site}
    (hz : PureBottom frame.closedPolygon z) :
    1 - frame.parents.odd.den ≤ frame.parentTGrade (z - frame.sheetShift) ∧
      frame.parentTGrade (z - frame.sheetShift) ≤ frame.parents.odd.num + 2 * frame.parents.odd.den - 1 := by
  obtain ⟨h0, h1⟩ := pureBottom_parentT frame hz
  have hsub : frame.parentTGrade (z - frame.sheetShift) =
      frame.parentTGrade z - frame.parentTGrade frame.sheetShift := by
    unfold ChildFrame.parentTGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  rw [hsub, parentTGrade_sheetShift]
  rcases frame.eps_unit with h | h
  · have hW : frame.phaseW = 1 := by
      unfold ChildFrame.phaseW
      rw [h]
      norm_num
    rw [hW, h]
    constructor <;> omega
  · have hW : frame.phaseW = 0 := by
      unfold ChildFrame.phaseW
      rw [h]
      norm_num
    rw [hW, h]
    constructor <;> omega

/-- **`A = 0` on the pure bottom arc**: the sheet `A(z) = F_p(z − lv)` vanishes, by the zero strip of the quarter turn of the
conjugate (`zeroStrip_of_strips`) at the shifted parent argument. -/
theorem sheetA_bottom_eq_zero {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) {z : Site}
    (hz : PureBottom (frameAt word).closedPolygon z) :
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z = 0 := by
  have hD2 := odd_den_ge_two (frameAt word) (child_num_ge_three h)
  obtain ⟨hlo, hhi⟩ := parentT_shift_window (frameAt word) hD2 hz
  have hcj : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate :=
    frameAt_conj_child h
  have hrot := Fraction.rotate_of_odd (frameAt word).valid.odd_parity
  have hrot' : (frameAt word).parents.odd.rotate =
      ⟨(frameAt word).parents.odd.den - (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den + (frameAt word).parents.odd.num⟩ := hrot
  have hb : (frameAt (conjWord word)).child.num =
      (frameAt word).parents.odd.den - (frameAt word).parents.odd.num := by
    rw [hcj, hrot']
  have hr : (frameAt (conjWord word)).child.den =
      (frameAt word).parents.odd.den + (frameAt word).parents.odd.num := by
    rw [hcj, hrot']
  unfold ChildFrame.parentTGrade at hlo hhi
  have hz0 := FLatticePaper.W1ZeroStrip.zeroStrip_of_strips (frameAt (conjWord word)) hS.packet.strips
    (z - (frameAt word).sheetShift)
    (by
      rw [hb, hr]
      have e1 : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num -
          ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num)) / 2 =
          (frameAt word).parents.odd.num := by omega
      have e2 : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num +
          ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num)) / 2 =
          (frameAt word).parents.odd.den := by omega
      rw [e1, e2]
      exact hlo)
    (by
      rw [hb, hr]
      have e1 : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num -
          ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num)) / 2 =
          (frameAt word).parents.odd.num := by omega
      have e2 : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num +
          ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num)) / 2 =
          (frameAt word).parents.odd.den := by omega
      rw [e1, e2]
      exact hhi)
  unfold ChildFrame.sheetA
  exact hz0

/-- **`A ≤ C` on the pure bottom arc** (task 72, piece (1)): `A = 0` (`sheetA_bottom_eq_zero`) and `C ≥ 0` (the zone of I1,
`ZoneI1.I1_of_strong`, which needs `t(z) ≥ 1 − d`). -/
theorem bottom_sheetA_le_sheetC {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) {z : Site}
    (hz : PureBottom (frameAt word).closedPolygon z) :
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z ≤
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z := by
  have hA := sheetA_bottom_eq_zero h hS hz
  have hmem : z ∈ (frameAt word).closedPolygon := by
    unfold PureBottom OutwardDir at hz
    exact hz.1.1
  have hsh := (frameAt word).pureBottom_shape hz
  obtain ⟨hn0, -, -, hd3, -⟩ := (frameAt word).child_facts
  have ht : 1 - (frameAt word).child.den ≤ (frameAt word).tGrade z := by
    rcases hsh with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> omega
  have hC := ZoneI1.I1_of_strong h hS z hmem ht
  rw [hA]
  exact hC

end FLatticePaper.W1ArcBottom
