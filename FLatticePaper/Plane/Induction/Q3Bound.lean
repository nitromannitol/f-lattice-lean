import FLatticePaper.Plane.Induction.Q3Hlat

/-! Task 59, paragraph 5: the field identity with no hypothesis `hlat`, and the bound `p(x − e) ≥ p(x) − 1`.

Let `p(y) = c₀ − P(Z y)` (the paper's `p`, which is `f(y − ε U_q) − f(y)` by the field identity), and `e = V_q + ε U_q`
(`ChildFrame.sheetStep`). Then:
* `price_floor_bound` gives `p(y) ∈ [φ(y), φ(y) + 1]` with `φ(y) = parentFloor(y) = ⌊(t_p(y) − N)/B⌋`, `B = D²+2DN−N²`;
* `t_p(x − e) = t_p(x) + t_p(−e)` and `t_p(−e) = D(d_q+n_q) + N(d_q−n_q) − 1 ≥ 0` (parent bounds);
* so `φ(x − e) ≥ φ(x)` and `p(x − e) ≥ φ(x − e) ≥ φ(x) ≥ p(x) − 1`.
The hypotheses `hR`, `hD`, `hN1`, `hND` are the conjugate's price range and drift and the parent bounds of `price_floor_bound`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The paragraph-5 field identity at every site, with the lattice bridge proved. -/
theorem paragraph5_field_identity_proved {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hG : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV) (x : Site) :
    quarterTurnField G (x + (-frame.eps * frame.parents.even.den, -frame.eps * frame.parents.even.num)) -
        quarterTurnField G x =
      conj.cutPrice - conj.price G (-x.2, x.1 - 1) := by
  obtain ⟨j, hj⟩ := ChildFrame.lattice_bridge_exists frame conj hconj
  have h1 := quarterTurnField_sub_shift (conj := conj) (G := G) x
  have e : x + (-frame.eps * frame.parents.even.den, -frame.eps * frame.parents.even.num) =
      (x + (-conj.eps * (conj.parents.odd.num + conj.parents.odd.den),
          conj.eps * (conj.parents.odd.num - conj.parents.odd.den))) +
        (j * (2 * frame.parents.odd.den), j * (2 * frame.parents.odd.num)) := by
    rw [hj]
    abel
  have h3 : quarterTurnField G (x + (-frame.eps * frame.parents.even.den, -frame.eps * frame.parents.even.num)) =
      quarterTurnField G (x + (-conj.eps * (conj.parents.odd.num + conj.parents.odd.den),
          conj.eps * (conj.parents.odd.num - conj.parents.odd.den))) := by
    rw [e]
    exact quarterTurnField_add_mul_up (frame := frame) (conj := conj) (G := G) hconj hG j _
  linarith [h1, h3]

namespace ChildFrame
variable (frame : ChildFrame)

theorem parentTGrade_add (x y : Site) :
    frame.parentTGrade (x + y) = frame.parentTGrade x + frame.parentTGrade y := by
  unfold parentTGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- `t_p(x − e) ≥ t_p(x)`, since `t_p(−e) = D(d_q+n_q) + N(d_q−n_q) − 1 ≥ 0` by the parent bounds. -/
theorem parentTGrade_le_sub_sheetStep (x : Site) :
    frame.parentTGrade x ≤ frame.parentTGrade (x - frame.sheetStep) := by
  have hneg := frame.parentTGrade_neg_sheetStep
  have hE := frame.valid.even_bounds
  have hO := frame.valid.odd_bounds
  have hq : 0 < frame.parents.even.den := hE.1
  have hnq : 0 ≤ frame.parents.even.num := hE.2.1
  have hnqd : frame.parents.even.num ≤ frame.parents.even.den := hE.2.2
  have hD : 0 < frame.parents.odd.den := hO.1
  have hN : 0 ≤ frame.parents.odd.num := hO.2.1
  have hτ : 0 ≤ frame.parentTGrade (-frame.sheetStep) := by
    rw [hneg]
    nlinarith [mul_nonneg hN (sub_nonneg.mpr hnqd), mul_nonneg hD.le (add_nonneg hnq hq.le)]
  rw [sub_eq_add_neg, frame.parentTGrade_add]
  linarith

theorem parentFloor_le_sub_sheetStep (hB : 0 < frame.parents.odd.den ^ 2 +
      2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2) (x : Site) :
    parentFloor frame x ≤ parentFloor frame (x - frame.sheetStep) := by
  have hT := frame.parentTGrade_le_sub_sheetStep x
  unfold parentFloor
  apply Int.ediv_le_ediv hB
  unfold parentTGrade at hT
  linarith

/-- The bound `p(x − e) ≥ p(x) − 1`, for `p(y) = c₀ − P(Zy)`. -/
theorem p_shift_bound {conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hR : ∀ z ∈ conj.closedPolygon, conj.cutPrice - 1 ≤ conj.price G z ∧ conj.price G z ≤ conj.cutPrice)
    (hD : ∀ z, conj.price G (z + conj.child.modifiedDeck.kernel) - conj.price G z = -1 ∧
      conj.price G (z + conj.child.modifiedDeck.transverse) - conj.price G z = 0)
    (hN1 : 1 ≤ frame.parents.odd.num) (hND : frame.parents.odd.num + 1 ≤ frame.parents.odd.den) (x : Site) :
    conj.cutPrice - conj.price G (-x.2, x.1 - 1) - 1 ≤
      conj.cutPrice - conj.price G (-(x - frame.sheetStep).2, (x - frame.sheetStep).1 - 1) := by
  have hB : 0 < frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
      frame.parents.odd.num ^ 2 := by
    nlinarith
  obtain ⟨hx1, _⟩ := price_floor_bound (frame := frame) (conj := conj) (G := G) hconj hR hD hN1 hND x
  obtain ⟨_, hy2⟩ := price_floor_bound (frame := frame) (conj := conj) (G := G) hconj hR hD hN1 hND
    (x - frame.sheetStep)
  have hmono := frame.parentFloor_le_sub_sheetStep hB x
  linarith

end ChildFrame

end FLatticePaper.Induction
