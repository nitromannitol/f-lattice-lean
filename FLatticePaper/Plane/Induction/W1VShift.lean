import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.Induction.Q3Field

/-! # Task 72 (2): the V-shift of the packet field

For a packet `F` of a child frame, with `V = modifiedDeck.transverse = (n − d, n + d)` and `U = modifiedDeck.kernel`:
* `F(z + V) = F z + t(z) + c_V` (the transverse period; `transverseGrade = −t`);
* `t(z + mV) = t(z) − m T` (since `t(V) = −T`, `T = periodDenominator`);
* `F(z + mV) = F z + m t(z) − T·(m(m−1)/2) + m c_V` for all `m : ℤ`;
* `F(z + kU) = F z` (the kernel period, `c_U = 0`);
* the representative formula: if `y = x + lV + kU`, then `F x = F y + (−l) t(y) − T·((−l)(−l−1)/2) + (−l) c_V`. -/

namespace FLatticePaper.W1VShift

open Farey FLatticePaper FLatticePaper.Induction

/-- `m • p + p = (m + 1) • p`, the step used in both inductions. -/
theorem smul_add_self_site (m : ℤ) (p : Site) : m • p + p = (m + 1) • p := by
  rw [add_smul, one_smul]

/-- The transverse period of the packet in grade form: `F(z + V) = F z + t(z) + c_V`. -/
theorem packet_V_step (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (z : Site) :
    F (z + (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) =
      F z + frame.tGrade z + frame.coherentConstantV := by
  obtain ⟨-, hVz⟩ := hP.periods
  have h := hVz z
  rw [frame.child_modifiedDeck_transverse] at h
  rw [h]
  unfold Fraction.transverseGrade ChildFrame.tGrade
  ring

/-- The grade along the transverse direction: `t(z + mV) = t(z) − m T`. -/
theorem tGrade_add_zsmul_V (frame : ChildFrame) (z : Site) (m : ℤ) :
    frame.tGrade (z + m • (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) =
      frame.tGrade z - m * frame.child.periodDenominator := by
  unfold ChildFrame.tGrade Fraction.periodDenominator
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The quadratic term is an integer: `2 · (m(m−1)/2) = m(m−1)`. -/
theorem two_mul_tri (m : ℤ) : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
  Int.two_mul_ediv_two_of_even (Int.even_mul_pred_self m)

/-- The closed form of the transverse period at every integer multiple:
`F(z + mV) = F z + m t(z) − T·(m(m−1)/2) + m c_V`. -/
theorem packet_V_zsmul (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (y : Site) (m : ℤ) :
    F (y + m • (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) =
      F y + m * frame.tGrade y - frame.child.periodDenominator * (m * (m - 1) / 2) +
        m * frame.coherentConstantV := by
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have hstep := packet_V_step frame hP (y + (i : ℤ) • (frame.child.num - frame.child.den, frame.child.num + frame.child.den))
    have hsum : y + ((i : ℤ) + 1) • (frame.child.num - frame.child.den, frame.child.num + frame.child.den) =
        y + (i : ℤ) • (frame.child.num - frame.child.den, frame.child.num + frame.child.den) +
          (frame.child.num - frame.child.den, frame.child.num + frame.child.den) := by
      rw [add_smul, one_smul, add_assoc]
    rw [hsum, hstep, ih, tGrade_add_zsmul_V]
    have hq := two_mul_tri ((i : ℤ) + 1)
    have hq0 := two_mul_tri (i : ℤ)
    have key : 2 * (((i : ℤ) + 1) * ((i : ℤ) + 1 - 1) / 2) = 2 * ((i : ℤ) * ((i : ℤ) - 1) / 2 + (i : ℤ)) := by
      linear_combination hq - hq0
    have hQ : ((i : ℤ) + 1) * ((i : ℤ) + 1 - 1) / 2 = (i : ℤ) * ((i : ℤ) - 1) / 2 + (i : ℤ) := by
      linarith
    linear_combination frame.child.periodDenominator * hQ
  | pred i ih =>
    have hw : y + (-(i : ℤ) - 1) • (frame.child.num - frame.child.den, frame.child.num + frame.child.den) +
        (frame.child.num - frame.child.den, frame.child.num + frame.child.den) =
        y + (-(i : ℤ)) • (frame.child.num - frame.child.den, frame.child.num + frame.child.den) := by
      rw [add_assoc, smul_add_self_site, show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring]
    have hstep := packet_V_step frame hP
      (y + (-(i : ℤ) - 1) • (frame.child.num - frame.child.den, frame.child.num + frame.child.den))
    rw [hw, ih, tGrade_add_zsmul_V] at hstep
    have hq := two_mul_tri (-(i : ℤ))
    have hq' := two_mul_tri (-(i : ℤ) - 1)
    have key : 2 * ((-(i : ℤ) - 1) * (-(i : ℤ) - 1 - 1) / 2) =
        2 * (-(i : ℤ) * (-(i : ℤ) - 1) / 2 + ((i : ℤ) + 1)) := by
      linear_combination hq' - hq
    have hQ : (-(i : ℤ) - 1) * (-(i : ℤ) - 1 - 1) / 2 =
        -(i : ℤ) * (-(i : ℤ) - 1) / 2 + ((i : ℤ) + 1) := by
      linarith
    linear_combination (-1 : ℤ) * hstep + frame.child.periodDenominator * hQ

/-- The kernel period: `F(z + kU) = F z`, since the constant `c_U` vanishes. -/
theorem packet_U_zsmul (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (z : Site) (k : ℤ) :
    F (z + k • frame.child.modifiedDeck.kernel) = F z := by
  have hU : ∀ s : Site, F (s + frame.child.modifiedDeck.kernel) = F s := by
    intro s
    obtain ⟨hUs, -⟩ := hP.periods
    rw [hUs s, frame.coherentConstantU_eq_zero, add_zero]
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [add_smul, one_smul, ← add_assoc, hU, ih]
  | pred i ih =>
    have h2 := hU (z + (-(i : ℤ) - 1) • frame.child.modifiedDeck.kernel)
    rw [add_assoc, smul_add_self_site, show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring, ih] at h2
    exact h2.symm

/-- **The representative formula** (task 72 (2)): if `y = x + lV + kU`, then the field at `x` is the field at `y` shifted by the
transverse closed form, `F x = F y + (−l) t(y) − T·((−l)(−l−1)/2) + (−l) c_V`. The kernel period contributes nothing. -/
theorem field_rep_formula (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (x y : Site) (l k : ℤ)
    (hy : y = x + l • (frame.child.num - frame.child.den, frame.child.num + frame.child.den) +
      k • frame.child.modifiedDeck.kernel) :
    F x = F y + (-l) * frame.tGrade y - frame.child.periodDenominator * ((-l) * (-l - 1) / 2) +
      (-l) * frame.coherentConstantV := by
  have hx : x = (y + (-l) • (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) +
      (-k) • frame.child.modifiedDeck.kernel := by
    rw [hy, neg_smul, neg_smul]
    abel
  rw [hx, packet_U_zsmul frame hP, packet_V_zsmul frame hP]

end FLatticePaper.W1VShift
