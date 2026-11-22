import FLatticePaper.Plane.Induction.ChildFrame
import FLatticePaper.Plane.PeriodCocycle
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.LinearCombination

namespace FLatticePaper.Induction
open Farey

namespace ChildFrame
variable (frame : ChildFrame) (F : Field)

/-- `a·z` with `a = (N, −D)`. -/
def parentSlope (z : Site) : ℤ := frame.parents.odd.num * z.1 - frame.parents.odd.den * z.2
/-- The price `P(z) = F(z) − F(z − v) − ε a·z`. -/
def price (z : Site) : ℤ := F z - F (z - frame.parentShift) - frame.eps * frame.parentSlope z
/-- The signed short slip `D_η(z) = F(z) − F(z + ησ)`. -/
def slip (η : ℤ) (z : Site) : ℤ := F z - F (z + η • frame.shortShift)
/-- The rounded slip `J_η = ⌈D_η/2⌉`. -/
def roundedSlip (η : ℤ) (z : Site) : ℤ := (frame.slip F η z + 1) / 2
/-- The chain potential `Φ_η(z) = D_η(z) + P(z + ησ)`. -/
def chainPotential (η : ℤ) (z : Site) : ℤ := frame.slip F η z + frame.price F (z + η • frame.shortShift)
/-- The chain sheet `h_η(z) = F(z + ησ − v) + ε a·(z + ησ)`. -/
def chainSheet (η : ℤ) (z : Site) : ℤ :=
  F (z + η • frame.shortShift - frame.parentShift) + frame.eps * frame.parentSlope (z + η • frame.shortShift)
/-- The grade `K = A·P + C·J_η`. -/
def cutGrade (A C η : ℤ) (z : Site) : ℤ := A * frame.price F z + C * frame.roundedSlip F η z

end ChildFrame

/-- The modified kernel of the even child is `(d, n)`. -/
theorem ChildFrame.child_modifiedDeck_kernel (frame : ChildFrame) :
    frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) := by
  have hEven : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, hEven, Fraction.unmodifiedDeck]

/-- The modified transverse period of the even child is `(n − d, n + d)`. -/
theorem ChildFrame.child_modifiedDeck_transverse (frame : ChildFrame) :
    frame.child.modifiedDeck.transverse =
      (frame.child.num - frame.child.den, frame.child.num + frame.child.den) := by
  simp [Fraction.modifiedDeck, Fraction.unmodifiedDeck]

theorem ChildFrame.eps_sq (frame : ChildFrame) : frame.eps ^ 2 = 1 := by
  rcases frame.eps_unit with h | h <;> rw [h] <;> norm_num

theorem ChildFrame.parentSlope_kernel (frame : ChildFrame) :
    frame.parentSlope frame.child.modifiedDeck.kernel = frame.eps := by
  rw [ChildFrame.child_modifiedDeck_kernel]
  show frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = frame.eps
  rw [ChildFrame.eps_eq]

theorem ChildFrame.roundedSlip_eq_ceil (frame : ChildFrame) (F : Field) (η : ℤ) (z : Site) :
    (frame.roundedSlip F η z : ℚ) = ⌈((frame.slip F η z : ℚ) / 2)⌉ := by
  unfold ChildFrame.roundedSlip
  have hc : ⌈((frame.slip F η z : ℚ) / 2)⌉ = (frame.slip F η z + 1) / 2 := by
    rw [Int.ceil_eq_iff]
    have h1 : 2 * ((frame.slip F η z + 1) / 2 - 1) < frame.slip F η z := by omega
    have h2 : frame.slip F η z ≤ 2 * ((frame.slip F η z + 1) / 2) := by omega
    have h1' : (2 * (((frame.slip F η z + 1) / 2 : ℤ) - 1) : ℚ) < (frame.slip F η z : ℚ) := by
      exact_mod_cast h1
    have h2' : (frame.slip F η z : ℚ) ≤ (2 * ((frame.slip F η z + 1) / 2 : ℤ) : ℚ) := by
      exact_mod_cast h2
    constructor
    · linarith
    · linarith
  rw [hc]

theorem ChildFrame.chainPotential_eq (frame : ChildFrame) (F : Field) (η : ℤ) (z : Site) :
    frame.chainPotential F η z = F z - frame.chainSheet F η z := by
  unfold ChildFrame.chainPotential ChildFrame.slip ChildFrame.price ChildFrame.chainSheet
  ring

theorem ChildFrame.price_kernel (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (z : Site) :
    frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z - 1 := by
  have hU := frame.child_modifiedDeck_kernel
  have hsq := frame.eps_sq
  have e1 : F (z + frame.child.modifiedDeck.kernel) = F z + cU := h.1 z
  have e2 : F (z + frame.child.modifiedDeck.kernel - frame.parentShift) =
      F (z - frame.parentShift) + cU := by
    rw [show z + frame.child.modifiedDeck.kernel - frame.parentShift =
      (z - frame.parentShift) + frame.child.modifiedDeck.kernel by abel]
    exact h.1 _
  have e3 : frame.parentSlope (z + frame.child.modifiedDeck.kernel) =
      frame.parentSlope z + frame.eps := by
    unfold ChildFrame.parentSlope
    simp only [Prod.fst_add, Prod.snd_add, hU, ChildFrame.eps_eq]
    ring
  unfold ChildFrame.price
  rw [e1, e2, e3]
  linear_combination (-1 : ℤ) * hsq

theorem ChildFrame.price_transverse (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (z : Site) :
    frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z := by
  have hV := frame.child_modifiedDeck_transverse
  have e1 : F (z + frame.child.modifiedDeck.transverse) =
      F z - frame.child.transverseGrade z + cV := h.2 z
  have e2 : F (z + frame.child.modifiedDeck.transverse - frame.parentShift) =
      F (z - frame.parentShift) - frame.child.transverseGrade (z - frame.parentShift) + cV := by
    rw [show z + frame.child.modifiedDeck.transverse - frame.parentShift =
      (z - frame.parentShift) + frame.child.modifiedDeck.transverse by abel]
    exact h.2 _
  have e3 : frame.parentSlope (z + frame.child.modifiedDeck.transverse) =
      frame.parentSlope z + frame.parentSlope frame.child.modifiedDeck.transverse := by
    unfold ChildFrame.parentSlope
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have e4 : frame.child.transverseGrade (z - frame.parentShift) =
      frame.child.transverseGrade z - frame.child.transverseGrade frame.parentShift :=
    Fraction.transverseGrade_sub _ _ _
  have e5 : frame.child.transverseGrade frame.parentShift +
      frame.eps * frame.parentSlope frame.child.modifiedDeck.transverse = 0 := by
    rw [hV]
    unfold ChildFrame.parentShift ChildFrame.parentSlope Fraction.transverseGrade
    ring
  unfold ChildFrame.price
  rw [e1, e2, e3, e4]
  linear_combination (-1 : ℤ) * e5

theorem ChildFrame.slip_kernel (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (η : ℤ) (z : Site) :
    frame.slip F η (z + frame.child.modifiedDeck.kernel) = frame.slip F η z := by
  unfold ChildFrame.slip
  have e1 : F (z + frame.child.modifiedDeck.kernel) = F z + cU := h.1 z
  have e2 : F (z + frame.child.modifiedDeck.kernel + η • frame.shortShift) =
      F (z + η • frame.shortShift) + cU := by
    rw [show z + frame.child.modifiedDeck.kernel + η • frame.shortShift =
      (z + η • frame.shortShift) + frame.child.modifiedDeck.kernel by abel]
    exact h.1 _
  rw [e1, e2]
  ring

theorem ChildFrame.slip_transverse (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (η : ℤ) (z : Site) :
    frame.slip F η (z + frame.child.modifiedDeck.transverse) = frame.slip F η z + 2 * η := by
  unfold ChildFrame.slip
  have e1 : F (z + frame.child.modifiedDeck.transverse) =
      F z - frame.child.transverseGrade z + cV := h.2 z
  have e2 : F (z + frame.child.modifiedDeck.transverse + η • frame.shortShift) =
      F (z + η • frame.shortShift) - frame.child.transverseGrade (z + η • frame.shortShift) + cV := by
    rw [show z + frame.child.modifiedDeck.transverse + η • frame.shortShift =
      (z + η • frame.shortShift) + frame.child.modifiedDeck.transverse by abel]
    exact h.2 _
  have e3 : frame.child.transverseGrade (z + η • frame.shortShift) =
      frame.child.transverseGrade z + frame.child.transverseGrade (η • frame.shortShift) := by
    unfold Fraction.transverseGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hε : frame.eps = frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num :=
    ChildFrame.eps_eq frame
  have hsq := frame.eps_sq
  have e4 : frame.child.transverseGrade (η • frame.shortShift) = 2 * η := by
    unfold Fraction.transverseGrade ChildFrame.shortShift
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (-2 * η * frame.eps) * hε + (2 * η) * hsq
  rw [e1, e2, e3]
  linear_combination e4

theorem ChildFrame.roundedSlip_kernel (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (η : ℤ) (z : Site) :
    frame.roundedSlip F η (z + frame.child.modifiedDeck.kernel) = frame.roundedSlip F η z := by
  unfold ChildFrame.roundedSlip
  rw [frame.slip_kernel F h η z]

theorem ChildFrame.roundedSlip_transverse (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (η : ℤ) (z : Site) :
    frame.roundedSlip F η (z + frame.child.modifiedDeck.transverse) = frame.roundedSlip F η z + η := by
  unfold ChildFrame.roundedSlip
  rw [frame.slip_transverse F h η z]
  omega

theorem ChildFrame.chainPotential_kernel (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (η : ℤ) (z : Site) :
    frame.chainPotential F η (z + frame.child.modifiedDeck.kernel) =
      frame.chainPotential F η z - 1 := by
  unfold ChildFrame.chainPotential
  rw [frame.slip_kernel F h η z,
    show z + frame.child.modifiedDeck.kernel + η • frame.shortShift =
      (z + η • frame.shortShift) + frame.child.modifiedDeck.kernel by abel,
    frame.price_kernel F h (z + η • frame.shortShift)]
  ring

theorem ChildFrame.chainPotential_transverse (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (η : ℤ) (z : Site) :
    frame.chainPotential F η (z + frame.child.modifiedDeck.transverse) =
      frame.chainPotential F η z + 2 * η := by
  unfold ChildFrame.chainPotential
  rw [frame.slip_transverse F h η z,
    show z + frame.child.modifiedDeck.transverse + η • frame.shortShift =
      (z + η • frame.shortShift) + frame.child.modifiedDeck.transverse by abel,
    frame.price_transverse F h (z + η • frame.shortShift)]
  ring

theorem ChildFrame.cutGrade_kernel (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (A C η : ℤ) (z : Site) :
    frame.cutGrade F A C η (z + frame.child.modifiedDeck.kernel) = frame.cutGrade F A C η z - A := by
  unfold ChildFrame.cutGrade
  rw [frame.price_kernel F h z, frame.roundedSlip_kernel F h η z]
  ring

theorem ChildFrame.cutGrade_transverse (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (A C η : ℤ) (z : Site) :
    frame.cutGrade F A C η (z + frame.child.modifiedDeck.transverse) =
      frame.cutGrade F A C η z + C * η := by
  unfold ChildFrame.cutGrade
  rw [frame.price_transverse F h z, frame.roundedSlip_transverse F h η z]
  ring

/-- Translating by `n` kernel periods shifts the cut grade by `-n A`. -/
theorem ChildFrame.cutGrade_kernel_zsmul (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (A C η n : ℤ) (z : Site) :
    frame.cutGrade F A C η (z + n • frame.child.modifiedDeck.kernel) =
      frame.cutGrade F A C η z - n * A := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have e : z + ((k : ℤ) + 1) • frame.child.modifiedDeck.kernel =
        (z + (k : ℤ) • frame.child.modifiedDeck.kernel) + frame.child.modifiedDeck.kernel := by
      rw [add_smul, one_smul, add_assoc]
    rw [e, frame.cutGrade_kernel F h A C η, ih]
    ring
  | pred k ih =>
    have e : z + (-(k : ℤ)) • frame.child.modifiedDeck.kernel =
        (z + (-(k : ℤ) - 1) • frame.child.modifiedDeck.kernel) + frame.child.modifiedDeck.kernel := by
      rw [add_assoc, sub_smul, one_smul]
      abel
    have h1 := frame.cutGrade_kernel F h A C η (z + (-(k : ℤ) - 1) • frame.child.modifiedDeck.kernel)
    rw [← e, ih] at h1
    linear_combination (-1 : ℤ) * h1

/-- Translating by `n` transverse periods shifts the cut grade by `n C η`. -/
theorem ChildFrame.cutGrade_transverse_zsmul (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (A C η n : ℤ) (z : Site) :
    frame.cutGrade F A C η (z + n • frame.child.modifiedDeck.transverse) =
      frame.cutGrade F A C η z + n * (C * η) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have e : z + ((k : ℤ) + 1) • frame.child.modifiedDeck.transverse =
        (z + (k : ℤ) • frame.child.modifiedDeck.transverse) + frame.child.modifiedDeck.transverse := by
      rw [add_smul, one_smul, add_assoc]
    rw [e, frame.cutGrade_transverse F h A C η, ih]
    ring
  | pred k ih =>
    have e : z + (-(k : ℤ)) • frame.child.modifiedDeck.transverse =
        (z + (-(k : ℤ) - 1) • frame.child.modifiedDeck.transverse) + frame.child.modifiedDeck.transverse := by
      rw [add_assoc, sub_smul, one_smul]
      abel
    have h1 := frame.cutGrade_transverse F h A C η (z + (-(k : ℤ) - 1) • frame.child.modifiedDeck.transverse)
    rw [← e, ih] at h1
    linear_combination (-1 : ℤ) * h1

/-- Translating by `i U + j V` shifts the cut grade by `-i A + j C η`. -/
theorem ChildFrame.cutGrade_add_combine (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (A C η i j : ℤ) (z : Site) :
    frame.cutGrade F A C η (z + frame.child.modifiedDeck.combine i j) =
      frame.cutGrade F A C η z - i * A + j * (C * η) := by
  have e : z + frame.child.modifiedDeck.combine i j =
      (z + i • frame.child.modifiedDeck.kernel) + j • frame.child.modifiedDeck.transverse := by
    ext <;> simp [PeriodDeck.combine, zsmul_eq_mul] <;> ring
  rw [e, frame.cutGrade_transverse_zsmul F h A C η j, frame.cutGrade_kernel_zsmul F h A C η i]

end FLatticePaper.Induction
