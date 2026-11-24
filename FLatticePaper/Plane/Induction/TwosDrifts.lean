import FLatticePaper.Plane.Induction.TwosValues

/-! Task 72 / twos base: the drifts of the price and of the short slip of the standard field of `2^(k+1)` (the fields `priceDrift`
and `slipDrift` of `StrongResidual`), from the periods of `standardField` and the explicit frame.

The child is `(2k+3)/(2k+5)`, the odd parent `(k+1)/(k+2)`, `eps = −1`, `shortShift = (−2(k+2), −2(k+1))`,
`parentShift = (1, −(2k+3))`, `parentSlope z = (k+1) z₁ − (k+2) z₂`, the kernel is `(2k+5, 2k+3)` and the transverse is
`(−2, 4k+8)`. The periods are `F(z + kernel) = F z` and `F(z + transverse) = F z + (cV − t z)`. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- The kernel period: `F(z + kernel) = F z` for a field with the period constants `(0, cV)`. -/
theorem period_kernel_apply {fr : Fraction} {F : Field} {cV : ℤ} (h : HasGeneratorPeriods fr F 0 cV) (w : Site) :
    F (w + fr.modifiedDeck.kernel) = F w := by
  have h1 := periods_kernel h 1 w
  have hc : fr.modifiedDeck.combine 1 0 = fr.modifiedDeck.kernel := by
    apply Prod.ext <;> simp [PeriodDeck.combine]
  rw [hc] at h1
  simpa using h1

/-- The transverse period: `F(z + transverse) = F z + (cV − t z)` for a field with the period constants `(0, cV)`. -/
theorem period_transverse_apply {fr : Fraction} {F : Field} {cV : ℤ} (h : HasGeneratorPeriods fr F 0 cV) (w : Site) :
    F (w + fr.modifiedDeck.transverse) = F w + (cV - fr.transverseGrade w) := by
  have h1 := periods_transverse h 1 w
  have hc : fr.modifiedDeck.combine 0 1 = fr.modifiedDeck.transverse := by
    apply Prod.ext <;> simp [PeriodDeck.combine]
  have hct : chooseTwo 1 = 0 := by norm_num [chooseTwo]
  rw [hc, hct] at h1
  simpa using h1

/-- The periods of the standard field of `2^(k+1)` in the form of the two period lemmas. -/
theorem twos_standardField_hasPeriods (k : ℕ) :
    HasGeneratorPeriods (frameAt (List.replicate (k + 1) Digit.two)).child
      (standardField (List.replicate (k + 1) Digit.two)) 0 (ladderEvenConstantV (2 * (k : ℤ) + 4)) := by
  have hvalid : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) := ⟨by omega, by omega⟩
  obtain ⟨S, hagree, hperiod, -⟩ := ladderOdd_exists_extension hvalid
  exact twos_standardField_periods k hagree hperiod

theorem twos_parents_explicit (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).parents =
      ⟨⟨(k : ℤ) + 1, (k : ℤ) + 2⟩, ⟨1, 1⟩⟩ := by
  show parentsAt (List.replicate (k + 1) Digit.two) = _
  rw [parentsAt_replicate_two_explicit]
  push_cast
  rfl

theorem twos_eps_explicit (k : ℕ) : (frameAt (List.replicate (k + 1) Digit.two)).eps = -1 :=
  twos_frame_eps (k + 1)

theorem twos_parentShift_explicit (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).parentShift = (1, -(2 * (k : ℤ) + 3)) := by
  unfold ChildFrame.parentShift
  rw [twos_eps_explicit, twos_parents_explicit]
  ext <;> simp <;> ring

theorem twos_parentSlope_explicit (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).parentSlope z =
      ((k : ℤ) + 1) * z.1 - ((k : ℤ) + 2) * z.2 := by
  unfold ChildFrame.parentSlope
  rw [twos_parents_explicit]

theorem twos_shortShift_explicit (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).shortShift = (-2 * ((k : ℤ) + 2), -2 * ((k : ℤ) + 1)) := by
  unfold ChildFrame.shortShift
  rw [twos_eps_explicit, twos_parents_explicit]
  ext <;> simp <;> ring

theorem twos_child_explicit (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).child = ⟨2 * (k : ℤ) + 3, 2 * (k : ℤ) + 5⟩ :=
  twos_child_eq k

theorem twos_kernel_explicit (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel = (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) := by
  rw [ChildFrame.child_modifiedDeck_kernel, twos_child_explicit]

theorem twos_transverse_explicit (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse = (-2, 4 * (k : ℤ) + 8) := by
  rw [ChildFrame.child_modifiedDeck_transverse, twos_child_explicit]
  ext <;> simp <;> ring

theorem twos_transverseGrade_explicit (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).child.transverseGrade z =
      (2 * (k : ℤ) + 5) * z.2 - (2 * (k : ℤ) + 3) * z.1 := by
  rw [twos_child_explicit]
  unfold Fraction.transverseGrade
  simp

/-- **The slip drift along the kernel.** `D_η(z + U) − D_η z = 0`. -/
theorem twos_slip_drift_kernel (k : ℕ) (η : ℤ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).slip
        (standardField (List.replicate (k + 1) Digit.two)) η
        (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel) -
      (frameAt (List.replicate (k + 1) Digit.two)).slip
        (standardField (List.replicate (k + 1) Digit.two)) η z = 0 := by
  have hP := twos_standardField_hasPeriods k
  unfold ChildFrame.slip
  have e : z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel +
      η • (frameAt (List.replicate (k + 1) Digit.two)).shortShift =
      (z + η • (frameAt (List.replicate (k + 1) Digit.two)).shortShift) +
        (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel := by abel
  rw [e, period_kernel_apply hP z, period_kernel_apply hP]
  ring

/-- **The slip drift along the transverse.** `D_η(z + T) − D_η z = 2η` for `η = ±1`. -/
theorem twos_slip_drift_transverse (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).slip
        (standardField (List.replicate (k + 1) Digit.two)) η
        (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse) -
      (frameAt (List.replicate (k + 1) Digit.two)).slip
        (standardField (List.replicate (k + 1) Digit.two)) η z = 2 * η := by
  have hP := twos_standardField_hasPeriods k
  unfold ChildFrame.slip
  have e : z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse +
      η • (frameAt (List.replicate (k + 1) Digit.two)).shortShift =
      (z + η • (frameAt (List.replicate (k + 1) Digit.two)).shortShift) +
        (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse := by abel
  rw [e, period_transverse_apply hP z, period_transverse_apply hP]
  rw [twos_transverseGrade_explicit, twos_transverseGrade_explicit, twos_shortShift_explicit]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **The price drift along the kernel.** `P(z + U) − P z = −1`. -/
theorem twos_price_drift_kernel (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two))
        (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel) -
      (frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) z = -1 := by
  have hP := twos_standardField_hasPeriods k
  unfold ChildFrame.price
  have e : z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel -
      (frameAt (List.replicate (k + 1) Digit.two)).parentShift =
      (z - (frameAt (List.replicate (k + 1) Digit.two)).parentShift) +
        (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel := by abel
  rw [e, period_kernel_apply hP z, period_kernel_apply hP, twos_eps_explicit,
    twos_parentSlope_explicit, twos_parentSlope_explicit, twos_kernel_explicit]
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- **The price drift along the transverse.** `P(z + T) − P z = 0`. -/
theorem twos_price_drift_transverse (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two))
        (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse) -
      (frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) z = 0 := by
  have hP := twos_standardField_hasPeriods k
  unfold ChildFrame.price
  have e : z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse -
      (frameAt (List.replicate (k + 1) Digit.two)).parentShift =
      (z - (frameAt (List.replicate (k + 1) Digit.two)).parentShift) +
        (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse := by abel
  rw [e, period_transverse_apply hP z, period_transverse_apply hP, twos_eps_explicit,
    twos_parentSlope_explicit, twos_parentSlope_explicit, twos_transverse_explicit,
    twos_transverseGrade_explicit, twos_transverseGrade_explicit, twos_parentShift_explicit]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

end FLatticePaper.Induction
