import FLatticePaper.Plane.Induction.BaseInputsProof

/-! Task 72 / Q28: the grade congruence of two native free representatives. For a child frame, `t(x) = n x₁ − d x₂` (`tGrade`) is linear,
`t(η σ) = −2η` (`tGrade_add_shortShift`), and a deck vector `combine i j` of the modified deck has grade `−j T` (the kernel has grade zero,
the transverse grade is `−T`). Hence for `w₁ = w₀ + η σ + λ₀ − λ₁` with `λᵢ` deck vectors, `t(w₁) − t(w₀) + 2η = T (j₁ − j₀)`. -/

namespace FLatticePaper.NativeCongruence

open FLatticePaper FLatticePaper.Induction

/-- `t` is linear under integer scalars: `t(η x) = η t(x)`. -/
theorem tGrade_smul (frame : ChildFrame) (η : ℤ) (x : Site) :
    frame.tGrade (η • x) = η * frame.tGrade x := by
  unfold ChildFrame.tGrade
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The grade of the short shift is `−2`, and of `η σ` is `−2η` (`η = ±1`). -/
theorem tGrade_shortShift_smul (frame : ChildFrame) (η : ℤ) :
    frame.tGrade (η • frame.shortShift) = -2 * η := by
  have h := frame.tGrade_add_shortShift 0
  have h0 : frame.tGrade (0 : Site) = 0 := by
    unfold ChildFrame.tGrade
    simp
  rw [zero_add, h0] at h
  rw [tGrade_smul, h]
  ring

/-- The grade of a modified-deck vector: `t(combine i j) = −j T`. The modified kernel is `μ (d, n)` (grade zero), the transverse is the
unmodified one (grade `−T`). -/
theorem tGrade_combine (frame : ChildFrame) (i j : ℤ) :
    frame.tGrade (frame.child.modifiedDeck.combine i j) = -(j * frame.child.periodDenominator) := by
  have ht : frame.tGrade frame.child.unmodifiedDeck.transverse = -frame.child.periodDenominator :=
    frame.tGrade_transverse
  have hk : frame.child.modifiedDeck.kernel = (Farey.Fraction.periodMultiplicity frame.child * frame.child.den,
      Farey.Fraction.periodMultiplicity frame.child * frame.child.num) := rfl
  have htr : frame.child.modifiedDeck.transverse = frame.child.unmodifiedDeck.transverse := rfl
  unfold ChildFrame.tGrade at ht ⊢
  unfold Farey.PeriodDeck.combine
  simp only [hk, htr]
  linear_combination j * ht

/-- `t` is additive. -/
theorem tGrade_add (frame : ChildFrame) (x y : Site) : frame.tGrade (x + y) = frame.tGrade x + frame.tGrade y := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- **The congruence of two native representatives (Q28, equation (1)).** If `w₁ = w₀ + ησ + λ₀ − λ₁` with `λᵢ` modified-deck vectors
`combine iᵢ jᵢ`, then `t(w₁) − t(w₀) + 2η = T (j₁ − j₀)`: the two grades agree modulo the period `T` up to the shift `−2η`. -/
theorem t_congruence (frame : ChildFrame) (w0 w1 : Site) (η : ℤ) (i0 j0 i1 j1 : ℤ)
    (hw : w1 = w0 + η • frame.shortShift + frame.child.modifiedDeck.combine i0 j0 -
      frame.child.modifiedDeck.combine i1 j1) :
    frame.tGrade w1 - frame.tGrade w0 + 2 * η = frame.child.periodDenominator * (j1 - j0) := by
  subst hw
  have hsub : ∀ x y : Site, frame.tGrade (x - y) = frame.tGrade x - frame.tGrade y := by
    intro x y
    unfold ChildFrame.tGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  rw [hsub, tGrade_add, tGrade_add, tGrade_shortShift_smul, tGrade_combine, tGrade_combine]
  ring

/-- **The exact grade shift.** If the grades of two native representatives differ by less than the period `T` after the shift `−2η`, then
`t(w₁) − t(w₀) = −2η` exactly. -/
theorem t_exact_of_bounds (frame : ChildFrame) (w0 w1 : Site) (η : ℤ) (i0 j0 i1 j1 : ℤ)
    (hw : w1 = w0 + η • frame.shortShift + frame.child.modifiedDeck.combine i0 j0 -
      frame.child.modifiedDeck.combine i1 j1)
    (hbd : |frame.tGrade w1 - frame.tGrade w0 + 2 * η| < frame.child.periodDenominator) :
    frame.tGrade w1 - frame.tGrade w0 = -2 * η := by
  have hc := t_congruence frame w0 w1 η i0 j0 i1 j1 hw
  have hdvd : frame.child.periodDenominator ∣ frame.tGrade w1 - frame.tGrade w0 + 2 * η := by
    rw [hc]
    exact Dvd.intro (j1 - j0) rfl
  have h0 := Int.eq_zero_of_abs_lt_dvd hdvd hbd
  linarith

end FLatticePaper.NativeCongruence
