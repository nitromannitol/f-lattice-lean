import FLatticePaper.Plane.OdometerTheorem
import FLatticePaper.Plane.PeriodCocycle

/-! The algebra of the surgical global odometers (`lemma:global_odometers`, the standard case, eq:periodicity_growth).

For `g` on `Z^2` with the two translation rules of `HasGeneratorPeriods` (kernel `v_{n/d,1}` with constant `k_1`,
transverse `v_{n/d,2}` with the affine term `a_{n/d,2}·x` and constant `k_2`), the corrected function
`g - (1/2) x^T M x - b^T x` is periodic for the whole lattice of the period deck, for some `b ∈ R^2`. The lattice identities are
`M v_1 = 0`, `M v_2 = a_2`, `a_2·v_1 = 0`, `a_2·v_2 = -T(n,d)`, with `M = Fraction.matrix` and `T = periodDenominator`. -/

namespace FLatticePaper

open Farey
open scoped Matrix

theorem transverseGrade_kernel_zero (fraction : Fraction) :
    fraction.transverseGrade fraction.modifiedDeck.kernel = 0 := by
  unfold Fraction.transverseGrade Fraction.modifiedDeck Fraction.periodMultiplicity
  split_ifs <;> simp <;> ring

theorem transverseGrade_transverse (fraction : Fraction) :
    fraction.transverseGrade fraction.modifiedDeck.transverse = fraction.periodDenominator := by
  unfold Fraction.transverseGrade Fraction.modifiedDeck Fraction.unmodifiedDeck Fraction.periodDenominator
  simp only
  ring

theorem det_kernel_transverse (fraction : Fraction) :
    fraction.modifiedDeck.kernel.1 * fraction.modifiedDeck.transverse.2 -
      fraction.modifiedDeck.kernel.2 * fraction.modifiedDeck.transverse.1 =
      fraction.periodMultiplicity * fraction.periodDenominator := by
  unfold Fraction.modifiedDeck Fraction.unmodifiedDeck Fraction.periodDenominator
  simp only
  ring

theorem transverseGrade_add_mul (fraction : Fraction) (s t : Site) (m : ℤ) :
    fraction.transverseGrade (s + (m * t.1, m * t.2)) = fraction.transverseGrade s + m * fraction.transverseGrade t := by
  unfold Fraction.transverseGrade
  show fraction.den * (s.2 + m * t.2) - fraction.num * (s.1 + m * t.1) =
    (fraction.den * s.2 - fraction.num * s.1) + m * (fraction.den * t.2 - fraction.num * t.1)
  ring

/-- The matrix quadratic form of the period matrix, explicitly. -/
theorem matrix_quadratic_explicit (fraction : Fraction) (y : Site) :
    siteVector y ⬝ᵥ (fraction.matrix *ᵥ siteVector y) =
      (-(fraction.num : ℝ) ^ 2 * (y.1 : ℝ) ^ 2 + 2 * (fraction.den : ℝ) * (fraction.num : ℝ) * (y.1 : ℝ) * (y.2 : ℝ) -
        (fraction.den : ℝ) ^ 2 * (y.2 : ℝ) ^ 2) / (fraction.periodDenominator : ℝ) := by
  simp [Fraction.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, siteVector]
  ring

/-- Along the kernel the field shifts by the constant. -/
theorem field_kernel_shift {field : Field} {c : ℤ} {k : Site} (E : ∀ s, field (s + k) = field s + c) :
    ∀ (i : ℤ) (s : Site), field (s + (i * k.1, i * k.2)) = field s + i * c := by
  intro i
  refine Int.induction_on i ?_ ?_ ?_
  · intro s
    have e : s + ((0 : ℤ) * k.1, (0 : ℤ) * k.2) = s := by
      ext <;> simp
    rw [e]
    simp
  · intro n ih s
    have e : s + (((n : ℤ) + 1) * k.1, ((n : ℤ) + 1) * k.2) = (s + ((n : ℤ) * k.1, (n : ℤ) * k.2)) + k := by
      apply Prod.ext <;> simp <;> ring
    rw [e, E, ih]
    ring
  · intro n ih s
    have e : s + ((-(n : ℤ)) * k.1, (-(n : ℤ)) * k.2) =
        (s + ((-(n : ℤ) - 1) * k.1, (-(n : ℤ) - 1) * k.2)) + k := by
      apply Prod.ext <;> simp <;> ring
    have h1 := ih s
    rw [e, E] at h1
    linarith

/-- Along the transverse vector the field shifts by the grade, with the quadratic correction (over the reals). -/
theorem field_transverse_shift (fraction : Fraction) {field : Field} {c2 : ℤ} {t : Site}
    (E : ∀ s, field (s + t) = field s - fraction.transverseGrade s + c2) :
    ∀ (j : ℤ) (s : Site), (field (s + (j * t.1, j * t.2)) : ℝ) =
      (field s : ℝ) - (j : ℝ) * (fraction.transverseGrade s : ℝ) -
        ((j : ℝ) * ((j : ℝ) - 1) / 2) * (fraction.transverseGrade t : ℝ) + (j : ℝ) * (c2 : ℝ) := by
  intro j
  refine Int.induction_on j ?_ ?_ ?_
  · intro s
    have e : s + ((0 : ℤ) * t.1, (0 : ℤ) * t.2) = s := by
      ext <;> simp
    rw [e]
    simp
  · intro n ih s
    have e : s + (((n : ℤ) + 1) * t.1, ((n : ℤ) + 1) * t.2) = (s + ((n : ℤ) * t.1, (n : ℤ) * t.2)) + t := by
      apply Prod.ext <;> simp <;> ring
    have h1 := E (s + ((n : ℤ) * t.1, (n : ℤ) * t.2))
    rw [← e] at h1
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
    push_cast at h2
    rw [transverseGrade_add_mul] at h2
    have ih' := ih s
    push_cast at ih' h2 ⊢
    linear_combination h2 + ih'
  · intro n ih s
    have e : s + ((-(n : ℤ) - 1) * t.1, (-(n : ℤ) - 1) * t.2) + t = s + ((-(n : ℤ)) * t.1, (-(n : ℤ)) * t.2) := by
      apply Prod.ext <;> simp <;> ring
    have h1 := E (s + ((-(n : ℤ) - 1) * t.1, (-(n : ℤ) - 1) * t.2))
    rw [e] at h1
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
    push_cast at h2
    rw [transverseGrade_add_mul] at h2
    have ih' := ih s
    push_cast at ih' h2 ⊢
    linear_combination ih' - h2

/-- Two real coefficients solving the 2×2 system `b·k = A`, `b·t = B` when the determinant of `(k, t)` is nonzero. -/
theorem surgical_pair_solution {k1 k2 t1 t2 A B : ℝ} (h : k1 * t2 - k2 * t1 ≠ 0) :
    ∃ b0 b1 : ℝ, b0 * k1 + b1 * k2 = A ∧ b0 * t1 + b1 * t2 = B := by
  refine ⟨(A * t2 - k2 * B) / (k1 * t2 - k2 * t1), (k1 * B - t1 * A) / (k1 * t2 - k2 * t1), ?_, ?_⟩
  · have e : (A * t2 - k2 * B) / (k1 * t2 - k2 * t1) * k1 + (k1 * B - t1 * A) / (k1 * t2 - k2 * t1) * k2 =
        A * (k1 * t2 - k2 * t1) / (k1 * t2 - k2 * t1) := by ring
    rw [e, mul_div_assoc, div_self h, mul_one]
  · have e : (A * t2 - k2 * B) / (k1 * t2 - k2 * t1) * t1 + (k1 * B - t1 * A) / (k1 * t2 - k2 * t1) * t2 =
        B * (k1 * t2 - k2 * t1) / (k1 * t2 - k2 * t1) := by ring
    rw [e, mul_div_assoc, div_self h, mul_one]

/-- The matrix quadratic form changes along `x ↦ x + i·k + j·t` by `-2 j G(x) - j² T`, with `G` the transverse grade. -/
theorem surgical_quad_shift (fraction : Fraction) (hT : (fraction.periodDenominator : ℝ) ≠ 0) (x : Site) (i j : ℤ) :
    siteVector (x + PeriodDeck.combine fraction.modifiedDeck i j) ⬝ᵥ
        (fraction.matrix *ᵥ siteVector (x + PeriodDeck.combine fraction.modifiedDeck i j)) -
      siteVector x ⬝ᵥ (fraction.matrix *ᵥ siteVector x) =
    -2 * (j : ℝ) * (fraction.transverseGrade x : ℝ) - (j : ℝ) ^ 2 * (fraction.periodDenominator : ℝ) := by
  have hTdef : (fraction.periodDenominator : ℝ) =
      (fraction.den : ℝ) ^ 2 + 2 * (fraction.den : ℝ) * (fraction.num : ℝ) - (fraction.num : ℝ) ^ 2 := by
    simp [Fraction.periodDenominator]
  have hTpoly : (fraction.den : ℝ) ^ 2 + 2 * (fraction.den : ℝ) * (fraction.num : ℝ) - (fraction.num : ℝ) ^ 2 ≠ 0 := by
    rw [← hTdef]
    exact hT
  have hg : (fraction.transverseGrade x : ℝ) = (fraction.den : ℝ) * (x.2 : ℝ) - (fraction.num : ℝ) * (x.1 : ℝ) := by
    simp [Fraction.transverseGrade]
  have hk1 : fraction.modifiedDeck.kernel.1 = fraction.periodMultiplicity * fraction.den := rfl
  have hk2 : fraction.modifiedDeck.kernel.2 = fraction.periodMultiplicity * fraction.num := rfl
  have ht1 : fraction.modifiedDeck.transverse.1 = fraction.num - fraction.den := rfl
  have ht2 : fraction.modifiedDeck.transverse.2 = fraction.num + fraction.den := rfl
  simp only [matrix_quadratic_explicit, PeriodDeck.combine, hk1, hk2, ht1, ht2, Prod.fst_add, Prod.snd_add,
    hTdef, hg]
  push_cast
  rw [div_sub_div_same, div_eq_iff hTpoly]
  ring

/-- Corrected periodicity (eq:periodicity_growth, standard case): for some real `b`, the function
`g - (1/2) x^T M x - b·x` is invariant under the whole lattice of the modified period deck, given the two
generator periods of `g`. The corrector `b` solves `b·v_{n/d,1} = c_1` and `b·v_{n/d,2} = c_2 + T/2`. -/
theorem surgical_corrected_periodicity {fraction : Fraction} (hint : fraction.InUnitInterval) {field : Field}
    {c1 c2 : ℤ} (hperiod : HasGeneratorPeriods fraction field c1 c2) :
    ∃ b : Fin 2 → ℝ, ∀ v ∈ fraction.modifiedDeck.span, ∀ x : Site,
      (field (x + v) : ℝ) - (1 / 2 : ℝ) * (siteVector (x + v) ⬝ᵥ (fraction.matrix *ᵥ siteVector (x + v))) -
          (b ⬝ᵥ siteVector (x + v)) =
        (field x : ℝ) - (1 / 2 : ℝ) * (siteVector x ⬝ᵥ (fraction.matrix *ᵥ siteVector x)) -
          (b ⬝ᵥ siteVector x) := by
  obtain ⟨hK, hT⟩ := hperiod
  have hTpos : (0 : ℤ) < fraction.periodDenominator := Fraction.periodDenominator_pos hint
  have hTne : (fraction.periodDenominator : ℝ) ≠ 0 := by exact_mod_cast hTpos.ne'
  have hμ : fraction.periodMultiplicity ≠ 0 := by
    unfold Fraction.periodMultiplicity
    split_ifs <;> norm_num
  have hdetZ : fraction.modifiedDeck.kernel.1 * fraction.modifiedDeck.transverse.2 -
      fraction.modifiedDeck.kernel.2 * fraction.modifiedDeck.transverse.1 ≠ 0 := by
    rw [det_kernel_transverse fraction]
    exact mul_ne_zero hμ hTpos.ne'
  have hdet : (fraction.modifiedDeck.kernel.1 : ℝ) * (fraction.modifiedDeck.transverse.2 : ℝ) -
      (fraction.modifiedDeck.kernel.2 : ℝ) * (fraction.modifiedDeck.transverse.1 : ℝ) ≠ 0 := by
    exact_mod_cast hdetZ
  obtain ⟨b0, b1, hbk, hbt⟩ :=
    surgical_pair_solution (A := (c1 : ℝ)) (B := (c2 : ℝ) + (fraction.periodDenominator : ℝ) / 2) hdet
  refine ⟨![b0, b1], ?_⟩
  have hbd : ∀ y : Site, (![b0, b1] : Fin 2 → ℝ) ⬝ᵥ siteVector y = b0 * (y.1 : ℝ) + b1 * (y.2 : ℝ) := by
    intro y
    simp [dotProduct, Fin.sum_univ_two, siteVector]
  intro v hv x
  obtain ⟨i, j, rfl⟩ := hv
  have e : x + PeriodDeck.combine fraction.modifiedDeck i j =
      (x + (j * fraction.modifiedDeck.transverse.1, j * fraction.modifiedDeck.transverse.2)) +
        (i * fraction.modifiedDeck.kernel.1, i * fraction.modifiedDeck.kernel.2) := by
    ext <;> simp [PeriodDeck.combine] <;> ring
  have hgK : (field (x + PeriodDeck.combine fraction.modifiedDeck i j) : ℝ) =
      (field (x + (j * fraction.modifiedDeck.transverse.1, j * fraction.modifiedDeck.transverse.2)) : ℝ) +
        (i : ℝ) * (c1 : ℝ) := by
    rw [e]
    exact_mod_cast field_kernel_shift hK i
      (x + (j * fraction.modifiedDeck.transverse.1, j * fraction.modifiedDeck.transverse.2))
  have hgT : (field (x + (j * fraction.modifiedDeck.transverse.1, j * fraction.modifiedDeck.transverse.2)) : ℝ) =
      (field x : ℝ) - (j : ℝ) * (fraction.transverseGrade x : ℝ) -
        ((j : ℝ) * ((j : ℝ) - 1) / 2) * (fraction.periodDenominator : ℝ) + (j : ℝ) * (c2 : ℝ) := by
    have h := field_transverse_shift fraction hT j x
    rw [transverseGrade_transverse] at h
    exact h
  have hQ := surgical_quad_shift fraction hTne x i j
  have hb : (![b0, b1] : Fin 2 → ℝ) ⬝ᵥ siteVector (x + PeriodDeck.combine fraction.modifiedDeck i j) -
      (![b0, b1] : Fin 2 → ℝ) ⬝ᵥ siteVector x =
      (i : ℝ) * (c1 : ℝ) + (j : ℝ) * ((c2 : ℝ) + (fraction.periodDenominator : ℝ) / 2) := by
    rw [hbd, hbd]
    simp only [PeriodDeck.combine, Prod.fst_add, Prod.snd_add]
    push_cast
    linear_combination (i : ℝ) * hbk + (j : ℝ) * hbt
  linear_combination hgK + hgT - (1 / 2 : ℝ) * hQ - hb

end FLatticePaper
