import FLatticePaper.Farey.MatrixLattice
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.FieldSimp

namespace FLatticePaper

open Farey

/-- The two prescribed generator identities, in integer coordinates. -/
def HasGeneratorPeriods (fraction : Fraction) (field : Field) (constantU constantV : ℤ) : Prop :=
  (∀ site, field (site + fraction.modifiedDeck.kernel) = field site + constantU) ∧
  (∀ site, field (site + fraction.modifiedDeck.transverse) =
    field site - fraction.transverseGrade site + constantV)

noncomputable def matrixQuadratic (matrix : Matrix (Fin 2) (Fin 2) ℝ) (site : Site) : ℝ :=
  dotProduct (siteVector site) (matrix.mulVec (siteVector site)) / 2

/-- The real linear tilt with values `c_U` and `c_V+T/2` at the two periods. -/
noncomputable def periodicTilt (fraction : Fraction) (constantU constantV : ℤ) (site : Site) : ℝ :=
  let deck := fraction.modifiedDeck
  ((constantU : ℝ) * (deck.kernelNumerator site : ℝ) +
    ((constantV : ℝ) + (fraction.periodDenominator : ℝ) / 2) *
      (deck.transverseNumerator site : ℝ)) / (deck.det : ℝ)

noncomputable def periodRemainder (fraction : Fraction) (field : Field) (constantU constantV : ℤ)
    (site : Site) : ℝ :=
  (field site : ℝ) - matrixQuadratic fraction.matrix site - periodicTilt fraction constantU constantV site

theorem matrixQuadratic_eq_grade (fraction : Fraction) (site : Site) :
    matrixQuadratic fraction.matrix site =
      -((fraction.transverseGrade site : ℝ) ^ 2) / (2 * (fraction.periodDenominator : ℝ)) := by
  rw [matrixQuadratic, Fraction.matrix_mulVec_grade]
  simp [dotProduct, Fin.sum_univ_two, siteVector, Fraction.transverseGrade]
  ring

private theorem grade_add (fraction : Fraction) (first second : Site) :
    fraction.transverseGrade (first + second) =
      fraction.transverseGrade first + fraction.transverseGrade second := by
  dsimp [Fraction.transverseGrade]
  ring

private theorem grade_combine (fraction : Fraction) (kernelIndex transverseIndex : ℤ) :
    fraction.transverseGrade (fraction.modifiedDeck.combine kernelIndex transverseIndex) =
      fraction.periodDenominator * transverseIndex := by
  rw [Fraction.modifiedDeck_combine, Fraction.transverseGrade_combine]

theorem periodicTilt_add (fraction : Fraction) (constantU constantV : ℤ) (first second : Site) :
    periodicTilt fraction constantU constantV (first + second) =
      periodicTilt fraction constantU constantV first + periodicTilt fraction constantU constantV second := by
  simp only [periodicTilt, PeriodDeck.kernelNumerator, PeriodDeck.transverseNumerator,
    Prod.fst_add, Prod.snd_add, Int.cast_sub, Int.cast_mul, Int.cast_add]
  ring

theorem periodicTilt_combine {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    (constantU constantV kernelIndex transverseIndex : ℤ) :
    periodicTilt fraction constantU constantV (fraction.modifiedDeck.combine kernelIndex transverseIndex) =
      (kernelIndex : ℝ) * constantU +
        (transverseIndex : ℝ) * ((constantV : ℝ) + (fraction.periodDenominator : ℝ) / 2) := by
  have hdet : (fraction.modifiedDeck.det : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fraction.det_modifiedDeck_pos hinterval)
  simp only [periodicTilt, PeriodDeck.kernelNumerator_combine, PeriodDeck.transverseNumerator_combine,
    Int.cast_mul]
  apply (div_eq_iff hdet).mpr
  ring

private theorem quadratic_shift {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    (site : Site) (kernelIndex transverseIndex : ℤ) :
    matrixQuadratic fraction.matrix (site + fraction.modifiedDeck.combine kernelIndex transverseIndex) -
      matrixQuadratic fraction.matrix site =
      -(transverseIndex : ℝ) * (fraction.transverseGrade site : ℝ) -
        (fraction.periodDenominator : ℝ) * (transverseIndex : ℝ) ^ 2 / 2 := by
  have hden : (fraction.periodDenominator : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fraction.periodDenominator_pos hinterval)
  rw [matrixQuadratic_eq_grade, matrixQuadratic_eq_grade, grade_add, grade_combine]
  push_cast
  field_simp [hden]
  ring

private theorem tilt_quadratic_shift {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    (constantU constantV : ℤ) (site : Site) (kernelIndex transverseIndex : ℤ) :
    let point := site + fraction.modifiedDeck.combine kernelIndex transverseIndex
    matrixQuadratic fraction.matrix point + periodicTilt fraction constantU constantV point -
      (matrixQuadratic fraction.matrix site + periodicTilt fraction constantU constantV site) =
        (kernelIndex : ℝ) * constantU +
        (transverseIndex : ℝ) * (-(fraction.transverseGrade site : ℝ) + constantV) -
        (fraction.periodDenominator : ℝ) * (transverseIndex : ℝ) * (transverseIndex - 1) / 2 := by
  dsimp only
  rw [periodicTilt_add, periodicTilt_combine hinterval]
  linear_combination quadratic_shift hinterval site kernelIndex transverseIndex

private theorem combine_eq_zsmul (deck : PeriodDeck) (kernelIndex transverseIndex : ℤ) :
    deck.combine kernelIndex transverseIndex = kernelIndex • deck.kernel + transverseIndex • deck.transverse := by
  ext <;> simp [PeriodDeck.combine, zsmul_eq_mul]

private theorem combine_one_zero (deck : PeriodDeck) : deck.combine 1 0 = deck.kernel := by
  ext <;> simp [PeriodDeck.combine]

private theorem combine_zero_one (deck : PeriodDeck) : deck.combine 0 1 = deck.transverse := by
  ext <;> simp [PeriodDeck.combine]

/-- Subtracting the quadratic form and the real linear tilt leaves a
periodic remainder for the full modified lattice. -/
theorem periodRemainder_periodic {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {field : Field} {constantU constantV : ℤ}
    (hperiod : HasGeneratorPeriods fraction field constantU constantV)
    {period : Site} (hmem : period ∈ fraction.modifiedDeck.span) :
    Function.Periodic (periodRemainder fraction field constantU constantV) period := by
  have hkernel : Function.Periodic (periodRemainder fraction field constantU constantV)
      fraction.modifiedDeck.kernel := by
    intro site
    have hshift := tilt_quadratic_shift hinterval constantU constantV site 1 0
    simp only [combine_one_zero, Int.cast_one, Int.cast_zero] at hshift
    have hcast : (field (site + fraction.modifiedDeck.kernel) : ℝ) =
        (field site : ℝ) + constantU := by exact_mod_cast hperiod.1 site
    unfold periodRemainder
    linarith
  have htransverse : Function.Periodic (periodRemainder fraction field constantU constantV)
      fraction.modifiedDeck.transverse := by
    intro site
    have hshift := tilt_quadratic_shift hinterval constantU constantV site 0 1
    simp only [combine_zero_one, Int.cast_one, Int.cast_zero] at hshift
    have hcast : (field (site + fraction.modifiedDeck.transverse) : ℝ) =
        (field site : ℝ) - fraction.transverseGrade site + constantV := by
      exact_mod_cast hperiod.2 site
    unfold periodRemainder
    linarith
  obtain ⟨kernelIndex, transverseIndex, rfl⟩ := hmem
  rw [combine_eq_zsmul]
  exact (hkernel.zsmul kernelIndex).add_period (htransverse.zsmul transverseIndex)

/-- The joint cocycle formula for every integer combination of the prescribed
generators. The only constants are those of this particular field. -/
theorem generator_period_formula {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {field : Field} {constantU constantV : ℤ}
    (hperiod : HasGeneratorPeriods fraction field constantU constantV)
    (site : Site) (kernelIndex transverseIndex : ℤ) :
    (field (site + fraction.modifiedDeck.combine kernelIndex transverseIndex) : ℝ) =
      (field site : ℝ) + (kernelIndex : ℝ) * constantU +
      (transverseIndex : ℝ) * (-(fraction.transverseGrade site : ℝ) + constantV) -
      (fraction.periodDenominator : ℝ) * (transverseIndex : ℝ) * (transverseIndex - 1) / 2 := by
  have hrem := periodRemainder_periodic hinterval hperiod ⟨kernelIndex, transverseIndex, rfl⟩ site
  have htilt := tilt_quadratic_shift hinterval constantU constantV site kernelIndex transverseIndex
  dsimp only at htilt
  unfold periodRemainder at hrem
  linarith

private theorem dot_matrix_combine {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    (site : Site) (kernelIndex transverseIndex : ℤ) :
    dotProduct (siteVector site)
      (fraction.matrix.mulVec (siteVector (fraction.modifiedDeck.combine kernelIndex transverseIndex))) =
      -(transverseIndex : ℝ) * (fraction.transverseGrade site : ℝ) := by
  have hden : (fraction.periodDenominator : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fraction.periodDenominator_pos hinterval)
  rw [Fraction.matrix_mulVec_grade, grade_combine]
  push_cast
  rw [mul_comm (fraction.periodDenominator : ℝ), mul_div_cancel_right₀ _ hden]
  simp [dotProduct, Fin.sum_univ_two, siteVector, Fraction.transverseGrade]
  ring

/-- The full period condition of the two-odometers statement. The constant
for a period may be chosen as the integer height increment from the origin. -/
theorem generator_periods_affine {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {field : Field} {constantU constantV : ℤ}
    (hperiod : HasGeneratorPeriods fraction field constantU constantV) :
    ∀ period ∈ fraction.modifiedDeck.span, ∃ constant : ℤ, ∀ site : Site,
      (field (site + period) : ℝ) =
        (field site : ℝ) + dotProduct (siteVector site) (fraction.matrix.mulVec (siteVector period)) +
          (constant : ℝ) := by
  rintro period ⟨kernelIndex, transverseIndex, rfl⟩
  refine ⟨field (fraction.modifiedDeck.combine kernelIndex transverseIndex) - field 0, ?_⟩
  intro site
  have hlaw := generator_period_formula hinterval hperiod site kernelIndex transverseIndex
  have horigin := generator_period_formula hinterval hperiod 0 kernelIndex transverseIndex
  simp [Fraction.transverseGrade] at horigin
  rw [dot_matrix_combine hinterval]
  push_cast
  linarith

theorem eq_of_covered_generator_periods {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {first second : Field} {constantU constantV : ℤ}
    (hfirst : HasGeneratorPeriods fraction first constantU constantV)
    (hsecond : HasGeneratorPeriods fraction second constantU constantV)
    {sites : Finset Site} (hcover : fraction.modifiedDeck.Covers sites)
    (hagree : ∀ site ∈ sites, first site = second site) : first = second := by
  funext site
  obtain ⟨point, hpoint, ⟨kernelIndex, transverseIndex, htranslate⟩⟩ := hcover site
  have hsite : point + fraction.modifiedDeck.combine kernelIndex transverseIndex = site := by
    rw [← htranslate, add_comm, sub_add_cancel]
  have hfirstLaw := generator_period_formula hinterval hfirst point kernelIndex transverseIndex
  have hsecondLaw := generator_period_formula hinterval hsecond point kernelIndex transverseIndex
  rw [hsite, hagree point hpoint] at hfirstLaw
  rw [hsite] at hsecondLaw
  exact_mod_cast hfirstLaw.trans hsecondLaw.symm

end FLatticePaper
