import FLatticePaper.Farey.PeriodDeck
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace FLatticePaper.Farey

def siteVector (site : Site) : Fin 2 → ℝ := ![(site.1 : ℝ), (site.2 : ℝ)]

namespace Fraction

/-- The matrix `M(n,d)` in the manuscript. -/
noncomputable def matrix (fraction : Fraction) : Matrix (Fin 2) (Fin 2) ℝ :=
  let num : ℝ := fraction.num
  let den : ℝ := fraction.den
  let denom : ℝ := fraction.periodDenominator
  !![-num ^ 2 / denom, den * num / denom; den * num / denom, -den ^ 2 / denom]

/-- The coordinate dual to the second (transverse) period, before division by `T`. -/
def transverseGrade (fraction : Fraction) (site : Site) : ℤ :=
  fraction.den * site.2 - fraction.num * site.1

theorem matrix_mulVec_grade (fraction : Fraction) (site : Site) :
    let coefficient : ℝ := (fraction.transverseGrade site : ℝ) / fraction.periodDenominator
    fraction.matrix.mulVec (siteVector site) =
      ![coefficient * (fraction.num : ℝ), -(coefficient * (fraction.den : ℝ))] := by
  dsimp only
  ext coord
  fin_cases coord <;>
    simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, siteVector, transverseGrade] <;>
    ring

theorem transverseGrade_combine (fraction : Fraction) (kernelIndex transverseIndex : ℤ) :
    fraction.transverseGrade (fraction.unmodifiedDeck.combine kernelIndex transverseIndex) =
      fraction.periodDenominator * transverseIndex := by
  rw [← det_unmodifiedDeck]
  exact fraction.unmodifiedDeck.transverseNumerator_combine kernelIndex transverseIndex

theorem transverseGrade_sub (fraction : Fraction) (first second : Site) :
    fraction.transverseGrade (first - second) =
      fraction.transverseGrade first - fraction.transverseGrade second := by
  dsimp [transverseGrade]
  ring

theorem exists_kernel_multiple {fraction : Fraction} (hreduced : fraction.Reduced) {site : Site}
    (hgrade : fraction.transverseGrade site = 0) :
    ∃ kernelIndex : ℤ, site = fraction.unmodifiedDeck.combine kernelIndex 0 := by
  obtain ⟨numCoeff, denCoeff, hbezout⟩ := hreduced
  unfold transverseGrade at hgrade
  refine ⟨numCoeff * site.2 + denCoeff * site.1, Prod.ext ?_ ?_⟩
  · simp only [unmodifiedDeck, PeriodDeck.combine, zero_mul, add_zero]
    linear_combination -site.1 * hbezout - numCoeff * hgrade
  · simp only [unmodifiedDeck, PeriodDeck.combine, zero_mul, add_zero]
    linear_combination -site.2 * hbezout + denCoeff * hgrade

theorem mem_unmodifiedDeck_iff {fraction : Fraction} (hreduced : fraction.Reduced) (site : Site) :
    site ∈ fraction.unmodifiedDeck.span ↔ fraction.periodDenominator ∣ fraction.transverseGrade site := by
  constructor
  · rintro ⟨kernelIndex, transverseIndex, rfl⟩
    exact ⟨transverseIndex, transverseGrade_combine fraction kernelIndex transverseIndex⟩
  · rintro ⟨transverseIndex, hgrade⟩
    let transverse := fraction.unmodifiedDeck.combine 0 transverseIndex
    have hkernel : fraction.transverseGrade (site - transverse) = 0 := by
      rw [transverseGrade_sub, hgrade]
      dsimp only [transverse]
      rw [transverseGrade_combine]
      omega
    obtain ⟨kernelIndex, heq⟩ := exists_kernel_multiple hreduced hkernel
    refine ⟨kernelIndex, transverseIndex, Prod.ext ?_ ?_⟩
    · have hcoord := congrArg Prod.fst heq
      dsimp [transverse, PeriodDeck.combine] at hcoord ⊢
      omega
    · have hcoord := congrArg Prod.snd heq
      dsimp [transverse, PeriodDeck.combine] at hcoord ⊢
      omega

/-- The integer-action lattice, defined by the matrix rather than its span. -/
def integralLattice (fraction : Fraction) : Set Site :=
  {site | ∃ image : Site, fraction.matrix.mulVec (siteVector site) = siteVector image}

theorem mem_integralLattice_iff {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    (hreduced : fraction.Reduced) (site : Site) :
    site ∈ fraction.integralLattice ↔ fraction.periodDenominator ∣ fraction.transverseGrade site := by
  let coef : ℝ := (fraction.transverseGrade site : ℝ) / fraction.periodDenominator
  have hden : (fraction.periodDenominator : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (periodDenominator_pos hinterval)
  have haction : fraction.matrix.mulVec (siteVector site) =
      ![coef * (fraction.num : ℝ), -(coef * (fraction.den : ℝ))] := matrix_mulVec_grade fraction site
  constructor
  · rintro ⟨image, himage⟩
    obtain ⟨numCoeff, denCoeff, hbezout⟩ := hreduced
    have hbezR : (numCoeff : ℝ) * fraction.num + (denCoeff : ℝ) * fraction.den = 1 := by
      exact_mod_cast hbezout
    rw [haction] at himage
    have hx : coef * (fraction.num : ℝ) = (image.1 : ℝ) := congrFun himage 0
    have hy : -(coef * (fraction.den : ℝ)) = (image.2 : ℝ) := congrFun himage 1
    have hi : (numCoeff : ℝ) * image.1 - (denCoeff : ℝ) * image.2 = coef := by
      rw [← hx, ← hy]
      linear_combination coef * hbezR
    refine ⟨numCoeff * image.1 - denCoeff * image.2, ?_⟩
    have hi' := (eq_div_iff hden).mp hi
    exact_mod_cast (show (fraction.transverseGrade site : ℝ) =
      (fraction.periodDenominator : ℝ) * ((numCoeff : ℝ) * image.1 - (denCoeff : ℝ) * image.2)
      by rw [mul_comm]; exact hi'.symm)
  · rintro ⟨transverseIndex, hgrade⟩
    refine ⟨(transverseIndex * fraction.num, -(transverseIndex * fraction.den)), ?_⟩
    have hc : coef = transverseIndex := by
      apply (div_eq_iff hden).mpr
      exact_mod_cast hgrade.trans (mul_comm ..)
    rw [haction, hc]
    ext coord
    fin_cases coord <;> simp [siteVector]

/-- The two integral generators of `L(n,d)` in Section 3. -/
theorem integralLattice_eq_span {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    (hreduced : fraction.Reduced) : fraction.integralLattice = fraction.unmodifiedDeck.span := by
  ext site
  exact (mem_integralLattice_iff hinterval hreduced site).trans (mem_unmodifiedDeck_iff hreduced site).symm

theorem mem_modifiedDeck_iff_integral_even {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    (hreduced : fraction.Reduced) (site : Site) :
    site ∈ fraction.modifiedDeck.span ↔ site ∈ fraction.integralLattice ∧ EvenSite site := by
  rw [mem_modifiedDeck_iff, integralLattice_eq_span hinterval hreduced]

theorem matrix_mulVec_kernel (fraction : Fraction) :
    fraction.matrix.mulVec (siteVector fraction.modifiedDeck.kernel) = siteVector (0, 0) := by
  have hgrade : fraction.transverseGrade fraction.modifiedDeck.kernel = 0 := by
    simp only [transverseGrade, modifiedDeck]
    ring
  rw [matrix_mulVec_grade, hgrade]
  ext coord
  fin_cases coord <;> simp [siteVector]

theorem matrix_mulVec_transverse {fraction : Fraction} (hinterval : fraction.InUnitInterval) :
    fraction.matrix.mulVec (siteVector fraction.modifiedDeck.transverse) =
      siteVector (fraction.num, -fraction.den) := by
  have hgrade : fraction.transverseGrade fraction.modifiedDeck.transverse = fraction.periodDenominator := by
    simp only [transverseGrade, modifiedDeck, unmodifiedDeck, periodDenominator]
    ring
  have hden : (fraction.periodDenominator : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (periodDenominator_pos hinterval)
  rw [matrix_mulVec_grade, hgrade, div_self hden]
  ext coord
  fin_cases coord <;> simp [siteVector]

end Fraction

end FLatticePaper.Farey
