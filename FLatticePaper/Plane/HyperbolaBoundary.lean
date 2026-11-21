import FLatticePaper.Plane.CirclePacking
import FLatticePaper.Plane.RecurrentBoundary
import FLatticePaper.Construction.EndpointAtoms
import Mathlib.RingTheory.Int.Basic
import Mathlib.Topology.Order.IntermediateValue

namespace FLatticePaper

open Farey GeneralK Set

private noncomputable def slopeDenominator (r : ℝ) : ℝ := max 1 (1 + 2 * r - r ^ 2)

private theorem slopeDenominator_eq {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    slopeDenominator r = 1 + 2 * r - r ^ 2 := by
  unfold slopeDenominator
  exact max_eq_right (by nlinarith only [mul_nonneg hr.1 (sub_nonneg.mpr hr.2), hr.1])

private theorem slopeDenominator_pos (r : ℝ) : 0 < slopeDenominator r :=
  zero_lt_one.trans_le (le_max_left ..)

private theorem continuous_slopeDenominator : Continuous slopeDenominator := by
  unfold slopeDenominator
  fun_prop

private noncomputable def slopeMatrix (r : ℝ) : SymmetricMatrix :=
  ⟨symmetricMatrix (-r ^ 2 / slopeDenominator r) (r / slopeDenominator r) (-1 / slopeDenominator r), isSymm_symmetricMatrix ..⟩

private theorem continuous_slopeMatrix : Continuous slopeMatrix := by
  apply Continuous.subtype_mk
  apply continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  · exact ((continuous_id.pow 2).neg).div continuous_slopeDenominator (fun r => (slopeDenominator_pos r).ne')
  · exact continuous_id.div continuous_slopeDenominator (fun r => (slopeDenominator_pos r).ne')
  · exact continuous_id.div continuous_slopeDenominator (fun r => (slopeDenominator_pos r).ne')
  · exact continuous_const.div continuous_slopeDenominator (fun r => (slopeDenominator_pos r).ne')

private theorem matrix_eq_slopeMatrix {fraction : Fraction} (h : fraction.InUnitInterval) :
    fraction.matrix = (slopeMatrix ((fraction.num : ℝ) / (fraction.den : ℝ))).val := by
  have hd : 0 < (fraction.den : ℝ) := by exact_mod_cast h.1
  have hn : 0 ≤ (fraction.num : ℝ) := by exact_mod_cast h.2.1
  have hnd : (fraction.num : ℝ) ≤ (fraction.den : ℝ) := by exact_mod_cast h.2.2
  have hunit : (fraction.num : ℝ) / (fraction.den : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hn hd.le, (div_le_one hd).mpr hnd⟩
  have hp : ((fraction.periodDenominator : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fraction.periodDenominator_pos h).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fraction.matrix, slopeMatrix, symmetricMatrix, slopeDenominator_eq hunit] <;>
    field_simp [hd.ne', hp] <;> simp [Fraction.periodDenominator] <;> ring

private theorem rationalSlope_mem_frontier
    (hrep : ∀ fraction : Fraction, fraction.InUnitInterval → fraction.Reduced →
      ∃ height : Field, Superharmonic height ∧ Recurrent height ∧ HasQuadraticGrowth height fraction.matrix)
    (q : ℚ) (hq : (q : ℝ) ∈ Icc (0 : ℝ) 1) : slopeMatrix q ∈ frontier symmetricGrowthSet := by
  let fraction : Fraction := ⟨q.num, q.den⟩
  have hcast : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
  have hd : 0 < (q.den : ℤ) := by exact_mod_cast q.den_pos
  have hn : 0 ≤ q.num := by exact Rat.num_nonneg.mpr (by exact_mod_cast hq.1)
  have hnd : q.num ≤ (q.den : ℤ) := by
    have hbound := hq.2
    rw [hcast] at hbound
    have h := (div_le_one (show (0 : ℝ) < (q.den : ℝ) by exact_mod_cast q.den_pos)).mp hbound
    exact_mod_cast h
  have hunit : fraction.InUnitInterval := ⟨hd, hn, hnd⟩
  have hc : fraction.Reduced := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa [fraction] using q.reduced
  obtain ⟨height, hsup, hrec, hgrowth⟩ := hrep fraction hunit hc
  have heq := matrix_eq_slopeMatrix hunit
  change fraction.matrix = (slopeMatrix ((q.num : ℝ) / (q.den : ℝ))).val at heq
  rw [← hcast] at heq
  exact hrec.mem_frontier_of_quadraticGrowth hsup _ (heq ▸ hgrowth)

private theorem realSlope_mem_frontier
    (hrep : ∀ fraction : Fraction, fraction.InUnitInterval → fraction.Reduced →
      ∃ height : Field, Superharmonic height ∧ Recurrent height ∧ HasQuadraticGrowth height fraction.matrix)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : slopeMatrix r ∈ frontier symmetricGrowthSet := by
  rcases eq_or_lt_of_le hr.1 with hzero | hpos
  · simpa [← hzero] using rationalSlope_mem_frontier hrep 0 (by norm_num)
  let rationalSlopes : Set ℝ := {x | ∃ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) 1 ∧ (q : ℝ) = x}
  have hsubset : rationalSlopes ⊆ slopeMatrix ⁻¹' frontier symmetricGrowthSet := by
    rintro _ ⟨q, hq, rfl⟩
    exact rationalSlope_mem_frontier hrep q hq
  have hcl : r ∈ closure rationalSlopes := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨q, hql, hqu⟩ := exists_rat_btwn (max_lt hpos (sub_lt_self r hε))
    refine ⟨(q : ℝ), ⟨q, ⟨(le_max_left ..).trans hql.le, hqu.le.trans hr.2⟩, rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hqu.le)]
    linarith only [(le_max_right 0 (r - ε)).trans_lt hql]
  exact (closure_minimal hsubset (isClosed_frontier.preimage continuous_slopeMatrix)) hcl

private noncomputable def slopeHorizontal (r : ℝ) : ℝ := (1 - r ^ 2) / slopeDenominator r

private theorem slopeMatrix_eq_hyperbola {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    slopeMatrix r = symmetricCircleMatrix (slopeHorizontal r) (1 - slopeHorizontal r)
      (-Real.sqrt ((slopeHorizontal r) ^ 2 + (1 - slopeHorizontal r) ^ 2)) := by
  let d := slopeDenominator r
  have hd := slopeDenominator_pos r
  have hd' : d = 1 + 2 * r - r ^ 2 := slopeDenominator_eq hr
  have hb : 1 - slopeHorizontal r = 2 * r / d := by
    change 1 - (1 - r ^ 2) / d = _
    field_simp [show d ≠ 0 from hd.ne']
    linarith only [hd']
  have hsquare : (slopeHorizontal r) ^ 2 + (1 - slopeHorizontal r) ^ 2 = ((1 + r ^ 2) / d) ^ 2 := by
    rw [hb]
    change ((1 - r ^ 2) / d) ^ 2 + (2 * r / d) ^ 2 = _
    simp only [div_pow, ← add_div]
    congr 1
    ring
  have hsqrt : Real.sqrt ((slopeHorizontal r) ^ 2 + (1 - slopeHorizontal r) ^ 2) = (1 + r ^ 2) / d := by
    rw [hsquare, Real.sqrt_sq (div_nonneg (by positivity) hd.le)]
  rw [hsqrt, hb]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slopeMatrix, symmetricCircleMatrix, circleMatrix, symmetricMatrix, slopeHorizontal, d] <;>
    ring

/-- The primary paper's chosen rational fraction parameterization gives the
entire real boundary arc when its recurrent representatives are supplied. -/
theorem hyperbolaBoundary_of_recurrentFractions
    (hrep : ∀ fraction : Fraction, fraction.InUnitInterval → fraction.Reduced →
      ∃ height : Field, Superharmonic height ∧ Recurrent height ∧ HasQuadraticGrowth height fraction.matrix)
    (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1) :
    symmetricCircleMatrix t (1 - t) (-Real.sqrt (t ^ 2 + (1 - t) ^ 2)) ∈ frontier symmetricGrowthSet := by
  have hcont : Continuous slopeHorizontal := (continuous_const.sub (continuous_id.pow 2)).div
    continuous_slopeDenominator (fun r => (slopeDenominator_pos r).ne')
  have hzero : slopeHorizontal 0 = 1 := by norm_num [slopeHorizontal, slopeDenominator]
  have hone : slopeHorizontal 1 = 0 := by norm_num [slopeHorizontal, slopeDenominator]
  have hrange : t ∈ Icc (slopeHorizontal 1) (slopeHorizontal 0) := by
    rw [hone, hzero]
    exact mem_Icc.mpr ⟨ht, hu⟩
  obtain ⟨r, hr, rfl⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn hrange
  exact slopeMatrix_eq_hyperbola hr ▸ realSlope_mem_frontier hrep r hr

private theorem recurrent_fractions_of_recurrent_interior
    (hinterior : ∀ fraction : Fraction, fraction.Interior → fraction.Reduced →
      ∃ height : Field, Superharmonic height ∧ Recurrent height ∧ HasQuadraticGrowth height fraction.matrix)
    (fraction : Fraction) (hunit : fraction.InUnitInterval) (hred : fraction.Reduced) :
    ∃ height : Field, Superharmonic height ∧ Recurrent height ∧ HasQuadraticGrowth height fraction.matrix := by
  let transfer (atom : Construction.EndpointAtom)
      (hslope : (atom.fraction.num : ℝ) / (atom.fraction.den : ℝ) = (fraction.num : ℝ) / (fraction.den : ℝ)) :
      ∃ height : Field, Superharmonic height ∧ Recurrent height ∧ HasQuadraticGrowth height fraction.matrix := by
    have hatom : atom.fraction.InUnitInterval := by cases atom <;> exact ⟨by decide, by decide, by decide⟩
    have hmatrix : atom.fraction.matrix = fraction.matrix := by
      rw [matrix_eq_slopeMatrix hatom, matrix_eq_slopeMatrix hunit, hslope]
    exact ⟨atom.planeField, hmatrix ▸ atom.planeField_recurrent⟩
  rcases eq_or_lt_of_le hunit.2.1 with hzero | hpos
  · apply transfer .zero
    simp [Construction.EndpointAtom.fraction, ← hzero]
  rcases eq_or_lt_of_le hunit.2.2 with hone | hlt
  · apply transfer .one
    have hd : (fraction.den : ℝ) ≠ 0 := by exact_mod_cast hunit.1.ne'
    simp [Construction.EndpointAtom.fraction, hone, hd]
  exact hinterior fraction ⟨hpos, hlt⟩ hred

/-- The two verified endpoint fields and recurrent representatives at each
reduced interior slope suffice for the real hyperbola boundary theorem. -/
theorem hyperbolaBoundary_of_recurrentInterior
    (hinterior : ∀ fraction : Fraction, fraction.Interior → fraction.Reduced →
      ∃ height : Field, Superharmonic height ∧ Recurrent height ∧ HasQuadraticGrowth height fraction.matrix)
    (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1) :
    symmetricCircleMatrix t (1 - t) (-Real.sqrt (t ^ 2 + (1 - t) ^ 2)) ∈ frontier symmetricGrowthSet :=
  hyperbolaBoundary_of_recurrentFractions (recurrent_fractions_of_recurrent_interior hinterior) t ht hu

/-- The corrected circle-packing theorem follows from the recurrent height
existence assertion for the exact interior Farey matrices. -/
theorem circlePacking_of_recurrentInterior
    (hinterior : ∀ fraction : Fraction, fraction.Interior → fraction.Reduced →
      ∃ height : Field, Superharmonic height ∧ Recurrent height ∧ HasQuadraticGrowth height fraction.matrix)
    (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    matrix ∈ integerSuperharmonicMatrices ↔ ∃ s t : ℤ, (harmonicPeak s t - matrix).PosSemidef :=
  circlePacking_of_hyperbolaBoundary (hyperbolaBoundary_of_recurrentInterior hinterior) matrix

end FLatticePaper
