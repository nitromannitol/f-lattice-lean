import FLatticePaper.Farey.RationalBirth
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace FLatticePaper.Farey

/-- The value `(d²-n²)/(d²+2dn-n²)` of a fraction. -/
noncomputable def Fraction.slopeValue (fraction : Fraction) : ℝ :=
  ((fraction.den : ℝ) ^ 2 - (fraction.num : ℝ) ^ 2) /
    ((fraction.den : ℝ) ^ 2 + 2 * fraction.den * fraction.num - (fraction.num : ℝ) ^ 2)

/-- The curve `r ↦ (1-r²)/(1+2r-r²)`, whose values at reduced rational slopes are the slope values. -/
private noncomputable def slopeCurve (r : ℝ) : ℝ := (1 - r ^ 2) / (1 + 2 * r - r ^ 2)

private theorem slopeCurve_denominator_pos {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 + 2 * r - r ^ 2 := by
  nlinarith [hr.1, hr.2, mul_nonneg hr.1 (sub_nonneg.mpr hr.2)]

private theorem slopeCurve_continuousAt {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousAt slopeCurve r := by
  unfold slopeCurve
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact (slopeCurve_denominator_pos hr).ne'

private theorem slopeCurve_continuousOn : ContinuousOn slopeCurve (Set.Icc (0 : ℝ) 1) :=
  fun _ hr => (slopeCurve_continuousAt hr).continuousWithinAt

private theorem slopeCurve_zero : slopeCurve 0 = 1 := by
  norm_num [slopeCurve]

private theorem slopeCurve_one : slopeCurve 1 = 0 := by
  norm_num [slopeCurve]

/-- At a positive denominator, the slope value is the curve at the rational slope `n/d`. -/
private theorem slopeValue_eq_curve {fraction : Fraction} (hden : 0 < fraction.den) :
    fraction.slopeValue = slopeCurve ((fraction.num : ℝ) / fraction.den) := by
  have hd : (fraction.den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
  have hnum : 1 - ((fraction.num : ℝ) / fraction.den) ^ 2 =
      ((fraction.den : ℝ) ^ 2 - (fraction.num : ℝ) ^ 2) / (fraction.den : ℝ) ^ 2 := by
    field_simp
  have hdenom : 1 + 2 * ((fraction.num : ℝ) / fraction.den) - ((fraction.num : ℝ) / fraction.den) ^ 2 =
      ((fraction.den : ℝ) ^ 2 + 2 * fraction.den * fraction.num - (fraction.num : ℝ) ^ 2) /
        (fraction.den : ℝ) ^ 2 := by
    field_simp
  unfold Fraction.slopeValue slopeCurve
  rw [hnum, hdenom, div_div_div_cancel_right₀ (pow_ne_zero 2 hd)]

/-- The lemma at line 457 (it has no TeX label): `(d²-n²)/(d²+2dn-n²)` is dense in `[0,1]` over reduced fractions
`0 ≤ n/d ≤ 1`. -/
theorem slopeValue_dense :
    {x : ℝ | ∃ fraction : Fraction, fraction.Reduced ∧ fraction.InUnitInterval ∧ x = fraction.slopeValue} ⊆
        Set.Icc 0 1 ∧
      Set.Icc (0 : ℝ) 1 ⊆
        closure {x : ℝ | ∃ fraction : Fraction, fraction.Reduced ∧ fraction.InUnitInterval ∧ x = fraction.slopeValue} := by
  constructor
  · rintro x ⟨fraction, -, ⟨hden, hnum, hle⟩, rfl⟩
    have hd : (0 : ℝ) < fraction.den := by exact_mod_cast hden
    have hn : (0 : ℝ) ≤ fraction.num := by exact_mod_cast hnum
    have hle' : (fraction.num : ℝ) ≤ fraction.den := by exact_mod_cast hle
    have hD : 0 < (fraction.den : ℝ) ^ 2 + 2 * fraction.den * fraction.num - (fraction.num : ℝ) ^ 2 := by
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hle'), mul_nonneg hd.le hn, mul_pos hd hd]
    rw [Set.mem_Icc, Fraction.slopeValue]
    refine ⟨div_nonneg ?_ hD.le, ?_⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hle') (add_nonneg hn hd.le)]
    · rw [div_le_one hD]
      nlinarith [mul_nonneg hd.le hn]
  · have hsurj : Set.Icc (0 : ℝ) 1 ⊆ slopeCurve '' Set.Icc 0 1 := by
      have h := intermediate_value_Icc' (zero_le_one : (0 : ℝ) ≤ 1) slopeCurve_continuousOn
      rwa [slopeCurve_one, slopeCurve_zero] at h
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hsurj hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp (slopeCurve_continuousAt hr) ε hε
    have hab : max 0 (r - δ) < min 1 (r + δ) :=
      max_lt (lt_min zero_lt_one (by linarith [hr.1])) (lt_min (by linarith [hr.2]) (by linarith))
    obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn hab
    have hlo : (0 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hqa
    have hhi : (q : ℝ) < 1 := lt_of_lt_of_le hqb (min_le_left _ _)
    have hqlo : (0 : ℚ) < q := by exact_mod_cast hlo
    have hqhi : q < 1 := by exact_mod_cast hhi
    have hdist : dist (q : ℝ) r < δ := by
      rw [Real.dist_eq, abs_lt]
      have h1 : r - δ < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hqa
      have h2 : (q : ℝ) < r + δ := lt_of_lt_of_le hqb (min_le_right _ _)
      constructor <;> linarith
    have hinterval := (Fraction.ofRat_interior hqlo hqhi).inUnitInterval
    have hval : (Fraction.ofRat q).slopeValue = slopeCurve (q : ℝ) := by
      rw [slopeValue_eq_curve hinterval.1]
      congr 1
      show (q.num : ℝ) / ((q.den : ℤ) : ℝ) = (q : ℝ)
      rw [Int.cast_natCast, Rat.cast_def]
    refine ⟨slopeCurve q, ⟨Fraction.ofRat q, Fraction.ofRat_reduced q, hinterval, hval.symm⟩, ?_⟩
    rw [dist_comm]
    exact hcont hdist

end FLatticePaper.Farey
