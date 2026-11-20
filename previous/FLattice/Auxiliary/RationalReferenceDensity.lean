import FLattice.Auxiliary.RationalDescentData
import FLattice.Auxiliary.ElementaryDuality
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Density of primitive rational reference matrices

The actual rank-one reference entries are continuous on the closed unit
interval. Rational points in its interior have their usual reduced positive
numerator/denominator representation; endpoints are represented exactly.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.RationalReferenceDensity

open BranchMatrix RationalDescent
open scoped Topology

/-- Entrywise continuity of the literal reference formula at every allowed slope. -/
theorem continuousAt_reference_entry (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (i j : Fin 2) : ContinuousAt (fun s : ℝ => rankOneMatrix s 1 i j) r := by
  have hDen : denominator r 1 ≠ 0 := ne_of_gt (denominator_pos r 1 (by norm_num) hr0 hr1)
  have hd : ContinuousAt (fun s : ℝ => denominator s 1) r := by
    unfold denominator
    fun_prop
  simp only [rankOneMatrix_entries]
  fin_cases i <;> fin_cases j <;> simp only [mul_one, one_pow] <;>
    apply ContinuousAt.div <;> first | fun_prop | exact hd | exact hDen

/-- A nonnegative rational slope at most one is represented by a primitive pair. -/
theorem pair_of_rat (q : ℚ) (hq0 : (0 : ℝ) ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ 1) :
    ∃ p : Pair, rankOneMatrix (p.n : ℝ) (p.d : ℝ) = rankOneMatrix (q : ℝ) 1 := by
  have hq : 0 ≤ q := by exact_mod_cast hq0
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have hn : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hnum)
  have hd : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hcast : (q : ℝ) = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
    rw [hn, Rat.cast_def]
  have hnd : q.num.natAbs ≤ q.den := by
    have h := (div_le_one hd).mp (hcast ▸ hq1)
    exact_mod_cast h
  let p : Pair := ⟨q.num.natAbs, q.den, q.den_pos, hnd, q.reduced⟩
  refine ⟨p, ?_⟩
  have hscale := ElementaryDuality.rankOneMatrix_scale (q : ℝ) 1 (q.den : ℝ) (ne_of_gt hd)
  have hmul : (q.den : ℝ) * (q : ℝ) = (q.num.natAbs : ℝ) := by
    rw [hcast]
    field_simp
  simpa only [hmul, mul_one] using hscale

/-- Every real reference on the source interval is approximated entrywise by
actual primitive rational reference matrices. -/
theorem exists_primitive_reference_close (r δ : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hδ : 0 < δ) : ∃ p : Pair, ∀ i j : Fin 2,
      |rankOneMatrix (p.n : ℝ) (p.d : ℝ) i j - rankOneMatrix r 1 i j| < δ := by
  by_cases hz : r = 0
  · refine ⟨⟨0, 1, by decide, by decide, by decide⟩, ?_⟩
    intro i j
    simpa [hz] using hδ
  by_cases ho : r = 1
  · refine ⟨⟨1, 1, by decide, by decide, by decide⟩, ?_⟩
    intro i j
    simpa [ho] using hδ
  have hInterior0 : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hz)
  have hInterior1 : r < 1 := lt_of_le_of_ne hr1 ho
  have hNear : ∀ᶠ s in 𝓝 r, ∀ i j : Fin 2,
      |rankOneMatrix s 1 i j - rankOneMatrix r 1 i j| < δ := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun s : ℝ =>
        |rankOneMatrix s 1 i j - rankOneMatrix r 1 i j|) r :=
      ((continuousAt_reference_entry r hr0 hr1 i j).sub continuousAt_const).abs
    exact hc.eventually_lt_const (by simpa using hδ)
  obtain ⟨ε, hε, hClose⟩ := Metric.eventually_nhds_iff.mp hNear
  let a := max 0 (r - ε)
  let b := min 1 (r + ε)
  have har : a < r := max_lt hInterior0 (by linarith)
  have hrb : r < b := lt_min hInterior1 (by linarith)
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn (har.trans hrb)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_trans (le_max_left _ _) (le_of_lt haq)
  have hq1 : (q : ℝ) ≤ (1 : ℝ) := le_trans (le_of_lt hqb) (min_le_left _ _)
  obtain ⟨p, hp⟩ := pair_of_rat q hq0 hq1
  refine ⟨p, ?_⟩
  rw [hp]
  apply hClose
  rw [Real.dist_eq, abs_lt]
  have hlow : r - ε < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) haq
  have hhigh : (q : ℝ) < r + ε := lt_of_lt_of_le hqb (min_le_right _ _)
  constructor <;> linarith

end FLattice.Auxiliary.RationalReferenceDensity
