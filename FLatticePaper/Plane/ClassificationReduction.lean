import FLatticePaper.GeneralK.GrowthClosed
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Sqrt

namespace FLatticePaper

open GeneralK Filter Topology

/-- The real symmetric matrices represented by integer superharmonic
heights on the corrected manuscript's physical graph. -/
def integerSuperharmonicMatrices : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {matrix | matrix.IsSymm ∧ ∃ height : Field, FLatticePaper.Superharmonic height ∧ HasQuadraticGrowth height matrix}

/-- The symmetric matrix space carries its subspace topology. -/
abbrev SymmetricMatrix := {matrix : Matrix (Fin 2) (Fin 2) ℝ // matrix.IsSymm}

def symmetricGrowthSet : Set SymmetricMatrix := Subtype.val ⁻¹' integerSuperharmonicMatrices

theorem isClosed_symmetricGrowthSet : IsClosed symmetricGrowthSet :=
  isClosed_growthSet_two.preimage continuous_subtype_val

theorem integerSuperharmonicMatrices_eq_growthSet_two : integerSuperharmonicMatrices = growthSet 2 := by
  ext matrix
  constructor
  · rintro ⟨hsymm, hheight⟩
    exact (mem_growthSet_two_iff hsymm).mpr hheight
  · intro h
    exact ⟨h.1, (mem_growthSet_two_iff h.1).mp h⟩

/-- The matrix coordinates of the corrected circle-packing statement. -/
noncomputable def circleMatrix (horizontal vertical trace : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  symmetricMatrix ((trace + horizontal) / 2) (vertical / 2) ((trace - horizontal) / 2)

theorem circleMatrix_isSymm (horizontal vertical trace : ℝ) : (circleMatrix horizontal vertical trace).IsSymm :=
  isSymm_symmetricMatrix ..

noncomputable def symmetricCircleMatrix (horizontal vertical trace : ℝ) : SymmetricMatrix :=
  ⟨circleMatrix horizontal vertical trace, circleMatrix_isSymm ..⟩

/-- The harmonic apex at the lattice pair `(s,t)` in `theorem:circle_packing`. -/
noncomputable def harmonicPeak (s t : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  circleMatrix ((s : ℝ) - t) ((s : ℝ) + t) 0

theorem harmonicPeak_eq_harmonicMatrix (s t : ℤ) :
    harmonicPeak s t = harmonicMatrix 2 (((t - s : ℤ) : ℝ) / 2) s := by
  simp only [harmonicPeak, circleMatrix, harmonicMatrix, Int.cast_sub, Int.cast_ofNat, zero_add, zero_sub]
  congr 1 <;> ring

theorem harmonicPeak_mem_integerSuperharmonicMatrices (s t : ℤ) :
    harmonicPeak s t ∈ integerSuperharmonicMatrices := by
  rw [integerSuperharmonicMatrices_eq_growthSet_two, harmonicPeak_eq_harmonicMatrix]
  exact harmonicMatrix_mem_growthSet (by decide) (t - s) s

/-- The semidefinite cones in the corrected classification are admitted. -/
theorem mem_integerSuperharmonicMatrices_of_peak_sub_posSemidef {matrix : Matrix (Fin 2) (Fin 2) ℝ}
    (s t : ℤ) (hpos : (harmonicPeak s t - matrix).PosSemidef) : matrix ∈ integerSuperharmonicMatrices := by
  have hpeak := harmonicPeak_mem_integerSuperharmonicMatrices s t
  rw [integerSuperharmonicMatrices_eq_growthSet_two] at hpeak ⊢
  have hadmit := sub_mem_growthSet_of_posSemidef (by decide) hpeak hpos
  rwa [sub_sub_cancel] at hadmit

theorem add_harmonicPeak_mem_integerSuperharmonicMatrices_iff {matrix : Matrix (Fin 2) (Fin 2) ℝ} (s t : ℤ) :
    matrix + harmonicPeak s t ∈ integerSuperharmonicMatrices ↔ matrix ∈ integerSuperharmonicMatrices := by
  rw [integerSuperharmonicMatrices_eq_growthSet_two, harmonicPeak_eq_harmonicMatrix]
  exact add_harmonicMatrix_mem_growthSet_iff (by decide : (2 : ℤ) ≤ 2) (t - s) s matrix

theorem circleMatrix_trace_nonpos {horizontal vertical trace : ℝ}
    (h : circleMatrix horizontal vertical trace ∈ integerSuperharmonicMatrices) : trace ≤ 0 := by
  rw [integerSuperharmonicMatrices_eq_growthSet_two] at h
  have htrace := trace_le_zero_of_mem_growthSet (by decide : (2 : ℤ) ≤ 2) h
  norm_num at htrace
  linarith

/-- Every listed harmonic apex lies on the boundary for the physical
growth set. Positive trace perturbations approach the apex from outside. -/
theorem harmonicPeak_mem_frontier (s t : ℤ) :
    symmetricCircleMatrix ((s : ℝ) - t) ((s : ℝ) + t) 0 ∈ frontier symmetricGrowthSet := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let above (n : ℕ) := symmetricCircleMatrix ((s : ℝ) - t) ((s : ℝ) + t) (ε n)
  let peak := symmetricCircleMatrix ((s : ℝ) - t) ((s : ℝ) + t) 0
  have he : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto above atTop (𝓝 peak) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    fin_cases i <;> fin_cases j
    · exact (he.add tendsto_const_nhds).div_const 2
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · exact (he.sub tendsto_const_nhds).div_const 2
  have hnot : peak ∉ interior symmetricGrowthSet := by
    intro hinterior
    have hevent : ∀ᶠ n in atTop, above n ∈ interior symmetricGrowthSet := hlim (isOpen_interior.mem_nhds hinterior)
    obtain ⟨n, hn⟩ := hevent.exists
    have hmem : above n ∈ symmetricGrowthSet := interior_subset hn
    have hnonpos : ε n ≤ 0 := circleMatrix_trace_nonpos hmem
    have hpos : 0 < ε n := by unfold ε; positivity
    exact (not_lt_of_ge hnonpos) hpos
  exact ⟨subset_closure (harmonicPeak_mem_integerSuperharmonicMatrices s t), hnot⟩

private theorem dotProduct_circleMatrix (a b c : ℝ) (vector : Fin 2 → ℝ) :
    dotProduct vector ((circleMatrix a b c).mulVec vector) =
      (c * ((vector 0) ^ 2 + (vector 1) ^ 2) + a * ((vector 0) ^ 2 - (vector 1) ^ 2) +
        2 * b * vector 0 * vector 1) / 2 := by
  simp [circleMatrix, symmetricMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

private theorem cone_quadratic_bound (a b x y : ℝ) :
    |a * (x ^ 2 - y ^ 2) + 2 * b * x * y| ≤ Real.sqrt (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
  have hsq : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  apply abs_le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, hsq]
  nlinarith only [sq_nonneg (2 * a * x * y - b * (x ^ 2 - y ^ 2))]

/-- The semidefinite cone is exactly the circular cone in `M` coordinates. -/
theorem circleMatrix_posSemidef_iff (a b c : ℝ) : (circleMatrix a b c).PosSemidef ↔ Real.sqrt (a ^ 2 + b ^ 2) ≤ c := by
  let radius := Real.sqrt (a ^ 2 + b ^ 2)
  have hsquare : radius ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  constructor
  · intro hpsd
    by_cases hzero : a + radius = 0
    · have h := hpsd.dotProduct_mulVec_nonneg ![1, 0]
      simp only [star_trivial, dotProduct_circleMatrix, Matrix.cons_val_zero, Matrix.cons_val_one] at h
      norm_num at h
      linarith only [h, hzero]
    · have h := hpsd.dotProduct_mulVec_nonneg ![b, -(a + radius)]
      simp only [star_trivial, dotProduct_circleMatrix, Matrix.cons_val_zero, Matrix.cons_val_one] at h
      have heig : a * (b ^ 2 - (-(a + radius)) ^ 2) + 2 * b * b * -(a + radius) =
          -radius * (b ^ 2 + (-(a + radius)) ^ 2) := by
        linear_combination (a + radius) * hsquare
      have hrew : c * (b ^ 2 + (-(a + radius)) ^ 2) + a * (b ^ 2 - (-(a + radius)) ^ 2) +
          2 * b * b * -(a + radius) = (c - radius) * (b ^ 2 + (-(a + radius)) ^ 2) := by
        linear_combination heig
      rw [hrew] at h
      have hpos : 0 < b ^ 2 + (-(a + radius)) ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg b)
        (sq_pos_of_ne_zero (neg_ne_zero.mpr hzero))
      by_contra! hn
      exact (not_lt_of_ge h) (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr hn) hpos) (by norm_num))
  · intro hc
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr (circleMatrix_isSymm ..))
    intro v
    simp only [star_trivial, dotProduct_circleMatrix]
    have hb := (abs_le.mp (cone_quadratic_bound a b (v 0) (v 1))).1
    have hc' := mul_le_mul_of_nonneg_right hc (show 0 ≤ (v 0) ^ 2 + (v 1) ^ 2 by positivity)
    linarith only [hb, hc']

end FLatticePaper
