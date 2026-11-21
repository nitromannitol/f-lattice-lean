import FLatticePaper.Plane.ClassificationReduction
import FLatticePaper.Plane.Recurrence

namespace FLatticePaper

open Filter Topology

/-- The quadratic growth of a recurrent superharmonic height cannot be
strictly dominated in every direction by that of a superharmonic competitor. -/
theorem Recurrent.not_exists_superharmonic_growth_of_strict_gap {height : Field}
    {matrix upper : Matrix (Fin 2) (Fin 2) ℝ} (hr : Recurrent height) (hs : Superharmonic height)
    (hg : HasQuadraticGrowth height matrix) {gap : ℝ} (hgap : 0 < gap)
    (hquad : ∀ site, gap * squaredSize site ≤ matrixQuadratic upper site - matrixQuadratic matrix site) :
    ¬ ∃ competitor : Field, Superharmonic competitor ∧ HasQuadraticGrowth competitor upper := by
  rintro ⟨competitor, hc, hcg⟩
  let bound : ℤ := height 0 - competitor 0 - 1
  have he : 0 < gap / 4 := by positivity
  obtain ⟨r, hrpos, hrad⟩ := hg (gap / 4) he
  obtain ⟨s, hspos, hsrad⟩ := hcg (gap / 4) he
  obtain ⟨n, hn⟩ := exists_int_gt (max (max r s) (max 1 (-(bound : ℝ) / (gap / 2))))
  have hnr : r ≤ (n : ℝ) := ((le_max_left r s).trans (le_max_left ..)).trans hn.le
  have hns : s ≤ (n : ℝ) := ((le_max_right r s).trans (le_max_left ..)).trans hn.le
  have hnOne : 1 ≤ (n : ℝ) := ((le_max_left _ _).trans (le_max_right ..)).trans hn.le
  have hnBound : -(bound : ℝ) ≤ (n : ℝ) * (gap / 2) := by
    apply (div_le_iff₀ (show 0 < gap / 2 by positivity)).mp
    exact ((le_max_right _ _).trans (le_max_right ..)).trans hn.le
  have hnNat : (0 : ℤ) ≤ n := by exact_mod_cast (show (0 : ℝ) ≤ n by linarith only [hnOne])
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (show (0 : ℝ) ≤ n by linarith only [hnOne]) (sub_nonneg.mpr hnOne)]
  let test : Finset Site := (Finset.Icc (-n) n).product (Finset.Icc (-n) n)
  have hboundary (site : Site) (hin : site ∈ incomingBoundary test) : height site - competitor site ≤ bound := by
    have hsize : (n : ℝ) ^ 2 ≤ squaredSize site := by
      have hout : ¬ ((-n ≤ site.1 ∧ site.1 ≤ n) ∧ (-n ≤ site.2 ∧ site.2 ≤ n)) := by
        intro h
        exact hin.1 (Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr h.1, Finset.mem_Icc.mpr h.2⟩)
      have hcoord : n ≤ |site.1| ∨ n ≤ |site.2| := by
        by_contra! h
        have hx := abs_lt.mp h.1
        have hy := abs_lt.mp h.2
        exact hout ⟨⟨hx.1.le, hx.2.le⟩, ⟨hy.1.le, hy.2.le⟩⟩
      rcases hcoord with hx | hy
      · have hx' : (n : ℝ) ≤ |(site.1 : ℝ)| := by exact_mod_cast hx
        have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ n by linarith only [hnOne]) hx' 2
        rw [sq_abs] at hpow
        unfold squaredSize
        linarith only [hpow, sq_nonneg (site.2 : ℝ)]
      · have hy' : (n : ℝ) ≤ |(site.2 : ℝ)| := by exact_mod_cast hy
        have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ n by linarith only [hnOne]) hy' 2
        rw [sq_abs] at hpow
        unfold squaredSize
        linarith only [hpow, sq_nonneg (site.1 : ℝ)]
    have hfirst := (abs_le.mp (hrad site ((pow_le_pow_left₀ hrpos.le hnr 2).trans hsize))).2
    have hsecond := (abs_le.mp (hsrad site ((pow_le_pow_left₀ hspos.le hns 2).trans hsize))).1
    have hfar := mul_le_mul_of_nonneg_right (hsq.trans hsize) (show 0 ≤ gap / 2 by positivity)
    have hlocal := hquad site
    have hreal : (height site : ℝ) - (competitor site : ℝ) ≤ bound := by
      linarith only [hfirst, hsecond, hfar, hlocal, hnBound]
    exact_mod_cast hreal
  have hzero : (0 : Site) ∈ test := by simp [test, hnNat]
  have hcompare := finiteComparison_of_allowed test bound (hr.allowed hs) (fun site _ => hc site) hboundary 0 hzero
  dsimp [bound] at hcompare
  omega

/-- A recurrent integer superharmonic height places its symmetric quadratic
growth matrix on the boundary of the primary growth set. -/
theorem Recurrent.mem_frontier_of_quadraticGrowth {height : Field} (hr : Recurrent height)
    (hs : Superharmonic height) (matrix : SymmetricMatrix) (hg : HasQuadraticGrowth height matrix.val) :
    matrix ∈ frontier symmetricGrowthSet := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let above (n : ℕ) : SymmetricMatrix := ⟨matrix.val + circleMatrix 0 0 (ε n), by
    exact Matrix.IsSymm.add matrix.property (circleMatrix_isSymm ..)⟩
  have he : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto above atTop (𝓝 matrix) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    fin_cases i <;> fin_cases j
    · simpa [above, circleMatrix, GeneralK.symmetricMatrix] using
        ((tendsto_const_nhds (x := matrix.val 0 0)).add (he.div_const 2))
    · simp [above, circleMatrix, GeneralK.symmetricMatrix]
    · simp [above, circleMatrix, GeneralK.symmetricMatrix]
    · simpa [above, circleMatrix, GeneralK.symmetricMatrix] using
        ((tendsto_const_nhds (x := matrix.val 1 1)).add (he.div_const 2))
  have hnot (n : ℕ) : above n ∉ symmetricGrowthSet := by
    rintro ⟨-, competitor, hcs, hcg⟩
    have hgap : 0 < ε n / 4 := by unfold ε; positivity
    apply (hr.not_exists_superharmonic_growth_of_strict_gap hs hg hgap (upper := (above n).val) ?_)
      ⟨competitor, hcs, hcg⟩
    rintro ⟨x, y⟩
    simp [above, circleMatrix, GeneralK.symmetricMatrix, squaredSize, matrixQuadratic, Farey.siteVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring_nf
    exact le_rfl
  have hinterior : matrix ∉ interior symmetricGrowthSet := by
    intro hmem
    have hevent : ∀ᶠ n in atTop, above n ∈ interior symmetricGrowthSet :=
      hlim (isOpen_interior.mem_nhds hmem)
    obtain ⟨n, hn⟩ := hevent.exists
    exact hnot n (interior_subset hn)
  exact ⟨subset_closure ⟨matrix.property, height, hs, hg⟩, hinterior⟩

end FLatticePaper
