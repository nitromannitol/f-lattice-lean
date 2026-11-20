import FLatticePaper.GeneralK.Harmonic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace FLatticePaper.GeneralK

private def realLaplacian (k : ℤ) (field : Site → ℝ) (site : Site) : ℝ :=
  (field (incomingNeg k site) - field site) + (field (incomingPos k site) - field site)

private theorem realLaplacian_matrixQuadratic (k : ℤ) (a b c : ℝ) (site : Site) :
    realLaplacian k (matrixQuadratic (symmetricMatrix a b c)) site = if Retained k site then a else c := by
  obtain ⟨x, y⟩ := site
  by_cases h : Retained k (x, y) <;>
    simp only [realLaplacian, incomingNeg, incomingPos, if_pos, if_neg, h, not_false_eq_true,
      matrixQuadratic_symmetricMatrix, Int.cast_add, Int.cast_sub, Int.cast_one] <;> ring

theorem exists_min_of_quadratic_lower_bound {field : Site → ℝ} {radius slope : ℝ}
    (hradius : 0 ≤ radius) (hslope : 0 < slope)
    (hlower : ∀ site, radius ^ 2 ≤ squaredSize site → slope * squaredSize site ≤ field site) :
    ∃ point, ∀ site, field point ≤ field site := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max radius (max 1 (field 0 / slope)))
  have hsize : radius ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ hradius ((le_max_left ..).trans hn.le) 2
  have hn₁ : (1 : ℝ) ≤ n := (le_max_left ..).trans ((le_max_right ..).trans hn.le)
  have hvalue : field 0 ≤ slope * (n : ℝ) := by
    rw [mul_comm]
    apply (div_le_iff₀ hslope).mp
    exact (le_max_right ..).trans ((le_max_right ..).trans hn.le)
  let box := (Finset.Icc (-(n : ℤ)) (n : ℤ)).product (Finset.Icc (-(n : ℤ)) (n : ℤ))
  have horigin : (0 : Site) ∈ box := by
    simp [box, Prod.zero_eq_mk, Finset.mem_Icc]
  obtain ⟨point, _, hmin⟩ := box.exists_min_image field ⟨0, horigin⟩
  refine ⟨point, fun site => ?_⟩
  by_cases hsite : site ∈ box
  · exact hmin site hsite
  · have hfar : (n : ℝ) ^ 2 ≤ squaredSize site := by
      by_contra! hnear
      have hcoord (value : ℤ) (hv : (value : ℝ) ^ 2 ≤ squaredSize site) :
          value ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
        have ⟨hlo, hhi⟩ := abs_le_of_sq_le_sq' (hv.trans hnear.le) (by positivity)
        exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
      exact hsite (Finset.mem_product.mpr
        ⟨hcoord site.1 (le_add_of_nonneg_right (sq_nonneg _)),
          hcoord site.2 (le_add_of_nonneg_left (sq_nonneg _))⟩)
    have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hn₁ (by positivity : 0 ≤ (n : ℝ))
    exact (hmin 0 horigin).trans (hvalue.trans
      ((mul_le_mul_of_nonneg_left (hnsq.trans hfar) hslope.le).trans (hlower site (hsize.trans hfar))))

/-- Every admitted real matrix satisfies the physical weighted trace bound.
The harmonic grid height corrects the two phase Laplacians of a quadratic
to their weighted average. A small diagonal shift then permits comparison
at an attained minimum of the error on the plane. -/
theorem trace_le_zero_of_mem_growthSet {k : ℤ} (hk : 2 ≤ k) {a b c : ℝ}
    (hm : symmetricMatrix a b c ∈ growthSet k) : a + ((k : ℝ) - 1) * c ≤ 0 := by
  obtain ⟨height, hsuper, hgrowth⟩ := (symmetricMatrix_mem_growthSet_iff k a b c).mp hm
  by_contra! htrace
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  let shift := (a + ((k : ℝ) - 1) * c) / (2 * (k : ℝ))
  have hshift : 0 < shift := div_pos htrace (by positivity)
  let harmonicError (site : Site) := (harmonicGridField k site : ℝ) -
    matrixQuadratic (harmonicMatrix k (1 / (k : ℝ)) 0) site
  let comparison (site : Site) := matrixQuadratic (symmetricMatrix (a - shift) b (c - shift)) site +
    (c - a) * harmonicError site
  have hlap (site : Site) : realLaplacian k comparison site = shift := by
    have hlapH : realLaplacian k (fun point => harmonicGridField k point) site = 0 := by
      dsimp only [realLaplacian]
      exact_mod_cast laplacian_harmonicGridField hk site
    calc
      _ = realLaplacian k (matrixQuadratic (symmetricMatrix (a - shift) b (c - shift))) site +
          (c - a) * (realLaplacian k (fun point => harmonicGridField k point) site -
            realLaplacian k (matrixQuadratic (harmonicMatrix k (1 / (k : ℝ)) 0)) site) := by
        unfold realLaplacian comparison harmonicError
        ring
      _ = shift := by
        rw [hlapH, harmonicMatrix, realLaplacian_matrixQuadratic, realLaplacian_matrixQuadratic]
        split <;> dsimp [shift] <;> field_simp <;> ring
  have hquadShift (site : Site) : matrixQuadratic (symmetricMatrix a b c) site -
      matrixQuadratic (symmetricMatrix (a - shift) b (c - shift)) site = shift / 2 * squaredSize site := by
    obtain ⟨x, y⟩ := site
    simp only [matrixQuadratic_symmetricMatrix, squaredSize]
    ring
  let factor := |c - a| + 1
  have hfactor : 0 < factor := by dsimp [factor]; positivity
  obtain ⟨r₁, hr₁, h₁⟩ := hgrowth (shift / 8) (by positivity)
  obtain ⟨r₂, hr₂, h₂⟩ := quadraticGrowth_harmonicGridField hk (shift / (8 * factor)) (by positivity)
  let error : Site → ℝ := fun site => (height site : ℝ) - comparison site
  have herror (site : Site) (hfar : (max r₁ r₂) ^ 2 ≤ squaredSize site) :
      shift / 4 * squaredSize site ≤ error site := by
    have hfar₁ := (pow_le_pow_left₀ hr₁.le (le_max_left r₁ r₂) 2).trans hfar
    have hfar₂ := (pow_le_pow_left₀ hr₂.le (le_max_right r₁ r₂) 2).trans hfar
    have hmain := (abs_le.mp (h₁ site hfar₁)).1
    have hsecondary := h₂ site hfar₂
    have hproduct : (c - a) * harmonicError site ≤ shift / 8 * squaredSize site := by
      apply (le_abs_self _).trans
      rw [abs_mul]
      calc
        _ ≤ |c - a| * (shift / (8 * factor) * squaredSize site) :=
          mul_le_mul_of_nonneg_left hsecondary (abs_nonneg _)
        _ ≤ factor * (shift / (8 * factor) * squaredSize site) :=
          mul_le_mul_of_nonneg_right (by dsimp [factor]; linarith)
            (by unfold squaredSize; positivity)
        _ = _ := by field_simp
    dsimp only [error, comparison]
    linarith only [hquadShift site, hmain, hproduct]
  obtain ⟨point, hmin⟩ := exists_min_of_quadratic_lower_bound (hr₁.le.trans (le_max_left ..))
    (show 0 < shift / 4 by positivity) herror
  have hneg := hmin (incomingNeg k point)
  have hpos := hmin (incomingPos k point)
  have hheight : (laplacian k height point : ℝ) ≤ 0 := by exact_mod_cast hsuper point
  have hcomp := hlap point
  simp only [error] at hneg hpos
  simp only [realLaplacian] at hcomp
  simp only [laplacian, Int.cast_add, Int.cast_sub] at hheight
  linarith only [hheight, hcomp, hneg, hpos, hshift]

end FLatticePaper.GeneralK
