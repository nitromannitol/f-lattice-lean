import FLatticePaper.GeneralK.Growth

namespace FLatticePaper.GeneralK

private def blend (fraction first last : ℝ) : ℝ := (1 - fraction) * first + fraction * last

private theorem interpolate_abs_sub_blend_le {k : ℤ} (hk : 0 < k) (first last offset : ℤ)
    (hlo : 0 ≤ offset) (hhi : offset ≤ k) :
    |(interpolate k first last offset : ℝ) - blend ((offset : ℝ) / (k : ℝ)) first last| ≤ k := by
  let r : ℤ := (last - first) % k
  let q : ℤ := (last - first) / k
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hr₀ : 0 ≤ (r : ℝ) := by exact_mod_cast Int.emod_nonneg (last - first) (ne_of_gt hk)
  have hrk : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Int.emod_lt_of_pos (last - first) hk).le
  have hd : (r : ℝ) + (k : ℝ) * (q : ℝ) = (last : ℝ) - (first : ℝ) := by
    exact_mod_cast Int.emod_add_mul_ediv (last - first) k
  have ht₀ : 0 ≤ (offset : ℝ) / (k : ℝ) := div_nonneg (by exact_mod_cast hlo) hk'.le
  have ht₁ : (offset : ℝ) / (k : ℝ) ≤ 1 := (div_le_one hk').mpr (by exact_mod_cast hhi)
  have hmin₀ : 0 ≤ ((min offset r : ℤ) : ℝ) := by exact_mod_cast le_min hlo (Int.emod_nonneg _ (ne_of_gt hk))
  have hminK : ((min offset r : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (min_le_left offset r).trans hhi
  have heq : (interpolate k first last offset : ℝ) - blend ((offset : ℝ) / (k : ℝ)) first last =
      ((min offset r : ℤ) : ℝ) - (offset : ℝ) / (k : ℝ) * (r : ℝ) := by
    simp only [interpolate, blend, Int.cast_add, Int.cast_mul]
    have hmq := congrArg (fun value : ℝ => (offset : ℝ) / (k : ℝ) * value) hd
    have hcancel : (offset : ℝ) / (k : ℝ) * (k : ℝ) = offset := div_mul_cancel₀ _ hk'.ne'
    change (first : ℝ) + (offset : ℝ) * (q : ℝ) + ((min offset r : ℤ) : ℝ) -
      ((1 - (offset : ℝ) / (k : ℝ)) * (first : ℝ) + (offset : ℝ) / (k : ℝ) * (last : ℝ)) = _
    linear_combination hmq - (q : ℝ) * hcancel
  rw [heq]
  have hprod₀ : 0 ≤ (offset : ℝ) / (k : ℝ) * (r : ℝ) := mul_nonneg ht₀ hr₀
  have hprodK : (offset : ℝ) / (k : ℝ) * (r : ℝ) ≤ (k : ℝ) := by
    have h := mul_le_mul_of_nonneg_right ht₁ hr₀
    simpa only [one_mul] using h.trans (by simpa only [one_mul] using hrk)
  exact abs_le.mpr ⟨by linarith only [hmin₀, hprodK], by linarith only [hminK, hprod₀]⟩

/-- Uniform affine quadratic error on the actual retained vertices lifts
to uniform affine quadratic error on the physical plane. -/
theorem quadraticGrowth_liftColumns_of_retained_bound {k : ℤ} (hk : 0 < k) {columns : Field} {a b c : ℝ}
    (slopeX slopeY bound : ℝ) (hbound : 0 ≤ bound)
    (hretained : ∀ column row,
      |(columns (column, row) : ℝ) - matrixQuadratic (symmetricMatrix a b c) (columnSite k column row 0) -
        (slopeX * (column : ℝ) + slopeY * ((k * row - column : ℤ) : ℝ))| ≤ bound) :
    HasQuadraticGrowth (liftColumns k columns) (symmetricMatrix a b c) := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  apply quadraticGrowth_of_bounded_linear_error slopeX slopeY ((k : ℝ) + bound + |c| * (k : ℝ) ^ 2 / 2) (by positivity)
  intro site
  set column := site.1
  set row := (site.1 + site.2) / k
  set offset := (site.1 + site.2) % k
  have hcoords : columnSite k column row offset = site := columnSite_coordinates k site
  have hlo : 0 ≤ offset := Int.emod_nonneg _ (ne_of_gt hk)
  have hhi : offset ≤ k := (Int.emod_lt_of_pos _ hk).le
  rw [← hcoords, liftColumns_closedChain hk columns column row offset hlo hhi]
  let fraction : ℝ := (offset : ℝ) / (k : ℝ)
  have ht₀ : 0 ≤ fraction := div_nonneg (by exact_mod_cast hlo) hk'.le
  have ht₁ : fraction ≤ 1 := (div_le_one hk').mpr (by exact_mod_cast hhi)
  let target (step : ℤ) := matrixQuadratic (symmetricMatrix a b c) (columnSite k column row step) +
    (slopeX * (column : ℝ) + slopeY * (((k * row - column + step : ℤ)) : ℝ))
  let first := columns (column, row)
  let last := columns (column, row + 1)
  have hnum : (last : ℝ) - target k = (last : ℝ) - matrixQuadratic (symmetricMatrix a b c) (columnSite k column (row + 1) 0) -
      (slopeX * (column : ℝ) + slopeY * ((k * (row + 1) - column : ℤ) : ℝ)) := by
    have hsite : columnSite k column row k = columnSite k column (row + 1) 0 := by
      apply Prod.ext
      · rfl
      · dsimp [columnSite]
        ring
    unfold target
    rw [hsite, show k * row - column + k = k * (row + 1) - column by ring]
    ring
  have hf : |(first : ℝ) - target 0| ≤ bound := by
    simpa only [target, first, add_zero, sub_add_eq_sub_sub] using hretained column row
  have hl : |(last : ℝ) - target k| ≤ bound := by rw [hnum]; exact hretained column (row + 1)
  have hblend : |blend fraction first last - blend fraction (target 0) (target k)| ≤ bound := by
    have heq : blend fraction first last - blend fraction (target 0) (target k) =
      (1 - fraction) * ((first : ℝ) - target 0) + fraction * ((last : ℝ) - target k) := by unfold blend; ring
    rw [heq]
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht₁), abs_of_nonneg ht₀]
    calc
      _ ≤ (1 - fraction) * bound + fraction * bound :=
        add_le_add (mul_le_mul_of_nonneg_left hf (sub_nonneg.mpr ht₁)) (mul_le_mul_of_nonneg_left hl ht₀)
      _ = _ := by ring
  have hq : blend fraction (target 0) (target k) - target offset =
      c * (offset : ℝ) * ((k : ℝ) - (offset : ℝ)) / 2 := by
    simp only [blend, target, fraction, columnSite, matrixQuadratic_symmetricMatrix,
      Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_zero]
    field_simp
    ring
  have hc : |blend fraction (target 0) (target k) - target offset| ≤ |c| * (k : ℝ) ^ 2 / 2 := by
    rw [hq, abs_div, abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
      abs_of_nonneg (show (0 : ℝ) ≤ offset by exact_mod_cast hlo),
      abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) - offset by exact_mod_cast sub_nonneg.mpr hhi)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    have hoffset : (offset : ℝ) ≤ k := by exact_mod_cast hhi
    have hprod := mul_le_mul hoffset (show (k : ℝ) - offset ≤ k by exact sub_le_self _ (by exact_mod_cast hlo))
      (show (0 : ℝ) ≤ (k : ℝ) - offset by linarith) hk'.le
    calc
      _ = |c| * ((offset : ℝ) * ((k : ℝ) - offset)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [pow_two] using hprod) (abs_nonneg _)
  change |(interpolate k first last offset : ℝ) - matrixQuadratic (symmetricMatrix a b c) (columnSite k column row offset) -
    (slopeX * (column : ℝ) + slopeY * ((k * row - column + offset : ℤ) : ℝ))| ≤ _
  rw [← sub_add_eq_sub_sub]
  calc
    _ ≤ |(interpolate k first last offset : ℝ) - blend fraction first last| +
        |blend fraction first last - target offset| := abs_sub_le _ _ _
    _ ≤ (k : ℝ) + (|blend fraction first last - blend fraction (target 0) (target k)| +
        |blend fraction (target 0) (target k) - target offset|) :=
      add_le_add (interpolate_abs_sub_blend_le hk first last offset hlo hhi) (abs_sub_le _ _ _)
    _ ≤ _ := by linarith only [hblend, hc]

end FLatticePaper.GeneralK
