import FLatticePaper.GeneralK.ColumnUpperPath
import FLatticePaper.GeneralK.Obstacle

namespace FLatticePaper.GeneralK.ColumnSlice

private theorem retainedQuadratic_sub_reference (slice : ColumnSlice) (sector : ℤ)
    (a tiltX tiltY : ℝ) (hsector : (slice.vertical : ℝ) * ((slice.k : ℝ) * (slice.length : ℝ)) ^ 2 / 2 +
      tiltY * ((slice.k : ℝ) * (slice.length : ℝ)) = sector) (column row : ℤ) :
    let site := columnSite slice.k column row 0
    matrixQuadratic (symmetricMatrix a slice.mixed slice.vertical) site +
      (tiltX * (site.1 : ℝ) + tiltY * (site.2 : ℝ)) -
      (slice.referencePolynomial sector column row : ℝ) =
      (a - slice.a₀) * (column : ℝ) ^ 2 / 2 + (tiltX - tiltY) * (column : ℝ) := by
  have hlen : (slice.length : ℝ) ≠ 0 := by exact_mod_cast slice.length_pos.ne'
  have hsector' : ((sector : ℝ) - (slice.k : ℝ) ^ 2 * (slice.vertical : ℝ) * (slice.length : ℝ) ^ 2 / 2) /
      (slice.length : ℝ) = tiltY * (slice.k : ℝ) := by
    apply (div_eq_iff hlen).mpr
    linear_combination -hsector
  simp only [columnSite, add_zero, matrixQuadratic_symmetricMatrix, Int.cast_sub, Int.cast_mul,
    referencePolynomial, u, v, w, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_intCast, Rat.cast_natCast, Rat.cast_ofNat, hsector']
  ring

/-- The least ceiling majorant in a normalized transverse sector supplies the
actual periodic restriction and its bounded quadratic error. -/
theorem le_cyclePeak_of_leastMajorant (slice : ColumnSlice) (sector : slice.Sector)
    {a tiltX tiltY bound : ℝ} {height : Field} (hfirst : (slice.a₀ : ℝ) ≤ a)
    (hsector : (slice.vertical : ℝ) * ((slice.k : ℝ) * (slice.length : ℝ)) ^ 2 / 2 +
      tiltY * ((slice.k : ℝ) * (slice.length : ℝ)) = (sector.val : ℤ))
    (hmin : IsLeastMajorant slice.k (ceilingObstacle a slice.mixed slice.vertical tiltX tiltY) height)
    (herror : ∀ site, |(height site : ℝ) - matrixQuadratic (symmetricMatrix a slice.mixed slice.vertical) site -
      (tiltX * (site.1 : ℝ) + tiltY * (site.2 : ℝ))| ≤ bound) :
    a ≤ (slice.cyclePeak : ℝ) := by
  let field : Field := fun point => height (columnSite slice.k point.1 point.2 0)
  let reference := slice.reference (sector.val : ℤ)
  let step : Site := (0, slice.k * (slice.length : ℤ))
  obtain ⟨mixed, vertical, hmix, hvert, hreference⟩ := slice.reference_add_length (sector.val : ℤ)
  have hb : (slice.mixed : ℝ) * ((slice.k : ℝ) * (slice.length : ℝ)) = ((mixed + vertical : ℤ) : ℝ) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hmix
    have h' := congrArg (fun q : ℚ => (q : ℝ)) hvert
    push_cast [v, w] at h h' ⊢
    have hk : (slice.k : ℝ) ≠ 0 := by exact_mod_cast (show slice.k ≠ 0 by have := slice.hk; omega)
    have hv' : (slice.k : ℝ) * (slice.vertical : ℝ) * (slice.length : ℝ) = vertical := by
      apply mul_left_cancel₀ hk
      linear_combination h'
    linear_combination h + hv'
  have hc : (slice.vertical : ℝ) * ((slice.k : ℝ) * (slice.length : ℝ)) = vertical := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hvert
    push_cast [w] at h
    have hk : (slice.k : ℝ) ≠ 0 := by exact_mod_cast (show slice.k ≠ 0 by have := slice.hk; omega)
    apply mul_left_cancel₀ hk
    linear_combination h
  have hphase : Retained slice.k step := by
    change (0 + slice.k * (slice.length : ℤ)) % slice.k = 0
    simp
  let p (site : Site) := matrixQuadratic (symmetricMatrix a slice.mixed slice.vertical) site +
    (tiltX * (site.1 : ℝ) + tiltY * (site.2 : ℝ))
  have hp (site : Site) : p (site + step) = p site +
      (((mixed + vertical) * site.1 + vertical * site.2 + (sector.val : ℤ) : ℤ) : ℝ) := by
    obtain ⟨x, y⟩ := site
    rw [show (x, y) + step = (x, y + slice.k * (slice.length : ℤ)) by simp [step]]
    simp only [p, matrixQuadratic_symmetricMatrix,
      Int.cast_add, Int.cast_mul, Int.cast_natCast]
    push_cast at hb hsector
    linear_combination (x : ℝ) * hb + (y : ℝ) * hc + hsector
  have hobs (site : Site) : ceilingObstacle a slice.mixed slice.vertical tiltX tiltY (site + step) =
      ceilingObstacle a slice.mixed slice.vertical tiltX tiltY site +
        (mixed + vertical) * site.1 + vertical * site.2 + (sector.val : ℤ) := by
    change ⌈p (site + step)⌉ = ⌈p site⌉ + _ + _ + _
    rw [hp, Int.ceil_add_intCast]
    ring
  have hperiod (column : ℤ) : Function.Periodic (fun row => field (column, row) - reference (column, row))
      (slice.length : ℤ) := by
    intro row
    have h := hmin.add_period hphase (mixed + vertical) vertical (sector.val : ℤ) hobs (columnSite slice.k column row 0)
    have hstep : columnSite slice.k column row 0 + step = columnSite slice.k column (row + slice.length) 0 := by
      apply Prod.ext <;> (simp [step, columnSite]; all_goals ring)
    rw [hstep] at h
    change height (columnSite slice.k column (row + slice.length) 0) -
      slice.reference (sector.val : ℤ) (column, row + slice.length) = _
    rw [h, hreference]
    simp only [field, reference, columnSite, add_zero]
    ring
  have hcharge (site : Site) : 0 ≤ -laplacian slice.k height site ∧ -laplacian slice.k height site ≤ slice.chargeBound := by
    have h := hmin.chargeBound hfirst site
    have heq : ⌈2 - min (slice.a₀ : ℝ) (slice.vertical : ℝ)⌉ = ⌈2 - min (slice.a₀ : ℚ) slice.vertical⌉ := by
      have hcast : ((2 - min (slice.a₀ : ℚ) slice.vertical : ℚ) : ℝ) = 2 - min (slice.a₀ : ℝ) (slice.vertical : ℝ) := by
        simp [Rat.cast_min]
      rw [← hcast, Rat.ceil_cast]
    simpa only [chargeBound, heq] using h
  have hcorrection (column row : ℤ) : |((field (column, row) - reference (column, row) : ℤ) : ℝ) -
      ((a - slice.a₀) * (column : ℝ) ^ 2 / 2 + (tiltX - tiltY) * (column : ℝ))| ≤ bound + 1 := by
    let poly : ℚ := slice.referencePolynomial (sector.val : ℤ) column row
    have href : 0 ≤ (poly : ℝ) - (reference (column, row) : ℝ) ∧
        (poly : ℝ) - (reference (column, row) : ℝ) ≤ 1 := by
      have h₁ := Int.floor_le poly
      have h₂ := Int.lt_floor_add_one poly
      have h₁' : (reference (column, row) : ℝ) ≤ (poly : ℝ) := by exact_mod_cast h₁
      have h₂' : (poly : ℝ) < (reference (column, row) : ℝ) + 1 := by exact_mod_cast h₂
      constructor <;> linarith only [h₁', h₂']
    have h := abs_le.mp (herror (columnSite slice.k column row 0))
    have heq := slice.retainedQuadratic_sub_reference (sector.val : ℤ) a tiltX tiltY hsector column row
    change p (columnSite slice.k column row 0) - (poly : ℝ) = _ at heq
    rw [← heq, Int.cast_sub]
    apply abs_le.mpr
    change -(bound + 1) ≤ _ ∧ _ ≤ bound + 1
    dsimp only [field, p]
    constructor <;> linarith only [h.1, h.2, href.1, href.2]
  have hosc : ∃ initial : ℤ, ∀ column row,
      |(field (column, row) - reference (column, row)) - (field (column, 0) - reference (column, 0))| ≤ initial := by
    refine ⟨⌈2 * (bound + 1)⌉, fun column row => ?_⟩
    have h₁ := abs_le.mp (hcorrection column row)
    have h₂ := abs_le.mp (hcorrection column 0)
    have h := Int.le_ceil (2 * (bound + 1))
    have hreal : |((field (column, row) - reference (column, row) : ℤ) : ℝ) -
        ((field (column, 0) - reference (column, 0) : ℤ) : ℝ)| ≤ (⌈2 * (bound + 1)⌉ : ℤ) :=
      abs_le.mpr ⟨by linarith only [h₁.1, h₂.2, h], by linarith only [h₁.2, h₂.1, h]⟩
    exact_mod_cast hreal
  exact slice.le_cyclePeak_of_bounded_column_restriction sector
    (columnRow_restriction_nonpos slice.hk hmin.superharmonic) hperiod hosc
    (slice.abs_linearColumnRow_sub_reference_le (sector.val : ℤ) hcharge) a (tiltX - tiltY) (bound + 1)
    (fun column => hcorrection column 0)

/-- A bounded affine remainder with an integer transverse increment constant
is sufficient for the cycle upper bound. The constant is normalized by
adding an integer slope in the second physical coordinate. -/
theorem le_cyclePeak_of_transverse_representative (slice : ColumnSlice)
    {a tiltX tiltY bound : ℝ} {height : Field} (hfirst : (slice.a₀ : ℝ) ≤ a)
    (hsuper : Superharmonic slice.k height) (constant : ℤ)
    (hconstant : (slice.vertical : ℝ) * ((slice.k : ℝ) * (slice.length : ℝ)) ^ 2 / 2 +
      tiltY * ((slice.k : ℝ) * (slice.length : ℝ)) = (constant : ℝ))
    (herror : ∀ site, |(height site : ℝ) - matrixQuadratic (symmetricMatrix a slice.mixed slice.vertical) site -
      (tiltX * (site.1 : ℝ) + tiltY * (site.2 : ℝ))| ≤ bound) :
    a ≤ (slice.cyclePeak : ℝ) := by
  let stride := slice.k * (slice.length : ℤ)
  have hk : 0 < slice.k := by have := slice.hk; omega
  have hlen : 0 < (slice.length : ℤ) := by exact_mod_cast slice.length_pos
  have hstride : 0 < stride := mul_pos hk hlen
  let shift := constant / stride
  let rem := constant % stride
  have hrem : (rem.toNat : ℤ) = rem := Int.toNat_of_nonneg (Int.emod_nonneg _ hstride.ne')
  let sector : slice.Sector := ⟨rem.toNat, by
    have hcast : (slice.k.toNat * slice.length : ℕ) = (stride.toNat : ℕ) := by
      simp only [stride, Int.toNat_mul hk.le hlen.le, Int.toNat_natCast]
    rw [hcast]
    have h := Int.emod_lt_of_pos constant hstride
    omega⟩
  let tilt := tiltY - (shift : ℝ)
  have hnormalized : (slice.vertical : ℝ) * ((slice.k : ℝ) * (slice.length : ℝ)) ^ 2 / 2 +
      tilt * ((slice.k : ℝ) * (slice.length : ℝ)) = ((sector.val : ℤ) : ℝ) := by
    have hd := Int.emod_add_mul_ediv constant stride
    change rem + stride * shift = constant at hd
    have hd' : (rem : ℝ) + (stride : ℝ) * (shift : ℝ) = (constant : ℝ) := by exact_mod_cast hd
    change _ = ((rem.toNat : ℤ) : ℝ)
    rw [hrem]
    simp only [tilt, stride, Int.cast_mul, Int.cast_natCast] at hd' ⊢
    linarith only [hconstant, hd']
  let pad : ℤ := ⌈bound⌉
  let shifted : Field := fun site => height site - shift * site.2 - (-pad)
  have hshift : Superharmonic slice.k shifted := by
    have hzero : Retained slice.k (0 : Site) := by simp [Retained]
    simpa only [add_zero, zero_mul, sub_zero, shifted] using
      (superharmonic_translate_sub_affine hsuper hzero 0 shift (-pad))
  let q (site : Site) := matrixQuadratic (symmetricMatrix a slice.mixed slice.vertical) site +
    (tiltX * (site.1 : ℝ) + tilt * (site.2 : ℝ))
  have hshiftError (site : Site) : q site ≤ (shifted site : ℝ) ∧ (shifted site : ℝ) - q site ≤ bound + pad := by
    have h := abs_le.mp (herror site)
    have hpad : bound ≤ (pad : ℝ) := Int.le_ceil bound
    dsimp only [q, shifted, tilt]
    push_cast
    constructor <;> linarith only [h.1, h.2, hpad]
  let obstacle := ceilingObstacle a slice.mixed slice.vertical tiltX tilt
  obtain ⟨least, hleast⟩ := exists_leastMajorant obstacle shifted hshift (fun site =>
    Int.ceil_le.mpr (hshiftError site).1)
  have hleastError (site : Site) : |(least site : ℝ) - matrixQuadratic (symmetricMatrix a slice.mixed slice.vertical) site -
      (tiltX * (site.1 : ℝ) + tilt * (site.2 : ℝ))| ≤ bound + pad := by
    have hlow := Int.le_ceil (q site)
    have hdom : (obstacle site : ℝ) ≤ least site := by exact_mod_cast hleast.majorizes site
    have hupp : (least site : ℝ) ≤ shifted site := by
      exact_mod_cast hleast.least shifted hshift (fun point => Int.ceil_le.mpr (hshiftError point).1) site
    have h := (hshiftError site).2
    change q site ≤ (obstacle site : ℝ) at hlow
    have hrewrite : (least site : ℝ) - matrixQuadratic (symmetricMatrix a slice.mixed slice.vertical) site -
        (tiltX * (site.1 : ℝ) + tilt * (site.2 : ℝ)) = (least site : ℝ) - q site := by dsimp [q]; ring
    rw [hrewrite, abs_of_nonneg (sub_nonneg.mpr (hlow.trans hdom))]
    linarith only [hupp, h]
  exact slice.le_cyclePeak_of_leastMajorant sector hfirst hnormalized hleast hleastError

end FLatticePaper.GeneralK.ColumnSlice
