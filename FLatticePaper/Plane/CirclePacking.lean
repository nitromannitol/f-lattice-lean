import FLatticePaper.Plane.ClassificationReduction

namespace FLatticePaper

open GeneralK

theorem circleMatrix_sub (a b c x y z : ℝ) :
    circleMatrix a b c - circleMatrix x y z = circleMatrix (a - x) (b - y) (c - z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [circleMatrix, symmetricMatrix] <;> ring

theorem circleMatrix_add (a b c x y z : ℝ) :
    circleMatrix a b c + circleMatrix x y z = circleMatrix (a + x) (b + y) (c + z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [circleMatrix, symmetricMatrix] <;> ring

private theorem circleMatrix_coords (matrix : SymmetricMatrix) :
    circleMatrix (matrix.val 0 0 - matrix.val 1 1) (2 * matrix.val 0 1) (matrix.val 0 0 + matrix.val 1 1) = matrix.val := by
  have hs : matrix.val 1 0 = matrix.val 0 1 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 0 1) matrix.property
  ext i j
  fin_cases i <;> fin_cases j <;> simp [circleMatrix, symmetricMatrix, hs]

/-- A strictly dominating admitted matrix puts the lower point in the
interior of the growth set in the symmetric-matrix topology. -/
theorem symmetricCircleMatrix_mem_interior_of_lt {a b c x y z : ℝ}
    (hadmitted : circleMatrix a b c ∈ integerSuperharmonicMatrices)
    (hgap : Real.sqrt ((a - x) ^ 2 + (b - y) ^ 2) < c - z) :
    symmetricCircleMatrix x y z ∈ interior symmetricGrowthSet := by
  let horiz (matrix : SymmetricMatrix) := matrix.val 0 0 - matrix.val 1 1
  let vert (matrix : SymmetricMatrix) := 2 * matrix.val 0 1
  let trace (matrix : SymmetricMatrix) := matrix.val 0 0 + matrix.val 1 1
  have heval (i j : Fin 2) : Continuous (fun matrix : SymmetricMatrix => matrix.val i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  have hh : Continuous horiz := (heval 0 0).sub (heval 1 1)
  have hv : Continuous vert := continuous_const.mul (heval 0 1)
  have ht : Continuous trace := (heval 0 0).add (heval 1 1)
  let region := {matrix | Real.sqrt ((a - horiz matrix) ^ 2 + (b - vert matrix) ^ 2) < c - trace matrix}
  have hopen : IsOpen region := isOpen_lt (Real.continuous_sqrt.comp
    (((continuous_const.sub hh).pow 2).add ((continuous_const.sub hv).pow 2))) (continuous_const.sub ht)
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hopen.mem_nhds ?_)
  · intro matrix hmatrix
    change matrix.val ∈ integerSuperharmonicMatrices
    have hcoords : circleMatrix (horiz matrix) (vert matrix) (trace matrix) = matrix.val := circleMatrix_coords matrix
    have hpsd : (circleMatrix a b c - matrix.val).PosSemidef := by
      rw [← hcoords, circleMatrix_sub, circleMatrix_posSemidef_iff]
      exact (show Real.sqrt ((a - horiz matrix) ^ 2 + (b - vert matrix) ^ 2) < c - trace matrix from hmatrix).le
    rw [integerSuperharmonicMatrices_eq_growthSet_two] at hadmitted ⊢
    have h := sub_mem_growthSet_of_posSemidef (by decide) hadmitted hpsd
    rwa [sub_sub_cancel] at h
  · have hx : horiz (symmetricCircleMatrix x y z) = x := by
      simp [horiz, symmetricCircleMatrix, circleMatrix, symmetricMatrix]; ring
    have hy : vert (symmetricCircleMatrix x y z) = y := by
      simp [vert, symmetricCircleMatrix, circleMatrix, symmetricMatrix]; ring
    have hz : trace (symmetricCircleMatrix x y z) = z := by
      simp [trace, symmetricCircleMatrix, circleMatrix, symmetricMatrix]; ring
    change Real.sqrt ((a - horiz _) ^ 2 + (b - vert _) ^ 2) < c - trace _
    rwa [hx, hy, hz]

private theorem laplacian_reflect_first (height : Field) (site : Site) :
    laplacian (fun point => height (-point.1, point.2)) site = laplacian height (-site.1, site.2) := by
  obtain ⟨x, y⟩ := site
  have heven : EvenSite (-x, y) ↔ EvenSite (x, y) := by
    change (-x + y) % 2 = 0 ↔ (x + y) % 2 = 0
    omega
  simp only [laplacian, incomingNeg, incomingPos, heven]
  split
  · simp only [show -(x - 1) = -x + 1 by ring, show -(x + 1) = -x - 1 by ring]
    ring
  · rfl

theorem circleMatrix_neg_mixed_mem_integerSuperharmonicMatrices {a b c : ℝ}
    (h : circleMatrix a b c ∈ integerSuperharmonicMatrices) :
    circleMatrix a (-b) c ∈ integerSuperharmonicMatrices := by
  obtain ⟨-, height, hsuper, hgrowth⟩ := h
  refine ⟨circleMatrix_isSymm .., fun point => height (-point.1, point.2), fun point => ?_, ?_⟩
  · rw [laplacian_reflect_first]
    exact hsuper _
  · intro ε hε
    obtain ⟨radius, hr, herror⟩ := hgrowth ε hε
    refine ⟨radius, hr, fun point hpoint => ?_⟩
    obtain ⟨x, y⟩ := point
    have hsize : squaredSize (-x, y) = squaredSize (x, y) := by simp [squaredSize]
    have hquad : matrixQuadratic (circleMatrix a b c) (-x, y) = matrixQuadratic (circleMatrix a (-b) c) (x, y) := by
      simp only [circleMatrix, matrixQuadratic_symmetricMatrix, Int.cast_neg]
      ring
    have h := herror (-x, y) (hsize ▸ hpoint)
    rwa [hsize, hquad] at h

/-- The boundary assertion on the one positive hyperbola arc implies the
upper inclusion of the corrected circle-packing theorem. -/
theorem circlePacking_of_hyperbolaBoundary
    (hhyperbola : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      symmetricCircleMatrix t (1 - t) (-Real.sqrt (t ^ 2 + (1 - t) ^ 2)) ∈ frontier symmetricGrowthSet)
    (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    matrix ∈ integerSuperharmonicMatrices ↔ ∃ s t : ℤ, (harmonicPeak s t - matrix).PosSemidef := by
  constructor
  · intro hm
    let original := (⟨matrix, hm.1⟩ : SymmetricMatrix)
    let a := matrix 0 0 - matrix 1 1
    let b := 2 * matrix 0 1
    let c := matrix 0 0 + matrix 1 1
    have hmatrix : circleMatrix a b c = matrix := circleMatrix_coords original
    let s : ℤ := ⌊(a + b) / 2 + 1 / 2⌋
    let t : ℤ := ⌊(b - a) / 2 + 1 / 2⌋
    let u := a - ((s : ℝ) - t)
    let v := b - ((s : ℝ) + t)
    have hsum : |u + v| ≤ 1 := by
      have h₁ := Int.floor_le ((a + b) / 2 + 1 / 2)
      have h₂ := Int.lt_floor_add_one ((a + b) / 2 + 1 / 2)
      change (s : ℝ) ≤ _ at h₁
      change _ < (s : ℝ) + 1 at h₂
      apply abs_le.mpr
      constructor <;> dsimp [u, v] <;> linarith only [h₁, h₂]
    have hdiff : |v - u| ≤ 1 := by
      have h₁ := Int.floor_le ((b - a) / 2 + 1 / 2)
      have h₂ := Int.lt_floor_add_one ((b - a) / 2 + 1 / 2)
      change (t : ℝ) ≤ _ at h₁
      change _ < (t : ℝ) + 1 at h₂
      apply abs_le.mpr
      constructor <;> dsimp [u, v] <;> linarith only [h₁, h₂]
    have hdiamond : |u| + |v| ≤ 1 := by
      have h₁ := abs_le.mp hsum
      have h₂ := abs_le.mp hdiff
      by_cases hu : 0 ≤ u <;> by_cases hv : 0 ≤ v
      · rw [abs_of_nonneg hu, abs_of_nonneg hv]; exact h₁.2
      · rw [abs_of_nonneg hu, abs_of_neg (lt_of_not_ge hv)]; linarith only [h₂.1]
      · rw [abs_of_neg (lt_of_not_ge hu), abs_of_nonneg hv]; linarith only [h₂.2]
      · rw [abs_of_neg (lt_of_not_ge hu), abs_of_neg (lt_of_not_ge hv)]; linarith only [h₁.1]
    have hnormalize : circleMatrix u v c + harmonicPeak s t = matrix := by
      rw [harmonicPeak, circleMatrix_add, add_zero, ← hmatrix]
      dsimp [u, v]
      congr 1 <;> ring
    have hnormalized : circleMatrix u v c ∈ integerSuperharmonicMatrices :=
      (add_harmonicPeak_mem_integerSuperharmonicMatrices_iff s t).mp (hnormalize ▸ hm)
    let radius := Real.sqrt (u ^ 2 + v ^ 2)
    refine ⟨s, t, ?_⟩
    have hgoal : (harmonicPeak s t - matrix).PosSemidef ↔ c ≤ -radius := by
      rw [harmonicPeak, ← hmatrix, circleMatrix_sub, circleMatrix_posSemidef_iff]
      have hx : (s : ℝ) - t - a = -u := by dsimp [u]; ring
      have hy : (s : ℝ) + t - b = -v := by dsimp [v]; ring
      rw [hx, hy, neg_sq, neg_sq, zero_sub]
      change radius ≤ -c ↔ c ≤ -radius
      constructor <;> intro h <;> linarith only [h]
    apply hgoal.mpr
    by_contra! hbad
    have htrace := circleMatrix_trace_nonpos hnormalized
    let w := |v|
    have hw : 0 ≤ w := abs_nonneg _
    have hwr : w ^ 2 = v ^ 2 := sq_abs _
    have hpos : 0 < |u| + w := by
      by_contra! hz
      have hz' : |u| + w = 0 := le_antisymm hz (by positivity)
      have hu : u = 0 := abs_eq_zero.mp (by linarith only [abs_nonneg u, hw, hz'])
      have hv : v = 0 := abs_eq_zero.mp (by change w = 0; linarith only [abs_nonneg u, hw, hz'])
      simp [radius, hu, hv] at hbad
      linarith only [hbad, htrace]
    let scale := 1 / (|u| + w)
    have hscale : 1 ≤ scale := (le_div_iff₀ hpos).mpr (by simpa using hdiamond)
    have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
    let x := scale * u
    let y := scale * w
    have hy : 0 ≤ y := mul_nonneg hscalePos.le hw
    have hside : |x| + y = 1 := by
      dsimp [x, y]
      rw [abs_mul, abs_of_nonneg hscalePos.le, ← mul_add]
      exact div_mul_cancel₀ 1 hpos.ne'
    have hrad : Real.sqrt (x ^ 2 + y ^ 2) = scale * radius := by
      rw [show x ^ 2 + y ^ 2 = scale ^ 2 * (u ^ 2 + v ^ 2) by dsimp [x, y]; rw [mul_pow, mul_pow, hwr]; ring,
        Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq hscalePos.le]
    have hdist : Real.sqrt ((u - x) ^ 2 + (w - y) ^ 2) = (scale - 1) * radius := by
      have heq : (u - x) ^ 2 + (w - y) ^ 2 = (scale - 1) ^ 2 * (u ^ 2 + v ^ 2) := by
        dsimp [x, y]
        rw [← hwr]
        ring
      rw [heq, Real.sqrt_mul (sq_nonneg (scale - 1)), Real.sqrt_sq (sub_nonneg.mpr hscale)]
    have hstrict : Real.sqrt ((u - x) ^ 2 + (w - y) ^ 2) < c - (-Real.sqrt (x ^ 2 + y ^ 2)) := by
      rw [hdist, hrad]
      linarith only [hbad]
    have hupper : circleMatrix u w c ∈ integerSuperharmonicMatrices := by
      by_cases hv : 0 ≤ v
      · simpa [w, abs_of_nonneg hv] using hnormalized
      · simpa [w, abs_of_neg (lt_of_not_ge hv)] using circleMatrix_neg_mixed_mem_integerSuperharmonicMatrices hnormalized
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx] at hside
      have hy' : y = 1 - x := by linarith only [hside]
      rw [hy'] at hstrict
      exact (hhyperbola x hx (by linarith only [hside, hy])).2
        (symmetricCircleMatrix_mem_interior_of_lt hupper hstrict)
    · rw [abs_of_neg (lt_of_not_ge hx)] at hside
      have hx' : 0 ≤ x + 1 := by linarith only [hside, hy]
      have hy' : 1 - y = 1 - (x + 1) := by linarith only [hside]
      have hradius : Real.sqrt ((x + 1) ^ 2 + (1 - y) ^ 2) = Real.sqrt (x ^ 2 + y ^ 2) := by
        congr 1
        nlinarith only [hside]
      have hshift := (add_harmonicPeak_mem_integerSuperharmonicMatrices_iff 0 (-1)).mpr hupper
      have hshift' : circleMatrix (u + 1) (w - 1) c ∈ integerSuperharmonicMatrices := by
        rw [harmonicPeak, circleMatrix_add] at hshift
        norm_num at hshift
        simpa only [sub_eq_add_neg] using hshift
      have hreflected : circleMatrix (u + 1) (1 - w) c ∈ integerSuperharmonicMatrices := by
        have h := circleMatrix_neg_mixed_mem_integerSuperharmonicMatrices hshift'
        rwa [neg_sub] at h
      have hstrict' : Real.sqrt ((u + 1 - (x + 1)) ^ 2 + (1 - w - (1 - y)) ^ 2) <
          c - (-Real.sqrt ((x + 1) ^ 2 + (1 - y) ^ 2)) := by
        rw [hradius, show u + 1 - (x + 1) = u - x by ring, show 1 - w - (1 - y) = -(w - y) by ring, neg_sq]
        exact hstrict
      rw [hy'] at hstrict'
      exact (hhyperbola (x + 1) hx' (by linarith only [lt_of_not_ge hx])).2
        (symmetricCircleMatrix_mem_interior_of_lt hreflected hstrict')
  · rintro ⟨s, t, h⟩
    exact mem_integerSuperharmonicMatrices_of_peak_sub_posSemidef s t h

end FLatticePaper
