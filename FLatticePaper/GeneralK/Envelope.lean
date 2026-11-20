import FLatticePaper.GeneralK.Growth
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.LeastGreatest
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace FLatticePaper.GeneralK

theorem retained_add_iff {k : ℤ} {step : Site} (hstep : Retained k step) (site : Site) :
    Retained k (site + step) ↔ Retained k site := by
  change (step.1 + step.2) % k = 0 at hstep
  change (site.1 + step.1 + (site.2 + step.2)) % k = 0 ↔ (site.1 + site.2) % k = 0
  rw [show site.1 + step.1 + (site.2 + step.2) = (site.1 + site.2) + (step.1 + step.2) by ring,
    Int.add_emod, hstep, add_zero, Int.emod_emod]

theorem superharmonic_translate_sub_affine {k : ℤ} {field : Field} (hfield : Superharmonic k field)
    {step : Site} (hstep : Retained k step) (slopeX slopeY constant : ℤ) :
    Superharmonic k (fun site => field (site + step) - slopeX * site.1 - slopeY * site.2 - constant) := by
  rintro ⟨x, y⟩
  have hlap := hfield ((x, y) + step)
  have hphase := retained_add_iff hstep (x, y)
  by_cases h : Retained k (x, y)
  · have hs := hphase.mpr h
    simp only [laplacian, incomingNeg, incomingPos, if_pos h, if_pos hs] at hlap ⊢
    have hn : (x - 1, y) + step = (x + step.1 - 1, y + step.2) := by
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]
      omega
    have hp : (x + 1, y) + step = (x + step.1 + 1, y + step.2) := by
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [hn, hp]
    convert hlap using 1
    dsimp
    ring
  · have hs : ¬ Retained k ((x, y) + step) := fun h' => h (hphase.mp h')
    simp only [laplacian, incomingNeg, incomingPos, if_neg h, if_neg hs] at hlap ⊢
    have hn : (x, y - 1) + step = (x + step.1, y + step.2 - 1) := by
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]
      omega
    have hp : (x, y + 1) + step = (x + step.1, y + step.2 + 1) := by
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [hn, hp]
    convert hlap using 1
    dsimp
    ring

/-- A pointwise bounded family of integer superharmonic heights has an
attained minimum. At a given center its minimizing member controls both inputs. -/
theorem exists_superharmonic_min {k : ℤ} {ι : Type*} [Nonempty ι] (fields : ι → Field)
    (hfields : ∀ i, Superharmonic k (fields i)) (hbound : ∀ site, ∃ lower : ℤ, ∀ i, lower ≤ fields i site) :
    ∃ height : Field, Superharmonic k height ∧
      ∀ site, (∀ i, height site ≤ fields i site) ∧ ∃ i, height site = fields i site := by
  have hleast (site : Site) : ∃ least : ℤ, (∃ i, least = fields i site) ∧ ∀ i, least ≤ fields i site := by
    obtain ⟨lower, hlower⟩ := hbound site
    obtain ⟨index⟩ := ‹Nonempty ι›
    obtain ⟨least, hmem, hmin⟩ := Int.exists_least_of_bdd (P := fun value => ∃ i, value = fields i site)
      ⟨lower, fun _ ⟨i, hi⟩ => hi ▸ hlower i⟩ ⟨fields index site, index, rfl⟩
    exact ⟨least, hmem, fun i => hmin _ ⟨i, rfl⟩⟩
  choose height hchoice hmin using hleast
  refine ⟨height, ?_, fun site => ⟨hmin site, hchoice site⟩⟩
  intro site
  obtain ⟨index, heq⟩ := hchoice site
  have hneg := hmin (incomingNeg k site) index
  have hpos := hmin (incomingPos k site) index
  have hlap := hfields index site
  simp only [laplacian] at hlap ⊢
  omega

private theorem quadraticGrowth_of_abs_linear_bound {height : Field} {matrix : Matrix (Fin 2) (Fin 2) ℝ}
    (constant : ℝ) (hconstant : 0 ≤ constant)
    (hbound : ∀ site, |(height site : ℝ) - matrixQuadratic matrix site| ≤ |(site.1 : ℝ)| + |(site.2 : ℝ)| + constant) :
    HasQuadraticGrowth height matrix := by
  intro ε hε
  let radius := 1 + (2 + constant) / ε
  have hr₁ : 1 ≤ radius := by
    dsimp [radius]
    exact le_add_of_nonneg_right (by positivity)
  have hr : 0 < radius := by linarith
  refine ⟨radius, hr, fun site hlarge => (hbound site).trans ?_⟩
  have hsize : radius ≤ squaredSize site := by
    have hsq : radius ≤ radius ^ 2 := by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr₁)]
    exact hsq.trans hlarge
  have hcoord : |(site.1 : ℝ)| * radius ≤ squaredSize site ∧ |(site.2 : ℝ)| * radius ≤ squaredSize site := by
    unfold squaredSize at hlarge ⊢
    constructor
    · nlinarith only [hlarge, sq_nonneg (|(site.1 : ℝ)| - radius), sq_abs (site.1 : ℝ), sq_nonneg (site.2 : ℝ)]
    · nlinarith only [hlarge, sq_nonneg (|(site.2 : ℝ)| - radius), sq_abs (site.2 : ℝ), sq_nonneg (site.1 : ℝ)]
  have hrε : 2 + constant ≤ ε * radius := by
    dsimp [radius]
    field_simp
    nlinarith
  have hscale := mul_le_mul_of_nonneg_right hrε (show 0 ≤ squaredSize site by unfold squaredSize; positivity)
  have hconstant := mul_le_mul_of_nonneg_left hsize hconstant
  apply le_of_mul_le_mul_right ?_ hr
  nlinarith only [hcoord.1, hcoord.2, hscale, hconstant]

/-- A global affine lower quadratic bound can be upgraded to two-sided
growth by taking the minimum over phase-preserving translated heights. -/
theorem mem_growthSet_of_affine_lower_bound {k : ℤ} (hk : 2 ≤ k) {a b c : ℝ} {field : Field}
    (hfield : Superharmonic k field) (tiltX tiltY constant : ℝ)
    (hlower : ∀ site, matrixQuadratic (symmetricMatrix a b c) site +
      (tiltX * (site.1 : ℝ) + tiltY * (site.2 : ℝ)) + constant ≤ field site) :
    symmetricMatrix a b c ∈ growthSet k := by
  let q := matrixQuadratic (symmetricMatrix a b c)
  let tilt (site : Site) := tiltX * (site.1 : ℝ) + tiltY * (site.2 : ℝ)
  let discrepancy (site : Site) := (field site : ℝ) - (q site + tilt site + constant)
  let adjustedX (step : Site) := a * (step.1 : ℝ) + b * (step.2 : ℝ) + tiltX
  let adjustedY (step : Site) := b * (step.1 : ℝ) + c * (step.2 : ℝ) + tiltY
  let translated (step : {site : Site // Retained k site}) : Field := fun site =>
    field (site + step.val) - ⌊adjustedX step.val⌋ * site.1 - ⌊adjustedY step.val⌋ * site.2 -
      ⌊q step.val + tilt step.val + constant⌋
  have htranslate (step : {site : Site // Retained k site}) (site : Site) :
      |(translated step site : ℝ) - q site - discrepancy (site + step.val)| ≤
        |(site.1 : ℝ)| + |(site.2 : ℝ)| + 1 := by
    have heq : (translated step site : ℝ) - q site - discrepancy (site + step.val) =
        (adjustedX step.val - ⌊adjustedX step.val⌋) * (site.1 : ℝ) +
        (adjustedY step.val - ⌊adjustedY step.val⌋) * (site.2 : ℝ) +
        (q step.val + tilt step.val + constant - ⌊q step.val + tilt step.val + constant⌋) := by
      obtain ⟨x, y⟩ := site
      obtain ⟨⟨u, v⟩, hu⟩ := step
      simp only [translated, discrepancy, q, tilt, adjustedX, adjustedY, Prod.fst_add, Prod.snd_add,
        Int.cast_sub, Int.cast_mul, Int.cast_add]
      rw [matrixQuadratic_symmetricMatrix, matrixQuadratic_symmetricMatrix, matrixQuadratic_symmetricMatrix]
      simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
      ring
    rw [heq]
    have hf (value : ℝ) : |value - ⌊value⌋| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le value))]
      linarith only [Int.lt_floor_add_one value]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (hf _))
    · simpa only [one_mul, abs_mul] using
        (mul_le_mul_of_nonneg_right (hf (adjustedX step.val)) (abs_nonneg (site.1 : ℝ)))
    · simpa only [one_mul, abs_mul] using
        (mul_le_mul_of_nonneg_right (hf (adjustedY step.val)) (abs_nonneg (site.2 : ℝ)))
  letI : Nonempty {site : Site // Retained k site} := ⟨⟨0, by simp [Retained]⟩⟩
  obtain ⟨height, hheight, hmin⟩ := exists_superharmonic_min translated
    (fun step => superharmonic_translate_sub_affine hfield step.property _ _ _) (fun site => by
      refine ⟨⌊q site - (|(site.1 : ℝ)| + |(site.2 : ℝ)| + 1)⌋, fun step => ?_⟩
      have hfloor := Int.floor_le (q site - (|(site.1 : ℝ)| + |(site.2 : ℝ)| + 1))
      have hl := (abs_le.mp (htranslate step site)).1
      have hdisc : 0 ≤ discrepancy (site + step.val) := sub_nonneg.mpr (hlower _)
      exact_mod_cast (show (⌊q site - (|(site.1 : ℝ)| + |(site.2 : ℝ)| + 1)⌋ : ℝ) ≤ translated step site by
        linarith only [hfloor, hl, hdisc]))
  let rows := Finset.Ico (0 : ℤ) k
  obtain ⟨row, _, hmax⟩ := rows.exists_max_image (fun row => discrepancy (0, row))
    ⟨0, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
  let bound := max 0 (discrepancy (0, row))
  refine (symmetricMatrix_mem_growthSet_iff k a b c).mpr ⟨height, hheight, ?_⟩
  apply quadraticGrowth_of_abs_linear_bound (1 + bound) (by dsimp [bound]; positivity)
  intro site
  let r := (site.1 + site.2) % k
  let step : {site : Site // Retained k site} := ⟨(0, r) - site, by
    change (0 - site.1 + (r - site.2)) % k = 0
    rw [show 0 - site.1 + (r - site.2) = -((site.1 + site.2) - (site.1 + site.2) % k) by dsimp [r]; ring]
    exact Int.dvd_iff_emod_eq_zero.mp (dvd_neg.mpr Int.dvd_self_sub_emod)⟩
  have hpoint : site + step.val = (0, r) := by dsimp [step]; abel
  have hr : r ∈ rows := Finset.mem_Ico.mpr
    ⟨Int.emod_nonneg _ (by omega : k ≠ 0), Int.emod_lt_of_pos _ (by omega : 0 < k)⟩
  have hup := (abs_le.mp (htranslate step site)).2
  rw [hpoint] at hup
  have hrem := (hmax r hr).trans (le_max_right 0 (discrepancy (0, row)))
  have hheightUp : (height site : ℝ) ≤ translated step site := by exact_mod_cast (hmin site).1 step
  obtain ⟨index, hindex⟩ := (hmin site).2
  have hheightLo := (abs_le.mp (htranslate index site)).1
  rw [← hindex] at hheightLo
  have hremLo : 0 ≤ discrepancy (site + index.val) := sub_nonneg.mpr (hlower _)
  have hbound : 0 ≤ bound := le_max_left ..
  apply abs_le.mpr
  constructor <;> linarith only [hup, hrem, hheightUp, hheightLo, hremLo, hbound]

/-- A real symmetric matrix is recovered from its three independent entries. -/
theorem symmetricMatrix_entries {matrix : Matrix (Fin 2) (Fin 2) ℝ} (hsymm : matrix.IsSymm) :
    symmetricMatrix (matrix 0 0) (matrix 0 1) (matrix 1 1) = matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · exact hsymm.apply 1 0
  · rfl

/-- Any negative semidefinite real matrix is admitted. The zero field is
the global lower-bound witness, and the translated envelope realizes growth. -/
theorem neg_mem_growthSet_of_posSemidef {k : ℤ} (hk : 2 ≤ k) {matrix : Matrix (Fin 2) (Fin 2) ℝ}
    (hpos : matrix.PosSemidef) : -matrix ∈ growthSet k := by
  have hsymm : (-matrix).IsSymm := Matrix.isSymm_neg_iff.mpr (Matrix.isHermitian_iff_isSymm.mp hpos.isHermitian)
  have heq := symmetricMatrix_entries hsymm
  rw [← heq]
  refine mem_growthSet_of_affine_lower_bound hk (field := 0) (fun _ => by simp [laplacian]) 0 0 0 ?_
  intro site
  have hq := hpos.dotProduct_mulVec_nonneg (Farey.siteVector site)
  simp only [star_trivial] at hq
  rw [heq]
  simp only [matrixQuadratic, Matrix.neg_mulVec, dotProduct_neg, zero_mul, add_zero, Pi.zero_apply, Int.cast_zero]
  linarith

/-- Downward closure in the real positive semidefinite order, including
singular and irrational decrements. -/
theorem sub_mem_growthSet_of_posSemidef {k : ℤ} (hk : 2 ≤ k) {matrix decrement : Matrix (Fin 2) (Fin 2) ℝ}
    (hmatrix : matrix ∈ growthSet k) (hdecrement : decrement.PosSemidef) : matrix - decrement ∈ growthSet k := by
  rw [sub_eq_add_neg]
  exact add_mem_growthSet hmatrix (neg_mem_growthSet_of_posSemidef hk hdecrement)

end FLatticePaper.GeneralK
