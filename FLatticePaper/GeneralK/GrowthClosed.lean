import FLatticePaper.GeneralK.Connectivity
import FLatticePaper.GeneralK.Envelope
import FLatticePaper.GeneralK.Trace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Sequences

namespace FLatticePaper.GeneralK

open Filter Topology

/-- Normalizing at the minimum of a slightly lowered quadratic gives a
phase anchor and residual affine slopes with uniformly bounded coefficients. -/
private theorem exists_normalized_lower_bound {k : ℤ} (hk : 2 ≤ k) {a b c shift : ℝ} (hshift : 0 < shift)
    (hm : symmetricMatrix a b c ∈ growthSet k) :
    ∃ (row : ℤ) (tiltX tiltY : ℝ) (height : Field), row ∈ Set.Icc 0 (k - 1) ∧
      tiltX ∈ Set.Icc 0 1 ∧ tiltY ∈ Set.Icc 0 1 ∧ Superharmonic k height ∧ height (0, row) = 0 ∧
      ∀ site, matrixQuadratic (symmetricMatrix (a - shift) b (c - shift)) (site - (0, row)) +
        (tiltX * ((site - (0, row)).1 : ℝ) + tiltY * ((site - (0, row)).2 : ℝ)) ≤ height site := by
  obtain ⟨field, hsuper, hgrowth⟩ := (symmetricMatrix_mem_growthSet_iff ..).mp hm
  let below := symmetricMatrix (a - shift) b (c - shift)
  let error (site : Site) := (field site : ℝ) - matrixQuadratic below site
  obtain ⟨radius, hradius, herror⟩ := hgrowth (shift / 4) (by positivity)
  have hlower (site : Site) (hsize : radius ^ 2 ≤ squaredSize site) :
      shift / 4 * squaredSize site ≤ error site := by
    have herr := (abs_le.mp (herror site hsize)).1
    obtain ⟨x, y⟩ := site
    simp only [matrixQuadratic_symmetricMatrix, error, below, squaredSize] at herr ⊢
    linarith only [herr]
  obtain ⟨minimizer, hmin⟩ := exists_min_of_quadratic_lower_bound hradius.le (by positivity) hlower
  let row := (minimizer.1 + minimizer.2) % k
  let anchor : Site := (0, row)
  let step := minimizer - anchor
  have hrow : row ∈ Set.Icc 0 (k - 1) :=
    ⟨Int.emod_nonneg _ (by omega), by have h := Int.emod_lt_of_pos (minimizer.1 + minimizer.2) (by omega : 0 < k); omega⟩
  have hphase : Retained k step := by
    change (minimizer.1 - 0 + (minimizer.2 - row)) % k = 0
    rw [show minimizer.1 - 0 + (minimizer.2 - row) = (minimizer.1 + minimizer.2) - row by ring]
    exact Int.dvd_iff_emod_eq_zero.mp Int.dvd_self_sub_emod
  let sx : ℝ := (a - shift) * (minimizer.1 : ℝ) + b * (minimizer.2 : ℝ)
  let sy : ℝ := b * (minimizer.1 : ℝ) + (c - shift) * (minimizer.2 : ℝ)
  let height : Field := fun site => field (site + step) - ⌊sx⌋ * (site - anchor).1 - ⌊sy⌋ * (site - anchor).2 - field minimizer
  have hheight : Superharmonic k height := by
    convert superharmonic_translate_sub_affine hsuper hphase ⌊sx⌋ ⌊sy⌋
      (field minimizer - ⌊sx⌋ * anchor.1 - ⌊sy⌋ * anchor.2) using 1
    funext site
    simp only [height, Prod.fst_sub, Prod.snd_sub]
    ring
  have hround (value : ℝ) : value - ⌊value⌋ ∈ Set.Icc 0 1 :=
    ⟨sub_nonneg.mpr (Int.floor_le _), by linarith only [Int.lt_floor_add_one value]⟩
  refine ⟨row, sx - ⌊sx⌋, sy - ⌊sy⌋, height, hrow, hround _, hround _, hheight, ?_, fun site => ?_⟩
  · change height anchor = 0
    have hanchor : anchor + step = minimizer := by dsimp [step]; abel
    rw [show height anchor = field (anchor + step) - ⌊sx⌋ * (anchor - anchor).1 -
      ⌊sy⌋ * (anchor - anchor).2 - field minimizer by rfl, hanchor, sub_self]
    simp
  · have hquad : matrixQuadratic below (site + step) - matrixQuadratic below minimizer =
        matrixQuadratic below (site - anchor) + sx * ((site - anchor).1 : ℝ) + sy * ((site - anchor).2 : ℝ) := by
      have heq : site + step = (site - anchor) + minimizer := by dsimp [step]; abel
      rw [heq]
      simp only [below, sx, sy]
      rw [matrixQuadratic_symmetricMatrix (x := ((site - anchor) + minimizer).1) (y := ((site - anchor) + minimizer).2),
        matrixQuadratic_symmetricMatrix (x := minimizer.1) (y := minimizer.2),
        matrixQuadratic_symmetricMatrix (x := (site - anchor).1) (y := (site - anchor).2)]
      simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
      ring
    have hm := hmin (site + step)
    simp only [error] at hm
    change matrixQuadratic below (site - anchor) +
      ((sx - ⌊sx⌋) * ((site - anchor).1 : ℝ) + (sy - ⌊sy⌋) * ((site - anchor).2 : ℝ)) ≤ (height site : ℝ)
    simp only [height, Int.cast_sub, Int.cast_mul]
    linarith only [hquad, hm]

private theorem tendsto_quadratic_of_entries {a b c : ℕ → ℝ} {a₀ b₀ c₀ : ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀)) (hc : Tendsto c atTop (𝓝 c₀))
    (site : Site) : Tendsto (fun n => matrixQuadratic (symmetricMatrix (a n) (b n) (c n)) site)
      atTop (𝓝 (matrixQuadratic (symmetricMatrix a₀ b₀ c₀) site)) := by
  obtain ⟨x, y⟩ := site
  simp_rw [matrixQuadratic_symmetricMatrix]
  exact (((ha.mul_const ((x : ℝ) ^ 2)).add ((hb.const_mul 2).mul_const (x : ℝ) |>.mul_const (y : ℝ))).add
    (hc.mul_const ((y : ℝ) ^ 2))).div_const 2

private theorem eventuallyEq_of_tendsto_int {sequence : ℕ → ℤ} {value : ℤ}
    (h : Tendsto sequence atTop (𝓝 value)) : ∀ᶠ n in atTop, sequence n = value := by
  exact h (mem_nhds_discrete.mpr (Set.mem_singleton value))

private theorem mem_growthSet_of_tendsto_entries {k : ℤ} (hk : 2 ≤ k) {a b c : ℕ → ℝ} {a₀ b₀ c₀ : ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀)) (hc : Tendsto c atTop (𝓝 c₀))
    (hadmit : ∀ n, symmetricMatrix (a n) (b n) (c n) ∈ growthSet k) :
    symmetricMatrix a₀ b₀ c₀ ∈ growthSet k := by
  let shift (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hshift : Tendsto shift atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose row tiltX tiltY height hrow htiltX htiltY hsuper hnormalize hlower using
    fun n => exists_normalized_lower_bound hk (show 0 < shift n by dsimp [shift]; positivity) (hadmit n)
  have hcompactRows : IsCompact (Set.Icc (0 : ℤ) (k - 1)) := isCompact_Icc
  obtain ⟨anchorRow, _, phaseIndex, hphaseIndex, hphase⟩ := hcompactRows.tendsto_subseq hrow
  obtain ⟨start, hstart⟩ := eventually_atTop.mp (eventuallyEq_of_tendsto_int hphase)
  let index (n : ℕ) := phaseIndex (n + start)
  have hindex : Tendsto index atTop atTop := hphaseIndex.tendsto_atTop.comp (tendsto_add_atTop_nat start)
  have hrowIndex (n : ℕ) : row (index n) = anchorRow := hstart _ (by omega)
  let anchor : Site := (0, anchorRow)
  let adjusted (n : ℕ) := symmetricMatrix (a (index n) - shift (index n)) (b (index n)) (c (index n) - shift (index n))
  have ha' : Tendsto (fun n => a (index n) - shift (index n)) atTop (𝓝 a₀) := by
    simpa only [Function.comp_apply, sub_zero] using (ha.comp hindex).sub (hshift.comp hindex)
  have hc' : Tendsto (fun n => c (index n) - shift (index n)) atTop (𝓝 c₀) := by
    simpa only [Function.comp_apply, sub_zero] using (hc.comp hindex).sub (hshift.comp hindex)
  have hquadratic (site : Site) : Tendsto (fun n => matrixQuadratic (adjusted n) site) atTop
      (𝓝 (matrixQuadratic (symmetricMatrix a₀ b₀ c₀) site)) :=
    tendsto_quadratic_of_entries ha' (hb.comp hindex) hc' site
  have hfLower (site : Site) (n : ℕ) : matrixQuadratic (adjusted n) (site - anchor) +
      (tiltX (index n) * ((site - anchor).1 : ℝ) + tiltY (index n) * ((site - anchor).2 : ℝ)) ≤ height (index n) site := by
    have h := hlower (index n) site
    rw [hrowIndex] at h
    exact h
  have hfBound (site : Site) : ∃ lower : ℤ, ∀ n, lower ≤ height (index n) site := by
    obtain ⟨lower, hlow⟩ := (hquadratic (site - anchor)).bddBelow_range
    let x : ℝ := (site - anchor).1
    let y : ℝ := (site - anchor).2
    refine ⟨⌊lower - |x| - |y|⌋, fun n => ?_⟩
    have hx : -|x| ≤ tiltX (index n) * x := by
      have habs : |tiltX (index n) * x| ≤ |x| := by
        rw [abs_mul, abs_of_nonneg (htiltX (index n)).1]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (htiltX (index n)).2 (abs_nonneg x)
      exact (neg_le_neg habs).trans (neg_abs_le _)
    have hy : -|y| ≤ tiltY (index n) * y := by
      have habs : |tiltY (index n) * y| ≤ |y| := by
        rw [abs_mul, abs_of_nonneg (htiltY (index n)).1]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (htiltY (index n)).2 (abs_nonneg y)
      exact (neg_le_neg habs).trans (neg_abs_le _)
    have hq := hlow (Set.mem_range_self n)
    have hh := hfLower site n
    change matrixQuadratic (adjusted n) (site - anchor) + (tiltX (index n) * x + tiltY (index n) * y) ≤
      (height (index n) site : ℝ) at hh
    exact_mod_cast (show (⌊lower - |x| - |y|⌋ : ℝ) ≤ height (index n) site by
      linarith only [Int.floor_le (lower - |x| - |y|), hx, hy, hq, hh])
  have hfUpper (site : Site) : ∃ upper : ℤ, ∀ n, height (index n) site ≤ upper := by
    apply (inputReaches_all hk anchor site).exists_uniform_upper_bound (fun n => hsuper (index n)) hfBound
    refine ⟨0, fun n => ?_⟩
    have h := hnormalize (index n)
    rw [hrowIndex] at h
    exact h.le
  choose lower hl using hfBound
  choose upper hu using hfUpper
  let fields : Set Field := Set.pi Set.univ (fun site => Set.Icc (lower site) (upper site))
  let slopes : Set (ℝ × ℝ) := Set.Icc 0 1 ×ˢ Set.Icc 0 1
  have hcompactFields : IsCompact fields := by
    have heq : fields = {f : Field | ∀ site, f site ∈ Set.Icc (lower site) (upper site)} := by
      ext f
      exact ⟨fun hf site => hf site (Set.mem_univ site), fun hf site _ => hf site⟩
    rw [heq]
    exact isCompact_pi_infinite fun _ => isCompact_Icc
  have hcompact : IsCompact (fields ×ˢ slopes) := hcompactFields.prod (isCompact_Icc.prod isCompact_Icc)
  let approximants (n : ℕ) := (height (index n), tiltX (index n), tiltY (index n))
  have hmem (n : ℕ) : approximants n ∈ fields ×ˢ slopes :=
    ⟨fun site _ => ⟨hl site n, hu site n⟩, htiltX (index n), htiltY (index n)⟩
  obtain ⟨⟨limit, tx, ty⟩, _, finalIndex, hfinalIndex, hlimit⟩ := hcompact.tendsto_subseq hmem
  rw [nhds_prod_eq] at hlimit
  have hlimitSlope := hlimit.snd
  rw [nhds_prod_eq] at hlimitSlope
  have hfields : Tendsto (fun n => height (index (finalIndex n))) atTop (𝓝 limit) := by
    simpa only [Function.comp_apply, approximants] using hlimit.fst
  have hx : Tendsto (fun n => tiltX (index (finalIndex n))) atTop (𝓝 tx) := by
    simpa only [Function.comp_apply, approximants] using hlimitSlope.fst
  have hy : Tendsto (fun n => tiltY (index (finalIndex n))) atTop (𝓝 ty) := by
    simpa only [Function.comp_apply, approximants] using hlimitSlope.snd
  have hpoint (site : Site) : ∀ᶠ n in atTop, height (index (finalIndex n)) site = limit site :=
    eventuallyEq_of_tendsto_int (tendsto_pi_nhds.mp hfields site)
  have hlimitSuper : Superharmonic k limit := by
    intro site
    obtain ⟨n, heq, hneg, hpos⟩ := ((hpoint site).and
      ((hpoint (incomingNeg k site)).and (hpoint (incomingPos k site)))).exists
    simpa only [laplacian, heq, hneg, hpos] using hsuper (index (finalIndex n)) site
  have hlimitLower (site : Site) : matrixQuadratic (symmetricMatrix a₀ b₀ c₀) (site - anchor) +
      (tx * ((site - anchor).1 : ℝ) + ty * ((site - anchor).2 : ℝ)) ≤ limit site := by
    apply le_of_tendsto_of_tendsto' (((hquadratic (site - anchor)).comp hfinalIndex.tendsto_atTop).add
      ((hx.mul_const ((site - anchor).1 : ℝ)).add (hy.mul_const ((site - anchor).2 : ℝ))))
    · exact tendsto_nhds_of_eventually_eq ((hpoint site).mono fun _ h => congrArg (fun x : ℤ => (x : ℝ)) h)
    · exact fun n => hfLower site (finalIndex n)
  refine mem_growthSet_of_affine_lower_bound hk hlimitSuper
    (tx - a₀ * (anchor.1 : ℝ) - b₀ * (anchor.2 : ℝ)) (ty - b₀ * (anchor.1 : ℝ) - c₀ * (anchor.2 : ℝ))
    (matrixQuadratic (symmetricMatrix a₀ b₀ c₀) anchor - (tx * (anchor.1 : ℝ) + ty * (anchor.2 : ℝ)))
    (fun site => ?_)
  refine le_trans (le_of_eq ?_) (hlimitLower site)
  rw [matrixQuadratic_symmetricMatrix (x := site.1) (y := site.2),
    matrixQuadratic_symmetricMatrix (x := anchor.1) (y := anchor.2),
    matrixQuadratic_symmetricMatrix (x := (site - anchor).1) (y := (site - anchor).2)]
  simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  ring

/-- The physical growth set of real matrices is closed. The normalization
uses a plane minimum, and the limiting height is taken in the discrete
compact product of the actual pointwise height ranges. -/
theorem isClosed_growthSet {k : ℤ} (hk : 2 ≤ k) : IsClosed (growthSet k) := by
  letI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → ℝ))
  apply isSeqClosed_iff_isClosed.mp
  intro matrices limit hmem hlimit
  have hentry (i j : Fin 2) : Tendsto (fun n => matrices n i j) atTop (𝓝 (limit i j)) :=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlimit i) j
  have hsymm : limit.IsSymm := by
    ext i j
    change limit j i = limit i j
    exact tendsto_nhds_unique (hentry j i)
      ((hentry i j).congr fun n => (hmem n).1.apply j i)
  rw [← symmetricMatrix_entries hsymm]
  exact mem_growthSet_of_tendsto_entries hk (hentry 0 0) (hentry 0 1) (hentry 1 1) fun n =>
    (symmetricMatrix_entries (hmem n).1).symm ▸ hmem n

/-- The same closedness theorem for the primary manuscript's physical graph. -/
theorem isClosed_growthSet_two : IsClosed {matrix : Matrix (Fin 2) (Fin 2) ℝ |
    matrix.IsSymm ∧ ∃ field : Field, FLatticePaper.Superharmonic field ∧ HasQuadraticGrowth field matrix} := by
  convert isClosed_growthSet (by decide : (2 : ℤ) ≤ 2) using 1
  ext matrix
  constructor
  · rintro ⟨hsymm, hfield⟩
    exact (mem_growthSet_two_iff hsymm).mpr hfield
  · intro h
    exact ⟨h.1, (mem_growthSet_two_iff h.1).mp h⟩

end FLatticePaper.GeneralK
