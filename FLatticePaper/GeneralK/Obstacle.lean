import FLatticePaper.GeneralK.Envelope
import FLatticePaper.GeneralK.Trace

namespace FLatticePaper.GeneralK

/-- The obstacle is majorized pointwise by the least integer superharmonic height. -/
structure IsLeastMajorant (k : ℤ) (obstacle height : Field) : Prop where
  superharmonic : Superharmonic k height
  majorizes : ∀ site, obstacle site ≤ height site
  least : ∀ field : Field, Superharmonic k field → (∀ site, obstacle site ≤ field site) → ∀ site, height site ≤ field site

theorem exists_leastMajorant {k : ℤ} (obstacle : Field) (field : Field) (hfield : Superharmonic k field)
    (hdom : ∀ site, obstacle site ≤ field site) : ∃ height, IsLeastMajorant k obstacle height := by
  let family := {f : Field // Superharmonic k f ∧ ∀ site, obstacle site ≤ f site}
  letI : Nonempty family := ⟨⟨field, hfield, hdom⟩⟩
  obtain ⟨height, hsuper, hmin⟩ := exists_superharmonic_min (fun f : family => f.val)
    (fun f => f.property.1) (fun site => ⟨obstacle site, fun f => f.property.2 site⟩)
  refine ⟨height, hsuper, fun site => ?_, fun f hf hfdom site => (hmin site).1 ⟨f, hf, hfdom⟩⟩
  obtain ⟨f, heq⟩ := (hmin site).2
  exact heq ▸ f.property.2 site

private theorem retained_neg {k : ℤ} {site : Site} (h : Retained k site) : Retained k (-site) := by
  change (site.1 + site.2) % k = 0 at h
  change (-site.1 + -site.2) % k = 0
  rw [← neg_add]
  exact Int.dvd_iff_emod_eq_zero.mp (dvd_neg.mpr (Int.dvd_iff_emod_eq_zero.mpr h))

/-- An integer affine increment of an obstacle under a phase-preserving
shift is inherited by its least majorant. -/
theorem IsLeastMajorant.add_period {k : ℤ} {obstacle height : Field} (h : IsLeastMajorant k obstacle height)
    {step : Site} (hphase : Retained k step) (slopeX slopeY constant : ℤ)
    (hperiod : ∀ site, obstacle (site + step) = obstacle site + slopeX * site.1 + slopeY * site.2 + constant)
    (site : Site) : height (site + step) = height site + slopeX * site.1 + slopeY * site.2 + constant := by
  let rotated : Field := fun site => height (site + step) - slopeX * site.1 - slopeY * site.2 - constant
  have hforward : height site ≤ rotated site := h.least rotated
    (superharmonic_translate_sub_affine h.superharmonic hphase slopeX slopeY constant) (fun p => by
      have hdom := h.majorizes (p + step)
      rw [hperiod] at hdom
      dsimp [rotated]
      omega) site
  let reversed : Field := fun p => height (p + -step) - (-slopeX) * p.1 - (-slopeY) * p.2 -
    (slopeX * step.1 + slopeY * step.2 - constant)
  have hreverse : height (site + step) ≤ reversed (site + step) := h.least reversed
    (superharmonic_translate_sub_affine h.superharmonic (retained_neg hphase) (-slopeX) (-slopeY)
      (slopeX * step.1 + slopeY * step.2 - constant)) (fun p => by
      have hdom := h.majorizes (p + -step)
      have hp := hperiod (p + -step)
      rw [neg_add_cancel_right] at hp
      dsimp only [reversed]
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at hp
      linarith only [hdom, hp]) (site + step)
  dsimp only [rotated] at hforward
  simp only [reversed, show site + step + -step = site by abel, Prod.fst_add, Prod.snd_add] at hreverse
  exact le_antisymm (by linarith only [hreverse]) (by linarith only [hforward])

private theorem incomingNeg_ne (k : ℤ) (site : Site) : incomingNeg k site ≠ site := by
  obtain ⟨x, y⟩ := site
  by_cases h : Retained k (x, y) <;> simp [incomingNeg, h]

private theorem incomingPos_ne (k : ℤ) (site : Site) : incomingPos k site ≠ site := by
  obtain ⟨x, y⟩ := site
  by_cases h : Retained k (x, y) <;> simp [incomingPos, h]

theorem IsLeastMajorant.charge_le_one_of_obstacle_lt {k : ℤ} {obstacle height : Field}
    (h : IsLeastMajorant k obstacle height) (site : Site) (hcontact : obstacle site < height site) :
    -laplacian k height site ≤ 1 := by
  by_contra! hbad
  let lowered : Field := fun point => if point = site then height point - 1 else height point
  have hle (point : Site) : lowered point ≤ height point := by
    dsimp [lowered]
    split <;> omega
  have hdom (point : Site) : obstacle point ≤ lowered point := by
    by_cases hp : point = site
    · subst point
      simp only [lowered, if_pos rfl]
      omega
    · simpa only [lowered, if_neg hp] using h.majorizes point
  have hsuper (point : Site) : laplacian k lowered point ≤ 0 := by
    by_cases hp : point = site
    · subst point
      simp only [laplacian, lowered, if_pos rfl, if_neg (incomingNeg_ne k site), if_neg (incomingPos_ne k site)]
      unfold laplacian at hbad
      omega
    · have hrow := h.superharmonic point
      have hn := hle (incomingNeg k point)
      have hpos := hle (incomingPos k point)
      simp only [laplacian] at hrow ⊢
      have heq : lowered point = height point := if_neg hp
      omega
  have hmin := h.least lowered hsuper hdom site
  simp only [lowered, if_pos rfl] at hmin
  omega

theorem IsLeastMajorant.charge_le_obstacle_of_contact {k : ℤ} {obstacle height : Field}
    (h : IsLeastMajorant k obstacle height) (site : Site) (hcontact : obstacle site = height site) :
    -laplacian k height site ≤ -laplacian k obstacle site := by
  have hneg := h.majorizes (incomingNeg k site)
  have hpos := h.majorizes (incomingPos k site)
  unfold laplacian
  omega

/-- The precise quadratic ceiling obstacle used in the rational upper bound. -/
noncomputable def ceilingObstacle (a b c slopeX slopeY : ℝ) : Field := fun site =>
  ⌈matrixQuadratic (symmetricMatrix a b c) site + (slopeX * (site.1 : ℝ) + slopeY * (site.2 : ℝ))⌉

theorem IsLeastMajorant.chargeBound {k : ℤ} {a b c a₀ slopeX slopeY : ℝ} {height : Field}
    (h : IsLeastMajorant k (ceilingObstacle a b c slopeX slopeY) height) (hfirst : a₀ ≤ a) (site : Site) :
    0 ≤ -laplacian k height site ∧ -laplacian k height site ≤ max 1 ⌈2 - min a₀ c⌉ := by
  refine ⟨neg_nonneg.mpr (h.superharmonic site), ?_⟩
  by_cases hc : ceilingObstacle a b c slopeX slopeY site = height site
  · apply (h.charge_le_obstacle_of_contact site hc).trans
    let q (site : Site) := matrixQuadratic (symmetricMatrix a b c) site + (slopeX * (site.1 : ℝ) + slopeY * (site.2 : ℝ))
    have hrow : realLaplacian k q site = if Retained k site then a else c := by
      rw [← realLaplacian_matrixQuadratic]
      unfold q realLaplacian
      by_cases ht : Retained k site <;> simp [incomingNeg, incomingPos, ht] <;> ring
    have hmin : min a₀ c ≤ realLaplacian k q site := by
      rw [hrow]
      split
      · exact (min_le_left ..).trans hfirst
      · exact min_le_right ..
    have hneg := Int.le_ceil (q (incomingNeg k site))
    have hpos := Int.le_ceil (q (incomingPos k site))
    have hcenter := Int.ceil_lt_add_one (q site)
    have hcharge : ((-laplacian k (ceilingObstacle a b c slopeX slopeY) site : ℤ) : ℝ) ≤ 2 - min a₀ c := by
      simp only [realLaplacian] at hmin
      simp only [laplacian, Int.cast_neg, Int.cast_add, Int.cast_sub]
      change -(((⌈q (incomingNeg k site)⌉ : ℤ) : ℝ) - ((⌈q site⌉ : ℤ) : ℝ) +
        (((⌈q (incomingPos k site)⌉ : ℤ) : ℝ) - ((⌈q site⌉ : ℤ) : ℝ))) ≤ _
      linarith only [hmin, hneg, hpos, hcenter]
    have hceil := hcharge.trans (Int.le_ceil (2 - min a₀ c))
    exact (by exact_mod_cast hceil : -laplacian k (ceilingObstacle a b c slopeX slopeY) site ≤ ⌈2 - min a₀ c⌉).trans
      (le_max_right ..)
  · exact (h.charge_le_one_of_obstacle_lt site (lt_of_le_of_ne (h.majorizes site) hc)).trans (le_max_left ..)

end FLatticePaper.GeneralK
