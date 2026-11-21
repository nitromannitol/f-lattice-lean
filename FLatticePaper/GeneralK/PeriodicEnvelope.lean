import FLatticePaper.GeneralK.GrowthClosed

namespace FLatticePaper.GeneralK

open Farey

private theorem span_add {deck : PeriodDeck} {first second : Site}
    (hfirst : first ∈ deck.span) (hsecond : second ∈ deck.span) : first + second ∈ deck.span := by
  obtain ⟨i, j, rfl⟩ := hfirst
  obtain ⟨i', j', rfl⟩ := hsecond
  refine ⟨i + i', j + j', ?_⟩
  apply Prod.ext <;> (simp only [PeriodDeck.combine, Prod.fst_add, Prod.snd_add]; ring)

private theorem span_neg {deck : PeriodDeck} {step : Site} (hstep : step ∈ deck.span) : -step ∈ deck.span := by
  obtain ⟨i, j, rfl⟩ := hstep
  refine ⟨-i, -j, ?_⟩
  apply Prod.ext <;> (simp only [PeriodDeck.combine, Prod.fst_neg, Prod.snd_neg]; ring)

/-- The fractional envelope of all translates has exact real affine
increments. Every common rounding parameter gives an integer superharmonic
height by the attained minimum over the true physical translates. -/
theorem exists_roundedEnvelope {k : ℤ} {deck : PeriodDeck} {reference height : Field}
    (hphase : ∀ step ∈ deck.span, Retained k step)
    (hperiod : ∀ step ∈ deck.span, ∃ slopeX slopeY constant : ℤ, ∀ site,
      reference (site + step) = reference site + slopeX * site.1 + slopeY * site.2 + constant)
    (hheight : Superharmonic k height) (tiltX tiltY lower : ℝ)
    (hlower : ∀ site, (reference site : ℝ) + (tiltX * (site.1 : ℝ) + tiltY * (site.2 : ℝ)) + lower ≤ height site) :
    ∃ envelope : Site → ℝ,
      (∀ step ∈ deck.span, ∀ site,
        envelope (site + step) = envelope site + (tiltX * (step.1 : ℝ) + tiltY * (step.2 : ℝ))) ∧
      ∀ offset : ℝ, Superharmonic k (fun site => reference site + ⌊envelope site + offset⌋) := by
  let tilt (site : Site) := tiltX * (site.1 : ℝ) + tiltY * (site.2 : ℝ)
  let steps := {step : Site // step ∈ deck.span}
  letI : Nonempty steps := ⟨⟨0, 0, 0, by ext <;> simp [PeriodDeck.combine]⟩⟩
  let value (site : Site) (step : steps) : ℝ := ((height (site + step.val) - reference (site + step.val) : ℤ) : ℝ) -
    tilt step.val
  let envelope (site : Site) := sInf (Set.range (value site))
  have htilt (first second : Site) : tilt (first + second) = tilt first + tilt second := by
    simp only [tilt, Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring
  have hbound (site : Site) : BddBelow (Set.range (value site)) := by
    refine ⟨tilt site + lower, ?_⟩
    rintro _ ⟨step, rfl⟩
    have h := hlower (site + step.val)
    change (reference (site + step.val) : ℝ) + tilt (site + step.val) + lower ≤ _ at h
    rw [htilt] at h
    simp only [value, Int.cast_sub]
    linarith only [h]
  have htiltPeriod (step : Site) (hstep : step ∈ deck.span) (site : Site) :
      envelope (site + step) = envelope site + tilt step := by
    have htrans (t : steps) : value (site + step) t = value site ⟨step + t.val, span_add hstep t.property⟩ + tilt step := by
      simp only [value, add_assoc, htilt]
      ring
    apply le_antisymm
    · apply sub_le_iff_le_add.mp
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨t, rfl⟩
      let inverse : steps := ⟨-step + t.val, span_add (span_neg hstep) t.property⟩
      have h := csInf_le (hbound (site + step)) (Set.mem_range_self inverse)
      rw [htrans] at h
      have heq : (⟨step + inverse.val, span_add hstep inverse.property⟩ : steps) = t := by
        apply Subtype.ext
        change step + (-step + t.val) = t.val
        abel
      rw [heq] at h
      linarith only [h]
    · apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨t, rfl⟩
      rw [htrans]
      exact add_le_add_left (csInf_le (hbound site) (Set.mem_range_self _)) _
  refine ⟨envelope, htiltPeriod, fun offset => ?_⟩
  let rounded : Field := fun site => reference site + ⌊envelope site + offset⌋
  let translated (step : steps) : Field := fun site => height (site + step.val) -
    (reference (site + step.val) - reference site) + ⌊offset - tilt step.val⌋
  have hformula (step : steps) (site : Site) : translated step site = reference site + ⌊value site step + offset⌋ := by
    have heq : value site step + offset = (offset - tilt step.val) +
        ((height (site + step.val) - reference (site + step.val) : ℤ) : ℝ) := by unfold value; ring
    simp only [translated, heq, Int.floor_add_intCast]
    ring
  have hsuper (step : steps) : Superharmonic k (translated step) := by
    obtain ⟨slopeX, slopeY, constant, hjet⟩ := hperiod step.val step.property
    convert superharmonic_translate_sub_affine hheight (hphase step.val step.property) slopeX slopeY
      (constant - ⌊offset - tilt step.val⌋) using 1
    funext site
    simp only [translated, hjet]
    ring
  have hmin (site : Site) (step : steps) : rounded site ≤ translated step site := by
    rw [hformula]
    apply add_le_add_right
    apply Int.floor_mono
    exact add_le_add_left (csInf_le (hbound site) (Set.mem_range_self step)) _
  have hnear (site : Site) : ∃ step : steps, translated step site = rounded site := by
    have hb : envelope site < ((⌊envelope site + offset⌋ : ℤ) : ℝ) + 1 - offset := by
      have h := Int.lt_floor_add_one (envelope site + offset)
      linarith only [h]
    obtain ⟨_, ⟨step, rfl⟩, hstep⟩ := exists_lt_of_csInf_lt (Set.range_nonempty (value site)) hb
    refine ⟨step, ?_⟩
    rw [hformula]
    change reference site + ⌊value site step + offset⌋ = reference site + ⌊envelope site + offset⌋
    congr 1
    apply Int.floor_eq_iff.mpr
    have hlow := (Int.floor_le (envelope site + offset)).trans
      (add_le_add_left (csInf_le (hbound site) (Set.mem_range_self step)) offset)
    exact ⟨hlow, by linarith only [hstep]⟩
  intro site
  obtain ⟨step, heq⟩ := hnear site
  have hn := hmin (incomingNeg k site) step
  have hp := hmin (incomingPos k site) step
  have h := hsuper step site
  change laplacian k rounded site ≤ 0
  simp only [laplacian] at h ⊢
  omega

/-- Choosing a single offset that simultaneously attains both ceilings
gives the true integer label bound at each physical incoming star. -/
theorem ceilEnvelope_input_sum_le {k : ℤ} {reference : Field} {envelope : Site → ℝ}
    (hsuper : ∀ offset : ℝ, Superharmonic k (fun site => reference site + ⌊envelope site + offset⌋))
    (site : Site) : ⌈envelope (incomingNeg k site) - envelope site⌉ +
      ⌈envelope (incomingPos k site) - envelope site⌉ ≤ -laplacian k reference site := by
  let dn := envelope (incomingNeg k site) - envelope site
  let dp := envelope (incomingPos k site) - envelope site
  let fraction := max ((⌈dn⌉ : ℝ) - dn) ((⌈dp⌉ : ℝ) - dp)
  have hf₀ : 0 ≤ fraction := (sub_nonneg.mpr (Int.le_ceil dn)).trans (le_max_left ..)
  have hf₁ : fraction < 1 := max_lt (by linarith only [Int.ceil_lt_add_one dn]) (by linarith only [Int.ceil_lt_add_one dp])
  let offset := fraction - envelope site
  have hcenter : ⌊envelope site + offset⌋ = 0 := by
    rw [show envelope site + offset = fraction by dsimp [offset]; ring]
    exact Int.floor_eq_zero_iff.mpr ⟨hf₀, hf₁⟩
  have hn : ⌊envelope (incomingNeg k site) + offset⌋ = ⌈dn⌉ := by
    rw [Int.floor_eq_iff]
    have hfrac : (⌈dn⌉ : ℝ) - dn ≤ fraction := le_max_left ..
    have hceil := Int.le_ceil dn
    dsimp only [offset, dn] at hfrac hceil ⊢
    constructor <;> linarith only [hfrac, hceil, hf₁]
  have hp : ⌊envelope (incomingPos k site) + offset⌋ = ⌈dp⌉ := by
    rw [Int.floor_eq_iff]
    have hfrac : (⌈dp⌉ : ℝ) - dp ≤ fraction := le_max_right ..
    have hceil := Int.le_ceil dp
    dsimp only [offset, dp] at hfrac hceil ⊢
    constructor <;> linarith only [hfrac, hceil, hf₁]
  have h := hsuper offset site
  simp only [laplacian, hcenter, hn, hp, add_zero] at h
  unfold laplacian
  change ⌈dn⌉ + ⌈dp⌉ ≤ _
  omega

end FLatticePaper.GeneralK
