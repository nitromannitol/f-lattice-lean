import FLatticePaper.GeneralK.TightPeriodWalk
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace FLatticePaper.GeneralK

open Farey

/-- The period classes represented by the adjugate residue codes. -/
abbrev PeriodClasses (deck : PeriodDeck) := ↑(deck.residueSquare.image deck.classCode)

def periodClassAt (deck : PeriodDeck) (hdet : 0 < deck.det) (site : Site) : PeriodClasses deck :=
  ⟨deck.classCode site, by
    obtain ⟨point, hp, hcode⟩ := deck.exists_square_representative hdet site
    exact hcode.symm ▸ Finset.mem_image_of_mem deck.classCode hp
  ⟩

theorem periodClassAt_eq_iff {deck : PeriodDeck} (hdet : 0 < deck.det) (x y : Site) :
    periodClassAt deck hdet x = periodClassAt deck hdet y ↔ x - y ∈ deck.span := by
  rw [Subtype.ext_iff]
  exact deck.classCode_eq_iff hdet.ne' x y

theorem periodClassAt_add {deck : PeriodDeck} (hdet : 0 < deck.det) {step : Site} (hstep : step ∈ deck.span)
    (site : Site) : periodClassAt deck hdet (site + step) = periodClassAt deck hdet site := by
  apply (periodClassAt_eq_iff hdet _ _).mpr
  simpa [add_sub_cancel_left] using hstep

theorem periodClassAt_surjective (deck : PeriodDeck) (hdet : 0 < deck.det) :
    Function.Surjective (periodClassAt deck hdet) := by
  intro code
  obtain ⟨point, -, hcode⟩ := Finset.mem_image.mp code.property
  exact ⟨point, Subtype.ext hcode⟩

abbrev PotentialParameters (deck : PeriodDeck) := (ℝ × ℝ) × (PeriodClasses deck → ℝ)

/-- A physical height with two free real slope coordinates and one
periodic value per class. -/
def evaluatePotential {deck : PeriodDeck} (hdet : 0 < deck.det) (param : PotentialParameters deck) (site : Site) : ℝ :=
  param.1.1 * (site.1 : ℝ) + param.1.2 * (site.2 : ℝ) + param.2 (periodClassAt deck hdet site)

theorem continuous_evaluatePotential {deck : PeriodDeck} (hdet : 0 < deck.det) (site : Site) :
    Continuous (fun param : PotentialParameters deck => evaluatePotential hdet param site) := by
  unfold evaluatePotential
  exact ((continuous_fst.fst.mul continuous_const).add (continuous_fst.snd.mul continuous_const)).add
    ((continuous_apply _).comp continuous_snd)

theorem hasDeckSlope_evaluatePotential {deck : PeriodDeck} (hdet : 0 < deck.det) (param : PotentialParameters deck) :
    HasDeckSlope deck (evaluatePotential hdet param) param.1.1 param.1.2 := by
  intro step hstep site
  simp only [evaluatePotential, periodClassAt_add hdet hstep, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

/-- The finite-dimensional set of feasible potentials, normalized at the physical origin. -/
def feasiblePotentialParameters {deck : PeriodDeck} (hdet : 0 < deck.det) (k : ℤ) (negative positive : Field) :
    Set (PotentialParameters deck) :=
  {param | evaluatePotential hdet param 0 = 0 ∧ SatisfiesInputLabels k negative positive (evaluatePotential hdet param)}

theorem isClosed_feasiblePotentialParameters {deck : PeriodDeck} (hdet : 0 < deck.det) (k : ℤ)
    (negative positive : Field) : IsClosed (feasiblePotentialParameters hdet k negative positive) := by
  have heq : feasiblePotentialParameters hdet k negative positive =
      {param | evaluatePotential hdet param 0 = 0} ∩
        ⋂ site : Site, ({param | evaluatePotential hdet param (incomingNeg k site) - evaluatePotential hdet param site ≤
          (negative site : ℝ)} ∩ {param | evaluatePotential hdet param (incomingPos k site) -
            evaluatePotential hdet param site ≤ (positive site : ℝ)}) := by
    ext param
    simp [feasiblePotentialParameters, SatisfiesInputLabels]
  rw [heq]
  apply (isClosed_eq (continuous_evaluatePotential hdet _) continuous_const).inter
  apply isClosed_iInter
  intro site
  exact (isClosed_le ((continuous_evaluatePotential hdet _).sub (continuous_evaluatePotential hdet _)) continuous_const).inter
    (isClosed_le ((continuous_evaluatePotential hdet _).sub (continuous_evaluatePotential hdet _)) continuous_const)

theorem feasiblePotentialParameters_nonempty {deck : PeriodDeck} (hdet : 0 < deck.det) {k : ℤ}
    {negative positive : Field} {potential : Site → ℝ} {slopeX slopeY : ℝ}
    (hfeasible : SatisfiesInputLabels k negative positive potential)
    (hslope : HasDeckSlope deck potential slopeX slopeY) :
    (feasiblePotentialParameters hdet k negative positive).Nonempty := by
  classical
  let periodicPart (site : Site) := potential site - potential 0 - (slopeX * (site.1 : ℝ) + slopeY * (site.2 : ℝ))
  have hperiod (step : Site) (hstep : step ∈ deck.span) (site : Site) : periodicPart (site + step) = periodicPart site := by
    simp only [periodicPart, hslope step hstep, Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring
  choose representative hrep using periodClassAt_surjective deck hdet
  let param : PotentialParameters deck := ((slopeX, slopeY), fun code => periodicPart (representative code))
  have hpart (site : Site) : periodicPart (representative (periodClassAt deck hdet site)) = periodicPart site := by
    let point := representative (periodClassAt deck hdet site)
    have hspan : point - site ∈ deck.span := (periodClassAt_eq_iff hdet _ _).mp (hrep _)
    have h := hperiod (point - site) hspan site
    simpa only [add_comm site (point - site), sub_add_cancel] using h
  have hval (site : Site) : evaluatePotential hdet param site = potential site - potential 0 := by
    simp only [evaluatePotential, param, hpart, periodicPart]
    ring
  refine ⟨param, ?_⟩
  change evaluatePotential hdet param 0 = 0 ∧ SatisfiesInputLabels k negative positive (evaluatePotential hdet param)
  refine ⟨by rw [hval, sub_self], fun site => ?_⟩
  simp only [hval]
  exact ⟨by linarith only [(hfeasible site).1], by linarith only [(hfeasible site).2]⟩

private theorem InputReaches.exists_inputLabel_bound {k : ℤ} {first last : Site}
    (hpath : InputReaches k first last) (negative positive : Field) :
    ∃ bound : ℝ, ∀ potential : Site → ℝ, SatisfiesInputLabels k negative positive potential →
      potential last - potential first ≤ bound := by
  induction hpath with
  | refl => exact ⟨0, fun _ _ => by simp⟩
  | @tail center input _ edge ih =>
    obtain ⟨bound, hb⟩ := ih
    refine ⟨bound + max (negative center : ℝ) (positive center : ℝ), fun potential hp => ?_⟩
    have hstep : potential input - potential center ≤ max (negative center : ℝ) (positive center : ℝ) := by
      rcases edge with rfl | rfl
      · exact (hp center).1.trans (le_max_left ..)
      · exact (hp center).2.trans (le_max_right ..)
    linarith only [hstep, hb potential hp]

/-- Connectivity bounds the value at each fixed physical site uniformly over the normalized feasible set. -/
theorem exists_evaluatePotential_bound {deck : PeriodDeck} (hdet : 0 < deck.det) {k : ℤ} (hk : 2 ≤ k)
    (negative positive : Field) (site : Site) : ∃ bound : ℝ, ∀ param ∈ feasiblePotentialParameters hdet k negative positive,
      |evaluatePotential hdet param site| ≤ bound := by
  obtain ⟨upper, hu⟩ := (inputReaches_all hk 0 site).exists_inputLabel_bound negative positive
  obtain ⟨lower, hl⟩ := (inputReaches_all hk site 0).exists_inputLabel_bound negative positive
  refine ⟨max lower upper, fun param hparam => ?_⟩
  have hzero : evaluatePotential hdet param 0 = 0 := hparam.1
  have hhigh := hu _ hparam.2
  have hlow := hl _ hparam.2
  rw [hzero, sub_zero] at hhigh
  rw [hzero, zero_sub] at hlow
  apply abs_le.mpr
  exact ⟨neg_le.mp (hlow.trans (le_max_left ..)), hhigh.trans (le_max_right ..)⟩

/-- Physical paths to the two determinant-axis periods bound the slopes.
Paths to one representative per period class bound the remaining coordinates. -/
theorem isCompact_feasiblePotentialParameters {deck : PeriodDeck} (hdet : 0 < deck.det) {k : ℤ} (hk : 2 ≤ k)
    (negative positive : Field) : IsCompact (feasiblePotentialParameters hdet k negative positive) := by
  classical
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_feasiblePotentialParameters hdet k negative positive)
  apply isBounded_iff_forall_norm_le.mpr
  have hX : (deck.det, 0) ∈ deck.span := by
    apply (deck.mem_span_iff_dvd hdet.ne' _).mpr
    simp [PeriodDeck.kernelNumerator, PeriodDeck.transverseNumerator, dvd_mul_left]
  have hY : (0, deck.det) ∈ deck.span := by
    apply (deck.mem_span_iff_dvd hdet.ne' _).mpr
    simp [PeriodDeck.kernelNumerator, PeriodDeck.transverseNumerator, dvd_mul_left]
  have hdpos : 0 < (deck.det : ℝ) := by exact_mod_cast hdet
  obtain ⟨boundX, hboundX⟩ := exists_evaluatePotential_bound hdet hk negative positive (deck.det, 0)
  obtain ⟨boundY, hboundY⟩ := exists_evaluatePotential_bound hdet hk negative positive (0, deck.det)
  let slopeBound := max 0 (max boundX boundY) / (deck.det : ℝ)
  have hnonneg : 0 ≤ slopeBound := div_nonneg (le_max_left ..) hdpos.le
  have hslopes (param : PotentialParameters deck) (hparam : param ∈ feasiblePotentialParameters hdet k negative positive) :
      |param.1.1| ≤ slopeBound ∧ |param.1.2| ≤ slopeBound := by
    have hzero : evaluatePotential hdet param 0 = 0 := hparam.1
    have hx := hasDeckSlope_evaluatePotential hdet param (deck.det, 0) hX 0
    have hy := hasDeckSlope_evaluatePotential hdet param (0, deck.det) hY 0
    rw [hzero] at hx hy
    simp only [zero_add, Int.cast_zero, mul_zero, add_zero] at hx hy
    have hbX := hboundX _ hparam
    have hbY := hboundY _ hparam
    rw [hx, abs_mul, abs_of_pos hdpos] at hbX
    rw [hy, abs_mul, abs_of_pos hdpos] at hbY
    exact ⟨(le_div_iff₀ hdpos).mpr (hbX.trans ((le_max_left ..).trans (le_max_right ..))),
      (le_div_iff₀ hdpos).mpr (hbY.trans ((le_max_right ..).trans (le_max_right ..)))⟩
  choose point hpoint using periodClassAt_surjective deck hdet
  choose bound hbound using fun code : PeriodClasses deck =>
    exists_evaluatePotential_bound hdet hk negative positive (point code)
  let classBound (code : PeriodClasses deck) : ℝ := |bound code| +
    slopeBound * (|((point code).1 : ℝ)| + |((point code).2 : ℝ)|)
  have hclassNonneg (code : PeriodClasses deck) : 0 ≤ classBound code := by
    dsimp only [classBound]
    positivity
  let total := slopeBound + ∑ code, classBound code
  have hslopeTotal : slopeBound ≤ total := by dsimp [total]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun c _ => hclassNonneg c)
  have hclassTotal (code : PeriodClasses deck) : classBound code ≤ total := by
    exact (Finset.single_le_sum (fun c _ => hclassNonneg c) (Finset.mem_univ code)).trans
      (le_add_of_nonneg_left hnonneg)
  refine ⟨total, fun param hparam => ?_⟩
  obtain ⟨hx, hy⟩ := hslopes param hparam
  rw [Prod.norm_def, Prod.norm_def]
  apply max_le (max_le (by rw [Real.norm_eq_abs]; exact hx.trans hslopeTotal)
    (by rw [Real.norm_eq_abs]; exact hy.trans hslopeTotal))
  apply (pi_norm_le_iff_of_nonneg (hnonneg.trans hslopeTotal)).mpr
  intro code
  rw [Real.norm_eq_abs]
  have hval : param.2 code = evaluatePotential hdet param (point code) -
      (param.1.1 * ((point code).1 : ℝ) + param.1.2 * ((point code).2 : ℝ)) := by
    simp only [evaluatePotential, hpoint code]
    ring
  apply le_trans _ (hclassTotal code)
  rw [hval]
  calc
    _ ≤ |evaluatePotential hdet param (point code)| +
        |param.1.1 * ((point code).1 : ℝ) + param.1.2 * ((point code).2 : ℝ)| := abs_sub _ _
    _ ≤ classBound code := by
      unfold classBound
      apply add_le_add ((hbound code param hparam).trans (le_abs_self _))
      apply (abs_add_le ..).trans
      rw [abs_mul, abs_mul, mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right hx (abs_nonneg _)) (mul_le_mul_of_nonneg_right hy (abs_nonneg _))

end FLatticePaper.GeneralK
