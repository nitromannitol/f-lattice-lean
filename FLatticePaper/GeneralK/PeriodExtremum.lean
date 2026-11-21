import FLatticePaper.GeneralK.PeriodQuotient

namespace FLatticePaper.GeneralK

open Farey

/-- Read one physical input slot. -/
def inputAt (k : ℤ) (positive : Bool) (site : Site) : Site :=
  if positive then incomingPos k site else incomingNeg k site

theorem inputAt_add_of_retained {k : ℤ} {step : Site} (hstep : Retained k step) (positive : Bool) (site : Site) :
    inputAt k positive (site + step) = inputAt k positive site + step := by
  cases positive <;> simp only [inputAt, Bool.false_eq_true, if_false, if_true, incomingNeg, incomingPos, retained_add_iff hstep]
  all_goals split <;> (apply Prod.ext <;> (simp; all_goals omega))

def inputDifference {deck : PeriodDeck} (hdet : 0 < deck.det) (k : ℤ) (param : PotentialParameters deck)
    (site : Site) (positive : Bool) : ℝ := evaluatePotential hdet param (inputAt k positive site) - evaluatePotential hdet param site

theorem inputDifference_add_period {deck : PeriodDeck} (hdet : 0 < deck.det) (k : ℤ) (param : PotentialParameters deck)
    {step : Site} (hspan : step ∈ deck.span) (hretained : Retained k step) (site : Site) (positive : Bool) :
    inputDifference hdet k param (site + step) positive = inputDifference hdet k param site positive := by
  simp only [inputDifference, inputAt_add_of_retained hretained, hasDeckSlope_evaluatePotential hdet param step hspan]
  ring

private theorem evaluatePotential_add_smul {deck : PeriodDeck} (hdet : 0 < deck.det)
    (param direction : PotentialParameters deck) (t : ℝ) (site : Site) :
    evaluatePotential hdet (param + t • direction) site =
      evaluatePotential hdet param site + t * evaluatePotential hdet direction site := by
  simp [evaluatePotential, smul_eq_mul]
  ring

private theorem inputDifference_add_smul {deck : PeriodDeck} (hdet : 0 < deck.det) (k : ℤ)
    (param direction : PotentialParameters deck) (t : ℝ) (site : Site) (positive : Bool) :
    inputDifference hdet k (param + t • direction) site positive = inputDifference hdet k param site positive +
      t * inputDifference hdet k direction site positive := by
  simp only [inputDifference, evaluatePotential_add_smul]
  ring

private noncomputable def energy {deck : PeriodDeck} (param : PotentialParameters deck) : ℝ :=
  param.1.1 ^ 2 + param.1.2 ^ 2 + ∑ code, (param.2 code) ^ 2

private theorem continuous_energy (deck : PeriodDeck) : Continuous (energy (deck := deck)) := by
  unfold energy
  apply ((continuous_fst.fst.pow 2).add (continuous_fst.snd.pow 2)).add
  exact continuous_finsetSum _ fun code _ => ((continuous_apply code).comp continuous_snd).pow 2

private theorem energy_pos_of_ne_zero {deck : PeriodDeck} {param : PotentialParameters deck} (h : param ≠ 0) :
    0 < energy param := by
  have hsum : 0 ≤ ∑ code : PeriodClasses deck, (param.2 code) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_contra! hzero
  simp only [energy] at hzero
  have hx : param.1.1 = 0 := by
    nlinarith only [hzero, hsum, sq_nonneg param.1.2]
  have hy : param.1.2 = 0 := by
    nlinarith only [hzero, hsum, sq_nonneg param.1.1]
  apply h
  apply Prod.ext (Prod.ext hx hy)
  funext code
  have hc : (param.2 code) ^ 2 ≤ ∑ code : PeriodClasses deck, (param.2 code) ^ 2 :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ code)
  change param.2 code = 0
  nlinarith only [hzero, hc, sq_nonneg param.1.1, sq_nonneg param.1.2]

private theorem energy_add_pair {deck : PeriodDeck} (param direction : PotentialParameters deck) (t : ℝ) :
    energy (param + t • direction) + energy (param + (-t) • direction) =
      2 * energy param + 2 * t ^ 2 * energy direction := by
  change ((param.1.1 + t * direction.1.1) ^ 2 + (param.1.2 + t * direction.1.2) ^ 2 +
      ∑ code : PeriodClasses deck, (param.2 code + t * direction.2 code) ^ 2) +
    ((param.1.1 + (-t) * direction.1.1) ^ 2 + (param.1.2 + (-t) * direction.1.2) ^ 2 +
      ∑ code : PeriodClasses deck, (param.2 code + (-t) * direction.2 code) ^ 2) =
    2 * (param.1.1 ^ 2 + param.1.2 ^ 2 + ∑ code : PeriodClasses deck, (param.2 code) ^ 2) +
      2 * t ^ 2 * (direction.1.1 ^ 2 + direction.1.2 ^ 2 + ∑ code : PeriodClasses deck, (direction.2 code) ^ 2)
  have h : (∑ code : PeriodClasses deck, (param.2 code + t * direction.2 code) ^ 2) +
      (∑ code : PeriodClasses deck, (param.2 code + -t * direction.2 code) ^ 2) =
      2 * (∑ code : PeriodClasses deck, (param.2 code) ^ 2) + 2 * t ^ 2 * ∑ code : PeriodClasses deck, (direction.2 code) ^ 2 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro code _
    ring
  linear_combination h

/-- A feasible extremizer on the physical quotient admits no nonzero
normalized perturbation that preserves all its tight edge differences. -/
theorem exists_feasible_extremum {deck : PeriodDeck} (hdet : 0 < deck.det) {k : ℤ} (hk : 2 ≤ k)
    (hphase : ∀ step ∈ deck.span, Retained k step) (negative positive : Field)
    (hneg : ∀ step ∈ deck.span, Function.Periodic negative step)
    (hpos : ∀ step ∈ deck.span, Function.Periodic positive step)
    (hne : (feasiblePotentialParameters hdet k negative positive).Nonempty) :
    ∃ param ∈ feasiblePotentialParameters hdet k negative positive, ∀ direction : PotentialParameters deck,
      evaluatePotential hdet direction 0 = 0 →
      (∀ site sign, inputDifference hdet k param site sign = (if sign then positive site else negative site : ℤ) →
        inputDifference hdet k direction site sign = 0) → direction = 0 := by
  classical
  obtain ⟨param, hparam, hmax⟩ := (isCompact_feasiblePotentialParameters hdet hk negative positive).exists_isMaxOn
    hne (continuous_energy deck).continuousOn
  refine ⟨param, hparam, fun direction hzero htight => ?_⟩
  by_contra hdir
  let label (site : Site) (sign : Bool) : ℝ := (if sign then positive site else negative site : ℤ)
  let row := inputDifference hdet k param
  let δ := inputDifference hdet k direction
  have hrow (site : Site) (sign : Bool) : row site sign ≤ label site sign := by
    cases sign
    · exact (hparam.2 site).1
    · exact (hparam.2 site).2
  let allowance (site : Site) (sign : Bool) : ℝ :=
    if row site sign = label site sign then 1 else (label site sign - row site sign) / (|δ site sign| + 1)
  have hallPositive (site : Site) (sign : Bool) : 0 < allowance site sign := by
    unfold allowance
    split
    · exact zero_lt_one
    · rename_i h
      exact div_pos (sub_pos.mpr (lt_of_le_of_ne (hrow site sign) h)) (by positivity)
  let tests := deck.residueSquare.product (Finset.univ : Finset Bool)
  have h0 : (0 : Site) ∈ deck.residueSquare := by
    exact Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨le_rfl, hdet⟩, Finset.mem_Ico.mpr ⟨le_rfl, hdet⟩⟩
  have htests : tests.Nonempty := ⟨(0, false), Finset.mem_product.mpr ⟨h0, Finset.mem_univ _⟩⟩
  obtain ⟨point, -, hmin⟩ := tests.exists_min_image (fun point => allowance point.1 point.2) htests
  let ε := allowance point.1 point.2
  have hε : 0 < ε := hallPositive ..
  have hall (site : Site) (sign : Bool) : ε ≤ allowance site sign := by
    obtain ⟨center, hc, hcode⟩ := deck.exists_square_representative hdet site
    let shift := site - center
    have hspan : shift ∈ deck.span := (deck.classCode_eq_iff hdet.ne' _ _).mp hcode
    have hsite : center + shift = site := by dsimp only [shift]; abel
    have hlabel : label site sign = label center sign := by
      rw [← hsite]
      cases sign
      · change (negative (center + shift) : ℝ) = (negative center : ℝ)
        exact_mod_cast hneg shift hspan center
      · change (positive (center + shift) : ℝ) = (positive center : ℝ)
        exact_mod_cast hpos shift hspan center
    have hrowShift (q : PotentialParameters deck) : inputDifference hdet k q site sign =
        inputDifference hdet k q center sign := by
      rw [← hsite, inputDifference_add_period hdet k q hspan (hphase shift hspan)]
    have heq : allowance site sign = allowance center sign := by
      simp only [allowance, label, row, δ] at hlabel ⊢
      rw [hrowShift, hrowShift, hlabel]
    rw [heq]
    exact hmin (center, sign) (Finset.mem_product.mpr ⟨hc, Finset.mem_univ _⟩)
  have hperturb (t : ℝ) (ht : |t| ≤ ε) : param + t • direction ∈ feasiblePotentialParameters hdet k negative positive := by
    have hbound (site : Site) (sign : Bool) : inputDifference hdet k (param + t • direction) site sign ≤ label site sign := by
      rw [inputDifference_add_smul]
      change row site sign + t * δ site sign ≤ label site sign
      by_cases h : row site sign = label site sign
      · have hd := htight site sign h
        rw [h, show δ site sign = 0 from hd, mul_zero, add_zero]
      · have ha := ht.trans (hall site sign)
        change |t| ≤ allowance site sign at ha
        simp only [allowance, if_neg h] at ha
        have hm := (le_div_iff₀ (by positivity : 0 < |δ site sign| + 1)).mp ha
        have habs := le_abs_self (t * δ site sign)
        rw [abs_mul] at habs
        linarith only [hm, habs, abs_nonneg t]
    change evaluatePotential hdet (param + t • direction) 0 = 0 ∧ SatisfiesInputLabels k negative positive
      (evaluatePotential hdet (param + t • direction))
    exact ⟨by rw [evaluatePotential_add_smul, hparam.1, hzero, mul_zero, add_zero], fun site =>
      ⟨hbound site false, hbound site true⟩⟩
  have hplus := hmax (hperturb ε (by rw [abs_of_pos hε]))
  have hminus := hmax (hperturb (-ε) (by rw [abs_neg, abs_of_pos hε]))
  change energy (param + ε • direction) ≤ energy param at hplus
  change energy (param + (-ε) • direction) ≤ energy param at hminus
  have hpositive : 0 < 2 * ε ^ 2 * energy direction := by positivity [energy_pos_of_ne_zero hdir, hε]
  linarith only [energy_add_pair param direction ε, hpositive, hplus, hminus]

end FLatticePaper.GeneralK
