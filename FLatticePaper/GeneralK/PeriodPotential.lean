import FLatticePaper.GeneralK.Classification

namespace FLatticePaper.GeneralK

open Farey

/-- The two real difference constraints from each physical center to its inputs. -/
def SatisfiesInputLabels (k : ℤ) (negative positive : Field) (potential : Site → ℝ) : Prop :=
  ∀ site, potential (incomingNeg k site) - potential site ≤ (negative site : ℝ) ∧
    potential (incomingPos k site) - potential site ≤ (positive site : ℝ)

/-- An affine increment on every shift in the prescribed period deck. -/
def HasDeckSlope (deck : PeriodDeck) (potential : Site → ℝ) (slopeX slopeY : ℝ) : Prop :=
  ∀ step ∈ deck.span, ∀ site,
    potential (site + step) = potential site + (slopeX * (step.1 : ℝ) + slopeY * (step.2 : ℝ))

/-- The finite difference-constraint assertion needed in rational period
realization. A feasible real drift can be chosen with integer deck increments. -/
def IntegralInputPotentials (k : ℤ) : Prop :=
  ∀ deck : PeriodDeck, deck.det ≠ 0 → (∀ step ∈ deck.span, Retained k step) →
    ∀ negative positive : Field,
      (∀ step ∈ deck.span, Function.Periodic negative step) →
      (∀ step ∈ deck.span, Function.Periodic positive step) →
      (∃ (potential : Site → ℝ) (slopeX slopeY : ℝ),
        SatisfiesInputLabels k negative positive potential ∧ HasDeckSlope deck potential slopeX slopeY) →
      ∃ (potential : Site → ℝ) (slopeX slopeY : ℚ),
        SatisfiesInputLabels k negative positive potential ∧ HasDeckSlope deck potential (slopeX : ℝ) (slopeY : ℝ) ∧
        ∀ step ∈ deck.span, ∃ increment : ℤ,
          (slopeX : ℝ) * (step.1 : ℝ) + (slopeY : ℝ) * (step.2 : ℝ) = (increment : ℝ)

theorem bounded_of_periodic_on_deck {deck : PeriodDeck} (hdet : deck.det ≠ 0) {field : Site → ℝ}
    (hperiod : ∀ step ∈ deck.span, Function.Periodic field step) : ∃ bound : ℝ, ∀ site, |field site| ≤ bound := by
  let box := (Finset.Ico (0 : ℤ) (deck.det.natAbs : ℤ)).product (Finset.Ico 0 (deck.det.natAbs : ℤ))
  have hpos : 0 < (deck.det.natAbs : ℤ) := by exact_mod_cast (Int.natAbs_pos.mpr hdet)
  have hzero : (0 : Site) ∈ box := Finset.mem_product.mpr
    ⟨Finset.mem_Ico.mpr ⟨le_rfl, hpos⟩, Finset.mem_Ico.mpr ⟨le_rfl, hpos⟩⟩
  obtain ⟨largest, -, hmax⟩ := box.exists_max_image (fun site => |field site|) ⟨0, hzero⟩
  refine ⟨|field largest|, fun site => ?_⟩
  let point : Site := (site.1 % deck.det, site.2 % deck.det)
  have hpoint : point ∈ box := Finset.mem_product.mpr
    ⟨Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hdet, Int.emod_lt _ hdet⟩,
      Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hdet, Int.emod_lt _ hdet⟩⟩
  have hspan : site - point ∈ deck.span := by
    apply (deck.mem_span_iff_dvd hdet _).mpr
    have hx : deck.det ∣ site.1 - site.1 % deck.det := Int.dvd_self_sub_emod
    have hy : deck.det ∣ site.2 - site.2 % deck.det := Int.dvd_self_sub_emod
    exact ⟨Int.dvd_sub (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right hy _),
      Int.dvd_sub (dvd_mul_of_dvd_right hy _) (dvd_mul_of_dvd_right hx _)⟩
  have h := hperiod (site - point) hspan point
  rw [add_comm point (site - point), sub_add_cancel] at h
  rw [h]
  exact hmax point hpoint

private theorem floor_sub_le_of_sub_le {u v : ℝ} {label : ℤ} (h : u - v ≤ (label : ℝ)) :
    ⌊u⌋ - ⌊v⌋ ≤ label := by
  have hr := Int.floor_mono (show u ≤ v + (label : ℝ) by linarith only [h])
  rw [Int.floor_add_intCast] at hr
  omega

/-- A feasible integral deck slope for the periodic ceiling labels gives the
source's superharmonic representative with bounded periodic remainder. -/
theorem rationalPeriodRealization_of_integralInputPotentials {k : ℤ} (hk : 2 ≤ k)
    (hsolve : IntegralInputPotentials k) : RationalPeriodRealization k := by
  intro a b c hadmit deck hdet hphase hkernel htransverse
  obtain ⟨baseX, baseY, hpoly⟩ := exists_rationalReferencePolynomial deck hdet hkernel htransverse
  let reference := rationalFloorReference a b c baseX baseY
  have href : ∀ step ∈ deck.span, ∃ sx sy c₀ : ℤ, ∀ site,
      reference (site + step) = reference site + sx * site.1 + sy * site.2 + c₀ := by
    intro step hstep
    obtain ⟨sx, sy, c₀, h⟩ := hpoly step hstep
    refine ⟨sx, sy, c₀, fun site => ?_⟩
    simp only [reference, rationalFloorReference, h site, Int.floor_add_intCast, ← add_assoc]
  obtain ⟨initialX, initialY, initial, hdrift, -, hcap⟩ :=
    exists_periodicEnvelope_of_reference hk hadmit deck hphase baseX baseY href
  let negative : Field := fun site => ⌈initial (incomingNeg k site) - initial site⌉
  let positive : Field := fun site => ⌈initial (incomingPos k site) - initial site⌉
  have hneg : ∀ step ∈ deck.span, Function.Periodic negative step := fun step hstep site =>
    (ceilEnvelope_input_periodic (hphase step hstep) (hdrift step hstep) site).1
  have hpos : ∀ step ∈ deck.span, Function.Periodic positive step := fun step hstep site =>
    (ceilEnvelope_input_periodic (hphase step hstep) (hdrift step hstep) site).2
  have hfeas : SatisfiesInputLabels k negative positive initial := fun site => ⟨Int.le_ceil _, Int.le_ceil _⟩
  obtain ⟨potential, slopeX, slopeY, hlabels, hslope, hinteger⟩ := hsolve deck hdet hphase negative positive hneg hpos
    ⟨initial, initialX, initialY, hfeas, hdrift⟩
  let height : Field := fun site => reference site + ⌊potential site⌋
  have hsuper : Superharmonic k height := by
    intro site
    have hn := floor_sub_le_of_sub_le (hlabels site).1
    have hp := floor_sub_le_of_sub_le (hlabels site).2
    have hc := hcap site
    change negative site + positive site ≤ -laplacian k reference site at hc
    simp only [laplacian, height] at hc ⊢
    omega
  let polynomial := rationalReferencePolynomial a b c baseX baseY
  let rem (site : Site) := (height site : ℝ) - (polynomial site : ℝ) -
    ((slopeX : ℝ) * (site.1 : ℝ) + (slopeY : ℝ) * (site.2 : ℝ))
  have hper : ∀ step ∈ deck.span, Function.Periodic rem step := by
    intro step hstep site
    have ⟨inc, hinc⟩ := hinteger step hstep
    obtain ⟨u, v, d, hQ⟩ := hpoly step hstep
    have hR' : reference (site + step) = reference site + (u * site.1 + v * site.2 + d) := by
      simp only [reference, rationalFloorReference, hQ site, Int.floor_add_intCast]
    have hp := hslope step hstep site
    rw [hinc] at hp
    dsimp only [rem, height, polynomial]
    rw [hR', hQ site, hp, Int.floor_add_intCast]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_intCast, Int.cast_add, Int.cast_mul, Prod.fst_add, Prod.snd_add]
    linarith only [hinc]
  obtain ⟨bound, hb⟩ := bounded_of_periodic_on_deck hdet hper
  refine ⟨height, baseX + slopeX, baseY + slopeY, rem, bound, hsuper, fun site => ?_, hb, hper⟩
  obtain ⟨x, y⟩ := site
  simp only [rem, polynomial, rationalReferencePolynomial, ratQuadratic, matrixQuadratic_symmetricMatrix,
    Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat]
  ring

end FLatticePaper.GeneralK
