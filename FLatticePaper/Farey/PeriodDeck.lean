import FLatticePaper.Farey.Recursion
import FLatticePaper.Graph
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

namespace FLatticePaper.Farey

/-- An ordered pair of integral period generators. -/
structure PeriodDeck where
  kernel : Site
  transverse : Site

namespace PeriodDeck

def det (deck : PeriodDeck) : ℤ :=
  deck.kernel.1 * deck.transverse.2 - deck.kernel.2 * deck.transverse.1

def combine (deck : PeriodDeck) (kernelIndex transverseIndex : ℤ) : Site :=
  (kernelIndex * deck.kernel.1 + transverseIndex * deck.transverse.1,
    kernelIndex * deck.kernel.2 + transverseIndex * deck.transverse.2)

def span (deck : PeriodDeck) : Set Site :=
  {site | ∃ kernelIndex transverseIndex : ℤ, site = deck.combine kernelIndex transverseIndex}

def kernelNumerator (deck : PeriodDeck) (site : Site) : ℤ :=
  deck.transverse.2 * site.1 - deck.transverse.1 * site.2

def transverseNumerator (deck : PeriodDeck) (site : Site) : ℤ :=
  deck.kernel.1 * site.2 - deck.kernel.2 * site.1

theorem kernelNumerator_combine (deck : PeriodDeck) (kernelIndex transverseIndex : ℤ) :
    deck.kernelNumerator (deck.combine kernelIndex transverseIndex) = deck.det * kernelIndex := by
  simp only [kernelNumerator, combine, det]
  ring

theorem transverseNumerator_combine (deck : PeriodDeck) (kernelIndex transverseIndex : ℤ) :
    deck.transverseNumerator (deck.combine kernelIndex transverseIndex) =
      deck.det * transverseIndex := by
  simp only [transverseNumerator, combine, det]
  ring

theorem det_mul_fst (deck : PeriodDeck) (site : Site) :
    deck.det * site.1 = (deck.combine (deck.kernelNumerator site) (deck.transverseNumerator site)).1 := by
  simp only [combine, kernelNumerator, transverseNumerator, det]
  ring

theorem det_mul_snd (deck : PeriodDeck) (site : Site) :
    deck.det * site.2 = (deck.combine (deck.kernelNumerator site) (deck.transverseNumerator site)).2 := by
  simp only [combine, kernelNumerator, transverseNumerator, det]
  ring

theorem mem_span_iff_dvd (deck : PeriodDeck) (hnonzero : deck.det ≠ 0) (site : Site) :
    site ∈ deck.span ↔
      deck.det ∣ deck.kernelNumerator site ∧ deck.det ∣ deck.transverseNumerator site := by
  constructor
  · rintro ⟨kernelIndex, transverseIndex, rfl⟩
    rw [kernelNumerator_combine, transverseNumerator_combine]
    exact ⟨⟨kernelIndex, rfl⟩, ⟨transverseIndex, rfl⟩⟩
  · rintro ⟨⟨kernelIndex, hk⟩, ⟨transverseIndex, ht⟩⟩
    refine ⟨kernelIndex, transverseIndex, Prod.ext ?_ ?_⟩
    · apply mul_left_cancel₀ hnonzero
      rw [det_mul_fst, hk, ht]
      simp only [combine]
      ring
    · apply mul_left_cancel₀ hnonzero
      rw [det_mul_snd, hk, ht]
      simp only [combine]
      ring

theorem combine_injective (deck : PeriodDeck) (hnonzero : deck.det ≠ 0)
    {firstKernel firstTransverse secondKernel secondTransverse : ℤ}
    (heq : deck.combine firstKernel firstTransverse =
      deck.combine secondKernel secondTransverse) :
    firstKernel = secondKernel ∧ firstTransverse = secondTransverse := by
  have hk := congrArg deck.kernelNumerator heq
  have ht := congrArg deck.transverseNumerator heq
  rw [kernelNumerator_combine, kernelNumerator_combine] at hk
  rw [transverseNumerator_combine, transverseNumerator_combine] at ht
  exact ⟨mul_left_cancel₀ hnonzero hk, mul_left_cancel₀ hnonzero ht⟩

/-- A complete invariant of a period class, using the two adjugate residues. -/
def classCode (deck : PeriodDeck) (site : Site) : ℤ × ℤ :=
  (deck.kernelNumerator site % deck.det, deck.transverseNumerator site % deck.det)

theorem classCode_eq_iff (deck : PeriodDeck) (hnonzero : deck.det ≠ 0) (first second : Site) :
    deck.classCode first = deck.classCode second ↔ first - second ∈ deck.span := by
  have hk : deck.kernelNumerator (first - second) =
      deck.kernelNumerator first - deck.kernelNumerator second := by
    dsimp [kernelNumerator]
    ring
  have ht : deck.transverseNumerator (first - second) =
      deck.transverseNumerator first - deck.transverseNumerator second := by
    dsimp [transverseNumerator]
    ring
  rw [mem_span_iff_dvd deck hnonzero, hk, ht]
  simp [classCode, Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.dvd_iff_emod_eq_zero]

/-- A finite superset of representatives, not necessarily one per class. -/
def residueSquare (deck : PeriodDeck) : Finset Site :=
  (Finset.Ico 0 deck.det).product (Finset.Ico 0 deck.det)

theorem exists_square_representative (deck : PeriodDeck) (hpos : 0 < deck.det) (site : Site) :
    ∃ representative ∈ deck.residueSquare,
      deck.classCode site = deck.classCode representative := by
  let representative : Site := (site.1 % deck.det, site.2 % deck.det)
  refine ⟨representative, ?_, ?_⟩
  · refine Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · exact Int.emod_nonneg _ (ne_of_gt hpos)
    · exact Int.emod_lt_of_pos _ hpos
    · exact Int.emod_nonneg _ (ne_of_gt hpos)
    · exact Int.emod_lt_of_pos _ hpos
  · apply (classCode_eq_iff deck (ne_of_gt hpos) _ _).mpr
    apply (mem_span_iff_dvd deck (ne_of_gt hpos) _).mpr
    have hfst : deck.det ∣ site.1 - site.1 % deck.det := Int.dvd_self_sub_emod
    have hsnd : deck.det ∣ site.2 - site.2 % deck.det := Int.dvd_self_sub_emod
    exact ⟨Int.dvd_sub (dvd_mul_of_dvd_right hfst _) (dvd_mul_of_dvd_right hsnd _),
      Int.dvd_sub (dvd_mul_of_dvd_right hsnd _) (dvd_mul_of_dvd_right hfst _)⟩

/-- Every site is a period translate of a site actually in the finite support. -/
def Covers (deck : PeriodDeck) (sites : Finset Site) : Prop :=
  ∀ site : Site, ∃ representative ∈ sites, site - representative ∈ deck.span

theorem covers_iff_square_codes_subset (deck : PeriodDeck) (hpos : 0 < deck.det)
    (sites : Finset Site) :
    deck.Covers sites ↔
      deck.residueSquare.image deck.classCode ⊆ sites.image deck.classCode := by
  constructor
  · intro h code hcode
    obtain ⟨point, _, rfl⟩ := Finset.mem_image.mp hcode
    obtain ⟨representative, hmem, hperiod⟩ := h point
    exact Finset.mem_image.mpr ⟨representative, hmem,
      ((deck.classCode_eq_iff (ne_of_gt hpos) _ _).mpr hperiod).symm⟩
  · intro h site
    obtain ⟨point, hpoint, heq⟩ := deck.exists_square_representative hpos site
    obtain ⟨representative, hmem, hcode⟩ :=
      Finset.mem_image.mp (h (Finset.mem_image_of_mem deck.classCode hpoint))
    exact ⟨representative, hmem, (deck.classCode_eq_iff (ne_of_gt hpos) _ _).mp (heq.trans hcode.symm)⟩

end PeriodDeck

def Fraction.periodDenominator (fraction : Fraction) : ℤ :=
  fraction.den ^ 2 + 2 * fraction.den * fraction.num - fraction.num ^ 2

theorem Fraction.periodDenominator_pos {fraction : Fraction} (h : fraction.InUnitInterval) :
    0 < fraction.periodDenominator := by
  obtain ⟨hden, hnum, hle⟩ := h
  unfold periodDenominator
  have hsum : 0 < fraction.den + fraction.num := by omega
  by_cases hlt : fraction.num < fraction.den
  · nlinarith [mul_pos (sub_pos.mpr hlt) hsum, mul_nonneg hden.le hnum]
  · nlinarith [mul_pos hden hden, show fraction.num = fraction.den by omega]

def Fraction.periodMultiplicity (fraction : Fraction) : ℤ :=
  if (fraction.num + fraction.den) % 2 = 0 then 1 else 2

def Fraction.unmodifiedDeck (fraction : Fraction) : PeriodDeck :=
  ⟨(fraction.den, fraction.num), (fraction.num - fraction.den, fraction.num + fraction.den)⟩

def Fraction.modifiedDeck (fraction : Fraction) : PeriodDeck :=
  let mu := fraction.periodMultiplicity
  ⟨(mu * fraction.den, mu * fraction.num), fraction.unmodifiedDeck.transverse⟩

theorem Fraction.det_unmodifiedDeck (fraction : Fraction) :
    fraction.unmodifiedDeck.det = fraction.periodDenominator := by
  dsimp [PeriodDeck.det, unmodifiedDeck, periodDenominator]
  ring

theorem Fraction.det_modifiedDeck (fraction : Fraction) :
    fraction.modifiedDeck.det = fraction.periodMultiplicity * fraction.periodDenominator := by
  dsimp [PeriodDeck.det, modifiedDeck, unmodifiedDeck, periodDenominator]
  ring

theorem Fraction.det_modifiedDeck_pos {fraction : Fraction} (h : fraction.InUnitInterval) :
    0 < fraction.modifiedDeck.det := by
  rw [det_modifiedDeck]
  apply mul_pos _ (periodDenominator_pos h)
  unfold periodMultiplicity
  split <;> decide

theorem Fraction.modifiedDeck_combine (fraction : Fraction) (kernelIndex transverseIndex : ℤ) :
    fraction.modifiedDeck.combine kernelIndex transverseIndex =
      fraction.unmodifiedDeck.combine (fraction.periodMultiplicity * kernelIndex) transverseIndex := by
  apply Prod.ext <;> simp only [PeriodDeck.combine, modifiedDeck, unmodifiedDeck] <;> ring

private theorem Fraction.unmodifiedDeck_combine_parity (fraction : Fraction)
    (kernelIndex transverseIndex : ℤ) :
    ((fraction.unmodifiedDeck.combine kernelIndex transverseIndex).1 +
      (fraction.unmodifiedDeck.combine kernelIndex transverseIndex).2) % 2 =
        (kernelIndex * (fraction.num + fraction.den)) % 2 := by
  rw [show (fraction.unmodifiedDeck.combine kernelIndex transverseIndex).1 +
      (fraction.unmodifiedDeck.combine kernelIndex transverseIndex).2 =
      kernelIndex * (fraction.num + fraction.den) + (transverseIndex * fraction.num) * 2 by
    dsimp [PeriodDeck.combine, unmodifiedDeck]
    ring, Int.add_mul_emod_self_right]

/-- Doubling the odd kernel gives exactly the parity-preserving periods. -/
theorem Fraction.mem_modifiedDeck_iff (fraction : Fraction) (site : Site) :
    site ∈ fraction.modifiedDeck.span ↔ site ∈ fraction.unmodifiedDeck.span ∧ EvenSite site := by
  constructor
  · rintro ⟨kernelIndex, transverseIndex, rfl⟩
    rw [modifiedDeck_combine]
    refine ⟨⟨_, _, rfl⟩, ?_⟩
    unfold EvenSite
    rw [unmodifiedDeck_combine_parity, periodMultiplicity, Int.mul_emod]
    split
    · simp_all
    · rw [Int.mul_emod 2 kernelIndex 2]
      simp
  · rintro ⟨⟨kernelIndex, transverseIndex, rfl⟩, heven⟩
    by_cases hparity : (fraction.num + fraction.den) % 2 = 0
    · refine ⟨kernelIndex, transverseIndex, ?_⟩
      simp [modifiedDeck_combine, periodMultiplicity, hparity]
    · have hodd : (fraction.num + fraction.den) % 2 = 1 := by omega
      unfold EvenSite at heven
      rw [unmodifiedDeck_combine_parity, Int.mul_emod, hodd, Int.mul_one, Int.emod_emod] at heven
      have hindex : kernelIndex = 2 * (kernelIndex / 2) := by omega
      refine ⟨kernelIndex / 2, transverseIndex, ?_⟩
      rw [modifiedDeck_combine, periodMultiplicity, if_neg hparity, ← hindex]

end FLatticePaper.Farey
