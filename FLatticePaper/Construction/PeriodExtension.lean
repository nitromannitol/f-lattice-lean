import FLatticePaper.Construction.OrderedOverlap
import FLatticePaper.Plane.PeriodCocycle

namespace FLatticePaper.Construction

open Farey

/-- The integer binomial polynomial, also at negative indices. -/
def chooseTwo (index : ℤ) : ℤ := index * (index - 1) / 2

theorem two_mul_chooseTwo (index : ℤ) : 2 * chooseTwo index = index * (index - 1) := by
  have heven : (index * (index - 1)) % 2 = 0 := by
    rw [Int.mul_emod]
    by_cases h : index % 2 = 0
    · simp [h]
    · have hprev : (index - 1) % 2 = 0 := by omega
      simp [hprev]
  unfold chooseTwo
  omega

theorem chooseTwo_add (first second : ℤ) :
    chooseTwo (first + second) = chooseTwo first + chooseTwo second + first * second := by
  apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide)
  linear_combination two_mul_chooseTwo (first + second) - two_mul_chooseTwo first - two_mul_chooseTwo second

/-- The prescribed integral height increment over an indexed deck translation. -/
def periodIncrement (fraction : Fraction) (constantU constantV : ℤ) (site : Site)
    (kernelIndex transverseIndex : ℤ) : ℤ :=
  kernelIndex * constantU + transverseIndex * (constantV - fraction.transverseGrade site) -
    fraction.periodDenominator * chooseTwo transverseIndex

private theorem combine_add (deck : PeriodDeck) (i j i' j' : ℤ) :
    deck.combine (i + i') (j + j') = deck.combine i j + deck.combine i' j' := by
  apply Prod.ext <;> simp only [PeriodDeck.combine, Prod.fst_add, Prod.snd_add] <;> ring

private theorem grade_add_combine (fraction : Fraction) (site : Site) (i j : ℤ) :
    fraction.transverseGrade (site + fraction.modifiedDeck.combine i j) =
      fraction.transverseGrade site + fraction.periodDenominator * j := by
  have hgrade : fraction.transverseGrade (fraction.modifiedDeck.combine i j) =
      fraction.periodDenominator * j := by
    rw [Fraction.modifiedDeck_combine, Fraction.transverseGrade_combine]
  rw [← hgrade]
  simp only [Fraction.transverseGrade, Prod.fst_add, Prod.snd_add]
  ring

theorem periodIncrement_add (fraction : Fraction) (constantU constantV : ℤ) (site : Site)
    (i j i' j' : ℤ) :
    periodIncrement fraction constantU constantV site (i + i') (j + j') =
      periodIncrement fraction constantU constantV site i j +
      periodIncrement fraction constantU constantV (site + fraction.modifiedDeck.combine i j) i' j' := by
  unfold periodIncrement
  rw [chooseTwo_add, grade_add_combine]
  ring

/-- Height compatibility on every pair of occupied sites in the same period class. -/
def HeightTile.RespectsPeriods (tile : HeightTile Site) (fraction : Fraction)
    (constantU constantV : ℤ) : Prop :=
  ∀ (first second : tile.sites) (i j : ℤ),
    second.val = first.val + fraction.modifiedDeck.combine i j →
    tile.height second = tile.height first + periodIncrement fraction constantU constantV first.val i j

/-- The height law on the occupied overlaps and coverage of the actual period
classes give an integer plane field agreeing with the tile. -/
theorem HeightTile.exists_extension_of_respectsPeriods {tile : HeightTile Site} {fraction : Fraction}
    {constantU constantV : ℤ} (hcover : fraction.modifiedDeck.Covers tile.sites)
    (hcompat : tile.RespectsPeriods fraction constantU constantV) :
    ∃ field : Field, tile.Agrees field 0 ∧ HasGeneratorPeriods fraction field constantU constantV := by
  classical
  let deck := fraction.modifiedDeck
  choose point hmem hspan using hcover
  choose kernel transverse htranslate using hspan
  let representative (site : Site) : tile.sites := ⟨point site, hmem site⟩
  let field : Field := fun site => tile.height (representative site) +
    periodIncrement fraction constantU constantV (point site) (kernel site) (transverse site)
  have hchart (site : Site) : site = point site + deck.combine (kernel site) (transverse site) := by
    rw [← htranslate site]
    rw [add_comm, sub_add_cancel]
  have hvalue (first : tile.sites) (i j : ℤ) :
      field (first.val + deck.combine i j) =
        tile.height first + periodIncrement fraction constantU constantV first.val i j := by
    let site := first.val + deck.combine i j
    have hshift (k l : ℤ) : deck.combine (k - i) (l - j) + deck.combine i j = deck.combine k l := by
      rw [← combine_add, sub_add_cancel, sub_add_cancel]
    have hrepr : first.val = point site + deck.combine (kernel site - i) (transverse site - j) := by
      apply add_right_cancel (b := deck.combine i j)
      rw [add_assoc, hshift]
      exact hchart site
    have hheight := hcompat (representative site) first (kernel site - i) (transverse site - j) hrepr
    have hstep := periodIncrement_add fraction constantU constantV (point site)
      (kernel site - i) (transverse site - j) i j
    change tile.height first = tile.height (representative site) +
      periodIncrement fraction constantU constantV (point site) (kernel site - i) (transverse site - j)
      at hheight
    rw [sub_add_cancel, sub_add_cancel, ← hrepr] at hstep
    change field site = _
    rw [show field site = tile.height (representative site) +
      periodIncrement fraction constantU constantV (point site) (kernel site) (transverse site) from rfl,
      hstep, ← add_assoc, ← hheight]
  refine ⟨field, ?_, ?_⟩
  · intro first
    have h := hvalue first 0 0
    have hzero : deck.combine 0 0 = 0 := by apply Prod.ext <;> simp [PeriodDeck.combine]
    simpa [hzero, periodIncrement, chooseTwo] using h.symm
  · have hlaw (site : Site) (i j : ℤ) :
        field (site + deck.combine i j) = field site + periodIncrement fraction constantU constantV site i j := by
      have hdest : site + deck.combine i j =
          (representative site).val + deck.combine (kernel site + i) (transverse site + j) := by
        rw [combine_add, ← add_assoc]
        exact congrArg (· + deck.combine i j) (hchart site)
      rw [hdest, hvalue, periodIncrement_add, ← hchart site, ← add_assoc]
    constructor
    · intro site
      have h := hlaw site 1 0
      simpa [deck, PeriodDeck.combine, periodIncrement, chooseTwo] using h
    · intro site
      have h := hlaw site 0 1
      simp [deck, PeriodDeck.combine, periodIncrement, chooseTwo] at h
      linarith only [h]

end FLatticePaper.Construction
