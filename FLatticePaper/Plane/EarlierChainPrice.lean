import FLatticePaper.Construction.QuarterTurnCorrection
import FLatticePaper.Farey.EarlierChain

namespace FLatticePaper

open Farey Construction

/-- The displacement `Vq + ε Uq` of the consumed even parent. -/
def consumedEvenShift (parent : Fraction) (orientation : ℤ) : Site :=
  parent.unmodifiedDeck.combine orientation 1

/-- The correction price of the odd donor in the coordinates of its field. -/
def donorPrice (donor : Field) (evenParent : Fraction) (orientation constant : ℤ) (site : Site) : ℤ :=
  donor (site - consumedEvenShift evenParent orientation) - donor site - evenParent.transverseGrade site + constant

/-- The earlier chain price with the actual signed slip and linear term. -/
def earlierChainPrice (earlier : Field) (oddParent : Fraction) (oldOrientation orientation : ℤ) (site : Site) : ℤ :=
  earlier site - earlier (site + earlierChainShift oddParent oldOrientation orientation) +
    oldOrientation * oddParent.transverseGrade site

private theorem period_increment_sub_origin {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {field : Field} {constantU constantV : ℤ}
    (hperiod : HasGeneratorPeriods fraction field constantU constantV)
    (start site : Site) (kernel transverse : ℤ) :
    let period := fraction.modifiedDeck.combine kernel transverse
    field (site + start + period) - field (site + start) - (field (start + period) - field start) =
      -transverse * fraction.transverseGrade site := by
  have hsite := generator_period_formula hinterval hperiod (site + start) kernel transverse
  have hstart := generator_period_formula hinterval hperiod start kernel transverse
  have hgrade : fraction.transverseGrade (site + start) =
      fraction.transverseGrade site + fraction.transverseGrade start := by
    dsimp [Fraction.transverseGrade]
    ring
  rw [hgrade, Int.cast_add] at hsite
  exact_mod_cast (by linear_combination hsite - hstart :
    ((field (site + start + fraction.modifiedDeck.combine kernel transverse) : ℝ) -
        field (site + start) - (field (start + fraction.modifiedDeck.combine kernel transverse) - (field start : ℝ))) =
      -(transverse : ℝ) * (fraction.transverseGrade site : ℝ))

/-- For the actual trailing-run parents, the donor price plus the earlier
chain price in the rotated chart is one constant on the whole plane.
The earlier field must have its physical deck jet and the odd donor must
be its authentic harmonically corrected quarter-turn. -/
theorem donorPrice_add_earlierChainPrice (origin : Word) (replaceEven : Bool) (steps : ℕ)
    (earlierField donorField : Field) (constantU constantV constant : ℤ)
    (hperiod : HasGeneratorPeriods ((parentsAt (origin.map Digit.swapTwoThree)).current .even)
      earlierField constantU constantV)
    (hrotate : ∀ site, donorField site = earlierField (QuarterTurn.counterclockwise.mapSite (0, -1) site) +
      centeredQuarterTurnCorrection site) :
    let old := parentsAt origin
    let current := parentsAt (donorWord origin replaceEven steps)
    let earlier := parentsAt (origin.map Digit.swapTwoThree)
    let orientation := current.odd.det current.even
    let oldOrientation := old.odd.det old.even
    ∃ value : ℤ, ∀ site,
      donorPrice donorField current.even orientation constant site +
        earlierChainPrice earlierField earlier.odd oldOrientation orientation
          (QuarterTurn.counterclockwise.mapSite (0, -1) site) = value := by
  let old := parentsAt origin
  let current := parentsAt (donorWord origin replaceEven steps)
  let earlier := parentsAt (origin.map Digit.swapTwoThree)
  let orientation := current.odd.det current.even
  let oldOrientation := old.odd.det old.even
  let e := consumedEvenShift current.even orientation
  let w := earlierChainShift earlier.odd oldOrientation orientation
  let rotatedDonor := earlier.current .even
  let z := QuarterTurn.counterclockwise.mapSite (0, -1)
  let transverse := -orientation * ((steps : ℤ) + if replaceEven then 1 else 0)
  obtain ⟨kernel, hshift⟩ := earlierChain_shift_eq_modified origin replaceEven steps
  let period := rotatedDonor.modifiedDeck.combine kernel transverse
  change rotatedTransverseShift current.even orientation = w + period at hshift
  have hz (site : Site) : z (site - e) = z site + w + period := by
    rw [add_assoc, ← hshift]
    apply Prod.ext <;>
      dsimp [z, QuarterTurn.mapSite, QuarterTurn.turn, e, consumedEvenShift, Fraction.unmodifiedDeck,
        PeriodDeck.combine, rotatedTransverseShift] <;> ring
  have heven : EvenSite (-e) := by
    have hp : (current.even.num + current.even.den) % 2 = 0 := (parentsAt_valid _).even_parity
    dsimp [EvenSite, e, consumedEvenShift, Fraction.unmodifiedDeck, PeriodDeck.combine]
    rcases (parentsAt_valid (donorWord origin replaceEven steps)).unit_det with hs | hs
    · change orientation = 1 at hs
      rw [hs]
      omega
    · change orientation = -1 at hs
      rw [hs]
      omega
  obtain ⟨hgradDen, hgradNum⟩ := earlierChain_signed_gradient origin replaceEven steps
  have hgradX : orientation * (current.even.den + current.even.num) - 2 * oldOrientation * earlier.odd.den =
      -2 * transverse * rotatedDonor.den := by
    rw [show -2 * transverse * rotatedDonor.den =
      2 * orientation * ((steps : ℤ) + if replaceEven then 1 else 0) * rotatedDonor.den by dsimp [transverse]; ring]
    exact hgradDen
  have hgradY : orientation * (current.even.den - current.even.num) - 2 * oldOrientation * earlier.odd.num =
      -2 * transverse * rotatedDonor.num := by
    rw [show -2 * transverse * rotatedDonor.num =
      2 * orientation * ((steps : ℤ) + if replaceEven then 1 else 0) * rotatedDonor.num by dsimp [transverse]; ring]
    exact hgradNum
  have hinterval : rotatedDonor.InUnitInterval :=
    (Birth.interior (origin.map Digit.swapTwoThree, .even)).inUnitInterval
  have hperiodAt := period_increment_sub_origin hinterval hperiod w
  let c := earlierField (w + period) - earlierField w
  refine ⟨c + centeredQuarterTurnCorrection (-e) + constant - transverse * rotatedDonor.transverseGrade (z 0) +
    oldOrientation * earlier.odd.transverseGrade (z 0), ?_⟩
  intro site
  change donorPrice donorField current.even orientation constant site +
    earlierChainPrice earlierField earlier.odd oldOrientation orientation (z site) = _
  unfold donorPrice earlierChainPrice
  change donorField (site - e) - donorField site - current.even.transverseGrade site + constant +
    (earlierField (z site) - earlierField (z site + w) + oldOrientation * earlier.odd.transverseGrade (z site)) = _
  change ∀ site, donorField site = earlierField (z site) + centeredQuarterTurnCorrection site at hrotate
  rw [hrotate, hrotate, hz]
  have hc := hperiodAt (z site) kernel transverse
  change earlierField (z site + w + period) - earlierField (z site + w) - c = _ at hc
  have hcorrection := centeredQuarterTurnCorrection_add site heven
  rw [← sub_eq_add_neg] at hcorrection
  have hp : ((-e).1 + (-e).2) % 2 = 0 := heven
  have hsum : 2 * (((-e).1 + (-e).2) / 2) =
      -2 * current.even.num - orientation * (current.even.den + current.even.num) := calc
    _ = (-e).1 + (-e).2 := by omega
    _ = _ := by dsimp [e, consumedEvenShift, Fraction.unmodifiedDeck, PeriodDeck.combine]; ring
  have hdiff : 2 * (((-e).1 - (-e).2) / 2) =
      2 * current.even.den - orientation * (current.even.den - current.even.num) := calc
    _ = (-e).1 - (-e).2 := by omega
    _ = _ := by dsimp [e, consumedEvenShift, Fraction.unmodifiedDeck, PeriodDeck.combine]; ring
  apply (mul_right_inj' (show (2 : ℤ) ≠ 0 by decide)).mp
  dsimp only [z, QuarterTurn.mapSite, QuarterTurn.turn, Fraction.transverseGrade] at hc ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at hc ⊢
  linear_combination 2 * hc + 2 * hcorrection + site.1 * (hsum - hgradX) + site.2 * (hdiff - hgradY)

end FLatticePaper
