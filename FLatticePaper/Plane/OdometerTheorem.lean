import FLatticePaper.Plane.AlternatePeriods
import FLatticePaper.Plane.PeriodCocycle
import FLatticePaper.Plane.QuadraticGrowth
import FLatticePaper.Plane.Recurrence
import FLatticePaper.Construction.AlternateLadderRank
import FLatticePaper.Construction.AlternateLadderRotation
import FLatticePaper.Construction.AlternateStaircaseExtension
import FLatticePaper.Construction.AlternateStaircaseRank
import FLatticePaper.Construction.AlternateStaircaseRecurrence
import FLatticePaper.Construction.AlternateStaircaseRotation
import FLatticePaper.Construction.LadderRank
import FLatticePaper.Construction.LadderRotation
import FLatticePaper.Construction.StaircaseExtension
import FLatticePaper.Construction.StaircaseRank
import FLatticePaper.Construction.StaircaseRotation

namespace FLatticePaper

open Farey Construction
open scoped Matrix

/-- An odometer for the matrix of `fraction`: a recurrent integer superharmonic representative (line 51). -/
def IsOdometer (fraction : Fraction) (field : Field) : Prop :=
  Superharmonic field ∧ Recurrent field ∧ HasQuadraticGrowth field fraction.matrix

/-- `eq:periodicity`: for every `v ∈ L'(n,d)` there is a constant `c_v` with `g(x+v) = g(x) + xᵀ M v + c_v`. -/
def SatisfiesPeriodicity (fraction : Fraction) (field : Field) : Prop :=
  ∀ v ∈ fraction.modifiedDeck.span, ∃ c : ℤ, ∀ x : Site,
    (field (x + v) : ℝ) = field x + siteVector x ⬝ᵥ (fraction.matrix *ᵥ siteVector v) + c

/-- The conclusion of `theorem:odometers` at one fraction. -/
def OdometersTheoremAt (fraction : Fraction) : Prop :=
  ∃ standard alternate : Field,
    IsOdometer fraction standard ∧ IsOdometer fraction alternate ∧
    SatisfiesPeriodicity fraction standard ∧ SatisfiesPeriodicity fraction alternate ∧
    standard ≠ alternate ∧ ¬ IntegerAffine (fun x => alternate x - standard x)

/-- The generator identities give `eq:periodicity` on all of `L'(n,d)`. -/
theorem satisfiesPeriodicity_of_generatorPeriods {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {field : Field} {constantU constantV : ℤ} (h : HasGeneratorPeriods fraction field constantU constantV) :
    SatisfiesPeriodicity fraction field :=
  generator_periods_affine hinterval h

/-- A non-affine difference forces the two fields to be distinct, since the zero difference is affine. -/
private theorem ne_of_not_integerAffine_sub {standard alternate : Field}
    (h : ¬ IntegerAffine (fun x => alternate x - standard x)) : standard ≠ alternate := by
  rintro rfl
  exact h ⟨0, 0, fun x => by simp⟩

private theorem odometersTheoremAt_of_pair {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {standard alternate : Field} {standardU standardV alternateU alternateV : ℤ}
    (hstandard : IsOdometer fraction standard) (halternate : IsOdometer fraction alternate)
    (hperiodStandard : HasGeneratorPeriods fraction standard standardU standardV)
    (hperiodAlternate : HasGeneratorPeriods fraction alternate alternateU alternateV)
    (hdistinct : ¬ IntegerAffine (fun x => alternate x - standard x)) :
    OdometersTheoremAt fraction :=
  ⟨standard, alternate, hstandard, halternate,
    satisfiesPeriodicity_of_generatorPeriods hinterval hperiodStandard,
    satisfiesPeriodicity_of_generatorPeriods hinterval hperiodAlternate,
    ne_of_not_integerAffine_sub hdistinct, hdistinct⟩

/-- The standard and alternate B1/B3 fields of the odd staircase, with the alternate built from
the standard field, so that the distinctness theorem applies to the same pair. -/
private theorem stairEvenPair {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) :
    ∃ standard : Field,
      IsOdometer (Fraction.mk 1 den) standard ∧
      HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den) ∧
      IsOdometer (Fraction.mk 1 den) (stairEvenAltField den standard) ∧
      HasGeneratorPeriods (Fraction.mk 1 den) (stairEvenAltField den standard) 0 (stairEvenConstantV den - 1) := by
  obtain ⟨standard, hagree, hperiod, hgrowth⟩ := stairEven_exists_extension hden
  obtain ⟨_, _, _, hrankStandard⟩ := stairEven_exists_burningRank hden hagree hperiod
  obtain ⟨_, _, _, hrankAlternate⟩ := stairEvenAlt_exists_burningRank hden hagree hperiod
  have hinterval : (Fraction.mk 1 den).InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  have halt := stairEvenAltField_periods hperiod
  exact ⟨standard, ⟨hrankStandard.superharmonic, hrankStandard.recurrent, hgrowth⟩, hperiod,
    ⟨hrankAlternate.superharmonic, hrankAlternate.recurrent,
      generator_periods_growth hinterval halt⟩, halt⟩

/-- The base fractions `1/d` and `R(1/d)` for odd `d ≥ 3`, from the staircase families. -/
private theorem odd_base {d : ℤ} (hd : 3 ≤ d) (hodd : d % 2 = 1) :
    OdometersTheoremAt ⟨1, d⟩ ∧ OdometersTheoremAt (Fraction.rotate ⟨1, d⟩) := by
  have hstairEven : BaseMask.stairEven.Valid d := show 3 ≤ d ∧ d % 2 = 1 from ⟨hd, hodd⟩
  have hstairEvenAlt : BaseMask.stairEvenAlt.Valid d := show 3 ≤ d ∧ d % 2 = 1 from ⟨hd, hodd⟩
  have hstairOdd : BaseMask.stairOdd.Valid d := show 3 ≤ d ∧ d % 2 = 1 from ⟨hd, hodd⟩
  have hstairOddAlt : BaseMask.stairOddAlt.Valid d := show 3 ≤ d ∧ d % 2 = 1 from ⟨hd, hodd⟩
  have hinterval : (Fraction.mk 1 d).InUnitInterval := by
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  constructor
  · obtain ⟨standard, hstd, hstdPeriods, halt, haltPeriods⟩ := stairEvenPair hstairEvenAlt
    exact odometersTheoremAt_of_pair hinterval hstd halt hstdPeriods haltPeriods
      (stairEvenAltField_sub_standard_not_integerAffine hodd hstdPeriods)
  · obtain ⟨standard, _, hstdPeriods, hstdGrowth, hstdSuper, hstdRec⟩ :=
      stairOdd_exists_recurrent_extension hstairOdd
    obtain ⟨alternate, _, haltPeriods, haltGrowth, haltSuper, haltRec⟩ :=
      stairOddAlt_exists_recurrent_extension hstairOddAlt
    exact odometersTheoremAt_of_pair (staircase_rotate_inUnitInterval hd hodd)
      ⟨hstdSuper, hstdRec, hstdGrowth⟩ ⟨haltSuper, haltRec, haltGrowth⟩ hstdPeriods haltPeriods
      (stairOddAlt_sub_standard_not_integerAffine hodd hstdPeriods haltPeriods)

/-- The base fractions `1/d` and `R(1/d)` for even `d ≥ 4`, from the ladder families. -/
private theorem even_base {d : ℤ} (hd : 4 ≤ d) (heven : d % 2 = 0) :
    OdometersTheoremAt ⟨1, d⟩ ∧ OdometersTheoremAt (Fraction.rotate ⟨1, d⟩) := by
  have hladderOdd : BaseMask.ladderOdd.Valid d := show 4 ≤ d ∧ d % 2 = 0 from ⟨hd, heven⟩
  have hladderOddAlt : BaseMask.ladderOddAlt.Valid d := show 4 ≤ d ∧ d % 2 = 0 from ⟨hd, heven⟩
  have hladderEven : BaseMask.ladderEven.Valid d := show 4 ≤ d ∧ d % 2 = 0 from ⟨hd, heven⟩
  have hladderEvenAlt : BaseMask.ladderEvenAlt.Valid d := show 4 ≤ d ∧ d % 2 = 0 from ⟨hd, heven⟩
  have hinterval : (Fraction.mk 1 d).InUnitInterval := by
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  constructor
  · obtain ⟨standard, _, hstdPeriods, hstdGrowth, hstdSuper, hstdRec⟩ :=
      ladderOdd_exists_recurrent_extension hladderOdd
    obtain ⟨alternate, _, haltPeriods, haltGrowth, haltSuper, haltRec⟩ :=
      ladderOddAlt_exists_recurrent_extension hladderOddAlt
    exact odometersTheoremAt_of_pair hinterval ⟨hstdSuper, hstdRec, hstdGrowth⟩
      ⟨haltSuper, haltRec, haltGrowth⟩ hstdPeriods haltPeriods
      (ladderOddAlt_sub_standard_not_integerAffine heven hstdPeriods haltPeriods)
  · obtain ⟨standard, _, hstdPeriods, hstdGrowth, hstdSuper, hstdRec⟩ :=
      ladderEven_exists_recurrent_extension hladderEven
    obtain ⟨alternate, _, haltPeriods, haltGrowth, haltSuper, haltRec⟩ :=
      ladderEvenAlt_exists_recurrent_extension hladderEvenAlt
    exact odometersTheoremAt_of_pair (ladder_rotate_inUnitInterval hd heven)
      ⟨hstdSuper, hstdRec, hstdGrowth⟩ ⟨haltSuper, haltRec, haltGrowth⟩ hstdPeriods haltPeriods
      (ladderEvenAlt_sub_standard_not_integerAffine heven hstdPeriods haltPeriods)

/-- `theorem:odometers` for the base fractions of Section 6: `1/d` and `R(1/d)` for every `d ≥ 3`. -/
theorem odometersTheoremAt_base {d : ℤ} (hd : 3 ≤ d) :
    OdometersTheoremAt ⟨1, d⟩ ∧ OdometersTheoremAt (Fraction.rotate ⟨1, d⟩) := by
  rcases (by omega : d % 2 = 0 ∨ d % 2 = 1) with heven | hodd
  · exact even_base (by omega) heven
  · exact odd_base hd hodd

end FLatticePaper
