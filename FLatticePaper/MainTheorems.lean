import FLatticePaper.Plane.HyperbolaBoundary
import FLatticePaper.Plane.OdometerTheorem
import FLatticePaper.Plane.OdometersStatement
import FLatticePaper.Plane.Induction.EvenStep
import FLatticePaper.Plane.Induction.OddStep

/-! The two headline theorems from `theorem:odometers` at every reduced interior slope. -/

namespace FLatticePaper

open Farey

private theorem recurrentInterior_of_odometersTheorem (h : OdometersTheorem) :
    ∀ fraction : Fraction, fraction.Interior → fraction.Reduced →
      ∃ height : Field, Superharmonic height ∧ Recurrent height ∧
        HasQuadraticGrowth height fraction.matrix := by
  intro fraction hinterior hreduced
  obtain ⟨standard, _, ⟨hsuper, hrec, hgrowth⟩, _⟩ := h fraction hinterior hreduced
  exact ⟨standard, hsuper, hrec, hgrowth⟩

/-- `theorem:hyperbola` from `theorem:odometers`. -/
theorem hyperbola_of_odometersTheorem (h : OdometersTheorem) (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1) :
    symmetricCircleMatrix t (1 - t) (-Real.sqrt (t ^ 2 + (1 - t) ^ 2)) ∈ frontier symmetricGrowthSet :=
  hyperbolaBoundary_of_recurrentInterior (recurrentInterior_of_odometersTheorem h) t ht hu

/-- `theorem:circle_packing` from `theorem:odometers`. -/
theorem circlePacking_of_odometersTheorem (h : OdometersTheorem) (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    matrix ∈ integerSuperharmonicMatrices ↔ ∃ s t : ℤ, (harmonicPeak s t - matrix).PosSemidef :=
  circlePacking_of_recurrentInterior (recurrentInterior_of_odometersTheorem h) matrix

/-- The Part I data of the standard field at the even child of a frame (used in `EvenStep`). -/
def Induction.ChildFrame.HasStandardData (frame : Induction.ChildFrame) : Prop :=
  ∃ F : Field, ∃ cU cV : ℤ, HasGeneratorPeriods frame.child F cU cV ∧
    HasUnitSlip F (fun z => F (z + frame.shortShift)) ∧
    NoEvenSlipSaddle F (fun z => F (z + frame.shortShift)) ∧
    ∃ rank : Site → ℤ, IsConstrainedBurningRank F rank
      (fun center input => slipIncrement F (fun z => F (z + frame.shortShift)) center input ≤ 0)

/-- All three headline results follow from the standard data at the even child of every word. -/
theorem odometersTheorem_of_standardData
    (h : ∀ word : Word, (⟨parentsAt word, parentsAt_valid word⟩ : Induction.ChildFrame).HasStandardData) :
    OdometersTheorem := by
  refine Induction.odometersTheorem_of_even ?_
  intro fraction hint hred heven
  obtain ⟨birth, hbirth, -⟩ := existsUnique_birth fraction hint hred
  obtain ⟨word, parity⟩ := birth
  have hparity : parity = Parity.even := by
    cases parity with
    | even => rfl
    | odd =>
      exfalso
      have hodd : fraction.Odd := by
        rw [← hbirth]
        exact (parentsAt_valid word).current_odd_parity
      unfold Fraction.Odd at hodd
      unfold Fraction.Even at heven
      omega
  subst hparity
  have hchild : (⟨parentsAt word, parentsAt_valid word⟩ : Induction.ChildFrame).child = fraction := hbirth
  obtain ⟨F, cU, cV, hper, hstep, hnoSaddle, rank, hrank⟩ := h word
  have key := Induction.ChildFrame.odometersTheoremAt_of_standard
    (⟨parentsAt word, parentsAt_valid word⟩ : Induction.ChildFrame) hper hstep hnoSaddle hrank
  rw [hchild] at key
  exact key

end FLatticePaper
