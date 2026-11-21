import FLatticePaper.Plane.HyperbolaBoundary
import FLatticePaper.Plane.OdometerTheorem

/-! The two headline theorems from `theorem:odometers` at every reduced interior slope. -/

namespace FLatticePaper

open Farey

/-- `theorem:odometers` for every reduced fraction `0 < n/d < 1`. -/
def OdometersTheorem : Prop :=
  ∀ fraction : Fraction, fraction.Interior → fraction.Reduced → OdometersTheoremAt fraction

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

end FLatticePaper
