import FLatticePaper.MainTheorems

/-!
# Comparator challenge: circle packing (`theorem:circle_packing`)

The statement of `FLatticePaper.circlePacking_of_odometersTheorem`, with the odometers theorem as an explicit hypothesis.
The only `sorry` is the proof of `FLatticeAudit.circlePacking`, which the solution module supplies.
-/

namespace FLatticeAudit

open FLatticePaper

theorem circlePacking :
    ∀ (h : OdometersTheorem) (matrix : Matrix (Fin 2) (Fin 2) ℝ),
      matrix ∈ integerSuperharmonicMatrices ↔ ∃ s t : ℤ, (harmonicPeak s t - matrix).PosSemidef := by
  sorry

end FLatticeAudit
