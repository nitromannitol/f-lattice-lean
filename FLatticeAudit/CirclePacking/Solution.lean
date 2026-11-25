import FLatticePaper.MainTheorems

/-!
# Solution: circle packing

Proves the statement of `FLatticeAudit/CirclePacking/Challenge.lean` from the repository's `circlePacking_of_odometersTheorem`.
-/

namespace FLatticeAudit

open FLatticePaper

theorem circlePacking :
    ∀ (h : OdometersTheorem) (matrix : Matrix (Fin 2) (Fin 2) ℝ),
      matrix ∈ integerSuperharmonicMatrices ↔ ∃ s t : ℤ, (harmonicPeak s t - matrix).PosSemidef :=
  fun h matrix => circlePacking_of_odometersTheorem h matrix

end FLatticeAudit
