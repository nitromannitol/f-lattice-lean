import FLatticePaper.MainTheorems

/-!
# Comparator challenge: the hyperbola (`theorem:hyperbola`)

The statement of `FLatticePaper.hyperbola_of_odometersTheorem`, with the odometers theorem as an explicit hypothesis. The
only `sorry` is the proof of `FLatticeAudit.hyperbola`, which the solution module supplies.
-/

namespace FLatticeAudit

open FLatticePaper

theorem hyperbola :
    ∀ (h : OdometersTheorem) (t : ℝ), 0 ≤ t → t ≤ 1 →
      symmetricCircleMatrix t (1 - t) (-Real.sqrt (t ^ 2 + (1 - t) ^ 2)) ∈ frontier symmetricGrowthSet := by
  sorry

end FLatticeAudit
